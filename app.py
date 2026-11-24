"""UPVAC - Plateforme de gestion de stock des vaccins (Flask + SQLite).

Lancement :  python app.py   puis ouvrir http://127.0.0.1:5000
"""
import math
import os
import re
import secrets
import smtplib
import sqlite3
import ssl
import sys
import threading
from io import BytesIO
from datetime import date, datetime, timedelta
from functools import wraps
from itertools import zip_longest

from flask import (Flask, abort, flash, g, redirect, render_template, request, send_file,
                   session, url_for)
from email.message import EmailMessage
from email.utils import formataddr
from jinja2 import DictLoader
from markupsafe import Markup
from werkzeug.security import check_password_hash, generate_password_hash

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(BASE_DIR, "upvac.db")

app = Flask(__name__)


def _charger_cle_secrete():
    """Clé de session : variable UPVAC_SECRET, sinon fichier secret.key généré une seule fois."""
    cle = os.environ.get("UPVAC_SECRET")
    if cle:
        return cle
    chemin = os.path.join(BASE_DIR, "secret.key")
    if not os.path.exists(chemin):
        with open(chemin, "w") as f:
            f.write(os.urandom(32).hex())
    with open(chemin) as f:
        return f.read().strip()


app.secret_key = _charger_cle_secrete()
app.config.update(SESSION_COOKIE_HTTPONLY=True, SESSION_COOKIE_SAMESITE="Lax")

# Informations affichées sur le bon de vente (à compléter / adapter)
ENTREPRISE_NOM = "ISRA - Productions"
ENTREPRISE_ADRESSE = "Route du Front de Terre, BP 2057 LNERV Hann"
ENTREPRISE_TEL = "33 832 27 62"
ENTREPRISE_EMAIL = ""     # ex. "contact@exemple.sn"
DEVISE = "FCFA"

# Paramètres métier
SEUILS_PEREMPTION = (30, 60, 90)  # alertes en jours
STATUTS = ("conforme", "quarantaine", "rappelé", "périmé", "détruit")
STATUTS_COMMANDE = ("enregistrée", "transmise", "facturée", "validée", "livrée", "archivée", "annulée")
ORDRE_CIRCUIT = ("enregistrée", "transmise", "facturée", "validée", "livrée", "archivée")
# Les étapes du circuit de vente (libellé, acteur). Le Directeur n'intervient pas : le CSA valide la vente.
ETAPES = (("Commande saisie", "Responsable vente"), ("Transmise pour contrôle", "Responsable vente"),
          ("Contrôle et facture", "Responsable stock"), ("Validation CSA", "CSA"),
          ("Livraison et déstockage", "Responsable stock"), ("Archivage", "Tous profils autorisés"))
ATTENTE = {"enregistrée": "Responsable vente (transmission)", "transmise": "Responsable stock (contrôle et facture)",
           "facturée": "CSA (validation)", "validée": "Responsable stock (livraison)",
           "livrée": "archivage du dossier"}
EN_COURS = ("enregistrée", "transmise", "facturée", "validée")
A_TRAITER = {"responsable_vente": ("enregistrée",), "responsable_stock": ("transmise", "validée"),
             "csa": ("facturée",)}
# Emplacements de stockage : il n'y en a que deux
EMPLACEMENTS_BASE = ("Chambre froide", "Local")
# Catalogue des vaccins produits (nom, type, prix unitaire en FCFA), d'après la fiche « Variation stock de vaccins ».
# CARBEQUIN n'a pas encore de prix : à renseigner dans le catalogue.
CATALOGUE = (("ANABOT C", "bactérien", 120), ("CARBOSYMPTO", "bactérien", 25), ("CARBOVIN", "bactérien", 22),
             ("CLAVESEC", "viral", 25), ("I-2 (New Castle)", "viral", 22), ("POLYEQUIPESTE", "viral", 1400),
             ("PPR", "viral", 30), ("T1/44", "bactérien", 40), ("PASTEURELLOX", "bactérien", 25),
             ("PASTEURELLAD", "bactérien", 25), ("CARBEQUIN", "bactérien", 0))
MODES_VENTE = {"comptant": "Vente au comptant", "terme": "Vente à terme", "commande": "Commande livrée"}
MODES_PAIEMENT = ("espèces", "mobile money", "virement", "chèque")
MOTIFS_ENTREE = ("Réception", "Retour")
MOTIFS_SORTIE = ("Vente", "Destruction", "Don")
STATUTS_LOT = ("disponible", "réservé", "vendu")   # statut affiché d'un lot (calculé d'après le stock)
PROVENANCES_BASE = ("Labo Bact de Dkr", "Labo Bact de Dahra", "Labo Viro de Dkr")
MDP_STANDARD = "Vaccin@2027"                       # mot de passe initial de tout nouveau compte (à changer à la 1re connexion)
DELAI_INACTIVITE_MIN = 10                       # minutes sans activité avant déconnexion automatique
MAX_ECHECS = 3                                     # tentatives de connexion avant blocage du compte
# Préfixe du code d'identification (affiché sur les documents) selon le rôle : GS01, RV01, CS01…
PREFIXES_CODE = {"responsable_stock": "GS", "responsable_vente": "RV", "csa": "CS",
                 "admin": "AD", "directeur": "DI", "qualite": "QL"}

# ---------------------------------------------------------------- Base de données
SCHEMA = """
CREATE TABLE IF NOT EXISTS users(
  id INTEGER PRIMARY KEY, username TEXT UNIQUE NOT NULL,
  password_hash TEXT NOT NULL, role TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS vaccins(
  id INTEGER PRIMARY KEY, nom TEXT NOT NULL, type TEXT NOT NULL, espece TEXT,
  fabricant TEXT, doses_par_flacon INTEGER DEFAULT 1,
  temp_min REAL DEFAULT 2, temp_max REAL DEFAULT 8, seuil_min INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS categories(
  id INTEGER PRIMARY KEY, nom TEXT UNIQUE NOT NULL, description TEXT, actif INTEGER NOT NULL DEFAULT 1);
CREATE TABLE IF NOT EXISTS unites(
  id INTEGER PRIMARY KEY, nom TEXT UNIQUE NOT NULL, symbole TEXT, actif INTEGER NOT NULL DEFAULT 1);
CREATE TABLE IF NOT EXISTS emplacements(
  id INTEGER PRIMARY KEY, nom TEXT UNIQUE NOT NULL, description TEXT, actif INTEGER NOT NULL DEFAULT 1);
CREATE TABLE IF NOT EXISTS fournisseurs(
  id INTEGER PRIMARY KEY, nom TEXT UNIQUE NOT NULL, contact TEXT, telephone TEXT, email TEXT,
  adresse TEXT, actif INTEGER NOT NULL DEFAULT 1);
CREATE TABLE IF NOT EXISTS articles(
  id INTEGER PRIMARY KEY, nom TEXT UNIQUE NOT NULL, reference TEXT, description TEXT,
  categorie_id INTEGER NOT NULL REFERENCES categories(id), unite_id INTEGER NOT NULL REFERENCES unites(id),
  fournisseur_id INTEGER REFERENCES fournisseurs(id), emplacement_id INTEGER REFERENCES emplacements(id),
  seuil_min INTEGER NOT NULL DEFAULT 0, actif INTEGER NOT NULL DEFAULT 1);
CREATE TABLE IF NOT EXISTS mouvements_articles(
  id INTEGER PRIMARY KEY, article_id INTEGER NOT NULL REFERENCES articles(id),
  nature TEXT NOT NULL, delta INTEGER NOT NULL, motif TEXT, date TEXT NOT NULL,
  user_id INTEGER REFERENCES users(id));
CREATE TABLE IF NOT EXISTS fiches_techniques(
  id INTEGER PRIMARY KEY, vaccin_id INTEGER NOT NULL REFERENCES vaccins(id),
  titre TEXT NOT NULL, version TEXT, fichier TEXT NOT NULL, nom_original TEXT NOT NULL,
  taille INTEGER, date TEXT NOT NULL, user_id INTEGER REFERENCES users(id));
CREATE TABLE IF NOT EXISTS commandes(
  id INTEGER PRIMARY KEY, numero TEXT UNIQUE, client_id INTEGER NOT NULL REFERENCES clients(id),
  date TEXT NOT NULL, date_souhaitee TEXT, statut TEXT NOT NULL DEFAULT 'enregistrée', notes TEXT,
  user_id INTEGER REFERENCES users(id));
CREATE TABLE IF NOT EXISTS lignes_commande(
  id INTEGER PRIMARY KEY, commande_id INTEGER NOT NULL REFERENCES commandes(id),
  vaccin_id INTEGER NOT NULL REFERENCES vaccins(id),
  quantite INTEGER NOT NULL CHECK(quantite > 0), prix_unitaire REAL NOT NULL CHECK(prix_unitaire >= 0));
CREATE TABLE IF NOT EXISTS factures(
  id INTEGER PRIMARY KEY, numero TEXT UNIQUE, commande_id INTEGER NOT NULL REFERENCES commandes(id),
  client_id INTEGER NOT NULL REFERENCES clients(id), date TEXT NOT NULL, total REAL NOT NULL,
  statut TEXT NOT NULL DEFAULT 'émise', user_id INTEGER REFERENCES users(id),
  validee_par INTEGER REFERENCES users(id), validee_le TEXT);
CREATE TABLE IF NOT EXISTS lignes_facture(
  id INTEGER PRIMARY KEY, facture_id INTEGER NOT NULL REFERENCES factures(id),
  vaccin_id INTEGER NOT NULL REFERENCES vaccins(id), designation TEXT NOT NULL,
  quantite INTEGER NOT NULL, prix_unitaire REAL NOT NULL);
CREATE TABLE IF NOT EXISTS livraisons(
  id INTEGER PRIMARY KEY, numero TEXT UNIQUE, commande_id INTEGER NOT NULL REFERENCES commandes(id),
  vente_id INTEGER NOT NULL REFERENCES ventes(id), date TEXT NOT NULL,
  user_id INTEGER REFERENCES users(id));
CREATE TABLE IF NOT EXISTS historique_commande(
  id INTEGER PRIMARY KEY, commande_id INTEGER NOT NULL REFERENCES commandes(id),
  date TEXT NOT NULL, user_id INTEGER REFERENCES users(id), action TEXT NOT NULL,
  statut_apres TEXT NOT NULL, motif TEXT);
CREATE TABLE IF NOT EXISTS pieces_jointes(
  id INTEGER PRIMARY KEY, objet TEXT NOT NULL, objet_id INTEGER NOT NULL, type_doc TEXT NOT NULL,
  titre TEXT NOT NULL, fichier TEXT NOT NULL, nom_original TEXT NOT NULL, taille INTEGER,
  date TEXT NOT NULL, user_id INTEGER REFERENCES users(id));
CREATE TABLE IF NOT EXISTS rapports(
  id INTEGER PRIMARY KEY, type TEXT NOT NULL, periode TEXT NOT NULL, titre TEXT NOT NULL,
  fichier TEXT NOT NULL, taille INTEGER, date TEXT NOT NULL, origine TEXT NOT NULL,
  user_id INTEGER REFERENCES users(id));
CREATE UNIQUE INDEX IF NOT EXISTS idx_rapport_auto ON rapports(type, periode) WHERE origine = 'auto';
CREATE TABLE IF NOT EXISTS parametres(cle TEXT PRIMARY KEY, valeur TEXT);
CREATE TABLE IF NOT EXISTS emails_envoyes(
  id INTEGER PRIMARY KEY, date TEXT NOT NULL, destinataire TEXT NOT NULL, sujet TEXT NOT NULL,
  type TEXT NOT NULL, statut TEXT NOT NULL, erreur TEXT);
CREATE TABLE IF NOT EXISTS lots(
  id INTEGER PRIMARY KEY, vaccin_id INTEGER NOT NULL REFERENCES vaccins(id),
  numero_lot TEXT UNIQUE NOT NULL, date_fabrication TEXT NOT NULL,
  date_peremption TEXT NOT NULL, fournisseur TEXT, emplacement TEXT,
  statut TEXT NOT NULL DEFAULT 'conforme');
CREATE TABLE IF NOT EXISTS clients(
  id INTEGER PRIMARY KEY, nom TEXT NOT NULL, type TEXT, telephone TEXT);
CREATE TABLE IF NOT EXISTS ventes(
  id INTEGER PRIMARY KEY, client_id INTEGER NOT NULL REFERENCES clients(id),
  date TEXT NOT NULL, user_id INTEGER NOT NULL REFERENCES users(id));
CREATE TABLE IF NOT EXISTS lignes_vente(
  id INTEGER PRIMARY KEY, vente_id INTEGER NOT NULL REFERENCES ventes(id),
  lot_id INTEGER NOT NULL REFERENCES lots(id), quantite INTEGER NOT NULL,
  prix_unitaire REAL NOT NULL);
CREATE TABLE IF NOT EXISTS paiements(
  id INTEGER PRIMARY KEY, vente_id INTEGER NOT NULL REFERENCES ventes(id),
  montant REAL NOT NULL CHECK(montant > 0), mode TEXT, date TEXT NOT NULL,
  user_id INTEGER REFERENCES users(id));
CREATE TABLE IF NOT EXISTS mouvements(
  id INTEGER PRIMARY KEY, lot_id INTEGER NOT NULL REFERENCES lots(id),
  type TEXT NOT NULL CHECK(type IN ('ENTREE','SORTIE')),
  quantite INTEGER NOT NULL CHECK(quantite > 0), motif TEXT, date TEXT NOT NULL,
  user_id INTEGER REFERENCES users(id), vente_id INTEGER REFERENCES ventes(id));
CREATE TABLE IF NOT EXISTS messages(
  id INTEGER PRIMARY KEY, expediteur_id INTEGER NOT NULL REFERENCES users(id),
  destinataire_id INTEGER NOT NULL REFERENCES users(id),
  sujet TEXT NOT NULL, corps TEXT, date TEXT NOT NULL, lu INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS inventaires(
  id INTEGER PRIMARY KEY, date TEXT NOT NULL, user_id INTEGER NOT NULL,
  valide INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS lignes_inventaire(
  id INTEGER PRIMARY KEY, inventaire_id INTEGER NOT NULL REFERENCES inventaires(id),
  lot_id INTEGER NOT NULL REFERENCES lots(id), theorique INTEGER NOT NULL,
  compte INTEGER, ecart INTEGER);
CREATE TABLE IF NOT EXISTS reservations(
  id INTEGER PRIMARY KEY, lot_id INTEGER NOT NULL REFERENCES lots(id),
  client_id INTEGER NOT NULL REFERENCES clients(id), quantite INTEGER NOT NULL,
  date TEXT NOT NULL, user_id INTEGER, note TEXT, actif INTEGER NOT NULL DEFAULT 1);
CREATE TABLE IF NOT EXISTS audit(
  id INTEGER PRIMARY KEY, date TEXT NOT NULL, user_id INTEGER, action TEXT NOT NULL);
"""

# Stock d'un lot = somme des entrées - somme des sorties
STOCK_SQL = """
SELECT l.*, v.nom AS vaccin_nom, v.seuil_min, f.nom AS fournisseur_nom, e.nom AS emplacement_nom,
  COALESCE((SELECT SUM(m.quantite) FROM mouvements m WHERE m.lot_id = l.id AND m.type = 'ENTREE'), 0) AS recu,
  COALESCE((SELECT SUM(m.quantite) FROM mouvements m WHERE m.lot_id = l.id AND m.nature = 'TEMOIN'), 0) AS temoins,
  COALESCE((SELECT SUM(m.quantite) FROM mouvements m WHERE m.lot_id = l.id AND m.nature = 'DETRUIT'), 0) AS detruites,
  COALESCE((SELECT SUM(CASE WHEN m.type='ENTREE' THEN m.quantite ELSE -m.quantite END)
            FROM mouvements m WHERE m.lot_id = l.id), 0) AS stock,
  COALESCE((SELECT SUM(r.quantite) FROM reservations r WHERE r.lot_id = l.id AND r.actif = 1), 0) AS reserve
FROM lots l JOIN vaccins v ON v.id = l.vaccin_id
LEFT JOIN fournisseurs f ON f.id = l.fournisseur_id
LEFT JOIN emplacements e ON e.id = l.emplacement_id
"""


def now():
    return datetime.now().isoformat(timespec="seconds")


def db():
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH)
        g.db.row_factory = sqlite3.Row
        g.db.execute("PRAGMA foreign_keys = ON")
    return g.db


@app.teardown_appcontext
def close_db(_exc):
    con = g.pop("db", None)
    if con is not None:
        con.close()


def query(sql, args=(), one=False):
    rows = db().execute(sql, args).fetchall()
    if one:
        return rows[0] if rows else None
    return rows


def execute(sql, args=()):
    cur = db().execute(sql, args)
    db().commit()
    return cur.lastrowid


def audit(action):
    uid = session.get("user", {}).get("id")
    execute("INSERT INTO audit(date, user_id, action) VALUES (?,?,?)", (now(), uid, action))


def init_db():
    con = sqlite3.connect(DB_PATH)
    tables_avant = {r[0] for r in con.execute("SELECT name FROM sqlite_master WHERE type='table'")}
    con.executescript(SCHEMA)
    # Migration : colonnes de gestion des comptes (bases créées avant cette version)
    colonnes = {r[1] for r in con.execute("PRAGMA table_info(users)")}
    if "actif" not in colonnes:
        con.execute("ALTER TABLE users ADD COLUMN actif INTEGER NOT NULL DEFAULT 1")
    if "doit_changer_mdp" not in colonnes:
        con.execute("ALTER TABLE users ADD COLUMN doit_changer_mdp INTEGER NOT NULL DEFAULT 0")
    for colonne, definition in (("email", "TEXT"), ("notif_alertes", "INTEGER NOT NULL DEFAULT 1"),
                                ("notif_rapports", "INTEGER NOT NULL DEFAULT 1"),
                                ("echecs", "INTEGER NOT NULL DEFAULT 0"), ("bloque", "INTEGER NOT NULL DEFAULT 0"),
                                ("code", "TEXT")):
        if colonne not in colonnes:
            con.execute(f"ALTER TABLE users ADD COLUMN {colonne} {definition}")
    if "commentaire" not in {r[1] for r in con.execute("PRAGMA table_info(inventaires)")}:
        con.execute("ALTER TABLE inventaires ADD COLUMN commentaire TEXT")
    # Rôles : anciens noms -> noms du cahier des charges (idempotent)
    con.execute("UPDATE users SET role='responsable_stock' WHERE role='magasinier'")
    con.execute("UPDATE users SET role='responsable_vente' WHERE role='vendeur'")
    if "actif" not in {r[1] for r in con.execute("PRAGMA table_info(vaccins)")}:
        con.execute("ALTER TABLE vaccins ADD COLUMN actif INTEGER NOT NULL DEFAULT 1")
    cols_v = {r[1] for r in con.execute("PRAGMA table_info(vaccins)")}
    if "prix_unitaire" not in cols_v:
        con.execute("ALTER TABLE vaccins ADD COLUMN prix_unitaire REAL NOT NULL DEFAULT 0")
        con.execute("UPDATE vaccins SET prix_unitaire = COALESCE("
                    "(SELECT lc.prix_unitaire FROM lignes_commande lc WHERE lc.vaccin_id=vaccins.id ORDER BY lc.id DESC LIMIT 1),"
                    "(SELECT lv.prix_unitaire FROM lignes_vente lv JOIN lots l ON l.id=lv.lot_id"
                    " WHERE l.vaccin_id=vaccins.id ORDER BY lv.id DESC LIMIT 1), 0)")
    # Référentiels : valeurs de départ (une seule fois, à la création des tables)
    if "categories" not in tables_avant:
        con.executemany("INSERT INTO categories(nom) VALUES (?)", [("Vaccins",), ("Intrants",), ("Matériel",)])
    if "unites" not in tables_avant:
        con.executemany("INSERT INTO unites(nom) VALUES (?)", [("Dose",), ("Flacon",), ("Boîte",), ("Unité",)])
    # Ventes : lien avec la commande livrée
    if "commande_id" not in {r[1] for r in con.execute("PRAGMA table_info(ventes)")}:
        con.execute("ALTER TABLE ventes ADD COLUMN commande_id INTEGER REFERENCES commandes(id)")
    # Ventes : mode (comptant / terme / commande livrée), échéance et adresse figurant sur la facture
    cols_ventes = {r[1] for r in con.execute("PRAGMA table_info(ventes)")}
    if "mode" not in cols_ventes:
        con.execute("ALTER TABLE ventes ADD COLUMN mode TEXT NOT NULL DEFAULT 'commande'")
        con.execute("UPDATE ventes SET mode='comptant' WHERE commande_id IS NULL")
    for colonne in ("echeance", "adresse"):
        if colonne not in cols_ventes:
            con.execute(f"ALTER TABLE ventes ADD COLUMN {colonne} TEXT")
    # Clients : nature (entreprise / particulier), e-mail, adresse
    cols_clients = {r[1] for r in con.execute("PRAGMA table_info(clients)")}
    for colonne in ("nature", "email", "adresse"):
        if colonne not in cols_clients:
            con.execute(f"ALTER TABLE clients ADD COLUMN {colonne} TEXT")
    # Mouvements : « nature » distingue les sorties spéciales (témoins, destructions)
    if "nature" not in {r[1] for r in con.execute("PRAGMA table_info(mouvements)")}:
        con.execute("ALTER TABLE mouvements ADD COLUMN nature TEXT")
    # Lots : fournisseur et emplacement deviennent des références (les anciens textes sont repris)
    cols_lots = {r[1] for r in con.execute("PRAGMA table_info(lots)")}
    if "fournisseur_id" not in cols_lots:
        con.execute("ALTER TABLE lots ADD COLUMN fournisseur_id INTEGER REFERENCES fournisseurs(id)")
    if "emplacement_id" not in cols_lots:
        con.execute("ALTER TABLE lots ADD COLUMN emplacement_id INTEGER REFERENCES emplacements(id)")
    for col_txt, col_id, table in (("fournisseur", "fournisseur_id", "fournisseurs"),
                                   ("emplacement", "emplacement_id", "emplacements")):
        anciens = con.execute(f"SELECT DISTINCT TRIM({col_txt}) FROM lots WHERE {col_id} IS NULL"
                              f" AND {col_txt} IS NOT NULL AND TRIM({col_txt}) <> ''").fetchall()
        for (nom,) in anciens:
            ligne = con.execute(f"SELECT id FROM {table} WHERE lower(nom)=lower(?)", (nom,)).fetchone()
            rid = ligne[0] if ligne else con.execute(f"INSERT INTO {table}(nom) VALUES (?)", (nom,)).lastrowid
            con.execute(f"UPDATE lots SET {col_id}=? WHERE {col_id} IS NULL AND TRIM({col_txt})=?", (rid, nom))
    con.commit()
    if con.execute("SELECT COUNT(*) FROM users").fetchone()[0] == 0:
        for u, p, r in (("admin", "admin123", "admin"),
                        ("magasinier", "mag123", "responsable_stock"),
                        ("vendeur", "vend123", "responsable_vente")):
            con.execute("INSERT INTO users(username, password_hash, role) VALUES (?,?,?)",
                        (u, generate_password_hash(p), r))
        # Données d'exemple (à supprimer en production)
        con.execute("INSERT INTO clients(nom,type,telephone) VALUES ('Éleveur exemple','éleveur','770000000')")
        con.commit()
    amorcer_catalogue(con)
    reprise_suivi(con)
    for uid, role in con.execute("SELECT id, role FROM users WHERE code IS NULL ORDER BY id").fetchall():
        con.execute("UPDATE users SET code=? WHERE id=?", (prochain_code(con, role), uid))
    con.commit()
    con.close()


def prochain_code(con, role):
    """Code d'identification suivant pour ce rôle : GS01, GS02… (RV01…, CS01…)."""
    prefixe = PREFIXES_CODE.get(role, "US")
    n = 0
    for (c,) in con.execute("SELECT code FROM users WHERE code LIKE ?", (prefixe + "%",)):
        if re.fullmatch(prefixe + r"\d+", c or ""):
            n = max(n, int(c[len(prefixe):]))
    return f"{prefixe}{n + 1:02d}"


DONNEES_REPRISE = [   # fichier SUIVI_VACCIN_26.xlsx : (vaccin, n° de lot, stock disponible, prix unitaire)
    ("ANABOT C", "A05:25/A06:25;A01_03:26", 7000, 120),
    ("CARBOSYMPTO", "S09:25/S10-11:25;S01-09:26", 1156800, 25),
    ("CARBOVIN", "RV02_03:25/RV04:25;RV01:26", 410800, 22),
    ("CLAVESEC", "C09_10:25/C13-15:25;C01-08:26", 203200, 25),
    ("I-2 (New Castle)", "XX04:25/XX03-04:26", 92000, 22),
    ("POLYEQUIPESTE", "D03-08:25", 32300, 1400),
    ("PPR", "R09-10:25/R11-12:25;R01_07:26", 78900, 30),
    ("T1/44", "P06_11:25/P12_16:25;P01&02:26", 674640, 40),
    ("PASTEURELLOX", "J04:25/J01_04:26", 47700, 25),
    ("PASTEURELLAD", "N10:25/N11-12:25;N01-04:26", 30100, 25),
]
REPRISE_PEREMPTION = "2027-12-31"   # péremption donnée aux lots repris (absente du fichier Excel)


def reprise_suivi(con):
    """Une seule fois : supprime les données d'essai (clients, utilisateurs et catalogue conservés)
    et charge le stock du fichier SUIVI_VACCIN_26.xlsx. Sauvegarde upvac.db avant."""
    if con.execute("SELECT 1 FROM parametres WHERE cle='reprise_suivi_2026'").fetchone():
        return
    adm = (con.execute("SELECT id FROM users WHERE role='admin' ORDER BY id LIMIT 1").fetchone()
           or con.execute("SELECT id FROM users ORDER BY id LIMIT 1").fetchone())
    if adm is None:
        return
    import shutil
    try:
        shutil.copy(DB_PATH, os.path.join(BASE_DIR, f"upvac_avant_reprise_{datetime.now():%Y%m%d_%H%M}.db"))
    except OSError:
        pass
    fichiers = []
    for o in ("commande", "lot"):
        fichiers += [r[0] for r in con.execute("SELECT fichier FROM pieces_jointes WHERE objet=?", (o,))]
        con.execute("DELETE FROM pieces_jointes WHERE objet=?", (o,))
    for t in ("livraisons", "historique_commande", "lignes_facture", "factures", "paiements",
              "lignes_vente", "ventes", "lignes_commande", "commandes", "reservations",
              "lignes_inventaire", "inventaires", "mouvements", "lots"):
        con.execute(f"DELETE FROM {t}")
    if not con.execute("SELECT 1 FROM emplacements WHERE lower(nom)='chambre froide'").fetchone():
        con.execute("INSERT INTO emplacements(nom) VALUES ('Chambre froide')")
    maintenant = datetime.now().isoformat(timespec="seconds")
    total = 0
    for nom, lot, dispo, prix in DONNEES_REPRISE:
        v = con.execute("SELECT id FROM vaccins WHERE lower(replace(nom,' ',''))=lower(replace(?,' ',''))", (nom,)).fetchone()
        if v is None:
            continue
        con.execute("UPDATE vaccins SET prix_unitaire=? WHERE id=?", (prix, v[0]))
        lid = con.execute(
            "INSERT INTO lots(vaccin_id,numero_lot,date_fabrication,date_peremption,fournisseur,emplacement,statut)"
            " VALUES (?,?,?,?,?,?,'conforme')",
            (v[0], lot[:60], date.today().isoformat(), REPRISE_PEREMPTION, None, "Chambre froide")).lastrowid
        con.execute("INSERT INTO mouvements(lot_id,type,quantite,motif,date,user_id) VALUES (?,?,?,?,?,?)",
                    (lid, "ENTREE", dispo, "Reprise du stock (fichier SUIVI VACCIN)", maintenant, adm[0]))
        total += dispo
    con.execute("INSERT INTO audit(date,user_id,action) VALUES (?,?,?)",
                (maintenant, adm[0], f"Reprise du stock SUIVI VACCIN : {total} dose(s)"))
    con.execute("INSERT OR REPLACE INTO parametres(cle, valeur) VALUES ('reprise_suivi_2026', '1')")
    con.commit()
    for f in fichiers:
        try:
            supprimer_fichier(f)
        except Exception:
            pass


def amorcer_catalogue(con):
    """Emplacements (Chambre froide / Local) et catalogue des vaccins avec prix : une seule fois."""
    def deja(cle):
        return con.execute("SELECT 1 FROM parametres WHERE cle=?", (cle,)).fetchone()

    def marquer(cle):
        con.execute("INSERT OR REPLACE INTO parametres(cle, valeur) VALUES (?, '1')", (cle,))

    if not deja("init_emplacements"):
        for nom in EMPLACEMENTS_BASE:
            if not con.execute("SELECT 1 FROM emplacements WHERE lower(nom)=lower(?)", (nom,)).fetchone():
                con.execute("INSERT INTO emplacements(nom) VALUES (?)", (nom,))
        con.execute("UPDATE emplacements SET actif=0 WHERE lower(nom) NOT IN ('chambre froide', 'local')")
        con.execute("UPDATE emplacements SET actif=1 WHERE lower(nom) IN ('chambre froide', 'local')")
        marquer("init_emplacements")
    if not deja("init_provenances"):
        for nom in PROVENANCES_BASE:
            if not con.execute("SELECT 1 FROM fournisseurs WHERE lower(nom)=lower(?)", (nom,)).fetchone():
                con.execute("INSERT INTO fournisseurs(nom) VALUES (?)", (nom,))
        marqs = ",".join("?" for _ in PROVENANCES_BASE)
        con.execute(f"UPDATE fournisseurs SET actif=0 WHERE nom NOT IN ({marqs})", PROVENANCES_BASE)
        con.execute(f"UPDATE fournisseurs SET actif=1 WHERE nom IN ({marqs})", PROVENANCES_BASE)
        marquer("init_provenances")
    if not deja("init_catalogue"):
        for nom, type_, prix in CATALOGUE:
            ligne = con.execute("SELECT id, prix_unitaire FROM vaccins WHERE lower(nom)=lower(?)", (nom,)).fetchone()
            if ligne is None:
                con.execute("INSERT INTO vaccins(nom, type, fabricant, doses_par_flacon, prix_unitaire)"
                            " VALUES (?,?,?,?,?)", (nom, type_, "ISRA", 1, prix))
            elif not ligne[1] and prix:
                con.execute("UPDATE vaccins SET prix_unitaire=? WHERE id=?", (prix, ligne[0]))
        con.execute("DELETE FROM vaccins WHERE nom IN ('Vaccin exemple A', 'Vaccin exemple B')"
                    " AND NOT EXISTS (SELECT 1 FROM lots WHERE lots.vaccin_id = vaccins.id)")
        marquer("init_catalogue")
    con.commit()


# ---------------------------------------------------------------- Sécurité
def login_required(f):
    @wraps(f)
    def wrapper(*a, **kw):
        if "user" not in session:
            return redirect(url_for("login"))
        u = query("SELECT id, username, role, actif, doit_changer_mdp, code FROM users WHERE id=?",
                  (session["user"]["id"],), one=True)
        if u is None or not u["actif"]:
            session.clear()
            flash("Votre compte est désactivé ou n'existe plus.", "danger")
            return redirect(url_for("login"))
        session["user"] = {"id": u["id"], "username": u["username"], "role": u["role"], "code": u["code"]}
        if u["doit_changer_mdp"] and request.endpoint not in ("mot_de_passe", "logout"):
            flash("Vous devez choisir un nouveau mot de passe avant de continuer.", "warning")
            return redirect(url_for("mot_de_passe"))
        return f(*a, **kw)
    return wrapper


def roles(*autorises):
    def deco(f):
        @wraps(f)
        @login_required
        def wrapper(*a, **kw):
            if session["user"]["role"] not in autorises:
                flash("Accès refusé pour votre rôle.", "danger")
                return redirect(url_for("index"))
            return f(*a, **kw)
        return wrapper
    return deco


# Rôles du cahier des charges (identifiant interne -> libellé affiché).
ROLES = {
    "admin": "Admin CSA",
    "responsable_stock": "Responsable stock",
    "responsable_vente": "Responsable vente",
    "csa": "CSA",
    "directeur": "Directeur",
    "qualite": "Qualité",
}

# Séparation des responsabilités : qui peut faire quoi (modifiable ici, en un seul endroit).
#  - admin             : administre (comptes, audit, suppressions de correction), valide les
#                        inventaires et consulte tout. Ne saisit ni stock ni vente.
#  - responsable_stock : catalogue, lots, entrées/sorties, comptage d'inventaire, référentiels.
#  - responsable_vente : caisse (ventes au comptant et à terme), encaissements, clients, commandes.
#  - csa               : consulte et valide les ventes (factures contrôlées par le responsable stock).
#  - directeur         : consultation uniquement (n'intervient pas dans le circuit de vente).
#  - qualite           : consultation du stock, des alertes et des péremptions.
LECTURE_STOCK = ("admin", "responsable_stock", "csa", "directeur", "qualite")
LECTURE_VENTES = ("admin", "responsable_vente", "csa", "directeur")
DROITS = {
    "vaccins_voir": LECTURE_STOCK,
    "vaccins_gerer": ("responsable_stock",),        # ajouter / archiver un vaccin
    "lots_gerer": ("responsable_stock",),           # réception d'un lot, changement de statut
    "articles_voir": LECTURE_STOCK,
    "articles_gerer": ("responsable_stock",),       # créer / modifier / archiver un article
    "articles_mouvements": ("responsable_stock",),  # entrées, sorties, ajustements d'articles
    "mouvements_voir": LECTURE_STOCK,
    "mouvements_saisir": ("responsable_stock",),
    "reservations_gerer": ("csa",),                 # réserver / annuler une réservation de doses (ministère, structures…)
    "referentiels_voir": LECTURE_STOCK,
    "referentiels_gerer": ("responsable_stock",),   # catégories, unités, emplacements, fournisseurs
    "inventaire_voir": LECTURE_STOCK,
    "inventaire_compter": ("responsable_stock",),   # ouvrir un inventaire et saisir le comptage
    "inventaire_valider": ("admin",),               # valider = régulariser les écarts dans le stock
    "ventes_voir": LECTURE_VENTES,
    "ventes_saisir": ("responsable_vente", "csa"),        # caisse : vente au comptant / à terme
    "paiements_saisir": ("responsable_vente", "csa"),     # encaissement des ventes à terme
    "commandes_voir": ("admin", "responsable_vente", "responsable_stock", "csa", "directeur"),
    "commandes_saisir": ("responsable_vente",),     # créer, modifier, annuler, transmettre une commande
    "commandes_controler": ("responsable_stock",),  # étape 3 : contrôle et génération de la facture
    "commandes_valider": ("csa",),                  # étape 4 : validation de la vente par le CSA
    "commandes_livrer": ("responsable_stock",),     # étape 5 : livraison et déstockage
    "commandes_archiver": ("responsable_vente", "responsable_stock"),  # étape 6 : archivage
    "factures_voir": ("admin", "responsable_vente", "responsable_stock", "csa", "directeur"),
    "rapports_voir": ("admin", "responsable_stock", "responsable_vente", "csa", "directeur"),  # consulter, générer
    "pj_fournisseur_voir": ("admin", "responsable_stock", "csa", "directeur"),  # documents fournisseurs (lots, articles)
    "pj_fournisseur_gerer": ("responsable_stock",),
    "pj_commande_voir": ("admin", "responsable_vente", "responsable_stock", "csa", "directeur"),
    "pj_commande_gerer": ("responsable_vente", "responsable_stock"),
    "clients_voir": LECTURE_VENTES,
    "clients_gerer": ("responsable_vente", "csa"),
    "supprimer": ("admin",),                        # suppressions de correction (vaccin, lot, client)
    "utilisateurs": ("admin",),
    "reinitialiser": ("admin",),                    # purge des données d'essai (ventes, commandes, stock, clients)
    "email_config": ("admin",),                     # serveur d'envoi, journal des e-mails
    "audit": ("admin",),
}


def droit(nom):
    return session.get("user", {}).get("role") in DROITS[nom]


def peut_gerer():
    return droit("lots_gerer")


JOURS_FR = ("lundi", "mardi", "mercredi", "jeudi", "vendredi", "samedi", "dimanche")


def jour_en_lettres(d):
    """« Dimanche 22 novembre 2026 » pour l'en-tête des pages."""
    return f"{JOURS_FR[d.weekday()].capitalize()} {d.day} {MOIS_LONGS[d.month - 1]} {d.year}"


# ---------------------------------------------------------------- Icônes de l'interface
# Jeu d'icônes vectorielles au trait (24 × 24, style inspiré de Lucide, licence ISC) :
# rendu identique sur tous les postes, contrairement aux émojis.
ICONES = {
    "accueil": '<rect x="3" y="3" width="7" height="9" rx="1.5"/><rect x="14" y="3" width="7" height="5" rx="1.5"/><rect x="14" y="12" width="7" height="9" rx="1.5"/><rect x="3" y="16" width="7" height="5" rx="1.5"/>',
    "graphique": '<path d="M3 3v18h18"/><path d="M8 17v-5"/><path d="M13 17V8"/><path d="M18 17v-3"/>',
    "hausse": '<path d="m3 17 6-6 4 4 8-8"/><path d="M15 7h6v6"/>',
    "baisse": '<path d="m3 7 6 6 4-4 8 8"/><path d="M15 17h6v-6"/>',
    "seringue": '<path d="m18 2 4 4"/><path d="m17 7 3-3"/><path d="M19 9 8.7 19.3a2.4 2.4 0 0 1-3.4 0l-.6-.6a2.4 2.4 0 0 1 0-3.4L15 5"/><path d="m9 11 4 4"/><path d="m5 19-3 3"/><path d="m14 4 6 6"/>',
    "colis": '<path d="M21 8 12 3 3 8v8l9 5 9-5z"/><path d="m3 8 9 5 9-5"/><path d="M12 13v8"/><path d="m7.5 5.5 9 5"/>',
    "echange": '<path d="M7 7h13"/><path d="m16 3 4 4-4 4"/><path d="M17 17H4"/><path d="m8 21-4-4 4-4"/>',
    "inventaire": '<rect x="8" y="2" width="8" height="4" rx="1"/><path d="M16 4h2a2 2 0 0 1 2 2v14a2 2 0 0 1-2 2H6a2 2 0 0 1-2-2V6a2 2 0 0 1 2-2h2"/><path d="m9 13 2 2 4-4"/>',
    "outils": '<path d="M14.7 6.3a1 1 0 0 0 0 1.4l1.6 1.6a1 1 0 0 0 1.4 0l3.8-3.8a6 6 0 0 1-7.9 7.9l-6.9 6.9a2.1 2.1 0 0 1-3-3l6.9-6.9a6 6 0 0 1 7.9-7.9z"/>',
    "panier": '<circle cx="9" cy="20" r="1.5"/><circle cx="18" cy="20" r="1.5"/><path d="M2 3h3l2.7 12.4a2 2 0 0 0 2 1.6h8.6a2 2 0 0 0 2-1.6L22 7H6"/>',
    "recu": '<path d="M4 2v20l2.7-1.5L9.3 22l2.7-1.5 2.7 1.5 2.6-1.5L20 22V2l-2.7 1.5L14.7 2 12 3.5 9.3 2 6.7 3.5z"/><path d="M8 8h8"/><path d="M8 12h8"/><path d="M8 16h5"/>',
    "billets": '<rect x="2" y="6" width="20" height="12" rx="2"/><circle cx="12" cy="12" r="2.5"/><path d="M6 12h.01M18 12h.01"/>',
    "fichier": '<path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/><path d="M14 2v6h6"/><path d="M8 13h8"/><path d="M8 17h8"/>',
    "utilisateurs": '<path d="M16 21v-2a4 4 0 0 0-4-4H6a4 4 0 0 0-4 4v2"/><circle cx="9" cy="7" r="4"/><path d="M22 21v-2a4 4 0 0 0-3-3.9"/><path d="M16 3.1a4 4 0 0 1 0 7.8"/>',
    "utilisateur": '<circle cx="12" cy="8" r="4"/><path d="M4 21v-1a6 6 0 0 1 6-6h4a6 6 0 0 1 6 6v1"/>',
    "mail": '<rect x="2" y="4" width="20" height="16" rx="2"/><path d="m22 7-10 6L2 7"/>',
    "dossier": '<path d="M3 6a2 2 0 0 1 2-2h4l2 2h8a2 2 0 0 1 2 2v10a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2z"/>',
    "bouclier": '<path d="M12 22s8-4 8-10V5l-8-3-8 3v7c0 6 8 10 8 10z"/><path d="m9 12 2 2 4-4"/>',
    "historique": '<path d="M3 12a9 9 0 1 0 3-6.7L3 8"/><path d="M3 3v5h5"/><path d="M12 7v5l4 2"/>',
    "fiole": '<path d="M9 3h6"/><path d="M10 3v6l-5.5 9.5A2 2 0 0 0 6.2 21.5h11.6a2 2 0 0 0 1.7-3L14 9V3"/><path d="M7 15h10"/>',
    "cle": '<circle cx="7.5" cy="15.5" r="4.5"/><path d="m10.7 12.3 9.3-9.3"/><path d="m16 7 3 3"/><path d="m19 4 2 2"/>',
    "cloche": '<path d="M6 8a6 6 0 0 1 12 0c0 7 3 9 3 9H3s3-2 3-9"/><path d="M10.3 21a1.9 1.9 0 0 0 3.4 0"/>',
    "interdit": '<circle cx="12" cy="12" r="9"/><path d="m5.7 5.7 12.6 12.6"/>',
    "sablier": '<path d="M5 22h14"/><path d="M5 2h14"/><path d="M17 22v-4.2a2 2 0 0 0-.6-1.4L12 12l-4.4 4.4a2 2 0 0 0-.6 1.4V22"/><path d="M7 2v4.2a2 2 0 0 0 .6 1.4L12 12l4.4-4.4a2 2 0 0 0 .6-1.4V2"/>',
    "carte": '<rect x="2" y="5" width="20" height="14" rx="2"/><path d="M2 10h20"/><path d="M6 15h4"/>',
    "recherche": '<circle cx="11" cy="11" r="7"/><path d="m21 21-4.3-4.3"/>',
    "livre": '<path d="M4 19.5A2.5 2.5 0 0 1 6.5 17H20V3H6.5A2.5 2.5 0 0 0 4 5.5z"/><path d="M4 19.5A2.5 2.5 0 0 0 6.5 22H20v-5"/>',
    "telecharger": '<path d="M12 3v12"/><path d="m7 10 5 5 5-5"/><path d="M5 21h14"/>',
    "envoyer": '<path d="m22 2-7 20-4-9-9-4z"/><path d="M22 2 11 13"/>',
    "poubelle": '<path d="M3 6h18"/><path d="M8 6V4h8v2"/><path d="m19 6-1 14a2 2 0 0 1-2 2H8a2 2 0 0 1-2-2L5 6"/><path d="M10 11v6M14 11v6"/>',
    "gauche": '<path d="M19 12H5"/><path d="m12 19-7-7 7-7"/>',
    "imprimante": '<path d="M6 9V2h12v7"/><path d="M6 18H4a2 2 0 0 1-2-2v-5a2 2 0 0 1 2-2h16a2 2 0 0 1 2 2v5a2 2 0 0 1-2 2h-2"/><rect x="6" y="14" width="12" height="8" rx="1"/>',
    "croix": '<path d="M18 6 6 18M6 6l12 12"/>',
    "coche": '<path d="M20 6 9 17l-5-5"/>',
    "valide": '<circle cx="12" cy="12" r="9"/><path d="m8 12 3 3 5-6"/>',
    "trombone": '<path d="m21.4 11-8.8 8.8a5.5 5.5 0 0 1-7.8-7.8l8.8-8.8a3.7 3.7 0 0 1 5.2 5.2l-8.8 8.8a1.8 1.8 0 0 1-2.6-2.6l8.1-8.1"/>',
    "plus": '<path d="M12 5v14M5 12h14"/>',
    "crayon": '<path d="M17 3a2.8 2.8 0 0 1 4 4L7.5 20.5 2 22l1.5-5.5z"/>',
    "archive": '<rect x="2" y="3" width="20" height="5" rx="1"/><path d="M4 8v11a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8"/><path d="M10 12h4"/>',
    "retour": '<path d="M9 14 4 9l5-5"/><path d="M4 9h10.5a5.5 5.5 0 0 1 0 11H11"/>',
    "alerte": '<path d="M10.3 3.9 1.8 18a2 2 0 0 0 1.7 3h17a2 2 0 0 0 1.7-3L13.7 3.9a2 2 0 0 0-3.4 0z"/><path d="M12 9v4M12 17h.01"/>',
    "calendrier": '<rect x="3" y="4" width="18" height="18" rx="2"/><path d="M16 2v4M8 2v4M3 10h18"/>',
    "lune": '<path d="M21 12.8A9 9 0 1 1 11.2 3a7 7 0 0 0 9.8 9.8z"/>',
    "soleil": '<circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M4.9 4.9l1.4 1.4M17.7 17.7l1.4 1.4M2 12h2M20 12h2M4.9 19.1l1.4-1.4M17.7 6.3l1.4-1.4"/>',
    "menu": '<path d="M4 6h16M4 12h16M4 18h16"/>',
    "sortie": '<path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><path d="m16 17 5-5-5-5"/><path d="M21 12H9"/>',
    "chevron-bas": '<path d="m6 9 6 6 6-6"/>',
    "chevron-droite": '<path d="m9 18 6-6-6-6"/>',
    "oeil": '<path d="M2 12s3.5-7 10-7 10 7 10 7-3.5 7-10 7S2 12 2 12z"/><circle cx="12" cy="12" r="3"/>',
    "oeil-barre": '<path d="m3 3 18 18"/><path d="M10.6 5.1A10 10 0 0 1 12 5c6.5 0 10 7 10 7a17 17 0 0 1-2.2 3.2"/><path d="M6.6 6.6A17 17 0 0 0 2 12s3.5 7 10 7a9.8 9.8 0 0 0 5.4-1.6"/><path d="M9.9 9.9a3 3 0 0 0 4.2 4.2"/>',
    "cadenas": '<rect x="4" y="11" width="16" height="10" rx="2"/><path d="M8 11V7a4 4 0 0 1 8 0v4"/>',
    "cadenas-ouvert": '<rect x="4" y="11" width="16" height="10" rx="2"/><path d="M8 11V7a4 4 0 0 1 7.9-1"/>',
    "gomme": '<path d="m7 21-4.3-4.3a1 1 0 0 1 0-1.4l10-10a1 1 0 0 1 1.4 0l5.6 5.6a1 1 0 0 1 0 1.4L11 21"/><path d="M22 21H7"/><path d="m5 11 9 9"/>',
    "etiquette": '<path d="M20.6 13.4 13.4 20.6a2 2 0 0 1-2.8 0L3 13V3h10l7.6 7.6a2 2 0 0 1 0 2.8z"/><circle cx="7.5" cy="7.5" r="1.5"/>',
    "regle": '<path d="M21.3 15.3 8.7 2.7a1 1 0 0 0-1.4 0L2.7 7.3a1 1 0 0 0 0 1.4l12.6 12.6a1 1 0 0 0 1.4 0l4.6-4.6a1 1 0 0 0 0-1.4z"/><path d="m7.5 10.5 2-2M10.5 13.5l2-2M13.5 16.5l2-2"/>',
    "epingle": '<path d="M20 10c0 6-8 12-8 12s-8-6-8-12a8 8 0 0 1 16 0z"/><circle cx="12" cy="10" r="3"/>',
    "camion": '<path d="M1 4h14v12H1z"/><path d="M15 8h4l3 3v5h-7z"/><circle cx="5.5" cy="18.5" r="2.5"/><circle cx="18.5" cy="18.5" r="2.5"/>',
    "boite": '<path d="M22 12h-6l-2 3h-4l-2-3H2"/><path d="M5.5 5.1 2 12v6a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2v-6l-3.5-6.9A2 2 0 0 0 16.8 4H7.2a2 2 0 0 0-1.7 1.1z"/>',
}


def ic(nom, taille=None):
    """Icône SVG en ligne : {{ ic('panier') }}. Prend la couleur du texte (currentColor)."""
    style = f' style="width:{taille}px;height:{taille}px"' if taille else ""
    return Markup(f'<svg class="ic" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" '
                  f'stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"{style}>{ICONES[nom]}</svg>')


def icone_url(nom, couleur):
    """Icône en image (data URI) pour les décorations CSS : titres de page, champs de recherche…"""
    from urllib.parse import quote
    svg = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="{couleur}" '
           f'stroke-width="2" stroke-linecap="round" stroke-linejoin="round">{ICONES[nom]}</svg>')
    return "url('data:image/svg+xml," + quote(svg, safe="") + "')"


app.jinja_env.globals["ic"] = ic

# Rubrique de chaque page : icône du titre et fil d'Ariane de la barre du haut
RUBRIQUES = (("index", "accueil", "Pilotage", "Tableau de bord"), ("rapport", "graphique", "Pilotage", "Rapports"),
             ("lot", "seringue", "Stock", "Vaccins & lots"), ("vaccin", "seringue", "Stock", "Catalogue des vaccins"),
             ("mouvement", "echange", "Stock", "Entrées / sorties"), ("inventaire", "inventaire", "Stock", "Inventaire"),
             ("article", "outils", "Stock", "Articles"), ("caisse", "panier", "Vente", "Caisse"),
             ("commande", "recu", "Vente", "Commandes"), ("vente", "billets", "Vente", "Ventes"),
             ("facture", "fichier", "Vente", "Factures"), ("client", "utilisateurs", "Vente", "Clients"),
             ("message", "mail", "Communication", "Messagerie"), ("referentiel", "dossier", "Administration", "Référentiels"),
             ("ref_", "dossier", "Administration", "Référentiels"), ("utilisateur", "bouclier", "Administration", "Utilisateurs"),
             ("email", "mail", "Administration", "Notifications e-mail"), ("journal", "historique", "Administration", "Audit"),
             ("donnees", "fiole", "Administration", "Données d'essai"), ("mon_compte", "utilisateur", "Mon compte", "Profil"),
             ("mot_de_passe", "cle", "Mon compte", "Mot de passe"))


def rubrique(endpoint):
    for prefixe, ico, section, page in RUBRIQUES:
        if (endpoint or "").startswith(prefixe):
            return {"ico": ico, "section": section, "page": page}
    return {"ico": "fichier", "section": "", "page": ""}


def style_page(endpoint):
    """Variables CSS de la page : icône du titre en vert (thème clair) et vert pâle (thème sombre)."""
    nom = rubrique(endpoint)["ico"]
    return Markup(f"--ico-page:{icone_url(nom, '#2b7313')};--ico-page-sombre:{icone_url(nom, '#8fd66a')}")


@app.context_processor
def inject_globals():
    nb = 0
    if "user" in session:
        nb = query("SELECT COUNT(*) AS n FROM messages WHERE destinataire_id=? AND lu=0",
                   (session["user"]["id"],), one=True)["n"]
    return {"nb_non_lus": nb, "peut_gerer": peut_gerer(), "STATUTS": STATUTS,
            "MOTIFS_SORTIE": MOTIFS_SORTIE, "annee": date.today().year, "style_page": style_page(request.endpoint), "rubrique": rubrique(request.endpoint), "jour_fr": jour_en_lettres(date.today()), "devise": DEVISE, "TYPES_DOC": TYPES_DOC,
            "droits": {k: droit(k) for k in DROITS}}


@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        u = query("SELECT * FROM users WHERE lower(username)=lower(?)",
                  (request.form["username"].strip(),), one=True)
        if u and u["bloque"]:
            flash("Ce compte est bloqué après trop de tentatives. Contactez l'administrateur pour le débloquer.", "danger")
            return render_template("login.html")
        if u and check_password_hash(u["password_hash"], request.form["password"]):
            if not u["actif"]:
                flash("Ce compte est désactivé. Contactez l'administrateur.", "danger")
                return render_template("login.html")
            execute("UPDATE users SET echecs=0 WHERE id=?", (u["id"],))
            session.permanent = True   # le cookie expire après DELAI_INACTIVITE_MIN minutes sans requête
            session["user"] = {"id": u["id"], "username": u["username"], "role": u["role"], "code": u["code"]}
            audit("Connexion")
            return redirect(url_for("index"))
        if u:
            echecs = u["echecs"] + 1
            if echecs >= MAX_ECHECS:
                execute("UPDATE users SET echecs=?, bloque=1 WHERE id=?", (echecs, u["id"]))
                execute("INSERT INTO audit(date, user_id, action) VALUES (?,?,?)",
                        (now(), u["id"], f"Compte bloqué après {MAX_ECHECS} tentatives de connexion échouées"))
                for a in query("SELECT id FROM users WHERE role='admin' AND actif=1 AND id<>?", (u["id"],)):
                    execute("INSERT INTO messages(expediteur_id,destinataire_id,sujet,corps,date) VALUES (?,?,?,?,?)",
                            (u["id"], a["id"], f"Compte bloqué : {u['username']}",
                             f"Le compte « {u['username']} » a été bloqué après {MAX_ECHECS} tentatives de connexion "
                             "échouées. Débloquez-le depuis la page Utilisateurs si c'est légitime.", now()))
                flash(f"Compte bloqué après {MAX_ECHECS} tentatives. Contactez l'administrateur pour le débloquer.", "danger")
                return render_template("login.html")
            execute("UPDATE users SET echecs=? WHERE id=?", (echecs, u["id"]))
            flash(f"Identifiants incorrects. Il vous reste {MAX_ECHECS - echecs} tentative(s) avant le blocage du compte.", "danger")
        else:
            flash("Identifiants incorrects.", "danger")
    return render_template("login.html")


@app.route("/mot-de-passe", methods=["GET", "POST"])
@login_required
def mot_de_passe():
    if request.method == "POST":
        u = query("SELECT * FROM users WHERE id=?", (session["user"]["id"],), one=True)
        actuel = request.form["actuel"]
        nouveau = request.form["nouveau"]
        if not check_password_hash(u["password_hash"], actuel):
            flash("Mot de passe actuel incorrect.", "danger")
        elif len(nouveau) < 8:
            flash("Le nouveau mot de passe doit contenir au moins 8 caractères.", "danger")
        elif nouveau != request.form["confirmation"]:
            flash("La confirmation ne correspond pas.", "danger")
        elif nouveau == actuel:
            flash("Le nouveau mot de passe doit être différent de l'ancien.", "warning")
        else:
            execute("UPDATE users SET password_hash=?, doit_changer_mdp=0 WHERE id=?",
                    (generate_password_hash(nouveau), u["id"]))
            audit("Changement de mot de passe")
            flash("Mot de passe modifié avec succès.", "success")
            return redirect(url_for("index"))
    return render_template("mot_de_passe.html")


@app.route("/logout")
def logout():
    if "user" in session:
        audit("Déconnexion automatique (inactivité)" if request.args.get("expire") else "Déconnexion")
    session.clear()
    if request.args.get("expire"):
        flash(f"Session fermée après {DELAI_INACTIVITE_MIN} minutes d'inactivité. Reconnectez-vous.", "warning")
    return redirect(url_for("login"))


@app.route("/session/ping")
@login_required
def session_ping():
    """Appelé par la page tant que l'utilisateur est actif : prolonge la session."""
    return ("", 204)


# ---------------------------------------------------------------- Utilitaires métier
def reservations_client(client_id):
    """{lot_id: quantité} réservée pour ce client (réservations actives)."""
    if not client_id:
        return {}
    return {r["lot_id"]: r["n"] for r in query(
        "SELECT lot_id, SUM(quantite) AS n FROM reservations WHERE client_id=? AND actif=1 GROUP BY lot_id",
        (client_id,))}


def dispo_pour(lot, mes_reservations):
    """Doses d'un lot que ce client peut acheter : le stock moins ce qui est réservé pour d'autres."""
    return max(0, lot["stock"] - (lot["reserve"] - mes_reservations.get(lot["id"], 0)))


def consommer_reservation(con, lot_id, client_id, prise):
    """Une vente au client qui a réservé réduit d'autant sa réservation."""
    reste = prise
    for r in con.execute("SELECT id, quantite FROM reservations WHERE lot_id=? AND client_id=? AND actif=1"
                         " ORDER BY id", (lot_id, client_id)).fetchall():
        if reste <= 0:
            break
        pris = min(reste, r["quantite"])
        con.execute("UPDATE reservations SET quantite=?, actif=? WHERE id=?",
                    (r["quantite"] - pris, 1 if r["quantite"] > pris else 0, r["id"]))
        reste -= pris


def statut_lot(l):
    """Statut affiché : vendu (plus de stock), réservé (tout le stock est réservé) ou disponible."""
    if l["stock"] <= 0:
        return "vendu"
    if l["reserve"] >= l["stock"]:
        return "réservé"
    return "disponible"


@app.template_filter("statut_lot")
def filtre_statut_lot(l):
    return statut_lot(l)


def stocks_utilisables(client_id=None):
    """Stock vendable par vaccin : lots conformes et non périmés, hors doses réservées pour d'autres clients."""
    rows = query(STOCK_SQL + " WHERE l.statut='conforme' AND l.date_peremption >= ?",
                 (date.today().isoformat(),))
    mine = reservations_client(client_id)
    total = {}
    for r in rows:
        total[r["vaccin_id"]] = total.get(r["vaccin_id"], 0) + dispo_pour(r, mine)
    return total


_UNITES = ("zéro", "un", "deux", "trois", "quatre", "cinq", "six", "sept", "huit", "neuf", "dix", "onze",
           "douze", "treize", "quatorze", "quinze", "seize")
_DIZAINES = ("", "", "vingt", "trente", "quarante", "cinquante", "soixante")


def _lettres_100(n):
    if n < 17:
        return _UNITES[n]
    if n < 20:
        return "dix-" + _UNITES[n - 10]
    if n < 70:
        d, u = divmod(n, 10)
        if u == 0:
            return _DIZAINES[d]
        return _DIZAINES[d] + (" et un" if u == 1 else "-" + _UNITES[u])
    if n < 80:
        return "soixante et onze" if n == 71 else "soixante-" + _lettres_100(n - 60)
    return "quatre-vingts" if n == 80 else "quatre-vingt-" + _lettres_100(n - 80)


def _lettres_1000(n, final=True):
    c, r = divmod(n, 100)
    texte = ""
    if c:
        texte = "cent" if c == 1 else _UNITES[c] + " cent"
        if r == 0 and final and c > 1:
            texte += "s"
    if r:
        reste = _lettres_100(r)
        if r == 80 and not final:
            reste = "quatre-vingt"
        texte = (texte + " " + reste).strip()
    return texte


def nombre_en_lettres(n):
    """12500 -> « douze mille cinq cents » (pour « Arrêté la présente à la somme de… »)."""
    n = int(round(n))
    if n == 0:
        return "zéro"
    parts = []
    for echelle, nom in ((10 ** 9, "milliard"), (10 ** 6, "million")):
        q, n = divmod(n, echelle)
        if q:
            parts.append(f"{_lettres_1000(q)} {nom}" + ("s" if q > 1 else ""))
    q, r = divmod(n, 1000)
    if q:
        parts.append("mille" if q == 1 else _lettres_1000(q, final=False) + " mille")
    if r:
        parts.append(_lettres_1000(r))
    return " ".join(parts)


def jours_restants(date_peremption):
    return (date.fromisoformat(date_peremption) - date.today()).days


def notifier(sujet, corps, roles_dest=(), user_ids=()):
    """Message interne aux utilisateurs actifs de ces rôles et/ou à ces utilisateurs (sauf l'expéditeur)."""
    expediteur = session["user"]["id"]
    destinataires = set(user_ids)
    for r in roles_dest:
        destinataires |= {u["id"] for u in query("SELECT id FROM users WHERE role=? AND actif=1", (r,))}
    for uid in destinataires - {expediteur}:
        db().execute("INSERT INTO messages(expediteur_id,destinataire_id,sujet,corps,date)"
                     " VALUES (?,?,?,?,?)", (expediteur, uid, sujet, corps, now()))
    db().commit()


def notifier_admins(sujet, corps):
    notifier(sujet, corps, roles_dest=("admin", "responsable_stock"))


# ---------------------------------------------------------------- Tableau de bord
# ---------------------------------------------------------------- Graphiques (SVG sans dépendance)
MOIS_FR = ("Janv", "Févr", "Mars", "Avr", "Mai", "Juin", "Juil", "Août", "Sept", "Oct", "Nov", "Déc")


def derniers_mois(n=6):
    """Liste des n derniers mois (le mois courant inclus) : [(« 2026-11 », « Nov 26 »), ...]."""
    y, m = date.today().year, date.today().month
    res = []
    for _ in range(n):
        res.append((f"{y}-{m:02d}", f"{MOIS_FR[m - 1]} {str(y)[2:]}"))
        m -= 1
        if m == 0:
            y, m = y - 1, 12
    return res[::-1]


def sommet_graduation(v):
    """Plus petite valeur « ronde » >= v, pour l'échelle verticale."""
    if v <= 0:
        return 1
    mag = 10 ** math.floor(math.log10(v))
    for k in (1, 1.2, 1.6, 2, 2.4, 2.8, 3.2, 4, 4.8, 6, 8, 10):
        if v <= k * mag:
            return k * mag
    return 10 * mag


def _fmt(v):
    return f"{v:,.0f}".replace(",", " ")


def _cadre(labels, haut):
    """Axes, grille et libellés communs aux deux graphiques ; renvoie (svg_partiel, geometrie).
    Les couleurs viennent de la feuille de style (classes g-*), pour suivre le mode clair / sombre."""
    G, D, H, B = 58, 16, 26, 38           # marges gauche, droite, haut, bas
    W, T = 640, 300
    zone_w, zone_h = W - G - D, T - H - B
    out = []
    for i in range(5):
        val = haut * i / 4
        y = H + zone_h - zone_h * i / 4
        tirets = "" if i == 0 else ' stroke-dasharray="4 4"'
        out.append(f'<line class="g-grille" x1="{G}" y1="{y:.1f}" x2="{W - D}" y2="{y:.1f}" stroke-width="1"{tirets}/>')
        out.append(f'<text class="g-axe" x="{G - 10}" y="{y + 4:.1f}" text-anchor="end">{_fmt(val)}</text>')
    pas = zone_w / len(labels)
    for i, lab in enumerate(labels):
        out.append(f'<text class="g-lib" x="{G + pas * (i + 0.5):.1f}" y="{T - 12}" text-anchor="middle">{lab}</text>')
    return out, (G, H, zone_w, zone_h, pas, W, T)


def _svg(W, T, titre, corps):
    return Markup(f'<svg class="graph" viewBox="0 0 {W} {T}" role="img" aria-label="{titre}">' + corps + "</svg>")


def svg_barres(labels, valeurs, couleur=None):
    haut = sommet_graduation(max(valeurs) if valeurs else 0)
    out, (G, H, zw, zh, pas, W, T) = _cadre(labels, haut)
    out.insert(0, '<defs><linearGradient id="g-barres" x1="0" y1="0" x2="0" y2="1">'
                  '<stop offset="0" style="stop-color:var(--g-barre-1)"/><stop offset="1" style="stop-color:var(--g-barre-2)"/>'
                  '</linearGradient></defs>')
    for i, v in enumerate(valeurs):
        h = zh * v / haut
        x = G + pas * i + pas * 0.18
        w = pas * 0.64
        out.append(f'<rect class="g-barre" x="{x:.1f}" y="{H + zh - h:.1f}" width="{w:.1f}" height="{h:.1f}" rx="6" fill="url(#g-barres)">'
                   f'<title>{labels[i]} : {_fmt(v)}</title></rect>')
        if v:
            out.append(f'<text class="g-val" x="{x + w / 2:.1f}" y="{H + zh - h - 7:.1f}" text-anchor="middle">{_fmt(v)}</text>')
    if not any(valeurs):
        out.append(f'<text class="g-vide" x="{W / 2}" y="{H + zh / 2}" text-anchor="middle">Aucune donnée sur la période</text>')
    return _svg(W, T, "Doses vendues par mois", "".join(out))


def svg_ligne(labels, valeurs, couleur=None):
    haut = sommet_graduation(max(valeurs) if valeurs else 0)
    out, (G, H, zw, zh, pas, W, T) = _cadre(labels, haut)
    out.insert(0, '<defs><linearGradient id="g-aire" x1="0" y1="0" x2="0" y2="1">'
                  '<stop offset="0" style="stop-color:var(--g-ligne);stop-opacity:.32"/>'
                  '<stop offset="1" style="stop-color:var(--g-ligne);stop-opacity:0"/></linearGradient></defs>')
    pts = [(G + pas * (i + 0.5), H + zh - zh * v / haut) for i, v in enumerate(valeurs)]
    if pts:
        aire = f"{pts[0][0]:.1f},{H + zh} " + " ".join(f"{x:.1f},{y:.1f}" for x, y in pts) + f" {pts[-1][0]:.1f},{H + zh}"
        out.append(f'<polygon points="{aire}" fill="url(#g-aire)"/>')
        out.append(f'<polyline points="{" ".join(f"{x:.1f},{y:.1f}" for x, y in pts)}" fill="none" '
                   'style="stroke:var(--g-ligne)" stroke-width="3.5" stroke-linejoin="round" stroke-linecap="round"/>')
        for (x, y), v, lab in zip(pts, valeurs, labels):
            out.append(f'<circle class="g-point" cx="{x:.1f}" cy="{y:.1f}" r="5.5"><title>{lab} : {_fmt(v)}</title></circle>')
            if v:
                out.append(f'<text class="g-val" x="{x:.1f}" y="{y - 12:.1f}" text-anchor="middle">{_fmt(v)}</text>')
    return _svg(W, T, "Évolution du stock", "".join(out))


def donnees_graphiques():
    """Stock cumulé en fin de mois et doses vendues par mois, sur les 6 derniers mois."""
    mois = derniers_mois(6)
    cles = [m[0] for m in mois]
    net = {r["m"]: r["net"] for r in query(
        "SELECT substr(date,1,7) AS m, SUM(CASE WHEN type='ENTREE' THEN quantite ELSE -quantite END)"
        " AS net FROM mouvements GROUP BY m")}
    cumul = sum(v for k, v in net.items() if k < cles[0])
    stock = []
    for k in cles:
        cumul += net.get(k, 0)
        stock.append(cumul)
    vendu = {r["m"]: r["q"] for r in query(
        "SELECT substr(v.date,1,7) AS m, SUM(lv.quantite) AS q FROM ventes v"
        " JOIN lignes_vente lv ON lv.vente_id=v.id GROUP BY m")}
    ventes_mois = [vendu.get(k, 0) for k in cles]
    labels = [m[1] for m in mois]
    resume = {"stock_fin": _fmt(stock[-1] if stock else 0),
              "stock_var": (stock[-1] - stock[-2]) if len(stock) > 1 else 0,
              "ventes_total": _fmt(sum(ventes_mois)),
              "ventes_moy": _fmt(sum(ventes_mois) / len(ventes_mois) if ventes_mois else 0)}
    return svg_ligne(labels, stock), svg_barres(labels, ventes_mois), resume


@app.route("/")
@login_required
def index():
    alertes = []
    n_lots = n_perimes = n_proches = 0
    prochaines = []
    for l in query(STOCK_SQL + " ORDER BY l.date_peremption"):
        if l["stock"] <= 0:
            continue
        n_lots += 1
        j = jours_restants(l["date_peremption"])
        if j < 0:
            n_perimes += 1
            alertes.append(("danger", f"PÉRIMÉ : {l['vaccin_nom']} lot {l['numero_lot']} "
                                      f"({l['stock']} en stock)"))
        else:
            if j <= 30:
                n_proches += 1
            if len(prochaines) < 5:
                niveau = "danger" if j <= 30 else "warning" if j <= 90 else "ok"
                prochaines.append({"vaccin": l["vaccin_nom"], "lot": l["numero_lot"],
                                   "date": l["date_peremption"], "jours": j,
                                   "stock": l["stock"], "niveau": niveau})
            for s in SEUILS_PEREMPTION:
                if j <= s:
                    alertes.append(("warning", f"Péremption dans {j} j (≤ {s} j) : "
                                               f"{l['vaccin_nom']} lot {l['numero_lot']} "
                                               f"({l['stock']} en stock)"))
                    break
        if l["statut"] in ("rappelé", "quarantaine"):
            alertes.append(("warning", f"Lot {l['numero_lot']} en statut « {l['statut']} »"))
    utilisables = stocks_utilisables()
    vaccins = []
    n_bas = 0
    for v in query("SELECT * FROM vaccins WHERE actif=1 ORDER BY nom"):
        total = utilisables.get(v["id"], 0)
        bas = total < v["seuil_min"]
        if bas:
            n_bas += 1
            alertes.append(("danger", f"Stock bas : {v['nom']} ({total} < seuil {v['seuil_min']})"))
        pct = 100 if v["seuil_min"] <= 0 else min(100, round(total * 100 / v["seuil_min"]))
        vaccins.append({"nom": v["nom"], "total": total, "seuil": v["seuil_min"],
                        "bas": bas, "pct": pct})
    statuts_cmd = A_TRAITER.get(session["user"]["role"], EN_COURS)
    n_cmd = query(f"SELECT COUNT(*) AS n FROM commandes WHERE statut IN ({', '.join('?' for _ in statuts_cmd)})",
                  statuts_cmd, one=True)["n"] if droit("commandes_voir") else 0
    n_art_bas = 0
    if droit("articles_voir"):
        for a in liste_articles({k: "" for k in ARTICLES_FILTRES}):
            if a["stock"] < a["seuil_min"]:
                n_art_bas += 1
                alertes.append(("danger", f"Stock bas : article {a['nom']} ({a['stock']} < seuil {a['seuil_min']})"))
    vm = query("SELECT COUNT(DISTINCT v.id) AS n, "
               "COALESCE(SUM(lv.quantite * lv.prix_unitaire), 0) AS montant "
               "FROM ventes v LEFT JOIN lignes_vente lv ON lv.vente_id = v.id "
               "WHERE v.date LIKE ?", (date.today().strftime("%Y-%m") + "%",), one=True)
    non_lus = query("SELECT COUNT(*) AS n FROM messages WHERE destinataire_id=? AND lu=0",
                    (session["user"]["id"],), one=True)["n"]
    reste_encaisser, nb_retard = creances() if droit("ventes_voir") else (0, 0)
    if nb_retard:
        alertes.append(("danger", f"{nb_retard} vente(s) à terme en retard de paiement"))
    stats = {"a_encaisser": f"{reste_encaisser:,.0f}".replace(",", " "), "nb_retard": nb_retard, "doses": sum(utilisables.values()), "nb_vaccins": len(vaccins),
             "lots": n_lots, "alertes": len(alertes), "perimes": n_perimes,
             "proches": n_proches, "bas": n_bas, "art_bas": n_art_bas, "commandes": n_cmd,
             "commandes_libelle": "Commande(s) à traiter par vous" if session["user"]["role"] in A_TRAITER
             else "Commande(s) en cours", "ventes": vm["n"],
             "montant": f"{vm['montant']:,.0f}".replace(",", " "), "non_lus": non_lus,
             "debut_mois": date.today().replace(day=1).isoformat()}
    graphique_stock, graphique_ventes, resume_graph = donnees_graphiques()
    return render_template("index.html", alertes=alertes, vaccins=vaccins, stats=stats,
                           prochaines=prochaines, graphique_stock=graphique_stock,
                           graphique_ventes=graphique_ventes, resume_graph=resume_graph)


# ---------------------------------------------------------------- Vaccins
@app.route("/vaccins", methods=["GET", "POST"])
@roles(*DROITS["vaccins_voir"])
def vaccins():
    if request.method == "POST":
        if not droit("vaccins_gerer"):
            flash("Action réservée à un autre rôle : l'ajout d'un vaccin revient au responsable stock.", "danger")
            return redirect(url_for("vaccins"))
        vals, erreur = lire_vaccin()
        if erreur:
            flash(erreur, "danger")
        elif query("SELECT 1 FROM vaccins WHERE lower(nom)=lower(?)", (vals["nom"],), one=True):
            flash(f"Un vaccin « {vals['nom']} » existe déjà.", "danger")
        else:
            execute(f"INSERT INTO vaccins({', '.join(vals)}) VALUES ({', '.join('?' for _ in vals)})",
                    tuple(vals.values()))
            audit(f"Ajout vaccin {vals['nom']}")
            flash("Vaccin ajouté.", "success")
        return redirect(url_for("vaccins"))
    archives = request.args.get("archives") == "1"
    liste = query(
        "SELECT v.*,"
        " (SELECT COUNT(*) FROM lots l WHERE l.vaccin_id=v.id) AS nb_lots,"
        " (SELECT COUNT(*) FROM lignes_vente lv JOIN lots l ON l.id=lv.lot_id"
        "   WHERE l.vaccin_id=v.id) AS nb_ventes,"
        " (SELECT COALESCE(SUM(CASE WHEN m.type='ENTREE' THEN m.quantite ELSE -m.quantite END), 0)"
        "   FROM mouvements m JOIN lots l ON l.id=m.lot_id WHERE l.vaccin_id=v.id) AS stock_total"
        " FROM vaccins v" + ("" if archives else " WHERE v.actif=1") + " ORDER BY v.actif DESC, v.nom")
    vendable = stocks_utilisables()
    liste = [dict(v, vendable=vendable.get(v["id"], 0)) for v in liste]
    return render_template("vaccins.html", vaccins=liste, archives=archives)


# ---------------------------------------------------------------- Recherche et filtres
def args_filtres(*noms):
    """Valeurs des filtres lues dans l'URL (chaînes vides si absents)."""
    return {n: request.args.get(n, "").strip() for n in noms}


def filtres_actifs(flt):
    """Seuls les filtres renseignés : sert à reporter la recherche dans le lien d'export."""
    return {k: v for k, v in flt.items() if v}


LOTS_FILTRES = ("q", "vaccin_id", "statut", "conformite", "delai", "du", "au", "stock")


def liste_lots(flt):
    sql, args = STOCK_SQL + " WHERE 1=1", []
    if flt["q"]:
        sql += " AND (l.numero_lot LIKE ? OR e.nom LIKE ? OR f.nom LIKE ? OR v.nom LIKE ?)"
        args += [f"%{flt['q']}%"] * 4
    if flt["vaccin_id"].isdigit():
        sql += " AND l.vaccin_id=?"
        args.append(int(flt["vaccin_id"]))
    if flt["conformite"] in STATUTS:
        sql += " AND l.statut=?"
        args.append(flt["conformite"])
    if flt["du"]:
        sql += " AND l.date_peremption >= ?"
        args.append(flt["du"])
    if flt["au"]:
        sql += " AND l.date_peremption <= ?"
        args.append(flt["au"])
    res = []
    for l in query(sql + " ORDER BY l.date_peremption", args):
        j = jours_restants(l["date_peremption"])
        if flt["stock"] == "1" and l["stock"] <= 0:
            continue
        if flt["statut"] in STATUTS_LOT and statut_lot(l) != flt["statut"]:
            continue
        if flt["delai"] == "perimes" and j >= 0:
            continue
        if flt["delai"].isdigit() and not 0 <= j <= int(flt["delai"]):
            continue
        res.append(dict(l, jours=j))
    return res


MOUVEMENTS_FILTRES = ("q", "type", "nature", "vaccin_id", "du", "au")


def liste_mouvements(flt):
    sql = ("SELECT m.*, l.numero_lot, v.nom AS vaccin_nom, u.username FROM mouvements m"
           " JOIN lots l ON l.id=m.lot_id JOIN vaccins v ON v.id=l.vaccin_id"
           " LEFT JOIN users u ON u.id=m.user_id WHERE 1=1")
    args = []
    if flt["q"]:
        sql += " AND (l.numero_lot LIKE ? OR v.nom LIKE ? OR m.motif LIKE ? OR u.username LIKE ?)"
        args += [f"%{flt['q']}%"] * 4
    if flt["type"] in ("ENTREE", "SORTIE"):
        sql += " AND m.type=?"
        args.append(flt["type"])
    if flt["nature"] in ("TEMOIN", "DETRUIT"):
        sql += " AND m.nature=?"
        args.append(flt["nature"])
    if flt["vaccin_id"].isdigit():
        sql += " AND l.vaccin_id=?"
        args.append(int(flt["vaccin_id"]))
    if flt["du"]:
        sql += " AND substr(m.date,1,10) >= ?"
        args.append(flt["du"])
    if flt["au"]:
        sql += " AND substr(m.date,1,10) <= ?"
        args.append(flt["au"])
    return query(sql + " ORDER BY m.id DESC", args)


VENTES_FILTRES = ("q", "vaccin_id", "vendeur_id", "du", "au", "mode")
VENTES_FROM = (" FROM ventes v JOIN clients c ON c.id=v.client_id JOIN users u ON u.id=v.user_id"
               " JOIN lignes_vente lv ON lv.vente_id=v.id JOIN lots l ON l.id=lv.lot_id"
               " JOIN vaccins va ON va.id=l.vaccin_id WHERE 1=1")


def clause_ventes(flt):
    sql, args = "", []
    if flt["q"]:
        sql += " AND (c.nom LIKE ? OR u.username LIKE ? OR CAST(v.id AS TEXT)=?)"
        args += [f"%{flt['q']}%", f"%{flt['q']}%", flt["q"]]
    if flt["vaccin_id"].isdigit():
        sql += " AND l.vaccin_id=?"
        args.append(int(flt["vaccin_id"]))
    if flt["vendeur_id"].isdigit():
        sql += " AND v.user_id=?"
        args.append(int(flt["vendeur_id"]))
    if flt["mode"] in MODES_VENTE:
        sql += " AND v.mode=?"
        args.append(flt["mode"])
    if flt["du"]:
        sql += " AND substr(v.date,1,10) >= ?"
        args.append(flt["du"])
    if flt["au"]:
        sql += " AND substr(v.date,1,10) <= ?"
        args.append(flt["au"])
    return sql, args


# ---------------------------------------------------------------- Lots
def resoudre_vaccin(f):
    """Retrouve le vaccin saisi par son nom (le crée s'il est nouveau) ; renvoie (id, erreur)."""
    nom = re.sub(r"\s+", " ", f.get("vaccin_nom", "")).strip()[:120]
    if not nom:
        return None, "Indiquez le nom du vaccin."
    prix_txt = f.get("prix_unitaire", "").strip()
    prix = decimal(prix_txt) if prix_txt else None
    if prix_txt and prix is None:
        return None, "Le prix unitaire doit être un nombre positif."
    v = query("SELECT * FROM vaccins WHERE lower(nom)=lower(?)", (nom,), one=True)
    if v is None:
        if f.get("type") not in TYPES_VACCIN:
            return None, f"« {nom} » n'est pas encore dans le catalogue : choisissez son type pour le créer."
        seuil = entier(f.get("seuil_min") or 0)
        if seuil is None:
            return None, "Le seuil minimal doit être un nombre entier positif."
        vid = execute("INSERT INTO vaccins(nom, type, seuil_min, prix_unitaire) VALUES (?,?,?,?)",
                      (nom, f["type"], seuil, prix or 0))
        audit(f"Nouveau vaccin au catalogue (à la réception d'un lot) : {nom}")
        return vid, None
    if not v["actif"]:
        return None, f"« {v['nom']} » est archivé : restaurez-le dans le catalogue avant de réceptionner un lot."
    if prix is not None and prix > 0 and abs(prix - v["prix_unitaire"]) > 1e-9:
        execute("UPDATE vaccins SET prix_unitaire=? WHERE id=?", (prix, v["id"]))
        audit(f"Prix unitaire de {v['nom']} : {filtre_nombre(v['prix_unitaire'])} -> {filtre_nombre(prix)}")
    return v["id"], None


def fournisseur_par_nom(nom):
    """Identifiant de la provenance saisie (créée dans les fournisseurs si elle est nouvelle)."""
    nom = re.sub(r"\s+", " ", nom or "").strip()[:120]
    if not nom:
        return None
    ligne = query("SELECT id FROM fournisseurs WHERE lower(nom)=lower(?)", (nom,), one=True)
    return ligne["id"] if ligne else execute("INSERT INTO fournisseurs(nom) VALUES (?)", (nom,))


@app.route("/lots", methods=["GET", "POST"])
@login_required
def lots():
    if request.method == "POST":
        if not peut_gerer():
            flash("Accès refusé pour votre rôle.", "danger")
            return redirect(url_for("lots"))
        f = request.form
        retour = redirect(url_for("lots"))
        numero = f.get("numero_lot", "").strip()[:60]
        qte = entier(f.get("quantite"), 1)
        try:
            fab, per = date.fromisoformat(f.get("date_fabrication", "")), date.fromisoformat(f.get("date_peremption", ""))
        except ValueError:
            fab = per = None
        emplacement = ref_id("emplacements", f.get("emplacement_id"))
        provenance = f.get("provenance", "").strip()
        erreur = None
        if not numero:
            erreur = "Le numéro de lot est obligatoire."
        elif qte is None:
            erreur = "La quantité doit être un nombre entier supérieur à zéro."
        elif fab is None or per is None or per <= fab:
            erreur = "Dates invalides : la péremption doit être postérieure à la fabrication."
        elif emplacement is None:
            erreur = "Choisissez l'emplacement : Chambre froide ou Local."
        elif provenance not in PROVENANCES_BASE:
            erreur = "Choisissez la provenance du lot dans la liste."
        elif query("SELECT 1 FROM lots WHERE lower(numero_lot)=lower(?)", (numero,), one=True):
            erreur = "Ce numéro de lot existe déjà."
        if erreur:
            flash(erreur, "danger")
            return retour
        fichiers, erreur_fichier = fichiers_joints(FICHIERS_LOT)
        if erreur_fichier:
            flash(erreur_fichier, "danger")
            return retour
        vaccin_id, erreur = resoudre_vaccin(f)
        if erreur:
            for _type, nom_stocke, _orig, _taille in fichiers:
                supprimer_fichier(nom_stocke)
            flash(erreur, "danger")
            return retour
        lot_id = execute("INSERT INTO lots(vaccin_id,numero_lot,date_fabrication,"
                         "date_peremption,fournisseur_id,emplacement_id) VALUES (?,?,?,?,?,?)",
                         (vaccin_id, numero, fab.isoformat(), per.isoformat(),
                          fournisseur_par_nom(provenance), emplacement))
        execute("INSERT INTO mouvements(lot_id,type,quantite,motif,date,user_id)"
                " VALUES (?,?,?,?,?,?)",
                (lot_id, "ENTREE", qte, "Réception initiale", now(), session["user"]["id"]))
        for type_doc, stocke, original, taille in fichiers:
            ajouter_piece("lot", lot_id, type_doc, "", stocke, original, taille)
        audit(f"Réception lot {numero} ({qte})" + (f" avec {len(fichiers)} document(s)" if fichiers else ""))
        flash("Lot enregistré et entrée de stock créée.", "success")
        return retour
    flt = args_filtres(*LOTS_FILTRES)
    catalogue = {v["nom"].lower(): {"prix": v["prix_unitaire"]}
                 for v in query("SELECT nom, prix_unitaire FROM vaccins WHERE actif=1")}
    return render_template("lots.html", lots=liste_lots(flt), flt=flt, fq=filtres_actifs(flt),
                           vaccins=query("SELECT id, nom FROM vaccins WHERE actif=1 ORDER BY nom COLLATE NOCASE"),
                           vaccins_tous=query("SELECT id, nom FROM vaccins ORDER BY nom COLLATE NOCASE"),
                           fournisseurs=query("SELECT id, nom FROM fournisseurs WHERE actif=1 ORDER BY nom COLLATE NOCASE"),
                           emplacements=query("SELECT id, nom FROM emplacements WHERE actif=1 ORDER BY nom COLLATE NOCASE"),
                           STATUTS_LOT=STATUTS_LOT, catalogue_js=catalogue, types_vaccin=TYPES_VACCIN)


@app.route("/lots/<int:lot_id>", methods=["GET", "POST"])
@login_required
def lot_detail(lot_id):
    lot = query(STOCK_SQL + " WHERE l.id=?", (lot_id,), one=True)
    if lot is None:
        return redirect(url_for("lots"))
    if request.method == "POST":
        if not peut_gerer():
            flash("Accès refusé pour votre rôle.", "danger")
            return redirect(url_for("lot_detail", lot_id=lot_id))
        statut = request.form["statut"]
        if statut in STATUTS:
            execute("UPDATE lots SET statut=? WHERE id=?", (statut, lot_id))
            audit(f"Lot {lot['numero_lot']} -> statut {statut}")
            flash("Statut mis à jour.", "success")
        return redirect(url_for("lot_detail", lot_id=lot_id))
    mouvements = query("SELECT m.*, u.username FROM mouvements m LEFT JOIN users u ON u.id=m.user_id"
                       " WHERE m.lot_id=? ORDER BY m.id DESC", (lot_id,))
    clients = query("SELECT c.nom, c.telephone, v.date, lv.quantite FROM lignes_vente lv"
                    " JOIN ventes v ON v.id=lv.vente_id JOIN clients c ON c.id=v.client_id"
                    " WHERE lv.lot_id=? ORDER BY v.date DESC", (lot_id,))
    return render_template("lot.html", lot=lot, jours=jours_restants(lot["date_peremption"]),
                           mouvements=mouvements, clients=clients,
                           pieces=pieces_de("lot", lot_id) if droit("pj_fournisseur_voir") else [],
                           types_pj=OBJETS_PJ["lot"]["types"])


# ---------------------------------------------------------------- Entrées / sorties
@app.route("/mouvements", methods=["GET", "POST"])
@roles(*DROITS["mouvements_voir"])
def mouvements():
    if request.method == "POST":
        if not droit("mouvements_saisir"):
            flash("Action réservée à un autre rôle : la saisie des entrées et sorties revient au responsable stock.", "danger")
            return redirect(url_for("mouvements"))
        lot = query(STOCK_SQL + " WHERE l.id=?", (int(request.form["lot_id"]),), one=True)
        type_ = request.form["type"]
        qte = int(request.form["quantite"])
        motif = request.form.get("motif", "")
        if qte <= 0 or lot is None or type_ not in ("ENTREE", "SORTIE") \
                or motif not in (MOTIFS_ENTREE if type_ == "ENTREE" else MOTIFS_SORTIE):
            flash("Saisie invalide : choisissez un type et un motif de la liste.", "danger")
        elif type_ == "SORTIE" and qte > lot["stock"] - lot["reserve"]:
            flash(f"Stock insuffisant : {lot['stock'] - lot['reserve']} dose(s) non réservée(s) disponible(s)"
                  f" ({lot['reserve']} réservée(s) pour des clients).", "danger")
        else:
            execute("INSERT INTO mouvements(lot_id,type,quantite,motif,date,user_id,nature)"
                    " VALUES (?,?,?,?,?,?,?)",
                    (lot["id"], type_, qte, motif, now(), session["user"]["id"],
                     "DETRUIT" if motif == "Destruction" else None))
            audit(f"{type_} {qte} du lot {lot['numero_lot']} ({motif})")
            flash("Mouvement enregistré.", "success")
        return redirect(url_for("mouvements"))
    flt = args_filtres(*MOUVEMENTS_FILTRES)
    tous = liste_mouvements(flt)
    reservations = query("SELECT r.*, c.nom AS client, l.numero_lot, v.nom AS vaccin_nom, u.username"
                         " FROM reservations r JOIN clients c ON c.id=r.client_id JOIN lots l ON l.id=r.lot_id"
                         " JOIN vaccins v ON v.id=l.vaccin_id LEFT JOIN users u ON u.id=r.user_id"
                         " WHERE r.actif=1 ORDER BY r.id DESC")
    return render_template("mouvements.html", mouvements=tous[:200], total=len(tous), flt=flt,
                           fq=filtres_actifs(flt), reservations=reservations,
                           MOTIFS_ENTREE=MOTIFS_ENTREE,
                           clients=query("SELECT id, nom FROM clients ORDER BY nom COLLATE NOCASE"),
                           vaccins=query("SELECT id, nom FROM vaccins ORDER BY nom"),
                           lots=query(STOCK_SQL + " ORDER BY l.date_peremption"))


@app.route("/mouvements/reservation", methods=["POST"])
@roles(*DROITS["reservations_gerer"])
def mouvement_reservation():
    lot = query(STOCK_SQL + " WHERE l.id=?", (entier(request.form.get("lot_id"), 1) or 0,), one=True)
    client = query("SELECT id, nom FROM clients WHERE id=?", (entier(request.form.get("client_id"), 1) or 0,), one=True)
    qte = entier(request.form.get("quantite"), 1)
    note = request.form.get("note", "").strip()[:200]
    if lot is None or client is None or qte is None:
        flash("Réservation invalide : choisissez un lot, un client et une quantité.", "danger")
    elif lot["statut"] != "conforme":
        flash("Seuls les lots conformes peuvent être réservés.", "danger")
    elif qte > lot["stock"] - lot["reserve"]:
        flash(f"Quantité trop élevée : {lot['stock'] - lot['reserve']} dose(s) non réservée(s) sur ce lot.", "danger")
    else:
        execute("INSERT INTO reservations(lot_id, client_id, quantite, date, user_id, note) VALUES (?,?,?,?,?,?)",
                (lot["id"], client["id"], qte, now(), session["user"]["id"], note or None))
        audit(f"Réservation de {qte} dose(s) du lot {lot['numero_lot']} pour {client['nom']}")
        notifier("Nouvelle réservation de vaccins",
                 f"Le CSA a réservé {qte} dose(s) de {lot['vaccin_nom']} (lot {lot['numero_lot']}) pour {client['nom']}."
                 " Ces doses ne doivent pas être vendues à d'autres clients.", roles_dest=("responsable_stock",))
        flash(f"{qte} dose(s) du lot {lot['numero_lot']} réservée(s) pour {client['nom']}.", "success")
    return redirect(url_for("mouvements") + "#reservations")


@app.route("/mouvements/reservation/<int:rid>/annuler", methods=["POST"])
@roles(*DROITS["reservations_gerer"])
def mouvement_reservation_annuler(rid):
    r = query("SELECT r.*, c.nom AS client, l.numero_lot FROM reservations r JOIN clients c ON c.id=r.client_id"
              " JOIN lots l ON l.id=r.lot_id WHERE r.id=? AND r.actif=1", (rid,), one=True)
    if r:
        execute("UPDATE reservations SET actif=0 WHERE id=?", (rid,))
        audit(f"Annulation de la réservation de {r['quantite']} dose(s) du lot {r['numero_lot']} pour {r['client']}")
        notifier("Réservation annulée",
                 f"Le CSA a annulé la réservation de {r['quantite']} dose(s) du lot {r['numero_lot']} pour {r['client']} :"
                 " ces doses sont de nouveau disponibles.", roles_dest=("responsable_stock",))
        flash("Réservation annulée : les doses sont de nouveau disponibles.", "success")
    return redirect(url_for("mouvements") + "#reservations")


# ---------------------------------------------------------------- Témoins et destructions d'un lot
def sortie_speciale(lot_id, nature):
    """Retire des doses du stock disponible : mise de côté de témoins ou destruction."""
    lot = query(STOCK_SQL + " WHERE l.id=?", (lot_id,), one=True)
    if lot is None:
        flash("Lot introuvable.", "danger")
        return redirect(url_for("lots"))
    retour = redirect(url_for("lot_detail", lot_id=lot_id))
    quantite = entier(request.form.get("quantite"), 1)
    motif = request.form.get("motif", "").strip()[:200]
    if quantite is None:
        flash("La quantité doit être un nombre entier supérieur à zéro.", "danger")
    elif nature == "DETRUIT" and not motif:
        flash("Le motif de la destruction est obligatoire.", "danger")
    elif quantite > lot["stock"]:
        flash(f"Quantité supérieure au stock disponible du lot ({lot['stock']}).", "danger")
    else:
        execute("INSERT INTO mouvements(lot_id, type, quantite, motif, date, user_id, nature)"
                " VALUES (?,?,?,?,?,?,?)",
                (lot_id, "SORTIE", quantite, motif or "Mise de côté de témoins", now(),
                 session["user"]["id"], nature))
        if nature == "TEMOIN":
            audit(f"Lot {lot['numero_lot']} : {quantite} témoin(s) mis de côté")
            flash(f"{quantite} témoin(s) mis de côté. Disponible : {lot['stock'] - quantite}.", "success")
        else:
            audit(f"Lot {lot['numero_lot']} : destruction de {quantite} dose(s) ({motif})")
            reste = lot["stock"] - quantite
            if reste == 0 and lot["temoins"] == 0:
                execute("UPDATE lots SET statut='détruit' WHERE id=?", (lot_id,))
                audit(f"Lot {lot['numero_lot']} -> statut détruit")
                flash("Destruction enregistrée : le lot est entièrement détruit (statut « détruit »).", "success")
            else:
                flash(f"Destruction enregistrée. Disponible : {reste}.", "success")
    return retour


@app.route("/lots/<int:lot_id>/temoins", methods=["POST"])
@roles(*DROITS["lots_gerer"])
def lot_temoins(lot_id):
    return sortie_speciale(lot_id, "TEMOIN")


@app.route("/lots/<int:lot_id>/destruction", methods=["POST"])
@roles(*DROITS["lots_gerer"])
def lot_destruction(lot_id):
    return sortie_speciale(lot_id, "DETRUIT")


# ---------------------------------------------------------------- Fiche vaccin et fiches techniques
TYPES_VACCIN = ("viral", "bactérien", "vivant atténué", "inactivé")
UPLOAD_DIR = os.path.join(BASE_DIR, "uploads")
TAILLE_MAX_FICHIER = 10 * 1024 * 1024
app.config["MAX_CONTENT_LENGTH"] = 12 * 1024 * 1024
app.config["PERMANENT_SESSION_LIFETIME"] = timedelta(minutes=DELAI_INACTIVITE_MIN)
app.jinja_env.globals["delai_inactivite"] = DELAI_INACTIVITE_MIN
# extension autorisée -> début attendu du contenu (empêche de déguiser un autre type de fichier)
SIGNATURES = {"pdf": b"%PDF", "png": b"\x89PNG", "jpg": b"\xff\xd8", "jpeg": b"\xff\xd8",
              "docx": b"PK", "xlsx": b"PK", "doc": b"\xd0\xcf\x11\xe0", "xls": b"\xd0\xcf\x11\xe0"}


@app.errorhandler(413)
def fichier_trop_gros(_erreur):
    flash("Fichier trop volumineux : 10 Mo maximum.", "danger")
    return redirect(request.referrer or url_for("index"))


def supprimer_fichier(nom_stocke):
    try:
        os.remove(os.path.join(UPLOAD_DIR, nom_stocke))
    except OSError:
        pass


def lire_vaccin():
    """Lit et vérifie le formulaire d'un vaccin ; renvoie (valeurs, erreur)."""
    f = request.form
    nom = f.get("nom", "").strip()[:120]
    if not nom:
        return None, "Le nom du vaccin est obligatoire."
    if f.get("type") not in TYPES_VACCIN:
        return None, "Type de vaccin invalide."
    try:
        doses = int(f.get("doses") or 1)
        tmin = float(f.get("temp_min") or 2)
        tmax = float(f.get("temp_max") or 8)
        seuil = int(f.get("seuil_min") or 0)
        prix = decimal(f.get("prix_unitaire") or 0)
    except ValueError:
        return None, "Les valeurs numériques sont invalides."
    if prix is None:
        return None, "Le prix unitaire doit être un nombre positif."
    if doses < 1 or seuil < 0:
        return None, "Doses par flacon (au moins 1) et seuil (0 ou plus) invalides."
    if tmin > tmax:
        return None, "La température minimale doit être inférieure à la température maximale."
    return {"nom": nom, "type": f["type"], "espece": f.get("espece", "").strip()[:80],
            "fabricant": f.get("fabricant", "").strip()[:80], "doses_par_flacon": doses,
            "temp_min": tmin, "temp_max": tmax, "seuil_min": seuil, "prix_unitaire": prix}, None


@app.route("/vaccins/<int:vid>", methods=["GET", "POST"])
@roles(*DROITS["vaccins_voir"])
def vaccin_detail(vid):
    v = query("SELECT * FROM vaccins WHERE id=?", (vid,), one=True)
    if v is None:
        flash("Vaccin introuvable.", "danger")
        return redirect(url_for("vaccins"))
    if request.method == "POST":
        if not droit("vaccins_gerer"):
            flash("Action réservée au responsable stock.", "danger")
            return redirect(url_for("vaccin_detail", vid=vid))
        vals, erreur = lire_vaccin()
        if erreur:
            flash(erreur, "danger")
        elif query("SELECT 1 FROM vaccins WHERE lower(nom)=lower(?) AND id<>?", (vals["nom"], vid), one=True):
            flash(f"Un vaccin « {vals['nom']} » existe déjà.", "danger")
        else:
            execute(f"UPDATE vaccins SET {', '.join(k + '=?' for k in vals)} WHERE id=?", (*vals.values(), vid))
            audit(f"Vaccin modifié : {v['nom']}" + (f" → {vals['nom']}" if vals["nom"] != v["nom"] else ""))
            flash("Modifications enregistrées.", "success")
            return redirect(url_for("vaccin_detail", vid=vid))
    lots_v = [dict(l, jours=jours_restants(l["date_peremption"]))
              for l in query(STOCK_SQL + " WHERE l.vaccin_id=? ORDER BY l.date_peremption", (vid,))]
    fiches = query("SELECT ft.*, u.username FROM fiches_techniques ft LEFT JOIN users u ON u.id=ft.user_id"
                   " WHERE ft.vaccin_id=? ORDER BY ft.id DESC", (vid,))
    return render_template("vaccin.html", v=v, lots=lots_v, fiches=fiches, types=TYPES_VACCIN,
                           vendable=stocks_utilisables().get(vid, 0),
                           stock_total=sum(l["stock"] for l in lots_v),
                           temoins=sum(l["temoins"] for l in lots_v),
                           detruites=sum(l["detruites"] for l in lots_v))


def stocker_fichier(fichier):
    """Contrôle (extension, taille, contenu) puis enregistre un fichier téléversé.
    Renvoie (nom_stocké, nom_original, taille, erreur)."""
    original = re.sub(r'[\\/:*?"<>|\r\n]', "_", os.path.basename(fichier.filename or ""))[:120]
    extension = original.rsplit(".", 1)[-1].lower() if "." in original else ""
    contenu = fichier.read(TAILLE_MAX_FICHIER + 1)
    if extension not in SIGNATURES:
        return None, None, 0, "Format non accepté. Formats autorisés : " + ", ".join(sorted(SIGNATURES)) + "."
    if len(contenu) > TAILLE_MAX_FICHIER:
        return None, None, 0, "Fichier trop volumineux : 10 Mo maximum."
    if not contenu or not contenu.startswith(SIGNATURES[extension]):
        return None, None, 0, "Le contenu du fichier ne correspond pas à son extension."
    os.makedirs(UPLOAD_DIR, exist_ok=True)
    nom_stocke = f"{secrets.token_hex(16)}.{extension}"
    with open(os.path.join(UPLOAD_DIR, nom_stocke), "wb") as sortie:
        sortie.write(contenu)
    return nom_stocke, original, len(contenu), None


@app.route("/vaccins/<int:vid>/fiches", methods=["POST"])
@roles(*DROITS["vaccins_gerer"])
def fiche_ajouter(vid):
    v = query("SELECT * FROM vaccins WHERE id=?", (vid,), one=True)
    if v is None:
        flash("Vaccin introuvable.", "danger")
        return redirect(url_for("vaccins"))
    retour = redirect(url_for("vaccin_detail", vid=vid))
    fichier = request.files.get("fichier")
    titre = request.form.get("titre", "").strip()[:120]
    if not fichier or not fichier.filename:
        flash("Choisissez un fichier.", "danger")
        return retour
    stocke, original, taille, erreur = stocker_fichier(fichier)
    if erreur:
        flash(erreur, "danger")
    else:
        execute("INSERT INTO fiches_techniques(vaccin_id, titre, version, fichier, nom_original, taille,"
                " date, user_id) VALUES (?,?,?,?,?,?,?,?)",
                (vid, titre or original, request.form.get("version", "").strip()[:40], stocke,
                 original, taille, now(), session["user"]["id"]))
        audit(f"Fiche technique ajoutée au vaccin {v['nom']} : {titre or original}")
        flash("Fiche technique ajoutée.", "success")
    return retour


# ---------------------------------------------------------------- Pièces jointes (factures, bons de livraison…)
TYPES_DOC = {"fiche_fabrication": "Fiche de fabrication", "facture_fournisseur": "Facture fournisseur", "bl_fournisseur": "Bon de livraison fournisseur",
             "facture_client": "Facture client", "bl_client": "Bon de livraison signé (client)",
             "autre": "Autre document"}
# objet -> types de documents autorisés, droit de consultation, droit d'ajout
OBJETS_PJ = {"lot": {"types": ("fiche_fabrication", "bl_fournisseur", "autre"),
                     "voir": "pj_fournisseur_voir", "gerer": "pj_fournisseur_gerer", "table": "lots"},
             "article_mvt": {"types": ("facture_fournisseur", "bl_fournisseur", "autre"),
                             "voir": "pj_fournisseur_voir", "gerer": "pj_fournisseur_gerer",
                             "table": "mouvements_articles"},
             "commande": {"types": ("facture_client", "bl_client", "autre"),
                          "voir": "pj_commande_voir", "gerer": "pj_commande_gerer", "table": "commandes"}}
FICHIERS_FOURNISSEUR = (("facture_fichier", "facture_fournisseur"), ("bl_fichier", "bl_fournisseur"))
FICHIERS_LOT = (("fiche_fichier", "fiche_fabrication"), ("bl_fichier", "bl_fournisseur"))
MAX_PIECES = 20


def fichiers_joints(champs=FICHIERS_FOURNISSEUR):
    """Contrôle et enregistre les fichiers facultatifs d'un formulaire d'enregistrement.
    Renvoie (liste, erreur) ; en cas d'erreur, aucun fichier n'est conservé."""
    stockes = []
    for champ, type_doc in champs:
        fichier = request.files.get(champ)
        if fichier and fichier.filename:
            stocke, original, taille, erreur = stocker_fichier(fichier)
            if erreur:
                for _type, nom_stocke, _orig, _taille in stockes:
                    supprimer_fichier(nom_stocke)
                return [], f"{TYPES_DOC[type_doc]} : {erreur[0].lower() + erreur[1:]}"
            stockes.append((type_doc, stocke, original, taille))
    return stockes, None


def ajouter_piece(objet, objet_id, type_doc, titre, stocke, original, taille):
    return execute("INSERT INTO pieces_jointes(objet, objet_id, type_doc, titre, fichier, nom_original, taille,"
                   " date, user_id) VALUES (?,?,?,?,?,?,?,?,?)",
                   (objet, objet_id, type_doc, titre or original, stocke, original, taille, now(),
                    session["user"]["id"]))


def pieces_de(objet, objet_id):
    return query("SELECT p.*, u.username FROM pieces_jointes p LEFT JOIN users u ON u.id=p.user_id"
                 " WHERE p.objet=? AND p.objet_id=? ORDER BY p.id", (objet, objet_id))


def retirer_pieces(objet, ids):
    """Supprime les pièces jointes (fichiers et lignes) de ces objets."""
    for oid in ids:
        for p in query("SELECT fichier FROM pieces_jointes WHERE objet=? AND objet_id=?", (objet, oid)):
            supprimer_fichier(p["fichier"])
        execute("DELETE FROM pieces_jointes WHERE objet=? AND objet_id=?", (objet, oid))


def url_objet(objet, oid):
    if objet == "lot":
        return url_for("lot_detail", lot_id=oid)
    if objet == "commande":
        return url_for("commande_detail", cmd_id=oid)
    m = query("SELECT article_id FROM mouvements_articles WHERE id=?", (oid,), one=True)
    return url_for("article_detail", aid=m["article_id"]) if m else url_for("articles")


@app.route("/pieces/<objet>/<int:oid>/ajouter", methods=["POST"])
@login_required
def piece_ajouter(objet, oid):
    conf = OBJETS_PJ.get(objet)
    if conf is None or objet == "article_mvt":
        abort(404)
    if not droit(conf["gerer"]):
        flash("Action réservée à un autre rôle.", "danger")
        return redirect(url_for("index"))
    if query(f"SELECT 1 FROM {conf['table']} WHERE id=?", (oid,), one=True) is None:
        flash("Élément introuvable.", "danger")
        return redirect(url_for("index"))
    retour = redirect(url_objet(objet, oid))
    type_doc = request.form.get("type_doc", "")
    fichier = request.files.get("fichier")
    if type_doc not in conf["types"]:
        flash("Type de document invalide.", "danger")
    elif not fichier or not fichier.filename:
        flash("Choisissez un fichier.", "danger")
    elif query("SELECT COUNT(*) AS n FROM pieces_jointes WHERE objet=? AND objet_id=?", (objet, oid),
               one=True)["n"] >= MAX_PIECES:
        flash(f"Limite atteinte : {MAX_PIECES} documents au maximum.", "danger")
    else:
        stocke, original, taille, erreur = stocker_fichier(fichier)
        if erreur:
            flash(erreur, "danger")
        else:
            titre = request.form.get("titre", "").strip()[:120]
            ajouter_piece(objet, oid, type_doc, titre, stocke, original, taille)
            audit(f"Pièce jointe ajoutée ({objet} n°{oid}) : {TYPES_DOC[type_doc]} · {titre or original}")
            flash("Document joint.", "success")
    return retour


@app.route("/pieces/<int:pid>/telecharger")
@login_required
def piece_telecharger(pid):
    p = query("SELECT * FROM pieces_jointes WHERE id=?", (pid,), one=True)
    if p is None or p["objet"] not in OBJETS_PJ or not droit(OBJETS_PJ[p["objet"]]["voir"]):
        flash("Document introuvable ou accès refusé.", "danger")
        return redirect(url_for("index"))
    chemin = os.path.join(UPLOAD_DIR, p["fichier"])
    if not os.path.exists(chemin):
        flash("Le fichier n'est plus disponible sur le serveur.", "danger")
        return redirect(url_objet(p["objet"], p["objet_id"]))
    return send_file(chemin, as_attachment=True, download_name=p["nom_original"])


@app.route("/pieces/<int:pid>/supprimer", methods=["POST"])
@login_required
def piece_supprimer(pid):
    p = query("SELECT * FROM pieces_jointes WHERE id=?", (pid,), one=True)
    if p is None or p["objet"] not in OBJETS_PJ:
        flash("Document introuvable.", "danger")
        return redirect(url_for("index"))
    if not (droit(OBJETS_PJ[p["objet"]]["gerer"]) or droit("supprimer")):
        flash("Action réservée à un autre rôle.", "danger")
        return redirect(url_objet(p["objet"], p["objet_id"]))
    supprimer_fichier(p["fichier"])
    execute("DELETE FROM pieces_jointes WHERE id=?", (pid,))
    audit(f"Pièce jointe supprimée ({p['objet']} n°{p['objet_id']}) : {p['titre']}")
    flash("Document supprimé.", "success")
    return redirect(url_objet(p["objet"], p["objet_id"]))


@app.route("/fiches/<int:fid>/telecharger")
@roles(*DROITS["vaccins_voir"])
def fiche_telecharger(fid):
    ft = query("SELECT * FROM fiches_techniques WHERE id=?", (fid,), one=True)
    if ft is None or not os.path.exists(os.path.join(UPLOAD_DIR, ft["fichier"])):
        flash("Fichier introuvable.", "danger")
        return redirect(url_for("vaccins"))
    return send_file(os.path.join(UPLOAD_DIR, ft["fichier"]), as_attachment=True,
                     download_name=ft["nom_original"])


@app.route("/fiches/<int:fid>/supprimer", methods=["POST"])
@roles(*DROITS["vaccins_gerer"])
def fiche_supprimer(fid):
    ft = query("SELECT * FROM fiches_techniques WHERE id=?", (fid,), one=True)
    if ft is None:
        flash("Fiche introuvable.", "danger")
        return redirect(url_for("vaccins"))
    supprimer_fichier(ft["fichier"])
    execute("DELETE FROM fiches_techniques WHERE id=?", (fid,))
    audit(f"Fiche technique supprimée : {ft['titre']}")
    flash("Fiche technique supprimée.", "success")
    return redirect(url_for("vaccin_detail", vid=ft["vaccin_id"]))


# ---------------------------------------------------------------- Clients : validation et fiche
TYPES_CLIENT = ("éleveur", "vétérinaire", "structure")
NATURES_CLIENT = ("entreprise", "particulier")


def lire_client(prefixe=""):
    """Lit un client dans le formulaire (avec un préfixe éventuel) ; renvoie (valeurs, erreur)."""
    f = request.form
    nom = f.get(prefixe + "nom", "").strip()[:120]
    nature = f.get(prefixe + "nature", "")
    type_ = f.get(prefixe + "type", "")
    email = f.get(prefixe + "email", "").strip()[:120]
    if not nom:
        return None, "le nom du client est obligatoire."
    if nature not in NATURES_CLIENT:
        return None, "choisissez entreprise ou particulier."
    if type_ and type_ not in TYPES_CLIENT:
        return None, "type de client invalide."
    if email and not re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", email):
        return None, "adresse e-mail invalide."
    return {"nom": nom, "nature": nature, "type": type_,
            "telephone": f.get(prefixe + "telephone", "").strip()[:40], "email": email,
            "adresse": f.get(prefixe + "adresse", "").strip()[:200]}, None


@app.route("/clients/<int:cid>", methods=["GET", "POST"])
@roles(*DROITS["clients_voir"])
def client_fiche(cid):
    c = query("SELECT * FROM clients WHERE id=?", (cid,), one=True)
    if c is None:
        flash("Client introuvable.", "danger")
        return redirect(url_for("clients"))
    if request.method == "POST":
        if not droit("clients_gerer"):
            flash("Action réservée au responsable vente.", "danger")
            return redirect(url_for("client_fiche", cid=cid))
        vals, erreur = lire_client()
        if erreur:
            flash(erreur[0].upper() + erreur[1:], "danger")
        elif query("SELECT 1 FROM clients WHERE lower(nom)=lower(?) AND id<>?", (vals["nom"], cid), one=True):
            flash(f"Un client « {vals['nom']} » existe déjà.", "danger")
        else:
            execute(f"UPDATE clients SET {', '.join(k + '=?' for k in vals)} WHERE id=?", (*vals.values(), cid))
            audit(f"Client modifié : {c['nom']}" + (f" → {vals['nom']}" if vals["nom"] != c["nom"] else ""))
            flash("Modifications enregistrées.", "success")
            return redirect(url_for("client_fiche", cid=cid))
    commandes_c = query("SELECT o.*, COALESCE((SELECT SUM(l.quantite*l.prix_unitaire) FROM lignes_commande l"
                        " WHERE l.commande_id=o.id), 0) AS total FROM commandes o WHERE o.client_id=?"
                        " ORDER BY o.id DESC", (cid,)) if droit("commandes_voir") else []
    return render_template("client_fiche.html", c=c, commandes=commandes_c)


# ---------------------------------------------------------------- Commandes clients
COMMANDES_FILTRES = ("q", "statut", "du", "au", "a_traiter", "archives")
COMMANDES_SQL = (
    "SELECT o.*, cl.nom AS client_nom, cl.nature AS client_nature, u.username,"
    " (SELECT COUNT(*) FROM lignes_commande l WHERE l.commande_id = o.id) AS nb_lignes,"
    " COALESCE((SELECT SUM(l.quantite * l.prix_unitaire) FROM lignes_commande l"
    "           WHERE l.commande_id = o.id), 0) AS total"
    " FROM commandes o JOIN clients cl ON cl.id = o.client_id LEFT JOIN users u ON u.id = o.user_id")


def liste_commandes(flt):
    sql, args = COMMANDES_SQL + " WHERE 1=1", []
    if flt["q"]:
        sql += " AND (o.numero LIKE ? OR cl.nom LIKE ?)"
        args += [f"%{flt['q']}%"] * 2
    if flt["a_traiter"] == "1":
        mes_statuts = A_TRAITER.get(session["user"]["role"], EN_COURS)
        sql += f" AND o.statut IN ({', '.join('?' for _ in mes_statuts)})"
        args += list(mes_statuts)
    elif flt["statut"] in STATUTS_COMMANDE:
        sql += " AND o.statut=?"
        args.append(flt["statut"])
    elif flt["archives"] != "1":
        sql += " AND o.statut <> 'archivée'"
    if flt["du"]:
        sql += " AND substr(o.date,1,10) >= ?"
        args.append(flt["du"])
    if flt["au"]:
        sql += " AND substr(o.date,1,10) <= ?"
        args.append(flt["au"])
    return query(sql + " ORDER BY o.id DESC", args)


def historiser(cmd_id, action, statut, motif=None):
    execute("INSERT INTO historique_commande(commande_id, date, user_id, action, statut_apres, motif)"
            " VALUES (?,?,?,?,?,?)", (cmd_id, now(), session["user"]["id"], action, statut, motif))


def decimal(valeur):
    """Nombre décimal >= 0 (virgule ou point), ou None."""
    try:
        n = float(str(valeur).strip().replace(",", ".").replace(" ", ""))
    except ValueError:
        return None
    return n if n >= 0 else None


def lire_commande():
    """Lit le formulaire d'une commande ; renvoie ({client, nouveau, lignes, ...}, erreur)."""
    f = request.form
    client_id, nouveau = None, None
    if f.get("client_id", "").isdigit():
        if query("SELECT 1 FROM clients WHERE id=?", (int(f["client_id"]),), one=True) is None:
            return None, "Client introuvable."
        client_id = int(f["client_id"])
    else:
        nouveau, erreur = lire_client("nouveau_")
        if erreur:
            return None, "Nouveau client : " + erreur
    lignes = []
    for vaccin, quantite, prix in zip(f.getlist("ligne_vaccin"), f.getlist("ligne_quantite"),
                                      f.getlist("ligne_prix")):
        if not (vaccin or quantite.strip() or prix.strip()):
            continue  # ligne laissée vide
        if not (vaccin.isdigit() and query("SELECT 1 FROM vaccins WHERE id=? AND actif=1",
                                           (int(vaccin),), one=True)):
            return None, "Chaque ligne doit avoir un vaccin valide."
        q, p = entier(quantite, 1), decimal(prix)
        if q is None:
            return None, "La quantité de chaque ligne doit être un nombre entier supérieur à zéro."
        if p is None:
            return None, "Le prix unitaire de chaque ligne doit être un nombre positif ou nul."
        lignes.append((int(vaccin), q, p))
    if not lignes:
        return None, "Ajoutez au moins une ligne de commande."
    if len(lignes) > 30:
        return None, "Une commande ne peut pas dépasser 30 lignes."
    souhaitee = f.get("date_souhaitee", "").strip()
    if souhaitee:
        try:
            date.fromisoformat(souhaitee)
        except ValueError:
            return None, "Date de livraison souhaitée invalide."
    return {"client_id": client_id, "nouveau": nouveau, "lignes": lignes, "date_souhaitee": souhaitee or None,
            "notes": f.get("notes", "").strip()[:500]}, None


def saisie_formulaire():
    """Contenu du formulaire tel que saisi (pour le réafficher après une erreur)."""
    f = request.form
    return {"client_id": f.get("client_id", ""), "date_souhaitee": f.get("date_souhaitee", ""),
            "notes": f.get("notes", ""),
            "nouveau": {k: f.get("nouveau_" + k, "") for k in ("nom", "nature", "type", "telephone", "email", "adresse")},
            "lignes": [{"vaccin_id": v, "quantite": q, "prix": p} for v, q, p in
                       zip(f.getlist("ligne_vaccin"), f.getlist("ligne_quantite"), f.getlist("ligne_prix"))]}


def contexte_formulaire_commande():
    vendable = stocks_utilisables()
    vaccins_f = []
    for v in query("SELECT id, nom, prix_unitaire FROM vaccins WHERE actif=1 ORDER BY nom COLLATE NOCASE"):
        dernier = {"prix_unitaire": v["prix_unitaire"]} if v["prix_unitaire"] else query("SELECT prix_unitaire FROM lignes_commande WHERE vaccin_id=? ORDER BY id DESC LIMIT 1",
                        (v["id"],), one=True) or query(
            "SELECT lv.prix_unitaire FROM lignes_vente lv JOIN lots l ON l.id=lv.lot_id"
            " WHERE l.vaccin_id=? ORDER BY lv.id DESC LIMIT 1", (v["id"],), one=True)
        vaccins_f.append({"id": v["id"], "nom": v["nom"], "vendable": vendable.get(v["id"], 0),
                          "dernier_prix": f"{dernier['prix_unitaire']:g}" if dernier else ""})
    return {"clients": query("SELECT id, nom, nature FROM clients ORDER BY nom COLLATE NOCASE"),
            "vaccins": vaccins_f, "types_client": TYPES_CLIENT, "natures_client": NATURES_CLIENT}


def enregistrer_commande(donnees, cmd_id=None):
    """Crée ou remplace (lignes comprises) une commande en une transaction ; renvoie son identifiant."""
    con = db()
    try:
        client_id, client_cree = donnees["client_id"], False
        if client_id is None:
            n = donnees["nouveau"]
            existant = con.execute("SELECT id FROM clients WHERE lower(nom)=lower(?)", (n["nom"],)).fetchone()
            if existant:
                client_id = existant[0]
            else:
                client_id = con.execute(f"INSERT INTO clients({', '.join(n)}) VALUES ({', '.join('?' for _ in n)})",
                                        tuple(n.values())).lastrowid
                client_cree = True
        if cmd_id is None:
            cmd_id = con.execute("INSERT INTO commandes(client_id, date, date_souhaitee, statut, notes, user_id)"
                                 " VALUES (?,?,?,?,?,?)",
                                 (client_id, now(), donnees["date_souhaitee"], "enregistrée", donnees["notes"],
                                  session["user"]["id"])).lastrowid
            con.execute("UPDATE commandes SET numero=? WHERE id=?",
                        (f"CMD-{date.today().year}-{cmd_id:05d}", cmd_id))
        else:
            con.execute("UPDATE commandes SET client_id=?, date_souhaitee=?, notes=? WHERE id=?",
                        (client_id, donnees["date_souhaitee"], donnees["notes"], cmd_id))
            con.execute("DELETE FROM lignes_commande WHERE commande_id=?", (cmd_id,))
        con.executemany("INSERT INTO lignes_commande(commande_id, vaccin_id, quantite, prix_unitaire)"
                        " VALUES (?,?,?,?)", [(cmd_id, v, q, p) for v, q, p in donnees["lignes"]])
        con.commit()
    except Exception:
        con.rollback()
        raise
    if client_cree:
        audit(f"Client créé depuis une commande : {donnees['nouveau']['nom']}")
    return cmd_id


@app.route("/commandes")
@roles(*DROITS["commandes_voir"])
def commandes():
    flt = args_filtres(*COMMANDES_FILTRES)
    lignes = liste_commandes(flt)
    return render_template("commandes.html", commandes=lignes, flt=flt, fq=filtres_actifs(flt),
                           statuts=STATUTS_COMMANDE,
                           total=sum(o["total"] for o in lignes if o["statut"] != "annulée"))


@app.route("/commandes/nouvelle", methods=["GET", "POST"])
@roles(*DROITS["commandes_saisir"])
def commande_nouvelle():
    saisie = None
    if request.method == "POST":
        donnees, erreur = lire_commande()
        if erreur:
            flash(erreur, "danger")
            saisie = saisie_formulaire()
        else:
            cmd_id = enregistrer_commande(donnees)
            numero = query("SELECT numero FROM commandes WHERE id=?", (cmd_id,), one=True)["numero"]
            audit(f"Commande {numero} créée")
            historiser(cmd_id, "Commande créée", "enregistrée")
            flash(f"Commande {numero} enregistrée.", "success")
            return redirect(url_for("commande_detail", cmd_id=cmd_id))
    return render_template("commande_form.html", cmd=None, saisie=saisie, **contexte_formulaire_commande())


@app.route("/commandes/<int:cmd_id>/modifier", methods=["GET", "POST"])
@roles(*DROITS["commandes_saisir"])
def commande_modifier(cmd_id):
    cmd = query(COMMANDES_SQL + " WHERE o.id=?", (cmd_id,), one=True)
    if cmd is None:
        flash("Commande introuvable.", "danger")
        return redirect(url_for("commandes"))
    if cmd["statut"] != "enregistrée":
        flash("Seule une commande au statut « enregistrée » peut être modifiée.", "danger")
        return redirect(url_for("commande_detail", cmd_id=cmd_id))
    saisie = None
    if request.method == "POST":
        donnees, erreur = lire_commande()
        if erreur:
            flash(erreur, "danger")
            saisie = saisie_formulaire()
        else:
            enregistrer_commande(donnees, cmd_id)
            audit(f"Commande {cmd['numero']} modifiée")
            historiser(cmd_id, "Commande modifiée", "enregistrée")
            flash("Commande modifiée.", "success")
            return redirect(url_for("commande_detail", cmd_id=cmd_id))
    else:
        saisie = {"client_id": str(cmd["client_id"]), "date_souhaitee": cmd["date_souhaitee"] or "",
                  "notes": cmd["notes"] or "", "nouveau": {},
                  "lignes": [{"vaccin_id": str(l["vaccin_id"]), "quantite": l["quantite"], "prix": f"{l['prix_unitaire']:g}"}
                             for l in query("SELECT * FROM lignes_commande WHERE commande_id=? ORDER BY id", (cmd_id,))]}
    return render_template("commande_form.html", cmd=cmd, saisie=saisie, **contexte_formulaire_commande())


RENVOI_DROIT = {"transmise": "commandes_controler", "facturée": "commandes_valider"}


def actions_disponibles(cmd):
    """Actions possibles pour l'utilisateur connecté selon le statut de la commande."""
    st = cmd["statut"]
    return {"modifier": st == "enregistrée" and droit("commandes_saisir"),
            "annuler": st == "enregistrée" and droit("commandes_saisir"),
            "transmettre": st == "enregistrée" and droit("commandes_saisir"),
            "facturer": st == "transmise" and droit("commandes_controler"),
            "valider": st == "facturée" and droit("commandes_valider"),
            "livrer": st == "validée" and droit("commandes_livrer"),
            "archiver": st == "livrée" and droit("commandes_archiver"),
            "renvoyer": st in RENVOI_DROIT and droit(RENVOI_DROIT[st])}


@app.route("/commandes/<int:cmd_id>")
@roles(*DROITS["commandes_voir"])
def commande_detail(cmd_id):
    cmd = query(COMMANDES_SQL + " WHERE o.id=?", (cmd_id,), one=True)
    if cmd is None:
        flash("Commande introuvable.", "danger")
        return redirect(url_for("commandes"))
    client = query("SELECT * FROM clients WHERE id=?", (cmd["client_id"],), one=True)
    lignes = query("SELECT l.*, v.nom AS vaccin_nom, v.temp_min, v.temp_max, l.quantite*l.prix_unitaire AS montant"
                   " FROM lignes_commande l JOIN vaccins v ON v.id=l.vaccin_id WHERE l.commande_id=?"
                   " ORDER BY l.id", (cmd_id,))
    vendable, besoin = stocks_utilisables(), {}
    for l in lignes:
        besoin[l["vaccin_id"]] = besoin.get(l["vaccin_id"], 0) + l["quantite"]
    lignes = [dict(l, vendable=vendable.get(l["vaccin_id"], 0),
                   insuffisant=besoin[l["vaccin_id"]] > vendable.get(l["vaccin_id"], 0)) for l in lignes]
    idx = ORDRE_CIRCUIT.index(cmd["statut"]) if cmd["statut"] in ORDRE_CIRCUIT else -1
    etapes, courant = [], False
    for i, (libelle, acteur) in enumerate(ETAPES):
        if idx >= i:
            etat = "fait"
        elif not courant and idx >= 0:
            etat, courant = "courant", True
        else:
            etat = "a-venir"
        etapes.append({"libelle": libelle, "acteur": acteur, "etat": etat})
    act = actions_disponibles(cmd)
    historique = query("SELECT h.*, u.username, u.role FROM historique_commande h LEFT JOIN users u ON u.id=h.user_id"
                       " WHERE h.commande_id=? ORDER BY h.id", (cmd_id,))
    historique = [dict(h) for h in historique]
    if not historique or historique[0]["action"] != "Commande créée":
        createur = query("SELECT username, role FROM users WHERE id=?", (cmd["user_id"],), one=True)
        historique.insert(0, {"date": cmd["date"], "action": "Commande créée", "statut_apres": "enregistrée",
                              "motif": None, "username": createur["username"] if createur else None,
                              "role": createur["role"] if createur else None})
    return render_template(
        "commande.html", cmd=cmd, client=client, lignes=lignes, etapes=etapes, act=act, historique=historique,
        attente=None if any(act.values()) else ATTENTE.get(cmd["statut"]),
        pieces=pieces_de("commande", cmd_id) if droit("pj_commande_voir") else [],
        types_pj=OBJETS_PJ["commande"]["types"],
        factures=query("SELECT * FROM factures WHERE commande_id=? ORDER BY id", (cmd_id,)),
        livraison=query("SELECT * FROM livraisons WHERE commande_id=?", (cmd_id,), one=True),
        date_cmd=datetime.fromisoformat(cmd["date"]).strftime("%d/%m/%Y à %H:%M"),
        imprime_le=datetime.now().strftime("%d/%m/%Y à %H:%M"),
        societe={"nom": ENTREPRISE_NOM, "adresse": ENTREPRISE_ADRESSE, "tel": ENTREPRISE_TEL,
                 "email": ENTREPRISE_EMAIL})


@app.route("/commandes/<int:cmd_id>/annuler", methods=["POST"])
@roles(*DROITS["commandes_saisir"])
def commande_annuler(cmd_id):
    cmd = query("SELECT * FROM commandes WHERE id=?", (cmd_id,), one=True)
    if cmd is None:
        flash("Commande introuvable.", "danger")
        return redirect(url_for("commandes"))
    if cmd["statut"] != "enregistrée":
        flash("Seule une commande au statut « enregistrée » peut être annulée.", "danger")
    else:
        execute("UPDATE commandes SET statut='annulée' WHERE id=?", (cmd_id,))
        audit(f"Commande {cmd['numero']} annulée")
        historiser(cmd_id, "Commande annulée", "annulée")
        flash(f"Commande {cmd['numero']} annulée.", "success")
    return redirect(url_for("commande_detail", cmd_id=cmd_id))


@app.route("/export/commandes.xlsx")
@roles(*DROITS["commandes_voir"])
def export_commandes():
    lignes = [[o["numero"], o["date"].replace("T", " "), o["client_nom"], o["client_nature"], o["nb_lignes"],
               float(o["total"]), o["statut"], o["username"]]
              for o in liste_commandes(args_filtres(*COMMANDES_FILTRES))]
    return classeur_excel("Commandes", "Commandes clients",
                          ["N° commande", "Date", "Client", "Nature", "Lignes", f"Total ({DEVISE})", "Statut", "Créée par"],
                          lignes, [18, 20, 28, 14, 10, 18, 14, 16], "commandes")


# ---------------------------------------------------------------- Circuit de vente : transmission -> livraison
def commande_a_traiter(cmd_id, statuts_attendus):
    """Charge la commande et vérifie son statut ; renvoie (commande, redirection_en_cas_d_erreur)."""
    cmd = query("SELECT * FROM commandes WHERE id=?", (cmd_id,), one=True)
    if cmd is None:
        flash("Commande introuvable.", "danger")
        return None, redirect(url_for("commandes"))
    if cmd["statut"] not in statuts_attendus:
        flash(f"Action impossible : la commande est au statut « {cmd['statut']} ».", "danger")
        return None, redirect(url_for("commande_detail", cmd_id=cmd_id))
    return cmd, None


def passer_a(cmd_id, nouveau, action, motif=None):
    execute("UPDATE commandes SET statut=? WHERE id=?", (nouveau, cmd_id))
    historiser(cmd_id, action, nouveau, motif)


@app.route("/commandes/<int:cmd_id>/transmettre", methods=["POST"])
@roles(*DROITS["commandes_saisir"])
def commande_transmettre(cmd_id):
    cmd, erreur = commande_a_traiter(cmd_id, ("enregistrée",))
    if erreur:
        return erreur
    passer_a(cmd_id, "transmise", "Transmise pour contrôle")
    audit(f"Commande {cmd['numero']} transmise pour contrôle")
    notifier(f"Commande {cmd['numero']} à contrôler", f"La commande {cmd['numero']} est transmise : "
             "contrôlez les quantités et générez la facture.", roles_dest=("responsable_stock",))
    flash("Commande transmise au responsable stock pour contrôle.", "success")
    return redirect(url_for("commande_detail", cmd_id=cmd_id))


@app.route("/commandes/<int:cmd_id>/facturer", methods=["POST"])
@roles(*DROITS["commandes_controler"])
def commande_facturer(cmd_id):
    cmd, erreur = commande_a_traiter(cmd_id, ("transmise",))
    if erreur:
        return erreur
    retour = redirect(url_for("commande_detail", cmd_id=cmd_id))
    lignes = query("SELECT l.*, v.nom AS vaccin_nom FROM lignes_commande l JOIN vaccins v ON v.id=l.vaccin_id"
                   " WHERE l.commande_id=? ORDER BY l.id", (cmd_id,))
    besoin = {}
    for l in lignes:
        besoin[l["vaccin_id"]] = (l["vaccin_nom"], besoin.get(l["vaccin_id"], ("", 0))[1] + l["quantite"])
    vendable = stocks_utilisables(cmd["client_id"])
    manques = [f"{nom} : {q} demandé(s), {vendable.get(v, 0)} vendable(s)"
               for v, (nom, q) in besoin.items() if q > vendable.get(v, 0)]
    if manques:
        flash("Contrôle impossible, stock vendable insuffisant : " + " ; ".join(manques) +
              ". Renvoyez la commande pour correction ou attendez un réapprovisionnement.", "danger")
        return retour
    total = sum(l["quantite"] * l["prix_unitaire"] for l in lignes)
    con = db()
    try:
        fid = con.execute("INSERT INTO factures(commande_id, client_id, date, total, statut, user_id)"
                          " VALUES (?,?,?,?,?,?)", (cmd_id, cmd["client_id"], now(), total, "émise",
                                                    session["user"]["id"])).lastrowid
        numero = f"FAC-{date.today().year}-{fid:05d}"
        con.execute("UPDATE factures SET numero=? WHERE id=?", (numero, fid))
        con.executemany("INSERT INTO lignes_facture(facture_id, vaccin_id, designation, quantite, prix_unitaire)"
                        " VALUES (?,?,?,?,?)", [(fid, l["vaccin_id"], l["vaccin_nom"], l["quantite"],
                                                 l["prix_unitaire"]) for l in lignes])
        con.commit()
    except Exception:
        con.rollback()
        raise
    passer_a(cmd_id, "facturée", f"Contrôle effectué, facture {numero} générée")
    audit(f"Commande {cmd['numero']} : facture {numero} générée")
    notifier(f"Facture {numero} à valider", f"La facture {numero} (commande {cmd['numero']}) attend la "
             "validation CSA.", roles_dest=("csa",))
    flash(f"Contrôle effectué : facture {numero} générée.", "success")
    return retour


@app.route("/commandes/<int:cmd_id>/valider", methods=["POST"])
@roles(*DROITS["commandes_valider"])
def commande_valider(cmd_id):
    cmd, erreur = commande_a_traiter(cmd_id, ("facturée",))
    if erreur:
        return erreur
    execute("UPDATE factures SET validee_par=?, validee_le=? WHERE commande_id=? AND statut='émise'",
            (session["user"]["id"], now(), cmd_id))
    passer_a(cmd_id, "validée", "Vente validée par le CSA")
    audit(f"Commande {cmd['numero']} validée (CSA)")
    notifier(f"Commande {cmd['numero']} prête à livrer", f"La vente {cmd['numero']} est validée par le CSA : "
             "vous pouvez procéder à la livraison.", roles_dest=("responsable_stock",))
    flash("Vente validée. Le responsable stock peut maintenant livrer la commande.", "success")
    return redirect(url_for("commande_detail", cmd_id=cmd_id))


@app.route("/commandes/<int:cmd_id>/renvoyer", methods=["POST"])
@login_required
def commande_renvoyer(cmd_id):
    cmd = query("SELECT * FROM commandes WHERE id=?", (cmd_id,), one=True)
    if cmd is None:
        flash("Commande introuvable.", "danger")
        return redirect(url_for("commandes"))
    if cmd["statut"] not in RENVOI_DROIT or not droit(RENVOI_DROIT[cmd["statut"]]):
        flash("Action impossible pour votre rôle ou pour le statut actuel de la commande.", "danger")
        return redirect(url_for("commande_detail", cmd_id=cmd_id))
    motif = request.form.get("motif", "").strip()[:300]
    if not motif:
        flash("Le motif du renvoi est obligatoire.", "danger")
        return redirect(url_for("commande_detail", cmd_id=cmd_id))
    execute("UPDATE factures SET statut='annulée' WHERE commande_id=? AND statut='émise'", (cmd_id,))
    passer_a(cmd_id, "enregistrée", "Renvoyée pour correction", motif)
    audit(f"Commande {cmd['numero']} renvoyée pour correction ({motif})")
    notifier(f"Commande {cmd['numero']} renvoyée pour correction", f"Motif : {motif}",
             user_ids=(cmd["user_id"],))
    flash("Commande renvoyée au responsable vente pour correction (facture annulée s'il y en avait une).", "success")
    return redirect(url_for("commande_detail", cmd_id=cmd_id))


@app.route("/commandes/<int:cmd_id>/livrer", methods=["POST"])
@roles(*DROITS["commandes_livrer"])
def commande_livrer(cmd_id):
    cmd, erreur = commande_a_traiter(cmd_id, ("validée",))
    if erreur:
        return erreur
    retour = redirect(url_for("commande_detail", cmd_id=cmd_id))
    lignes = query("SELECT l.*, v.nom AS vaccin_nom, v.seuil_min FROM lignes_commande l"
                   " JOIN vaccins v ON v.id=l.vaccin_id WHERE l.commande_id=? ORDER BY l.id", (cmd_id,))
    besoin = {}
    for l in lignes:
        besoin[l["vaccin_id"]] = (l["vaccin_nom"], besoin.get(l["vaccin_id"], ("", 0))[1] + l["quantite"])
    vendable = stocks_utilisables(cmd["client_id"])
    manques = [f"{nom} : {q} demandé(s), {vendable.get(v, 0)} vendable(s)"
               for v, (nom, q) in besoin.items() if q > vendable.get(v, 0)]
    if manques:
        flash("Livraison impossible, stock vendable insuffisant : " + " ; ".join(manques), "danger")
        return retour
    uid, aujourd_hui = session["user"]["id"], date.today().isoformat()
    con = db()
    try:
        vente_id = con.execute("INSERT INTO ventes(client_id, date, user_id, commande_id) VALUES (?,?,?,?)",
                               (cmd["client_id"], now(), uid, cmd_id)).lastrowid
        lots = {}
        mes_res = reservations_client(cmd["client_id"])
        for l in lignes:
            if l["vaccin_id"] not in lots:  # règle FEFO : le lot conforme qui périme en premier part en premier
                lots[l["vaccin_id"]] = [dict(x, stock=dispo_pour(x, mes_res), reel=x["stock"]) for x in query(
                    STOCK_SQL + " WHERE l.vaccin_id=? AND l.statut='conforme' AND l.date_peremption >= ?"
                    " ORDER BY l.date_peremption", (l["vaccin_id"], aujourd_hui))]
            reste = l["quantite"]
            for lot in lots[l["vaccin_id"]]:
                prise = min(reste, lot["stock"])
                if prise <= 0:
                    continue
                con.execute("INSERT INTO lignes_vente(vente_id, lot_id, quantite, prix_unitaire) VALUES (?,?,?,?)",
                            (vente_id, lot["id"], prise, l["prix_unitaire"]))
                con.execute("INSERT INTO mouvements(lot_id, type, quantite, motif, date, user_id, vente_id)"
                            " VALUES (?,?,?,?,?,?,?)",
                            (lot["id"], "SORTIE", prise, f"Livraison commande {cmd['numero']}", now(), uid, vente_id))
                consommer_reservation(con, lot["id"], cmd["client_id"], prise)
                lot["stock"] -= prise
                reste -= prise
            if reste > 0:
                raise ValueError("stock insuffisant")
        liv_id = con.execute("INSERT INTO livraisons(commande_id, vente_id, date, user_id) VALUES (?,?,?,?)",
                             (cmd_id, vente_id, now(), uid)).lastrowid
        numero_bl = f"BL-{date.today().year}-{liv_id:05d}"
        con.execute("UPDATE livraisons SET numero=? WHERE id=?", (numero_bl, liv_id))
        con.execute("UPDATE commandes SET statut='livrée' WHERE id=?", (cmd_id,))
        con.execute("INSERT INTO historique_commande(commande_id, date, user_id, action, statut_apres, motif)"
                    " VALUES (?,?,?,?,?,?)", (cmd_id, now(), uid, f"Livrée, bordereau {numero_bl}", "livrée", None))
        con.commit()
    except ValueError:
        con.rollback()
        flash("Livraison annulée : le stock a changé pendant l'opération. Aucun mouvement n'a été enregistré.", "danger")
        return retour
    except Exception:
        con.rollback()
        raise
    audit(f"Commande {cmd['numero']} livrée (bordereau {numero_bl}, vente #{vente_id})")
    restant = stocks_utilisables()
    for v, (nom, _q) in besoin.items():
        seuil = query("SELECT seuil_min FROM vaccins WHERE id=?", (v,), one=True)["seuil_min"]
        if restant.get(v, 0) < seuil:
            notifier_admins(f"Stock bas : {nom}", f"Après la livraison {numero_bl}, il reste "
                            f"{restant.get(v, 0)} unités (seuil minimal : {seuil}). Prévoir une commande.")
    notifier(f"Commande {cmd['numero']} livrée", f"Bordereau de livraison {numero_bl} établi.",
             user_ids=(cmd["user_id"],))
    flash(f"Livraison enregistrée (bordereau {numero_bl}) ; stock décrémenté (lot qui expire en premier).", "success")
    return redirect(url_for("livraison_detail", liv_id=liv_id))


@app.route("/commandes/<int:cmd_id>/archiver", methods=["POST"])
@roles(*DROITS["commandes_archiver"])
def commande_archiver(cmd_id):
    cmd, erreur = commande_a_traiter(cmd_id, ("livrée",))
    if erreur:
        return erreur
    passer_a(cmd_id, "archivée", "Dossier archivé")
    audit(f"Commande {cmd['numero']} archivée")
    flash("Dossier archivé : il reste consultable avec « Inclure les archivées ».", "success")
    return redirect(url_for("commande_detail", cmd_id=cmd_id))


# ---------------------------------------------------------------- Factures et bordereaux de livraison
@app.template_filter("dt_fr")
def filtre_dt_fr(iso):
    return datetime.fromisoformat(iso).strftime("%d/%m/%Y à %H:%M") if iso else ""


FACTURES_FILTRES = ("q", "statut", "du", "au")
FACTURES_SQL = ("SELECT f.*, cl.nom AS client_nom, o.numero AS commande_numero, u.username"
                " FROM factures f JOIN clients cl ON cl.id=f.client_id JOIN commandes o ON o.id=f.commande_id"
                " LEFT JOIN users u ON u.id=f.user_id")


def liste_factures(flt):
    sql, args = FACTURES_SQL + " WHERE 1=1", []
    if flt["q"]:
        sql += " AND (f.numero LIKE ? OR cl.nom LIKE ? OR o.numero LIKE ?)"
        args += [f"%{flt['q']}%"] * 3
    if flt["statut"] in ("émise", "annulée"):
        sql += " AND f.statut=?"
        args.append(flt["statut"])
    if flt["du"]:
        sql += " AND substr(f.date,1,10) >= ?"
        args.append(flt["du"])
    if flt["au"]:
        sql += " AND substr(f.date,1,10) <= ?"
        args.append(flt["au"])
    return query(sql + " ORDER BY f.id DESC", args)


@app.route("/factures")
@roles(*DROITS["factures_voir"])
def factures():
    flt = args_filtres(*FACTURES_FILTRES)
    liste = liste_factures(flt)
    return render_template("factures.html", factures=liste, flt=flt, fq=filtres_actifs(flt),
                           total=sum(f["total"] for f in liste if f["statut"] == "émise"))


@app.route("/factures/<int:fid>")
@roles(*DROITS["factures_voir"])
def facture_detail(fid):
    f = query(FACTURES_SQL + " WHERE f.id=?", (fid,), one=True)
    if f is None:
        flash("Facture introuvable.", "danger")
        return redirect(url_for("factures"))
    nom_user = lambda uid: (query("SELECT username, role FROM users WHERE id=?", (uid,), one=True) if uid else None)
    return render_template(
        "facture.html", f=f, client=query("SELECT * FROM clients WHERE id=?", (f["client_id"],), one=True),
        lignes=query("SELECT *, quantite*prix_unitaire AS montant FROM lignes_facture WHERE facture_id=? ORDER BY id", (fid,)),
        valideur=nom_user(f["validee_par"]),
        date_f=datetime.fromisoformat(f["date"]).strftime("%d/%m/%Y"),
        imprime_le=datetime.now().strftime("%d/%m/%Y à %H:%M"),
        societe={"nom": ENTREPRISE_NOM, "adresse": ENTREPRISE_ADRESSE, "tel": ENTREPRISE_TEL, "email": ENTREPRISE_EMAIL})


@app.route("/export/factures.xlsx")
@roles(*DROITS["factures_voir"])
def export_factures():
    lignes = [[f["numero"], f["date"].replace("T", " "), f["commande_numero"], f["client_nom"], float(f["total"]),
               f["statut"], (f["validee_le"] or "").replace("T", " ")]
              for f in liste_factures(args_filtres(*FACTURES_FILTRES))]
    return classeur_excel("Factures", "Factures",
                          ["N° facture", "Date", "Commande", "Client", f"Total ({DEVISE})", "Statut",
                           "Validée le"], lignes, [18, 20, 18, 28, 18, 12, 20], "factures")


@app.route("/livraisons/<int:liv_id>")
@roles(*DROITS["commandes_voir"])
def livraison_detail(liv_id):
    liv = query("SELECT l.*, o.numero AS commande_numero, o.client_id, u.username FROM livraisons l"
                " JOIN commandes o ON o.id=l.commande_id LEFT JOIN users u ON u.id=l.user_id WHERE l.id=?",
                (liv_id,), one=True)
    if liv is None:
        flash("Bordereau introuvable.", "danger")
        return redirect(url_for("commandes"))
    return render_template(
        "livraison.html", liv=liv, client=query("SELECT * FROM clients WHERE id=?", (liv["client_id"],), one=True),
        lignes=query("SELECT lv.quantite, l.numero_lot, l.date_peremption, va.nom AS vaccin, va.temp_min, va.temp_max"
                     " FROM lignes_vente lv JOIN lots l ON l.id=lv.lot_id JOIN vaccins va ON va.id=l.vaccin_id"
                     " WHERE lv.vente_id=? ORDER BY lv.id", (liv["vente_id"],)),
        date_liv=datetime.fromisoformat(liv["date"]).strftime("%d/%m/%Y à %H:%M"),
        imprime_le=datetime.now().strftime("%d/%m/%Y à %H:%M"),
        societe={"nom": ENTREPRISE_NOM, "adresse": ENTREPRISE_ADRESSE, "tel": ENTREPRISE_TEL, "email": ENTREPRISE_EMAIL})


# ---------------------------------------------------------------- Rapports (PDF, Excel, archives mensuelles)
MOIS_LONGS = ("janvier", "février", "mars", "avril", "mai", "juin", "juillet", "août", "septembre",
              "octobre", "novembre", "décembre")
RAPPORTS_DIR = os.path.join(UPLOAD_DIR, "rapports")


def date_fr_txt(d):
    return d.strftime("%d/%m/%Y")


def bornes_mois(annee, mois):
    premier = date(annee, mois, 1)
    suivant = date(annee + 1, 1, 1) if mois == 12 else date(annee, mois + 1, 1)
    return premier, suivant - timedelta(days=1)


def lire_mois(valeur):
    """'2026-10' -> (2026, 10) ou None."""
    try:
        a, m = str(valeur).strip().split("-")
        a, m = int(a), int(m)
    except ValueError:
        return None
    return (a, m) if 2000 <= a <= 2100 and 1 <= m <= 12 else None


def donnees_vaccins(du, au):
    """Par vaccin, sur la période [du, au] : stock de début et de fin, entrées, livraisons, témoins,
    destructions, autres sorties et chiffre d'affaires livré."""
    lignes = query(
        "SELECT v.id, v.nom, v.type, v.seuil_min,"
        " COALESCE(SUM(CASE WHEN substr(m.date,1,10) < :du THEN CASE WHEN m.type='ENTREE' THEN m.quantite"
        "                                                           ELSE -m.quantite END END), 0) AS stock_debut,"
        " COALESCE(SUM(CASE WHEN substr(m.date,1,10) BETWEEN :du AND :au AND m.type='ENTREE' THEN m.quantite END), 0) AS entrees,"
        " COALESCE(SUM(CASE WHEN substr(m.date,1,10) BETWEEN :du AND :au AND m.type='SORTIE'"
        "                   AND m.vente_id IS NOT NULL THEN m.quantite END), 0) AS livrees,"
        " COALESCE(SUM(CASE WHEN substr(m.date,1,10) BETWEEN :du AND :au AND m.nature='TEMOIN' THEN m.quantite END), 0) AS temoins,"
        " COALESCE(SUM(CASE WHEN substr(m.date,1,10) BETWEEN :du AND :au AND m.nature='DETRUIT' THEN m.quantite END), 0) AS detruites,"
        " COALESCE(SUM(CASE WHEN substr(m.date,1,10) BETWEEN :du AND :au AND m.type='SORTIE'"
        "                   AND m.vente_id IS NULL AND m.nature IS NULL THEN m.quantite END), 0) AS autres"
        " FROM vaccins v LEFT JOIN lots l ON l.vaccin_id = v.id LEFT JOIN mouvements m ON m.lot_id = l.id"
        " GROUP BY v.id ORDER BY v.nom", {"du": du.isoformat(), "au": au.isoformat()})
    ca = {r["id"]: r["ca"] for r in query(
        "SELECT l.vaccin_id AS id, SUM(lv.quantite * lv.prix_unitaire) AS ca FROM lignes_vente lv"
        " JOIN ventes v ON v.id = lv.vente_id JOIN lots l ON l.id = lv.lot_id"
        " WHERE substr(v.date,1,10) BETWEEN ? AND ? GROUP BY l.vaccin_id", (du.isoformat(), au.isoformat()))}
    res = []
    for r in lignes:
        d = dict(r)
        d["ca"] = ca.get(r["id"], 0) or 0
        d["stock_fin"] = d["stock_debut"] + d["entrees"] - d["livrees"] - d["temoins"] - d["detruites"] - d["autres"]
        res.append(d)
    return res


def donnees_articles(du, au):
    lignes = query(
        "SELECT a.nom, u.nom AS unite,"
        " COALESCE(SUM(CASE WHEN substr(m.date,1,10) < :du THEN m.delta END), 0) AS stock_debut,"
        " COALESCE(SUM(CASE WHEN substr(m.date,1,10) BETWEEN :du AND :au AND m.delta > 0 THEN m.delta END), 0) AS entrees,"
        " COALESCE(-SUM(CASE WHEN substr(m.date,1,10) BETWEEN :du AND :au AND m.delta < 0 THEN m.delta END), 0) AS sorties,"
        " a.seuil_min"
        " FROM articles a JOIN unites u ON u.id = a.unite_id"
        " LEFT JOIN mouvements_articles m ON m.article_id = a.id GROUP BY a.id ORDER BY a.nom",
        {"du": du.isoformat(), "au": au.isoformat()})
    return [dict(r, stock_fin=r["stock_debut"] + r["entrees"] - r["sorties"]) for r in lignes]


def clients_periode(du, au, limite=15):
    return query("SELECT cl.nom, COUNT(DISTINCT v.id) AS nb, SUM(lv.quantite) AS qte,"
                 " SUM(lv.quantite * lv.prix_unitaire) AS ca FROM ventes v JOIN clients cl ON cl.id = v.client_id"
                 " JOIN lignes_vente lv ON lv.vente_id = v.id WHERE substr(v.date,1,10) BETWEEN ? AND ?"
                 " GROUP BY cl.id ORDER BY ca DESC LIMIT ?", (du.isoformat(), au.isoformat(), limite))


def activite_commerciale(du, au):
    d1, d2 = du.isoformat(), au.isoformat()
    cmd = query("SELECT statut, COUNT(*) AS n FROM commandes WHERE substr(date,1,10) BETWEEN ? AND ?"
                " GROUP BY statut", (d1, d2))
    fac = query("SELECT COUNT(*) AS n, COALESCE(SUM(total), 0) AS t FROM factures WHERE statut='émise'"
                " AND substr(date,1,10) BETWEEN ? AND ?", (d1, d2), one=True)
    liv = query("SELECT COUNT(*) AS n FROM livraisons WHERE substr(date,1,10) BETWEEN ? AND ?", (d1, d2), one=True)["n"]
    return {"commandes": [(r["statut"], r["n"]) for r in cmd], "nb_commandes": sum(r["n"] for r in cmd),
            "nb_factures": fac["n"], "montant_factures": fac["t"], "nb_livraisons": liv}


def lots_a_surveiller():
    """Photographie à l'instant T : lots en stock périmés, proches de la péremption, en quarantaine ou rappelés."""
    res = []
    for l in query(STOCK_SQL + " ORDER BY l.date_peremption"):
        if l["stock"] <= 0:
            continue
        j = jours_restants(l["date_peremption"])
        if j < 0:
            motif = "Périmé"
        elif l["statut"] in ("quarantaine", "rappelé"):
            motif = l["statut"].capitalize()
        elif j <= 90:
            motif = f"Expire dans {j} j"
        else:
            continue
        res.append([l["vaccin_nom"], l["numero_lot"], l["date_peremption"], j, l["stock"], l["statut"], motif])
    return res


def alertes_stock():
    vendable, lignes = stocks_utilisables(), []
    for v in query("SELECT * FROM vaccins WHERE actif=1 ORDER BY nom"):
        if vendable.get(v["id"], 0) < v["seuil_min"]:
            lignes.append(["Vaccin", v["nom"], vendable.get(v["id"], 0), v["seuil_min"]])
    for a in liste_articles({k: "" for k in ARTICLES_FILTRES}):
        if a["stock"] < a["seuil_min"]:
            lignes.append(["Article", a["nom"], a["stock"], a["seuil_min"]])
    return lignes


def tableau(titre, entetes, lignes, total=None, aligne=None, vide="Aucune donnée pour cette période.", feuille=None):
    return {"type": "tableau", "titre": titre, "entetes": entetes, "lignes": lignes, "total": total,
            "aligne": aligne or ["g"] * len(entetes), "vide": vide, "feuille": feuille}


def tableau_mouvements_vaccins(vaccins):
    lignes = [[v["nom"], v["type"], v["stock_debut"], v["entrees"], v["livrees"], v["temoins"], v["detruites"],
               v["autres"], v["stock_fin"]] for v in vaccins
              if any((v["stock_debut"], v["entrees"], v["livrees"], v["temoins"], v["detruites"], v["autres"], v["stock_fin"]))]
    total = ["TOTAL", ""] + [sum(l[i] for l in lignes) for i in range(2, 9)] if lignes else None
    return tableau("Mouvements des vaccins", ["Vaccin", "Type", "Stock début", "Entrées", "Livrées", "Témoins",
                                             "Détruites", "Autres sorties", "Stock fin"], lignes, total,
                   ["g", "g"] + ["d"] * 7)


def tableaux_commun(vaccins, du, au, avec_articles=True):
    """Blocs partagés : ventes par vaccin, principaux clients, articles."""
    blocs = []
    ventes = [[v["nom"], v["livrees"], v["ca"]] for v in vaccins if v["livrees"] or v["ca"]]
    blocs.append(tableau("Ventes livrées par vaccin", ["Vaccin", "Quantité livrée", f"Chiffre d'affaires ({DEVISE})"],
                         ventes, ["TOTAL", sum(v[1] for v in ventes), sum(v[2] for v in ventes)] if ventes else None,
                         ["g", "d", "d"]))
    blocs.append(tableau("Principaux clients", ["Client", "Livraisons", "Quantité", f"Chiffre d'affaires ({DEVISE})"],
                         [[c["nom"], c["nb"], c["qte"], c["ca"]] for c in clients_periode(du, au)],
                         None, ["g", "d", "d", "d"]))
    if avec_articles:
        arts = donnees_articles(du, au)
        blocs.append(tableau("Stock général (articles)", ["Article", "Unité", "Stock début", "Entrées", "Sorties", "Stock fin", "Seuil"],
                             [[a["nom"], a["unite"], a["stock_debut"], a["entrees"], a["sorties"], a["stock_fin"], a["seuil_min"]]
                              for a in arts if any((a["stock_debut"], a["entrees"], a["sorties"], a["stock_fin"]))],
                             None, ["g", "g", "d", "d", "d", "d", "d"]))
    return blocs


def blocs_situation():
    return [tableau("Lots à surveiller (situation à la date de génération)",
                    ["Vaccin", "Lot", "Péremption", "Jours", "Disponible", "Statut", "Motif"], lots_a_surveiller(),
                    None, ["g", "g", "g", "d", "d", "g", "g"], "Aucun lot à surveiller.", "Lots à surveiller"),
            tableau("Alertes de stock (situation à la date de génération)", ["Catégorie", "Élément", "Stock", "Seuil"],
                    alertes_stock(), None, ["g", "g", "d", "d"], "Aucune alerte de stock.", "Alertes de stock")]


def entete_rapport(titre, sous_titre, par):
    return {"titre": titre, "sous_titre": sous_titre, "blocs": [],
            "genere": f"Généré le {datetime.now().strftime('%d/%m/%Y à %H:%M')} · {par}"}


def rapport_mensuel(annee, mois, par):
    du, au = bornes_mois(annee, mois)
    vaccins, act = donnees_vaccins(du, au), activite_commerciale(du, au)
    r = entete_rapport(f"Rapport mensuel · {MOIS_LONGS[mois - 1]} {annee}",
                       f"Période du {date_fr_txt(du)} au {date_fr_txt(au)}", par)
    r["blocs"] = [
        {"type": "cartes", "items": [
            ("Doses reçues", sum(v["entrees"] for v in vaccins), ""),
            ("Doses livrées", sum(v["livrees"] for v in vaccins), ""),
            (f"Chiffre d'affaires livré", sum(v["ca"] for v in vaccins), DEVISE),
            ("Doses détruites", sum(v["detruites"] for v in vaccins), ""),
            ("Témoins mis de côté", sum(v["temoins"] for v in vaccins), "doses"),
            ("Commandes créées", act["nb_commandes"], ""), ("Livraisons effectuées", act["nb_livraisons"], ""),
            ("Factures émises", act["nb_factures"], f"pour {filtre_nombre(act['montant_factures'])} {DEVISE}")]},
        tableau_mouvements_vaccins(vaccins),
        *tableaux_commun(vaccins, du, au),
        tableau("Commandes créées pendant le mois (statut actuel)", ["Statut", "Nombre"], act["commandes"], None, ["g", "d"],
                "Aucune commande créée pendant ce mois.", "Commandes"),
        *blocs_situation()]
    return r


def rapport_annuel(annee, par):
    du, au = date(annee, 1, 1), date(annee, 12, 31)
    vaccins, act = donnees_vaccins(du, au), activite_commerciale(du, au)
    mensuel = []
    for m in range(1, 13):
        d1, d2 = bornes_mois(annee, m)
        v = donnees_vaccins(d1, d2)
        mensuel.append([MOIS_LONGS[m - 1].capitalize(), sum(x["entrees"] for x in v), sum(x["livrees"] for x in v),
                        sum(x["detruites"] for x in v), sum(x["ca"] for x in v)])
    r = entete_rapport(f"Rapport annuel · {annee}", f"Période du {date_fr_txt(du)} au {date_fr_txt(au)}", par)
    r["blocs"] = [
        {"type": "cartes", "items": [
            ("Doses reçues", sum(v["entrees"] for v in vaccins), ""),
            ("Doses livrées", sum(v["livrees"] for v in vaccins), ""),
            ("Chiffre d'affaires livré", sum(v["ca"] for v in vaccins), DEVISE),
            ("Doses détruites", sum(v["detruites"] for v in vaccins), ""),
            ("Commandes créées", act["nb_commandes"], ""), ("Livraisons effectuées", act["nb_livraisons"], ""),
            ("Factures émises", act["nb_factures"], f"pour {filtre_nombre(act['montant_factures'])} {DEVISE}")]},
        tableau("Évolution mois par mois", ["Mois", "Doses reçues", "Doses livrées", "Doses détruites",
                                            f"Chiffre d'affaires ({DEVISE})"], mensuel,
                ["TOTAL"] + [sum(l[i] for l in mensuel) for i in range(1, 5)], ["g", "d", "d", "d", "d"]),
        tableau_mouvements_vaccins(vaccins),
        *tableaux_commun(vaccins, du, au)]
    return r


def rapport_par_type(du, au, par):
    vaccins, act = donnees_vaccins(du, au), activite_commerciale(du, au)
    vendable = stocks_utilisables()
    par_type = {}
    for v in vaccins:
        t = par_type.setdefault(v["type"], {"nb": 0, "vendable": 0, "entrees": 0, "livrees": 0, "detruites": 0, "ca": 0, "lignes": []})
        t["nb"] += 1
        t["vendable"] += vendable.get(v["id"], 0)
        for k in ("entrees", "livrees", "detruites", "ca"):
            t[k] += v[k]
        t["lignes"].append([v["nom"], v["stock_debut"], v["entrees"], v["livrees"], v["detruites"], v["stock_fin"], v["ca"]])
    synth = [[t_, d["nb"], d["vendable"], d["entrees"], d["livrees"], d["detruites"], d["ca"]]
             for t_, d in sorted(par_type.items())]
    r = entete_rapport("Rapport par type de vaccin", f"Période du {date_fr_txt(du)} au {date_fr_txt(au)}", par)
    r["blocs"] = [
        {"type": "cartes", "items": [("Types de vaccin", len(par_type), ""), ("Vaccins au catalogue", len(vaccins), ""),
                                     ("Doses livrées", sum(v["livrees"] for v in vaccins), ""),
                                     ("Chiffre d'affaires livré", sum(v["ca"] for v in vaccins), DEVISE)]},
        tableau("Synthèse par type", ["Type", "Vaccins", "Vendable actuel", "Doses reçues", "Doses livrées",
                                      "Doses détruites", f"Chiffre d'affaires ({DEVISE})"], synth,
                ["TOTAL"] + [sum(l[i] for l in synth) for i in range(1, 7)] if synth else None,
                ["g"] + ["d"] * 6)]
    for t_, d in sorted(par_type.items()):
        r["blocs"].append(tableau(f"Type « {t_} » : détail par vaccin",
                                  ["Vaccin", "Stock début", "Reçues", "Livrées", "Détruites", "Stock fin", f"CA ({DEVISE})"],
                                  d["lignes"], None, ["g"] + ["d"] * 6, feuille=f"Type {t_}"))
    return r


def rapport_global(par):
    aujourdhui = date.today()
    depuis = date(2000, 1, 1)
    vaccins = donnees_vaccins(depuis, aujourdhui)
    vendable = stocks_utilisables()
    actifs = {v["id"]: v for v in query("SELECT id, actif FROM vaccins")}
    etat_vaccins = [[v["nom"], v["type"], v["stock_fin"], vendable.get(v["id"], 0), v["seuil_min"],
                     "Stock bas" if vendable.get(v["id"], 0) < v["seuil_min"] else "OK"]
                    for v in vaccins if actifs[v["id"]]["actif"] or v["stock_fin"]]
    articles = liste_articles({k: "" for k in ARTICLES_FILTRES})
    act = activite_commerciale(depuis, aujourdhui)
    r = entete_rapport("Rapport global", f"Situation au {date_fr_txt(aujourdhui)}", par)
    surveiller = lots_a_surveiller()
    r["blocs"] = [
        {"type": "cartes", "items": [
            ("Stock de vaccins (tous statuts)", sum(v["stock_fin"] for v in vaccins), "doses"),
            ("Vendable à ce jour", sum(vendable.values()), "doses"),
            ("Lots à surveiller", len(surveiller), ""),
            ("Articles sous le seuil", sum(1 for a in articles if a["stock"] < a["seuil_min"]), ""),
            ("Commandes en cours", sum(n_ for st_, n_ in act["commandes"] if st_ in EN_COURS), ""),
            ("Chiffre d'affaires livré (cumul)", sum(v["ca"] for v in vaccins), DEVISE)]},
        tableau("Vaccins : état du stock", ["Vaccin", "Type", "Stock total", "Vendable", "Seuil", "État"], etat_vaccins,
                None, ["g", "g", "d", "d", "d", "g"], "Aucun vaccin.", "Vaccins - stock"),
        tableau("Stock général (articles)", ["Article", "Catégorie", "Unité", "Stock", "Seuil", "État"],
                [[a["nom"], a["categorie_nom"], a["unite_nom"], a["stock"], a["seuil_min"],
                  "Stock bas" if a["stock"] < a["seuil_min"] else "OK"] for a in articles], None,
                ["g", "g", "g", "d", "d", "g"]),
        tableau("Cumul depuis le début", ["Indicateur", "Valeur"],
                [["Doses reçues", sum(v["entrees"] for v in vaccins)], ["Doses livrées", sum(v["livrees"] for v in vaccins)],
                 ["Doses détruites", sum(v["detruites"] for v in vaccins)], ["Témoins mis de côté", sum(v["temoins"] for v in vaccins)],
                 [f"Chiffre d'affaires livré ({DEVISE})", sum(v["ca"] for v in vaccins)],
                 ["Factures émises", act["nb_factures"]], ["Livraisons effectuées", act["nb_livraisons"]]], None, ["g", "d"]),
        tableau("Commandes par statut", ["Statut", "Nombre"], act["commandes"], None, ["g", "d"], "Aucune commande."),
        *blocs_situation()]
    return r


# ----- rendu PDF
def texte_pdf(valeur):
    """Texte compatible avec la police du PDF (caractères inconnus remplacés)."""
    return str("" if valeur is None else valeur).encode("cp1252", "replace").decode("cp1252")


def cellule(valeur):
    return filtre_nombre(valeur) if isinstance(valeur, (int, float)) and not isinstance(valeur, bool) else valeur


def logo_pdf(hauteur_mm=16):
    try:
        from PIL import Image as PilImage
        from reportlab.lib.units import mm
        from reportlab.platypus import Image
        petit = PilImage.open(os.path.join(BASE_DIR, "static", "logo.png"))
        petit.thumbnail((300, 224))
        tampon = BytesIO()
        petit.save(tampon, format="PNG")
        tampon.seek(0)
        h = hauteur_mm * mm
        return Image(tampon, width=h * petit.width / petit.height, height=h)
    except Exception:
        return ""


def construire_pdf(rapport):
    from xml.sax.saxutils import escape
    from reportlab.lib import colors
    from reportlab.lib.enums import TA_RIGHT
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
    from reportlab.lib.units import mm
    from reportlab.pdfgen import canvas
    from reportlab.platypus import KeepTogether, Paragraph, SimpleDocTemplate, Spacer, Table, TableStyle

    vert, vert_fonce, gris = colors.HexColor("#498d1e"), colors.HexColor("#2f6b14"), colors.HexColor("#666666")
    pied = texte_pdf(f"{ENTREPRISE_NOM} · {rapport['titre']}")
    base = getSampleStyleSheet()["Normal"]
    p = lambda txt, **kw: Paragraph(texte_pdf(escape(str(txt))), ParagraphStyle("x", parent=base, **kw))

    class PagesNumerotees(canvas.Canvas):
        def __init__(self, *a, **kw):
            super().__init__(*a, **kw)
            self._etats = []

        def showPage(self):
            self._etats.append(dict(self.__dict__))
            self._startPage()

        def save(self):
            total = len(self._etats)
            for etat in self._etats:
                self.__dict__.update(etat)
                self.setFont("Helvetica", 8)
                self.setFillColor(gris)
                self.drawString(14 * mm, 9 * mm, pied)
                self.drawRightString(A4[0] - 14 * mm, 9 * mm, f"Page {self._pageNumber}/{total}")
                super().showPage()
            super().save()

    tampon = BytesIO()
    doc = SimpleDocTemplate(tampon, pagesize=A4, leftMargin=14 * mm, rightMargin=14 * mm, topMargin=13 * mm,
                            bottomMargin=16 * mm, title=texte_pdf(rapport["titre"]), author=texte_pdf(ENTREPRISE_NOM))
    L = doc.width
    histoire = []
    entete = Table([[logo_pdf(), [p(rapport["titre"], fontName="Helvetica-Bold", fontSize=16, textColor=vert_fonce, leading=19),
                                  p(rapport["sous_titre"], fontSize=10, textColor=gris, leading=13)],
                     [p(ENTREPRISE_NOM, fontSize=8.5, textColor=vert_fonce, alignment=TA_RIGHT, leading=11, fontName="Helvetica-Bold"),
                      p(rapport["genere"], fontSize=7.5, textColor=gris, alignment=TA_RIGHT, leading=10)]]],
                   colWidths=[26 * mm, L - 26 * mm - 52 * mm, 52 * mm])
    entete.setStyle(TableStyle([("VALIGN", (0, 0), (-1, -1), "MIDDLE"), ("LINEBELOW", (0, 0), (-1, 0), 1.6, vert),
                                ("BOTTOMPADDING", (0, 0), (-1, -1), 6)]))
    histoire += [entete, Spacer(1, 8)]
    for bloc in rapport["blocs"]:
        if bloc["type"] == "cartes":
            cases = [[p(f"{filtre_nombre(v) if isinstance(v, (int, float)) else v}", fontName="Helvetica-Bold", fontSize=15, textColor=vert_fonce, leading=17),
                      p(lib + (f" · {unite}" if unite else ""), fontSize=7.5, textColor=gris, leading=9)] for lib, v, unite in bloc["items"]]
            while len(cases) % 4:
                cases.append("")
            grille = [cases[i:i + 4] for i in range(0, len(cases), 4)]
            t = Table(grille, colWidths=[L / 4] * 4)
            t.setStyle(TableStyle([("BOX", (0, 0), (-1, -1), 0.5, colors.HexColor("#cfd8c8")),
                                   ("INNERGRID", (0, 0), (-1, -1), 0.5, colors.HexColor("#cfd8c8")),
                                   ("BACKGROUND", (0, 0), (-1, -1), colors.HexColor("#f3f8ee")),
                                   ("TOPPADDING", (0, 0), (-1, -1), 5), ("BOTTOMPADDING", (0, 0), (-1, -1), 5)]))
            histoire += [t, Spacer(1, 10)]
        elif bloc["type"] == "tableau":
            titre = p(bloc["titre"], fontName="Helvetica-Bold", fontSize=10.5, textColor=vert_fonce, spaceBefore=4, spaceAfter=3, leading=13)
            if not bloc["lignes"]:
                histoire += [KeepTogether([titre, p(bloc["vide"], fontSize=8.5, textColor=gris)]), Spacer(1, 8)]
                continue
            n = len(bloc["entetes"])
            taille = 8.5 if n <= 6 else 7.8 if n <= 9 else 7
            from reportlab.pdfbase.pdfmetrics import stringWidth
            mesures = []
            for i, e in enumerate(bloc["entetes"]):  # largeur réelle du texte le plus long de la colonne
                w = stringWidth(texte_pdf(e), "Helvetica-Bold", taille)
                for l in bloc["lignes"][:300] + ([bloc["total"]] if bloc["total"] else []):
                    w = max(w, stringWidth(texte_pdf(cellule(l[i])), "Helvetica", taille))
                mesures.append(min(w + 12, L * 0.45))
            echelle = L / sum(mesures)  # on étire ou on comprime pour remplir exactement la page
            largeurs = [w * echelle for w in mesures]
            def cel(val, i, gras=False, blanc=False):
                return p(cellule(val), fontName="Helvetica-Bold" if gras else "Helvetica", fontSize=taille, leading=taille + 2.2,
                         alignment=TA_RIGHT if bloc["aligne"][i] == "d" else 0, textColor=colors.white if blanc else colors.black)
            donnees = [[cel(e, i, True, True) for i, e in enumerate(bloc["entetes"])]]
            donnees += [[cel(v, i) for i, v in enumerate(l)] for l in bloc["lignes"]]
            if bloc["total"]:
                donnees.append([cel(v, i, True) for i, v in enumerate(bloc["total"])])
            t = Table(donnees, colWidths=largeurs, repeatRows=1)
            style = [("BACKGROUND", (0, 0), (-1, 0), vert_fonce), ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
                     ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.white, colors.HexColor("#f3f8ee")]),
                     ("LINEBELOW", (0, 0), (-1, -1), 0.3, colors.HexColor("#d9e2d3")),
                     ("TOPPADDING", (0, 0), (-1, -1), 3), ("BOTTOMPADDING", (0, 0), (-1, -1), 3)]
            if bloc["total"]:
                style += [("BACKGROUND", (0, -1), (-1, -1), colors.HexColor("#e4efdb")), ("LINEABOVE", (0, -1), (-1, -1), 1, vert)]
            t.setStyle(TableStyle(style))
            histoire += [titre, t, Spacer(1, 10)]
        elif bloc["type"] == "texte":
            histoire += [p(bloc["texte"], fontSize=9), Spacer(1, 6)]
    doc.build(histoire, canvasmaker=PagesNumerotees)
    return tampon.getvalue()


# ----- rendu Excel
def construire_xlsx(rapport):
    from openpyxl import Workbook
    from openpyxl.styles import Alignment, Font, PatternFill
    wb = Workbook()
    ws = wb.active
    ws.title = "Synthèse"
    ws["A1"] = rapport["titre"]
    ws["A1"].font = Font(size=15, bold=True, color="2F6B14")
    ws["A2"] = rapport["sous_titre"]
    ws["A3"] = rapport["genere"]
    ws["A3"].font = Font(italic=True, color="666666", size=9)
    ligne = 5
    for bloc in rapport["blocs"]:
        if bloc["type"] == "cartes":
            for lib, v, unite in bloc["items"]:
                ws.cell(row=ligne, column=1, value=lib)
                cel = ws.cell(row=ligne, column=2, value=v)
                cel.font = Font(bold=True)
                if isinstance(v, float):
                    cel.number_format = "#,##0"
                ws.cell(row=ligne, column=3, value=unite)
                ligne += 1
    ws.column_dimensions["A"].width = 38
    ws.column_dimensions["B"].width = 20
    ws.column_dimensions["C"].width = 28
    interdits = "[]:*?/" + chr(92)
    noms = {"Synthèse"}
    for bloc in rapport["blocs"]:
        if bloc["type"] != "tableau":
            continue
        base = "".join(c for c in (bloc["feuille"] or bloc["titre"]) if c not in interdits)[:28] or "Tableau"
        nom, k = base, 2
        while nom in noms:
            nom, k = f"{base[:26]} {k}", k + 1
        noms.add(nom)
        feuille = wb.create_sheet(nom)
        feuille["A1"] = bloc["titre"]
        feuille["A1"].font = Font(size=13, bold=True, color="2F6B14")
        for c, texte in enumerate(bloc["entetes"], start=1):
            cel = feuille.cell(row=3, column=c, value=texte)
            cel.font = Font(bold=True, color="FFFFFF")
            cel.fill = PatternFill("solid", fgColor="2F6B14")
            cel.alignment = Alignment(horizontal="center", wrap_text=True)
        lignes = list(bloc["lignes"]) + ([bloc["total"]] if bloc["total"] else [])
        for r, valeurs in enumerate(lignes, start=4):
            for c, v in enumerate(valeurs, start=1):
                cel = feuille.cell(row=r, column=c, value=v)
                if isinstance(v, float):
                    cel.number_format = "#,##0"
                if bloc["total"] and r == 3 + len(lignes):
                    cel.font = Font(bold=True)
                    cel.fill = PatternFill("solid", fgColor="E4EFDB")
        for c in range(1, len(bloc["entetes"]) + 1):
            largeur = max([len(str(bloc["entetes"][c - 1]))] + [len(str(cellule(l[c - 1]))) for l in lignes[:200]])
            feuille.column_dimensions[feuille.cell(row=1, column=c).column_letter].width = min(max(largeur + 3, 10), 42)
        feuille.freeze_panes = "A4"
        if bloc["lignes"]:
            feuille.auto_filter.ref = f"A3:{feuille.cell(row=1, column=len(bloc['entetes'])).column_letter}{3 + len(bloc['lignes'])}"
    sortie = BytesIO()
    wb.save(sortie)
    sortie.seek(0)
    return sortie


# ----- archives mensuelles
def archiver_rapport_mensuel(annee, mois, origine, user_id=None):
    """Génère le rapport mensuel en PDF et l'archive. Renvoie l'identifiant, ou None si déjà archivé (auto)."""
    par = "génération automatique" if origine == "auto" else session["user"]["username"]
    rapport = rapport_mensuel(annee, mois, par)
    pdf = construire_pdf(rapport)
    os.makedirs(RAPPORTS_DIR, exist_ok=True)
    nom = f"rapport-mensuel-{annee}-{mois:02d}-{secrets.token_hex(6)}.pdf"
    chemin = os.path.join(RAPPORTS_DIR, nom)
    with open(chemin, "wb") as sortie:
        sortie.write(pdf)
    try:
        rid = execute("INSERT INTO rapports(type, periode, titre, fichier, taille, date, origine, user_id)"
                      " VALUES (?,?,?,?,?,?,?,?)",
                      ("mensuel", f"{annee}-{mois:02d}", rapport["titre"], nom, len(pdf), now(), origine, user_id))
    except sqlite3.IntegrityError:
        os.remove(chemin)
        return None
    audit(f"Rapport mensuel {MOIS_LONGS[mois - 1]} {annee} archivé ({'automatique' if origine == 'auto' else 'manuel'})")
    if origine == "auto":
        try:
            envoyer_rapport_par_email(rid)
        except Exception:
            app.logger.exception("Envoi du rapport mensuel par e-mail impossible")
    return rid


def generer_rapports_manquants(aujourdhui=None):
    """Archive automatiquement les rapports des mois écoulés qui ne l'ont pas encore été (12 mois au plus,
    à partir du premier mouvement enregistré). Renvoie le nombre de rapports créés."""
    aujourdhui = aujourdhui or date.today()
    premier = query("SELECT MIN(substr(date,1,7)) AS m FROM mouvements", one=True)["m"]
    if not premier:
        return 0
    a, m, mois = aujourdhui.year, aujourdhui.month, []
    for _ in range(12):
        m -= 1
        if m == 0:
            a, m = a - 1, 12
        mois.append((a, m))
    crees = 0
    for a, m in reversed(mois):
        periode = f"{a}-{m:02d}"
        if periode < premier or query("SELECT 1 FROM rapports WHERE type='mensuel' AND periode=?", (periode,), one=True):
            continue
        if archiver_rapport_mensuel(a, m, "auto") is not None:
            crees += 1
    return crees


_ETAT_RAPPORTS = {"jour": None}


@app.before_request
def controle_rapports_automatiques():
    """Une fois par jour (au premier accès), archive les rapports mensuels manquants."""
    if request.endpoint in (None, "static"):
        return
    jour = date.today().isoformat()
    if _ETAT_RAPPORTS["jour"] == jour:
        return
    _ETAT_RAPPORTS["jour"] = jour
    try:
        generer_rapports_manquants()
    except Exception:
        app.logger.exception("Archivage automatique des rapports mensuels impossible")
    try:
        envoyer_alertes_quotidiennes()
    except Exception:
        app.logger.exception("Envoi des alertes par e-mail impossible")


# ----- pages
def fabriquer_rapport(genre):
    """Construit le rapport demandé d'après l'adresse ; renvoie (rapport, nom_de_fichier, erreur)."""
    a = request.args
    par = session["user"]["username"]
    if genre == "mensuel":
        pm = lire_mois(a.get("mois", ""))
        if pm is None or (pm[0], pm[1]) > (date.today().year, date.today().month):
            return None, None, "Choisissez un mois valide (pas dans le futur)."
        return rapport_mensuel(pm[0], pm[1], par), f"rapport-mensuel-{pm[0]}-{pm[1]:02d}", None
    if genre == "annuel":
        try:
            annee = int(a.get("annee", ""))
        except ValueError:
            annee = 0
        if not 2000 <= annee <= date.today().year:
            return None, None, "Choisissez une année valide."
        return rapport_annuel(annee, par), f"rapport-annuel-{annee}", None
    if genre == "type":
        try:
            du, au = date.fromisoformat(a.get("du", "")), date.fromisoformat(a.get("au", ""))
        except ValueError:
            return None, None, "Choisissez deux dates valides."
        if du > au:
            return None, None, "La date de début doit précéder la date de fin."
        return rapport_par_type(du, au, par), f"rapport-par-type-{du.isoformat()}-{au.isoformat()}", None
    if genre == "global":
        return rapport_global(par), f"rapport-global-{date.today().isoformat()}", None
    abort(404)


@app.route("/rapports")
@roles(*DROITS["rapports_voir"])
def rapports():
    aujourdhui = date.today()
    return render_template(
        "rapports.html", mois_defaut=(aujourdhui.replace(day=1) - timedelta(days=1)).strftime("%Y-%m"),
        annee_defaut=aujourdhui.year, du_defaut=f"{aujourdhui.year}-01-01", au_defaut=aujourdhui.isoformat(),
        archives=query("SELECT r.*, u.username FROM rapports r LEFT JOIN users u ON u.id=r.user_id"
                       " ORDER BY r.periode DESC, r.id DESC"))


@app.route("/rapports/mensuel", methods=["POST"])
@roles(*DROITS["rapports_voir"])
def rapport_mensuel_generer():
    pm = lire_mois(request.form.get("mois", ""))
    if pm is None or pm > (date.today().year, date.today().month):
        flash("Choisissez un mois valide (pas dans le futur).", "danger")
    else:
        rid = archiver_rapport_mensuel(pm[0], pm[1], "manuel", session["user"]["id"])
        flash(f"Rapport de {MOIS_LONGS[pm[1] - 1]} {pm[0]} généré et archivé.", "success")
        if request.form.get("envoyer") == "1":
            if not email_pret():
                flash("Rapport non envoyé : l'envoi d'e-mails n'est pas activé.", "warning")
            else:
                nb = envoyer_rapport_par_email(rid)
                flash(f"Rapport envoyé par e-mail à {nb} abonné(s)." if nb else "Aucun abonné à qui envoyer ce rapport.", "success" if nb else "warning")
    return redirect(url_for("rapports") + "#archives")


@app.route("/rapports/pdf/<genre>")
@roles(*DROITS["rapports_voir"])
def rapport_pdf(genre):
    rapport, nom, erreur = fabriquer_rapport(genre)
    if erreur:
        flash(erreur, "danger")
        return redirect(url_for("rapports"))
    audit(f"Rapport PDF généré : {rapport['titre']}")
    return send_file(BytesIO(construire_pdf(rapport)), as_attachment=True, download_name=nom + ".pdf",
                     mimetype="application/pdf")


@app.route("/rapports/excel/<genre>")
@roles(*DROITS["rapports_voir"])
def rapport_excel(genre):
    rapport, nom, erreur = fabriquer_rapport(genre)
    if erreur:
        flash(erreur, "danger")
        return redirect(url_for("rapports"))
    audit(f"Rapport Excel généré : {rapport['titre']}")
    return send_file(construire_xlsx(rapport), as_attachment=True, download_name=nom + ".xlsx",
                     mimetype="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")


@app.route("/rapports/archives/<int:rid>/telecharger")
@roles(*DROITS["rapports_voir"])
def rapport_archive_telecharger(rid):
    r = query("SELECT * FROM rapports WHERE id=?", (rid,), one=True)
    chemin = os.path.join(RAPPORTS_DIR, r["fichier"]) if r else ""
    if r is None or not os.path.exists(chemin):
        flash("Rapport introuvable.", "danger")
        return redirect(url_for("rapports"))
    return send_file(chemin, as_attachment=True, mimetype="application/pdf",
                     download_name=f"rapport-{r['type']}-{r['periode']}.pdf")


@app.route("/rapports/archives/<int:rid>/supprimer", methods=["POST"])
@roles(*DROITS["supprimer"])
def rapport_archive_supprimer(rid):
    r = query("SELECT * FROM rapports WHERE id=?", (rid,), one=True)
    if r is None:
        flash("Rapport introuvable.", "danger")
    else:
        supprimer_fichier(os.path.join("rapports", r["fichier"]))
        execute("DELETE FROM rapports WHERE id=?", (rid,))
        audit(f"Rapport archivé supprimé : {r['titre']}")
        flash("Rapport supprimé de l'archive.", "success")
    return redirect(url_for("rapports") + "#archives")


# ---------------------------------------------------------------- Notifications par e-mail
EMAIL_RE = re.compile(r"[^@\s]+@[^@\s]+\.[^@\s]+")
PARAMS_DEFAUT = {"email_actif": "0", "smtp_hote": "", "smtp_port": "587", "smtp_securite": "starttls",
                 "smtp_utilisateur": "", "smtp_mot_de_passe": "", "email_expediteur": "",
                 "email_nom": "UPVac - ISRA", "url_site": "", "derniere_alerte": ""}


def param(cle):
    ligne = query("SELECT valeur FROM parametres WHERE cle=?", (cle,), one=True)
    return ligne["valeur"] if ligne and ligne["valeur"] is not None else PARAMS_DEFAUT.get(cle, "")


def ecrire_param(cle, valeur):
    execute("INSERT INTO parametres(cle, valeur) VALUES (?,?) ON CONFLICT(cle) DO UPDATE SET valeur=excluded.valeur",
            (cle, valeur))


def params_email():
    """Paramètres d'envoi ; le mot de passe peut venir de la variable d'environnement UPVAC_SMTP_PASSWORD."""
    p = {k: param(k) for k in PARAMS_DEFAUT}
    p["smtp_mot_de_passe"] = os.environ.get("UPVAC_SMTP_PASSWORD") or p["smtp_mot_de_passe"]
    return p


def email_pret(p=None):
    p = p or params_email()
    return (p["email_actif"] == "1" and bool(p["smtp_hote"]) and p["smtp_port"].isdigit()
            and bool(EMAIL_RE.fullmatch(p["email_expediteur"])))


def construire_message(t, p):
    msg = EmailMessage()
    msg["Subject"] = "[UPVac] " + " ".join(str(t["sujet"]).split())[:150]  # jamais de saut de ligne dans un en-tête
    msg["From"] = formataddr((p["email_nom"] or "UPVac", p["email_expediteur"]), charset="utf-8")
    msg["To"] = t["destinataire"]
    msg.set_content(t["texte"])
    if t.get("html"):
        msg.add_alternative(t["html"], subtype="html")
    for nom, contenu, mime in t.get("pieces", ()):
        principal, secondaire = mime.split("/")
        msg.add_attachment(contenu, maintype=principal, subtype=secondaire, filename=nom)
    return msg


def envoyer_smtp(msg, p):
    contexte = ssl.create_default_context()
    port = int(p["smtp_port"])
    if p["smtp_securite"] == "ssl":
        serveur = smtplib.SMTP_SSL(p["smtp_hote"], port, timeout=20, context=contexte)
    else:
        serveur = smtplib.SMTP(p["smtp_hote"], port, timeout=20)
    with serveur:
        if p["smtp_securite"] == "starttls":
            serveur.starttls(context=contexte)
        if p["smtp_utilisateur"]:
            serveur.login(p["smtp_utilisateur"], p["smtp_mot_de_passe"])
        serveur.send_message(msg)


def envoyer_et_journaliser(t, p):
    """Envoie un message et garde une trace (réussite ou erreur). Renvoie (ok, erreur)."""
    try:
        envoyer_smtp(construire_message(t, p), p)
        statut, erreur = "envoyé", ""
    except Exception as e:  # une erreur de messagerie ne doit jamais bloquer la plateforme
        statut, erreur = "erreur", f"{type(e).__name__} : {e}"[:300]
    execute("INSERT INTO emails_envoyes(date, destinataire, sujet, type, statut, erreur) VALUES (?,?,?,?,?,?)",
            (now(), t["destinataire"], str(t["sujet"])[:150], t["type"], statut, erreur))
    return statut == "envoyé", erreur


def lancer_envois(taches):
    """Envoie les messages en arrière-plan pour ne jamais ralentir la page. Renvoie le fil d'exécution."""
    p = params_email()

    def travail():
        with app.app_context():
            for t in taches:
                envoyer_et_journaliser(t, p)

    fil = threading.Thread(target=travail, daemon=True)
    fil.start()
    return fil


def destinataires_email(roles_ok, champ):
    """Utilisateurs actifs, avec adresse, ayant activé cette notification et dont le rôle y a droit."""
    return query(f"SELECT username, email FROM users WHERE actif=1 AND email IS NOT NULL AND email <> ''"
                 f" AND {champ}=1 AND role IN ({', '.join('?' for _ in roles_ok)}) ORDER BY username", tuple(roles_ok))


def lien_site():
    url = param("url_site").rstrip("/")
    return url if url.startswith(("http://", "https://")) else ""


def html_tableau(titre, entetes, lignes):
    from markupsafe import escape
    th = "".join(f'<th style="background:#2f6b14;color:#fff;padding:6px 8px;text-align:left">{escape(e)}</th>' for e in entetes)
    tr = "".join("<tr>" + "".join(f'<td style="padding:5px 8px;border-bottom:1px solid #dde5d6">{escape(c)}</td>' for c in l) + "</tr>"
                 for l in lignes)
    return (f'<h3 style="color:#2f6b14;margin:18px 0 6px">{escape(titre)}</h3>'
            f'<table style="border-collapse:collapse;font-size:13px;width:100%"><tr>{th}</tr>{tr}</table>')


def corps_alertes(aujourdhui):
    """Contenu de l'e-mail d'alertes : (sujet, texte, html), ou None s'il n'y a rien à signaler."""
    stock, lots = alertes_stock(), lots_a_surveiller()
    if not stock and not lots:
        return None
    sujet = f"Alertes du {date_fr_txt(aujourdhui)} : {len(stock)} stock(s) bas, {len(lots)} lot(s) à surveiller"
    texte = [f"Alertes UPVac du {date_fr_txt(aujourdhui)}", ""]
    html = [f'<p style="font-size:15px">Alertes <b>UPVac</b> du <b>{date_fr_txt(aujourdhui)}</b></p>']
    if stock:
        texte += ["STOCKS SOUS LE SEUIL MINIMAL"] + [f"- {c} {e} : {q} (seuil {sl})" for c, e, q, sl in stock] + [""]
        html.append(html_tableau("Stocks sous le seuil minimal", ["Catégorie", "Élément", "Stock", "Seuil"], stock))
    if lots:
        texte += ["LOTS À SURVEILLER"] + [f"- {v} lot {l} : {mo} (péremption {pe}, disponible {di})"
                                         for v, l, pe, _j, di, _st, mo in lots] + [""]
        html.append(html_tableau("Lots à surveiller", ["Vaccin", "Lot", "Péremption", "Jours", "Disponible", "Statut", "Motif"], lots))
    if lien_site():
        texte.append(f"Ouvrir la plateforme : {lien_site()}")
        html.append(f'<p style="margin-top:18px"><a href="{lien_site()}">Ouvrir la plateforme</a></p>')
    texte.append("Vous recevez ce message car les alertes par e-mail sont activées dans « Mon compte ».")
    return sujet, "\n".join(texte), '<div style="font-family:Arial,sans-serif;color:#222">' + "".join(html) + "</div>"


def envoyer_alertes_quotidiennes(aujourdhui=None, attendre=False):
    """Envoie, une seule fois par jour, le récapitulatif des alertes. Renvoie le nombre de messages lancés."""
    aujourdhui = aujourdhui or date.today()
    if not email_pret() or param("derniere_alerte") == aujourdhui.isoformat():
        return 0
    contenu = corps_alertes(aujourdhui)
    ecrire_param("derniere_alerte", aujourdhui.isoformat())  # marqué avant l'envoi : jamais de doublon
    if contenu is None:
        return 0
    sujet, texte, html = contenu
    taches = [{"destinataire": u["email"], "sujet": sujet, "texte": texte, "html": html, "type": "alertes"}
              for u in destinataires_email(DROITS["vaccins_voir"], "notif_alertes")]
    if not taches:
        return 0
    fil = lancer_envois(taches)
    if attendre:
        fil.join()
    return len(taches)


def envoyer_rapport_par_email(rid, attendre=False):
    """Envoie un rapport archivé (PDF en pièce jointe) aux abonnés. Renvoie le nombre de messages lancés."""
    r = query("SELECT * FROM rapports WHERE id=?", (rid,), one=True)
    chemin = os.path.join(RAPPORTS_DIR, r["fichier"]) if r else ""
    if r is None or not email_pret() or not os.path.exists(chemin):
        return 0
    with open(chemin, "rb") as f:
        pdf = f.read()
    texte = (f"Bonjour,\n\nLe {r['titre'].lower()} est disponible : vous le trouverez en pièce jointe.\n"
             + (f"Archives : {lien_site()}/rapports\n" if lien_site() else "")
             + "\nVous recevez ce message car les rapports par e-mail sont activés dans « Mon compte ».")
    html = ('<div style="font-family:Arial,sans-serif;color:#222"><p>Bonjour,</p>'
            f'<p>Le <b>{r["titre"].lower()}</b> est disponible : vous le trouverez en pièce jointe.</p>'
            + (f'<p><a href="{lien_site()}/rapports">Consulter les archives</a></p>' if lien_site() else "") + "</div>")
    taches = [{"destinataire": u["email"], "sujet": r["titre"], "texte": texte, "html": html, "type": "rapport",
               "pieces": [(f"rapport-{r['type']}-{r['periode']}.pdf", pdf, "application/pdf")]}
              for u in destinataires_email(DROITS["rapports_voir"], "notif_rapports")]
    if not taches:
        return 0
    fil = lancer_envois(taches)
    if attendre:
        fil.join()
    return len(taches)


def tache_quotidienne():
    """Archive les rapports mensuels manquants puis envoie les alertes du jour (à lancer chaque jour)."""
    return generer_rapports_manquants(), envoyer_alertes_quotidiennes(attendre=True)


# ----- pages
@app.route("/parametres/email", methods=["GET", "POST"])
@roles(*DROITS["email_config"])
def email_parametres():
    if request.method == "POST":
        f = request.form
        port = f.get("smtp_port", "").strip()
        site = f.get("url_site", "").strip()
        nouveau = {"email_actif": "1" if f.get("email_actif") == "1" else "0", "smtp_hote": f.get("smtp_hote", "").strip()[:200],
                   "smtp_port": port, "smtp_securite": f.get("smtp_securite", ""), "smtp_utilisateur": f.get("smtp_utilisateur", "").strip()[:200],
                   "email_expediteur": f.get("email_expediteur", "").strip()[:120], "email_nom": f.get("email_nom", "").strip()[:80],
                   "url_site": site[:200]}
        if nouveau["smtp_securite"] not in ("starttls", "ssl", "aucune"):
            flash("Type de sécurité invalide.", "danger")
        elif port and not (port.isdigit() and 1 <= int(port) <= 65535):
            flash("Le port doit être un nombre entre 1 et 65535.", "danger")
        elif nouveau["email_expediteur"] and not EMAIL_RE.fullmatch(nouveau["email_expediteur"]):
            flash("Adresse d'expédition invalide.", "danger")
        elif site and not site.startswith(("http://", "https://")):
            flash("L'adresse du site doit commencer par http:// ou https://.", "danger")
        elif nouveau["email_actif"] == "1" and not (nouveau["smtp_hote"] and port and nouveau["email_expediteur"]):
            flash("Pour activer l'envoi, renseignez le serveur, le port et l'adresse d'expédition.", "danger")
        else:
            for cle, valeur in nouveau.items():
                ecrire_param(cle, valeur)
            if f.get("smtp_mot_de_passe"):  # le mot de passe n'est modifié que s'il est saisi
                ecrire_param("smtp_mot_de_passe", f["smtp_mot_de_passe"])
            audit("Paramètres des notifications par e-mail modifiés" + (" (activées)" if nouveau["email_actif"] == "1" else " (désactivées)"))
            flash("Paramètres enregistrés.", "success")
            return redirect(url_for("email_parametres"))
    p = params_email()
    moi = query("SELECT email FROM users WHERE id=?", (session["user"]["id"],), one=True)
    return render_template("email_parametres.html", p=p, pret=email_pret(p), mdp_enregistre=bool(p["smtp_mot_de_passe"]),
                           mdp_env=bool(os.environ.get("UPVAC_SMTP_PASSWORD")), mon_email=moi["email"],
                           journal=query("SELECT * FROM emails_envoyes ORDER BY id DESC LIMIT 50"),
                           abonnes=query("SELECT username, role, email, notif_alertes, notif_rapports FROM users"
                                         " WHERE actif=1 AND email IS NOT NULL AND email <> '' ORDER BY username"),
                           roles_alertes=DROITS["vaccins_voir"], roles_rapports=DROITS["rapports_voir"])


@app.route("/parametres/email/test", methods=["POST"])
@roles(*DROITS["email_config"])
def email_test():
    moi = query("SELECT email FROM users WHERE id=?", (session["user"]["id"],), one=True)
    p = params_email()
    if not email_pret(p):
        flash("Activez et complétez d'abord les paramètres d'envoi.", "danger")
    elif not moi["email"]:
        flash("Renseignez votre adresse e-mail dans « Mon compte » pour recevoir le test.", "danger")
    else:
        ok, erreur = envoyer_et_journaliser({"destinataire": moi["email"], "sujet": "E-mail de test", "type": "test",
                                             "texte": "Ceci est un e-mail de test envoyé par la plateforme UPVac.\n"
                                                      "Si vous le recevez, la configuration est correcte."}, p)
        flash(f"E-mail de test envoyé à {moi['email']}." if ok else f"Échec de l'envoi : {erreur}", "success" if ok else "danger")
    return redirect(url_for("email_parametres"))


@app.route("/utilisateurs/<int:uid>/email", methods=["POST"])
@roles(*DROITS["utilisateurs"])
def utilisateur_email(uid):
    u = query("SELECT * FROM users WHERE id=?", (uid,), one=True)
    email = request.form.get("email", "").strip()[:120]
    if u is None:
        flash("Utilisateur introuvable.", "danger")
    elif email and not EMAIL_RE.fullmatch(email):
        flash("Adresse e-mail invalide.", "danger")
    else:
        execute("UPDATE users SET email=? WHERE id=?", (email or None, uid))
        audit(f"Adresse e-mail de {u['username']} {'modifiée' if email else 'supprimée'}")
        flash(f"Adresse e-mail de « {u['username']} » {'enregistrée' if email else 'supprimée'}.", "success")
    return redirect(url_for("utilisateurs"))


@app.route("/mon-compte", methods=["GET", "POST"])
@login_required
def mon_compte():
    uid = session["user"]["id"]
    if request.method == "POST":
        email = request.form.get("email", "").strip()[:120]
        if email and not EMAIL_RE.fullmatch(email):
            flash("Adresse e-mail invalide.", "danger")
        else:
            execute("UPDATE users SET email=?, notif_alertes=?, notif_rapports=? WHERE id=?",
                    (email or None, 1 if request.form.get("notif_alertes") else 0,
                     1 if request.form.get("notif_rapports") else 0, uid))
            flash("Votre compte est à jour.", "success")
            return redirect(url_for("mon_compte"))
    return render_template("mon_compte.html", u=query("SELECT * FROM users WHERE id=?", (uid,), one=True),
                           pret=email_pret())


@app.route("/rapports/archives/<int:rid>/envoyer", methods=["POST"])
@roles(*DROITS["email_config"])
def rapport_archive_envoyer(rid):
    if not email_pret():
        flash("L'envoi d'e-mails n'est pas activé : voir « Paramètres des notifications par e-mail ».", "danger")
    else:
        nb = envoyer_rapport_par_email(rid)
        flash(f"Rapport envoyé par e-mail à {nb} abonné(s)." if nb else "Aucun abonné à qui envoyer ce rapport.",
              "success" if nb else "warning")
    return redirect(url_for("rapports") + "#archives")


# ---------------------------------------------------------------- Suppressions et archivage
def supprimer_lots(ids):
    """Supprime des lots jamais vendus avec leurs mouvements et lignes d'inventaire (une transaction)."""
    retirer_pieces("lot", ids)
    con = db()
    try:
        for lot_id in ids:
            con.execute("DELETE FROM lignes_inventaire WHERE lot_id=?", (lot_id,))
            con.execute("DELETE FROM mouvements WHERE lot_id=?", (lot_id,))
            con.execute("DELETE FROM lots WHERE id=?", (lot_id,))
        con.commit()
    except Exception:
        con.rollback()
        raise


@app.route("/vaccins/<int:vid>/supprimer", methods=["POST"])
@roles(*DROITS["supprimer"])
def vaccin_supprimer(vid):
    v = query("SELECT * FROM vaccins WHERE id=?", (vid,), one=True)
    if v is None:
        flash("Vaccin introuvable.", "danger")
        return redirect(url_for("vaccins"))
    ventes = query("SELECT COUNT(*) AS n FROM lignes_vente lv JOIN lots l ON l.id=lv.lot_id"
                   " WHERE l.vaccin_id=?", (vid,), one=True)["n"]
    if ventes:
        flash(f"« {v['nom']} » a déjà été vendu : suppression impossible, pour conserver la "
              "traçabilité. Vous pouvez l'archiver quand son stock est à zéro.", "danger")
        return redirect(url_for("vaccins"))
    ids = [r["id"] for r in query("SELECT id FROM lots WHERE vaccin_id=?", (vid,))]
    supprimer_lots(ids)
    for ft in query("SELECT * FROM fiches_techniques WHERE vaccin_id=?", (vid,)):
        supprimer_fichier(ft["fichier"])
    execute("DELETE FROM fiches_techniques WHERE vaccin_id=?", (vid,))
    execute("DELETE FROM vaccins WHERE id=?", (vid,))
    audit(f"Suppression du vaccin {v['nom']} ({len(ids)} lot(s) supprimé(s))")
    flash(f"Vaccin « {v['nom']} » supprimé" + (f" avec ses {len(ids)} lot(s)." if ids else "."), "success")
    return redirect(url_for("vaccins"))


@app.route("/vaccins/<int:vid>/archiver", methods=["POST"])
@roles(*DROITS["vaccins_gerer"])
def vaccin_archiver(vid):
    v = query("SELECT * FROM vaccins WHERE id=?", (vid,), one=True)
    if v is None:
        flash("Vaccin introuvable.", "danger")
    elif v["actif"]:
        stock = query("SELECT COALESCE(SUM(CASE WHEN m.type='ENTREE' THEN m.quantite ELSE -m.quantite END),0)"
                      " AS n FROM mouvements m JOIN lots l ON l.id=m.lot_id WHERE l.vaccin_id=?",
                      (vid,), one=True)["n"]
        if stock != 0:
            flash(f"« {v['nom']} » a encore {stock} unité(s) en stock : archivage impossible.", "danger")
        else:
            execute("UPDATE vaccins SET actif=0 WHERE id=?", (vid,))
            audit(f"Archivage du vaccin {v['nom']}")
            flash(f"« {v['nom']} » archivé : il n'apparaît plus dans les listes ni les alertes.", "success")
    else:
        execute("UPDATE vaccins SET actif=1 WHERE id=?", (vid,))
        audit(f"Restauration du vaccin {v['nom']}")
        flash(f"« {v['nom']} » restauré.", "success")
    return redirect(url_for("vaccins"))


@app.route("/lots/<int:lot_id>/supprimer", methods=["POST"])
@roles(*DROITS["supprimer"])
def lot_supprimer(lot_id):
    lot = query("SELECT l.*, v.nom AS vaccin_nom FROM lots l JOIN vaccins v ON v.id=l.vaccin_id"
                " WHERE l.id=?", (lot_id,), one=True)
    if lot is None:
        flash("Lot introuvable.", "danger")
        return redirect(url_for("lots"))
    ventes = query("SELECT COUNT(*) AS n FROM lignes_vente WHERE lot_id=?", (lot_id,), one=True)["n"]
    if ventes:
        flash(f"Le lot {lot['numero_lot']} a déjà été vendu : suppression impossible. "
              "Changez plutôt son statut (rappelé, périmé…).", "danger")
        return redirect(url_for("lot_detail", lot_id=lot_id))
    nb = query("SELECT COUNT(*) AS n FROM mouvements WHERE lot_id=?", (lot_id,), one=True)["n"]
    supprimer_lots([lot_id])
    audit(f"Suppression du lot {lot['numero_lot']} ({lot['vaccin_nom']}) et de ses {nb} mouvement(s)")
    flash(f"Lot {lot['numero_lot']} supprimé.", "success")
    return redirect(url_for("lots"))


@app.route("/clients/<int:cid>/supprimer", methods=["POST"])
@roles(*DROITS["supprimer"])
def client_supprimer(cid):
    c = query("SELECT * FROM clients WHERE id=?", (cid,), one=True)
    if c is None:
        flash("Client introuvable.", "danger")
    elif query("SELECT (SELECT COUNT(*) FROM ventes WHERE client_id=?)"
               " + (SELECT COUNT(*) FROM commandes WHERE client_id=?) AS n", (cid, cid), one=True)["n"]:
        flash(f"« {c['nom']} » a déjà des ventes ou des commandes : suppression impossible.", "danger")
    else:
        execute("DELETE FROM clients WHERE id=?", (cid,))
        audit(f"Suppression du client {c['nom']}")
        flash(f"Client « {c['nom']} » supprimé.", "success")
    return redirect(url_for("clients"))


# ---------------------------------------------------------------- Articles (stock général : intrants, matériel)
NATURES_ART = {"STOCK_INITIAL": "Stock initial", "ENTREE": "Entrée (réception)",
               "SORTIE": "Sortie (consommation, perte…)", "AJUSTEMENT": "Ajustement"}
ARTICLES_FILTRES = ("q", "categorie_id", "fournisseur_id", "emplacement_id", "etat", "archives")
ARTICLES_SQL = (
    "SELECT a.*, c.nom AS categorie_nom, u.nom AS unite_nom, f.nom AS fournisseur_nom,"
    " e.nom AS emplacement_nom,"
    " COALESCE((SELECT SUM(m.delta) FROM mouvements_articles m WHERE m.article_id = a.id), 0) AS stock"
    " FROM articles a JOIN categories c ON c.id = a.categorie_id JOIN unites u ON u.id = a.unite_id"
    " LEFT JOIN fournisseurs f ON f.id = a.fournisseur_id"
    " LEFT JOIN emplacements e ON e.id = a.emplacement_id")


def entier(valeur, minimum=0):
    """Entier >= minimum, ou None si la saisie n'est pas valable."""
    try:
        n = int(str(valeur).strip())
    except (TypeError, ValueError):
        return None
    return n if n >= minimum else None


def ref_valide(table, valeur, courant=None):
    """Référence active ; l'ancienne valeur d'un article reste acceptée même si archivée depuis."""
    rid = ref_id(table, valeur)
    if rid is None and courant is not None and str(valeur) == str(courant):
        return int(courant)
    return rid


def choix_ref(table, courant=None):
    return query(f"SELECT id, nom FROM {table} WHERE actif=1 OR id=? ORDER BY nom COLLATE NOCASE",
                 (courant or 0,))


def liste_articles(flt):
    sql, args = ARTICLES_SQL + " WHERE 1=1", []
    if flt["q"]:
        sql += " AND (a.nom LIKE ? OR a.reference LIKE ?)"
        args += [f"%{flt['q']}%"] * 2
    for champ, colonne in (("categorie_id", "a.categorie_id"), ("fournisseur_id", "a.fournisseur_id"),
                           ("emplacement_id", "a.emplacement_id")):
        if flt[champ].isdigit():
            sql += f" AND {colonne}=?"
            args.append(int(flt[champ]))
    if flt["archives"] != "1":
        sql += " AND a.actif=1"
    lignes = query(sql + " ORDER BY a.actif DESC, a.nom COLLATE NOCASE", args)
    if flt["etat"] == "bas":
        lignes = [a for a in lignes if a["stock"] < a["seuil_min"]]
    return lignes


def lire_article(courant=None):
    """Lit le formulaire d'un article ; renvoie (valeurs, erreur)."""
    f = request.form
    nom = f.get("nom", "").strip()[:120]
    if not nom:
        return None, "Le nom de l'article est obligatoire."
    categorie = ref_valide("categories", f.get("categorie_id"), courant["categorie_id"] if courant else None)
    unite = ref_valide("unites", f.get("unite_id"), courant["unite_id"] if courant else None)
    if categorie is None or unite is None:
        return None, "Choisissez une catégorie et une unité."
    seuil = entier(f.get("seuil_min") or 0)
    if seuil is None:
        return None, "Le seuil minimal doit être un nombre entier positif ou nul."
    return {"nom": nom, "reference": f.get("reference", "").strip()[:60],
            "description": f.get("description", "").strip()[:300],
            "categorie_id": categorie, "unite_id": unite, "seuil_min": seuil,
            "fournisseur_id": ref_valide("fournisseurs", f.get("fournisseur_id"),
                                         courant["fournisseur_id"] if courant else None),
            "emplacement_id": ref_valide("emplacements", f.get("emplacement_id"),
                                         courant["emplacement_id"] if courant else None)}, None


def enregistrer_mouvement_article(aid, nature, delta, motif):
    return execute("INSERT INTO mouvements_articles(article_id, nature, delta, motif, date, user_id)"
                   " VALUES (?,?,?,?,?,?)", (aid, nature, delta, motif, now(), session["user"]["id"]))


def liens_referentiels():
    return {"categories": choix_ref("categories"), "unites": choix_ref("unites"),
            "fournisseurs": choix_ref("fournisseurs"), "emplacements": choix_ref("emplacements")}


@app.route("/articles", methods=["GET", "POST"])
@roles(*DROITS["articles_voir"])
def articles():
    if request.method == "POST":
        if not droit("articles_gerer"):
            flash("Action réservée au responsable stock.", "danger")
            return redirect(url_for("articles"))
        vals, erreur = lire_article()
        initial = entier(request.form.get("stock_initial") or 0)
        if erreur:
            flash(erreur, "danger")
        elif initial is None:
            flash("Le stock initial doit être un nombre entier positif ou nul.", "danger")
        elif query("SELECT 1 FROM articles WHERE lower(nom)=lower(?)", (vals["nom"],), one=True):
            flash(f"Un article « {vals['nom']} » existe déjà.", "danger")
        else:
            aid = execute(f"INSERT INTO articles({', '.join(vals)}) VALUES ({', '.join('?' for _ in vals)})",
                          tuple(vals.values()))
            if initial:
                enregistrer_mouvement_article(aid, "STOCK_INITIAL", initial, "Stock initial")
            audit(f"Article créé : {vals['nom']}" + (f" (stock initial {initial})" if initial else ""))
            flash(f"Article « {vals['nom']} » créé.", "success")
            return redirect(url_for("article_detail", aid=aid))
        return redirect(url_for("articles"))
    flt = args_filtres(*ARTICLES_FILTRES)
    return render_template("articles.html", articles=liste_articles(flt), flt=flt, fq=filtres_actifs(flt),
                           **liens_referentiels())


@app.route("/articles/<int:aid>", methods=["GET", "POST"])
@roles(*DROITS["articles_voir"])
def article_detail(aid):
    a = query(ARTICLES_SQL + " WHERE a.id=?", (aid,), one=True)
    if a is None:
        flash("Article introuvable.", "danger")
        return redirect(url_for("articles"))
    if request.method == "POST":
        if not droit("articles_gerer"):
            flash("Action réservée au responsable stock.", "danger")
            return redirect(url_for("article_detail", aid=aid))
        vals, erreur = lire_article(courant=a)
        if erreur:
            flash(erreur, "danger")
        elif query("SELECT 1 FROM articles WHERE lower(nom)=lower(?) AND id<>?", (vals["nom"], aid), one=True):
            flash(f"Un article « {vals['nom']} » existe déjà.", "danger")
        else:
            execute(f"UPDATE articles SET {', '.join(k + '=?' for k in vals)} WHERE id=?", (*vals.values(), aid))
            audit(f"Article modifié : {a['nom']}" + (f" → {vals['nom']}" if vals["nom"] != a["nom"] else ""))
            flash("Modifications enregistrées.", "success")
            return redirect(url_for("article_detail", aid=aid))
        a = query(ARTICLES_SQL + " WHERE a.id=?", (aid,), one=True)
    docs_mvt = {}
    if droit("pj_fournisseur_voir"):
        for p in query("SELECT * FROM pieces_jointes WHERE objet='article_mvt' AND objet_id IN"
                       " (SELECT id FROM mouvements_articles WHERE article_id=?) ORDER BY id", (aid,)):
            docs_mvt.setdefault(p["objet_id"], []).append(p)
    solde, historique = 0, []
    for m in query("SELECT m.*, u.username FROM mouvements_articles m LEFT JOIN users u ON u.id=m.user_id"
                   " WHERE m.article_id=? ORDER BY m.id", (aid,)):
        solde += m["delta"]
        historique.append(dict(m, solde=solde, docs=docs_mvt.get(m["id"], [])))
    historique.reverse()
    return render_template("article.html", a=a, historique=historique, NATURES=NATURES_ART,
                           categories=choix_ref("categories", a["categorie_id"]),
                           unites=choix_ref("unites", a["unite_id"]),
                           fournisseurs=choix_ref("fournisseurs", a["fournisseur_id"]),
                           emplacements=choix_ref("emplacements", a["emplacement_id"]))


@app.route("/articles/<int:aid>/mouvement", methods=["POST"])
@roles(*DROITS["articles_mouvements"])
def article_mouvement(aid):
    a = query(ARTICLES_SQL + " WHERE a.id=?", (aid,), one=True)
    if a is None:
        flash("Article introuvable.", "danger")
        return redirect(url_for("articles"))
    retour = redirect(url_for("article_detail", aid=aid))
    nature = request.form.get("nature", "")
    quantite = entier(request.form.get("quantite"), 1)
    motif = request.form.get("motif", "").strip()[:200]
    if not a["actif"]:
        flash("Cet article est archivé : restaurez-le avant d'enregistrer un mouvement.", "danger")
    elif nature not in NATURES_ART:
        flash("Choisissez le type de mouvement.", "danger")
    elif quantite is None:
        flash("La quantité doit être un nombre entier supérieur à zéro.", "danger")
    elif nature in ("SORTIE", "AJUSTEMENT") and not motif:
        flash("Le motif est obligatoire pour une sortie ou un ajustement.", "danger")
    elif nature == "STOCK_INITIAL" and query("SELECT 1 FROM mouvements_articles WHERE article_id=?",
                                             (aid,), one=True):
        flash("Le stock initial ne peut être saisi que sur un article sans mouvement.", "danger")
    else:
        sens = 1 if nature in ("STOCK_INITIAL", "ENTREE") else -1
        if nature == "AJUSTEMENT":
            sens = 1 if request.form.get("sens") == "+" else -1
        delta = sens * quantite
        if a["stock"] + delta < 0:
            flash(f"Stock insuffisant : il reste {a['stock']} {a['unite_nom']} de « {a['nom']} ».", "danger")
        else:
            fichiers, erreur_fichier = fichiers_joints()
            if erreur_fichier:
                flash(erreur_fichier, "danger")
                return retour
            mouvement_id = enregistrer_mouvement_article(aid, nature, delta, motif or NATURES_ART[nature])
            for type_doc, stocke, original, taille in fichiers:
                ajouter_piece("article_mvt", mouvement_id, type_doc, "", stocke, original, taille)
            apres = a["stock"] + delta
            audit(f"Article {a['nom']} : {NATURES_ART[nature].split(' (')[0].lower()} "
                  f"{'+' if delta > 0 else ''}{delta} (stock {apres})")
            flash(f"Mouvement enregistré : stock {apres} {a['unite_nom']}.", "success")
            if a["stock"] >= a["seuil_min"] > apres:
                notifier_admins(f"Stock bas : {a['nom']}",
                                f"L'article « {a['nom']} » est passé sous son seuil minimal "
                                f"({apres} {a['unite_nom']} pour un seuil de {a['seuil_min']}).")
    return retour


@app.route("/articles/<int:aid>/archiver", methods=["POST"])
@roles(*DROITS["articles_gerer"])
def article_archiver(aid):
    a = query(ARTICLES_SQL + " WHERE a.id=?", (aid,), one=True)
    if a is None:
        flash("Article introuvable.", "danger")
        return redirect(url_for("articles"))
    if a["actif"] and a["stock"] != 0:
        flash(f"« {a['nom']} » a encore {a['stock']} {a['unite_nom']} en stock : archivage impossible.", "danger")
    else:
        nouveau = 0 if a["actif"] else 1
        execute("UPDATE articles SET actif=? WHERE id=?", (nouveau, aid))
        audit(f"Article {'restauré' if nouveau else 'archivé'} : {a['nom']}")
        flash(f"« {a['nom']} » {'restauré' if nouveau else 'archivé'}.", "success")
    return redirect(url_for("article_detail", aid=aid))


@app.route("/articles/<int:aid>/supprimer", methods=["POST"])
@roles(*DROITS["supprimer"])
def article_supprimer(aid):
    a = query("SELECT * FROM articles WHERE id=?", (aid,), one=True)
    if a is None:
        flash("Article introuvable.", "danger")
        return redirect(url_for("articles"))
    if query("SELECT 1 FROM mouvements_articles WHERE article_id=? AND nature IN ('SORTIE','AJUSTEMENT')",
             (aid,), one=True):
        flash(f"« {a['nom']} » a déjà eu des sorties ou des ajustements : suppression impossible. "
              "Archivez-le plutôt.", "danger")
        return redirect(url_for("article_detail", aid=aid))
    retirer_pieces("article_mvt", [m["id"] for m in query("SELECT id FROM mouvements_articles WHERE article_id=?", (aid,))])
    con = db()
    con.execute("DELETE FROM mouvements_articles WHERE article_id=?", (aid,))
    con.execute("DELETE FROM articles WHERE id=?", (aid,))
    con.commit()
    audit(f"Article supprimé : {a['nom']}")
    flash(f"Article « {a['nom']} » supprimé.", "success")
    return redirect(url_for("articles"))


@app.route("/export/articles.xlsx")
@roles(*DROITS["articles_voir"])
def export_articles():
    from openpyxl.styles import Font, PatternFill
    lignes = [[a["nom"], a["reference"], a["categorie_nom"], a["unite_nom"], a["fournisseur_nom"],
               a["emplacement_nom"], a["stock"], a["seuil_min"],
               "Stock bas" if a["stock"] < a["seuil_min"] else "OK"]
              for a in liste_articles(args_filtres(*ARTICLES_FILTRES))]

    def colorer(ws, r, v):
        if v[8] == "Stock bas":
            for c in (7, 9):
                ws.cell(row=r, column=c).fill = PatternFill("solid", fgColor="FFE8B3")
                ws.cell(row=r, column=c).font = Font(bold=True, color="9B5B00")

    return classeur_excel("Articles", "Stock général : articles",
                          ["Article", "Référence", "Catégorie", "Unité", "Fournisseur", "Emplacement",
                           "Stock", "Seuil minimal", "État"],
                          lignes, [28, 14, 18, 12, 22, 20, 10, 14, 12], "articles", colorer=colorer)


# ---------------------------------------------------------------- Référentiels
REFERENTIELS = {
    "categories": {"titre": "Catégories", "ico": "etiquette", "table": "categories",
                   "desc": "familles d'articles (vaccins, intrants, matériel…)",
                   "champs": [("nom", "Nom", True), ("description", "Description", False)],
                   "usage": "(SELECT COUNT(*) FROM articles WHERE categorie_id = t.id)",
                   "usage_label": "article(s)"},
    "unites": {"titre": "Unités", "ico": "regle", "table": "unites",
               "desc": "dose, flacon, boîte…",
               "champs": [("nom", "Nom", True), ("symbole", "Symbole", False)],
               "usage": "(SELECT COUNT(*) FROM articles WHERE unite_id = t.id)",
               "usage_label": "article(s)"},
    "emplacements": {"titre": "Emplacements", "ico": "epingle", "table": "emplacements",
                     "desc": "chambres froides, rayons, magasins…",
                     "champs": [("nom", "Nom", True), ("description", "Description", False)],
                     "usage": "((SELECT COUNT(*) FROM lots WHERE emplacement_id = t.id)"
                              " + (SELECT COUNT(*) FROM articles WHERE emplacement_id = t.id))",
                     "usage_label": "lot(s) ou article(s)"},
    "fournisseurs": {"titre": "Fournisseurs", "ico": "camion", "table": "fournisseurs",
                     "desc": "base des fournisseurs",
                     "champs": [("nom", "Nom", True), ("contact", "Contact", False),
                                ("telephone", "Téléphone", False), ("email", "E-mail", False),
                                ("adresse", "Adresse", False)],
                     "usage": "((SELECT COUNT(*) FROM lots WHERE fournisseur_id = t.id)"
                              " + (SELECT COUNT(*) FROM articles WHERE fournisseur_id = t.id))",
                     "usage_label": "lot(s) ou article(s)"},
}


def ref_conf(cle):
    conf = REFERENTIELS.get(cle)
    if conf is None:
        abort(404)
    return conf


def ref_id(table, valeur):
    """Identifiant d'un élément de référentiel actif, ou None (champ vide ou invalide)."""
    if str(valeur or "").isdigit() and query(f"SELECT 1 FROM {table} WHERE id=? AND actif=1",
                                             (int(valeur),), one=True):
        return int(valeur)
    return None


def ref_valeurs(conf):
    """Lit et vérifie le formulaire ; renvoie (valeurs, message_d_erreur)."""
    vals = {}
    for nom, libelle, requis in conf["champs"]:
        v = request.form.get(nom, "").strip()[:200]
        if requis and not v:
            return None, f"Le champ « {libelle} » est obligatoire."
        vals[nom] = v
    if vals.get("email") and not re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", vals["email"]):
        return None, "Adresse e-mail invalide."
    return vals, None


@app.route("/referentiels")
@roles(*DROITS["referentiels_voir"])
def referentiels():
    cartes = []
    for cle, conf in REFERENTIELS.items():
        n = query(f"SELECT COUNT(*) AS n FROM {conf['table']} WHERE actif=1", one=True)["n"]
        cartes.append({"cle": cle, "titre": conf["titre"], "ico": conf["ico"], "desc": conf["desc"], "n": n})
    nb_clients = query("SELECT COUNT(*) AS n FROM clients", one=True)["n"]
    return render_template("referentiels.html", cartes=cartes, nb_clients=nb_clients)


@app.route("/referentiels/<cle>", methods=["GET", "POST"])
@roles(*DROITS["referentiels_voir"])
def ref_liste(cle):
    conf = ref_conf(cle)
    if request.method == "POST":
        if not droit("referentiels_gerer"):
            flash("Action réservée au responsable stock.", "danger")
            return redirect(url_for("ref_liste", cle=cle))
        vals, erreur = ref_valeurs(conf)
        if erreur:
            flash(erreur, "danger")
        elif query(f"SELECT 1 FROM {conf['table']} WHERE lower(nom)=lower(?)", (vals["nom"],), one=True):
            flash(f"« {vals['nom']} » existe déjà dans {conf['titre'].lower()}.", "danger")
        else:
            colonnes = ", ".join(vals)
            execute(f"INSERT INTO {conf['table']}({colonnes}) VALUES ({', '.join('?' for _ in vals)})",
                    tuple(vals.values()))
            audit(f"{conf['titre']} : ajout de « {vals['nom']} »")
            flash(f"« {vals['nom']} » ajouté.", "success")
        return redirect(url_for("ref_liste", cle=cle))
    archives = request.args.get("archives") == "1"
    lignes = query(f"SELECT t.*, {conf['usage']} AS nb_usages FROM {conf['table']} t"
                   + ("" if archives else " WHERE t.actif=1") + " ORDER BY t.actif DESC, t.nom COLLATE NOCASE")
    return render_template("ref_liste.html", cle=cle, conf=conf, lignes=lignes, archives=archives)


@app.route("/referentiels/<cle>/<int:rid>", methods=["GET", "POST"])
@roles(*DROITS["referentiels_voir"])
def ref_edit(cle, rid):
    conf = ref_conf(cle)
    r = query(f"SELECT t.*, {conf['usage']} AS nb_usages FROM {conf['table']} t WHERE t.id=?", (rid,), one=True)
    if r is None:
        flash("Élément introuvable.", "danger")
        return redirect(url_for("ref_liste", cle=cle))
    if request.method == "POST":
        if not droit("referentiels_gerer"):
            flash("Action réservée au responsable stock.", "danger")
            return redirect(url_for("ref_liste", cle=cle))
        vals, erreur = ref_valeurs(conf)
        if erreur:
            flash(erreur, "danger")
        elif query(f"SELECT 1 FROM {conf['table']} WHERE lower(nom)=lower(?) AND id<>?",
                   (vals["nom"], rid), one=True):
            flash(f"« {vals['nom']} » existe déjà.", "danger")
        else:
            affectation = ", ".join(f"{k}=?" for k in vals)
            execute(f"UPDATE {conf['table']} SET {affectation} WHERE id=?", (*vals.values(), rid))
            audit(f"{conf['titre']} : modification de « {r['nom']} »" +
                  (f" → « {vals['nom']} »" if vals["nom"] != r["nom"] else ""))
            flash("Modifications enregistrées.", "success")
            return redirect(url_for("ref_liste", cle=cle))
    return render_template("ref_edit.html", cle=cle, conf=conf, r=r)


@app.route("/referentiels/<cle>/<int:rid>/archiver", methods=["POST"])
@roles(*DROITS["referentiels_gerer"])
def ref_archiver(cle, rid):
    conf = ref_conf(cle)
    r = query(f"SELECT * FROM {conf['table']} WHERE id=?", (rid,), one=True)
    if r is None:
        flash("Élément introuvable.", "danger")
    else:
        nouveau = 0 if r["actif"] else 1
        execute(f"UPDATE {conf['table']} SET actif=? WHERE id=?", (nouveau, rid))
        audit(f"{conf['titre']} : {'restauration' if nouveau else 'archivage'} de « {r['nom']} »")
        flash(f"« {r['nom']} » {'restauré' if nouveau else 'archivé : il ne sera plus proposé dans les listes'}.", "success")
    return redirect(url_for("ref_liste", cle=cle))


@app.route("/referentiels/<cle>/<int:rid>/supprimer", methods=["POST"])
@roles(*DROITS["supprimer"])
def ref_supprimer(cle, rid):
    conf = ref_conf(cle)
    r = query(f"SELECT t.*, {conf['usage']} AS nb_usages FROM {conf['table']} t WHERE t.id=?", (rid,), one=True)
    if r is None:
        flash("Élément introuvable.", "danger")
    elif r["nb_usages"]:
        flash(f"« {r['nom']} » est utilisé par {r['nb_usages']} {conf['usage_label']} : suppression "
              "impossible. Archivez-le plutôt.", "danger")
    else:
        execute(f"DELETE FROM {conf['table']} WHERE id=?", (rid,))
        audit(f"{conf['titre']} : suppression de « {r['nom']} »")
        flash(f"« {r['nom']} » supprimé.", "success")
    return redirect(url_for("ref_liste", cle=cle))


# ---------------------------------------------------------------- Gestion des utilisateurs
ROLES_VALIDES = tuple(ROLES)


def mdp_temporaire(n=10):
    """Mot de passe aléatoire lisible (sans 0/O, 1/l/I) contenant minuscules, majuscules, chiffres."""
    alphabet = "abcdefghjkmnpqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ23456789"
    while True:
        m = "".join(secrets.choice(alphabet) for _ in range(n))
        if any(c.isdigit() for c in m) and any(c.islower() for c in m) and any(c.isupper() for c in m):
            return m


@app.route("/utilisateurs")
@roles(*DROITS["utilisateurs"])
def utilisateurs():
    liste = query("SELECT u.*, (SELECT MAX(date) FROM audit a WHERE a.user_id=u.id"
                  " AND a.action='Connexion') AS derniere FROM users u"
                  " ORDER BY u.actif DESC, u.username")
    mdp = session.pop("mdp_temp", None)  # affiché une seule fois
    return render_template("utilisateurs.html", users=liste, ROLES=ROLES_VALIDES, mdp=mdp, max_echecs=MAX_ECHECS,
                           moi=session["user"]["id"])


@app.route("/utilisateurs/nouveau", methods=["POST"])
@roles(*DROITS["utilisateurs"])
def utilisateur_nouveau():
    nom = re.sub(r"\s+", " ", request.form["username"]).strip()
    role = request.form["role"]
    email = request.form.get("email", "").strip()[:120]
    if email and not EMAIL_RE.fullmatch(email):
        flash("Adresse e-mail invalide.", "danger")
    elif not re.fullmatch(r"[\w .'-]{3,30}", nom):
        flash("Nom d'utilisateur invalide : 3 à 30 caractères (lettres, chiffres, espaces, . _ - ').", "danger")
    elif role not in ROLES_VALIDES:
        flash("Rôle invalide.", "danger")
    elif query("SELECT 1 FROM users WHERE lower(username)=lower(?)", (nom,), one=True):
        flash("Ce nom d'utilisateur existe déjà.", "danger")
    else:
        mdp = MDP_STANDARD
        execute("INSERT INTO users(username, password_hash, role, actif, doit_changer_mdp, email, code)"
                " VALUES (?,?,?,1,1,?,?)", (nom, generate_password_hash(mdp), role, email or None,
                                            prochain_code(db(), role)))
        audit(f"Création du compte {nom} (rôle {ROLES[role]})")
        session["mdp_temp"] = {"username": nom, "mdp": mdp}
        flash(f"Compte « {nom} » créé.", "success")
    return redirect(url_for("utilisateurs"))


@app.route("/utilisateurs/<int:uid>/etat", methods=["POST"])
@roles(*DROITS["utilisateurs"])
def utilisateur_etat(uid):
    u = query("SELECT * FROM users WHERE id=?", (uid,), one=True)
    if u is None:
        flash("Utilisateur introuvable.", "danger")
    elif u["id"] == session["user"]["id"]:
        flash("Vous ne pouvez pas désactiver votre propre compte.", "danger")
    else:
        nouveau = 0 if u["actif"] else 1
        execute("UPDATE users SET actif=? WHERE id=?", (nouveau, uid))
        audit(f"{'Réactivation' if nouveau else 'Désactivation'} du compte {u['username']}")
        flash(f"Compte « {u['username']} » {'réactivé' if nouveau else 'désactivé'}.", "success")
    return redirect(url_for("utilisateurs"))


@app.route("/utilisateurs/<int:uid>/debloquer", methods=["POST"])
@roles(*DROITS["utilisateurs"])
def utilisateur_debloquer(uid):
    u = query("SELECT * FROM users WHERE id=?", (uid,), one=True)
    if u is None:
        flash("Utilisateur introuvable.", "danger")
    else:
        execute("UPDATE users SET echecs=0, bloque=0 WHERE id=?", (uid,))
        audit(f"Déblocage du compte {u['username']}")
        flash(f"Compte « {u['username']} » débloqué : il peut se reconnecter.", "success")
    return redirect(url_for("utilisateurs"))


def historique_utilisateur(uid):
    """Nombre d'enregistrements métier (ventes, mouvements, commandes…) liés à ce compte."""
    total = 0
    for (table,) in db().execute("SELECT name FROM sqlite_master WHERE type='table'").fetchall():
        if table in ("audit", "messages", "users", "sqlite_sequence"):
            continue
        cols = {r[1] for r in db().execute(f"PRAGMA table_info({table})")}
        cols |= {r[3] for r in db().execute(f"PRAGMA foreign_key_list({table})") if r[2] == "users"}
        for col in cols & {"user_id", "created_by", "par", "valide_par", "utilisateur_id"}:
            total += db().execute(f"SELECT COUNT(*) FROM {table} WHERE {col}=?", (uid,)).fetchone()[0]
    return total


@app.route("/utilisateurs/<int:uid>/supprimer", methods=["POST"])
@roles(*DROITS["utilisateurs"])
def utilisateur_supprimer(uid):
    u = query("SELECT * FROM users WHERE id=?", (uid,), one=True)
    if u is None:
        flash("Utilisateur introuvable.", "danger")
    elif u["id"] == session["user"]["id"]:
        flash("Vous ne pouvez pas supprimer votre propre compte.", "danger")
    elif historique_utilisateur(uid):
        flash(f"« {u['username']} » a déjà des opérations enregistrées (ventes, mouvements, commandes…). "
              "Pour conserver l'historique, désactivez le compte au lieu de le supprimer.", "warning")
    else:
        con = db()
        con.execute("DELETE FROM messages WHERE expediteur_id=? OR destinataire_id=?", (uid, uid))
        con.execute("UPDATE audit SET user_id=NULL, action=action || ' (compte supprimé : ' || ? || ')' WHERE user_id=?",
                    (u["username"], uid))
        con.execute("DELETE FROM users WHERE id=?", (uid,))
        con.commit()
        audit(f"Suppression du compte {u['username']} ({u['code'] or '—'})")
        flash(f"Compte « {u['username']} » supprimé.", "success")
    return redirect(url_for("utilisateurs"))


@app.route("/utilisateurs/<int:uid>/reinitialiser", methods=["POST"])
@roles(*DROITS["utilisateurs"])
def utilisateur_reinit(uid):
    u = query("SELECT * FROM users WHERE id=?", (uid,), one=True)
    if u is None:
        flash("Utilisateur introuvable.", "danger")
    elif u["id"] == session["user"]["id"]:
        flash("Pour votre propre compte, utilisez « Mot de passe » dans la barre du haut.", "warning")
    else:
        mdp = MDP_STANDARD
        execute("UPDATE users SET password_hash=?, doit_changer_mdp=1, echecs=0, bloque=0 WHERE id=?",
                (generate_password_hash(mdp), uid))
        audit(f"Réinitialisation du mot de passe de {u['username']}")
        session["mdp_temp"] = {"username": u["username"], "mdp": mdp}
        flash(f"Mot de passe de « {u['username']} » réinitialisé.", "success")
    return redirect(url_for("utilisateurs"))


@app.route("/utilisateurs/<int:uid>/role", methods=["POST"])
@roles(*DROITS["utilisateurs"])
def utilisateur_role(uid):
    u = query("SELECT * FROM users WHERE id=?", (uid,), one=True)
    role = request.form.get("role")
    if u is None or role not in ROLES_VALIDES:
        flash("Demande invalide.", "danger")
    elif u["id"] == session["user"]["id"]:
        flash("Vous ne pouvez pas modifier votre propre rôle.", "danger")
    elif role != u["role"]:
        execute("UPDATE users SET role=?, code=? WHERE id=?", (role, prochain_code(db(), role), uid))
        audit(f"Changement de rôle de {u['username']} : {ROLES.get(u['role'], u['role'])} → {ROLES[role]}")
        flash(f"« {u['username']} » est maintenant {ROLES[role]}.", "success")
    return redirect(url_for("utilisateurs"))


# ---------------------------------------------------------------- Bon de vente imprimable
@app.template_filter("nombre")
def filtre_nombre(n):
    """12345.0 -> « 12 345 » ; 12.5 -> « 12,50 »."""
    n = float(n)
    txt = f"{n:,.0f}" if n == int(n) else f"{n:,.2f}"
    return txt.replace(",", " ").replace(".", ",") if n != int(n) else txt.replace(",", " ")


@app.template_filter("type_mvt")
def filtre_type_mvt(type_, nature=None):
    return {"TEMOIN": "Sortie · témoins", "DETRUIT": "Sortie · destruction"}.get(
        nature, "Entrée" if type_ == "ENTREE" else "Sortie")


@app.template_filter("role_lib")
def filtre_role_lib(role):
    return ROLES.get(role, role)


@app.template_filter("date_fr")
def filtre_date_fr(iso):
    return datetime.fromisoformat(iso).strftime("%d/%m/%Y")


@app.route("/ventes/<int:vente_id>/bon")
@roles(*DROITS["ventes_voir"])
def vente_bon(vente_id):
    v = query("SELECT v.*, c.nom AS client, c.type AS client_type, c.telephone AS client_tel,"
              " u.username FROM ventes v JOIN clients c ON c.id=v.client_id"
              " JOIN users u ON u.id=v.user_id WHERE v.id=?", (vente_id,), one=True)
    if v is None:
        flash("Vente introuvable.", "danger")
        return redirect(url_for("ventes"))
    lignes = query("SELECT lv.quantite, lv.prix_unitaire, lv.quantite*lv.prix_unitaire AS montant,"
                   " va.nom AS vaccin, va.temp_min, va.temp_max, l.numero_lot, l.date_peremption"
                   " FROM lignes_vente lv JOIN lots l ON l.id=lv.lot_id"
                   " JOIN vaccins va ON va.id=l.vaccin_id WHERE lv.vente_id=? ORDER BY lv.id",
                   (vente_id,))
    return render_template(
        "vente_bon.html", v=v, lignes=lignes, numero=f"BV-{vente_id:05d}",
        date_vente=datetime.fromisoformat(v["date"]).strftime("%d/%m/%Y à %H:%M"),
        total=sum(l["montant"] for l in lignes), qte=sum(l["quantite"] for l in lignes),
        imprime_le=datetime.now().strftime("%d/%m/%Y à %H:%M"), devise=DEVISE,
        societe={"nom": ENTREPRISE_NOM, "adresse": ENTREPRISE_ADRESSE,
                 "tel": ENTREPRISE_TEL, "email": ENTREPRISE_EMAIL})


# ---------------------------------------------------------------- Exports Excel
VERT_XLSX = "2F6B14"


def classeur_excel(nom_feuille, titre, entetes, lignes, largeurs, fichier,
                   colonnes_total=(), colorer=None):
    """Construit un fichier .xlsx mis en forme (logo, titre, filtres, totaux) et l'envoie."""
    from openpyxl import Workbook
    from openpyxl.styles import Alignment, Border, Font, PatternFill, Side

    wb = Workbook()
    ws = wb.active
    ws.title = nom_feuille
    ws["B1"] = titre
    ws["B1"].font = Font(size=16, bold=True, color=VERT_XLSX)
    ws["B2"] = f"UPVac - ISRA · exporté le {datetime.now().strftime('%d/%m/%Y à %H:%M')} " \
               f"par {session['user']['username']}"
    ws["B2"].font = Font(size=10, italic=True, color="666666")
    ws.row_dimensions[1].height = 30
    ws.row_dimensions[2].height = 20
    try:  # logo facultatif (nécessite Pillow)
        from openpyxl.drawing.image import Image as XlImage
        from PIL import Image as PilImage
        petit = PilImage.open(os.path.join(BASE_DIR, "static", "logo.png"))
        petit.thumbnail((210, 156))  # version légère pour ne pas alourdir le fichier
        tampon = BytesIO()
        petit.save(tampon, format="PNG")
        tampon.seek(0)
        logo = XlImage(tampon)
        logo.height, logo.width = 52, int(52 * petit.width / petit.height)
        ws.add_image(logo, "A1")
    except Exception:
        pass

    ligne_entete = 4
    fin = Side(style="thin", color="C9D3C2")
    bordure = Border(left=fin, right=fin, top=fin, bottom=fin)
    for c, texte in enumerate(entetes, start=1):
        cel = ws.cell(row=ligne_entete, column=c, value=texte)
        cel.font = Font(bold=True, color="FFFFFF")
        cel.fill = PatternFill("solid", fgColor=VERT_XLSX)
        cel.alignment = Alignment(horizontal="center", vertical="center", wrap_text=True)
        cel.border = bordure
    ws.row_dimensions[ligne_entete].height = 24

    for r, valeurs in enumerate(lignes, start=ligne_entete + 1):
        fond = PatternFill("solid", fgColor="F3F8EE") if r % 2 == 0 else None
        for c, v in enumerate(valeurs, start=1):
            cel = ws.cell(row=r, column=c, value=v)
            cel.border = bordure
            if fond:
                cel.fill = fond
            if isinstance(v, float):
                cel.number_format = "#,##0"
        if colorer:
            colorer(ws, r, valeurs)

    derniere = ligne_entete + len(lignes)
    if lignes and colonnes_total:
        r = derniere + 1
        ws.cell(row=r, column=1, value="TOTAL").font = Font(bold=True)
        for c in colonnes_total:
            lettre = ws.cell(row=ligne_entete, column=c).column_letter
            cel = ws.cell(row=r, column=c, value=f"=SUM({lettre}{ligne_entete + 1}:{lettre}{derniere})")
            cel.font = Font(bold=True)
            cel.number_format = "#,##0"
        for c in range(1, len(entetes) + 1):
            ws.cell(row=r, column=c).fill = PatternFill("solid", fgColor="E4EFDB")
            ws.cell(row=r, column=c).border = bordure

    for i, w in enumerate(largeurs, start=1):
        ws.column_dimensions[ws.cell(row=1, column=i).column_letter].width = w
    ws.freeze_panes = ws.cell(row=ligne_entete + 1, column=1)
    if lignes:
        ws.auto_filter.ref = f"A{ligne_entete}:{ws.cell(row=1, column=len(entetes)).column_letter}{derniere}"
    ws.sheet_view.showGridLines = False
    ws.page_setup.orientation = "landscape"
    ws.page_setup.fitToWidth = 1
    ws.page_setup.fitToHeight = 0
    ws.sheet_properties.pageSetUpPr.fitToPage = True

    sortie = BytesIO()
    wb.save(sortie)
    sortie.seek(0)
    audit(f"Export Excel : {nom_feuille}")
    return send_file(sortie, as_attachment=True,
                     download_name=f"{fichier}_{date.today().isoformat()}.xlsx",
                     mimetype="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")


@app.route("/export/stock.xlsx")
@login_required
def export_stock():
    from openpyxl.styles import Font, PatternFill
    lignes = []
    for l in liste_lots(args_filtres(*LOTS_FILTRES)):
        lignes.append([l["vaccin_nom"], l["numero_lot"], l["date_fabrication"],
                       l["date_peremption"], l["jours"],
                       l["stock"], l["emplacement_nom"], l["fournisseur_nom"], l["statut"],
                       l["temoins"], l["detruites"], l["recu"]])

    def colorer(ws, r, v):
        if v[4] < 0:
            for c in (4, 5):
                ws.cell(row=r, column=c).fill = PatternFill("solid", fgColor="F8D7DA")
                ws.cell(row=r, column=c).font = Font(bold=True, color="9B1C1C")
        elif v[4] <= 30:
            ws.cell(row=r, column=5).fill = PatternFill("solid", fgColor="FFE8B3")
        if v[8] in ("quarantaine", "rappelé"):
            ws.cell(row=r, column=9).font = Font(bold=True, color="B36B00")
        elif v[8] == "périmé":
            ws.cell(row=r, column=9).font = Font(bold=True, color="9B1C1C")

    return classeur_excel("Stock par lot", "État du stock de vaccins",
                          ["Nom du vaccin", "N° lot", "Fabrication", "Péremption", "Jours restants",
                           "Disponible", "Emplacement", "Provenance", "Statut", "Témoins", "Détruites",
                           "Quantité reçue"],
                          lignes, [26, 16, 14, 14, 14, 12, 20, 20, 14, 10, 10, 14], "stock_vaccins",
                          colonnes_total=(6,), colorer=colorer)


@app.route("/export/mouvements.xlsx")
@roles(*DROITS["mouvements_voir"])
def export_mouvements():
    rows = liste_mouvements(args_filtres(*MOUVEMENTS_FILTRES))
    lignes = [[m["date"].replace("T", " "), m["vaccin_nom"], m["numero_lot"],
               filtre_type_mvt(m["type"], m["nature"]),
               m["quantite"], m["motif"], m["username"]] for m in rows]
    return classeur_excel("Mouvements", "Entrées et sorties de stock",
                          ["Date", "Vaccin", "N° lot", "Type", "Quantité", "Motif", "Utilisateur"],
                          lignes, [20, 26, 16, 12, 12, 28, 16], "mouvements_stock")


@app.route("/export/ventes.xlsx")
@roles(*DROITS["ventes_voir"])
def export_ventes():
    where, args = clause_ventes(args_filtres(*VENTES_FILTRES))
    rows = query("SELECT v.id, v.date, v.mode, c.nom AS client, va.nom AS vaccin, l.numero_lot,"
                 " lv.quantite, lv.prix_unitaire, lv.quantite*lv.prix_unitaire AS total,"
                 " u.username" + VENTES_FROM + where + " ORDER BY v.id DESC, lv.id", args)
    lignes = [[r["id"], r["date"].replace("T", " "), r["client"], r["vaccin"], r["numero_lot"],
               r["quantite"], float(r["prix_unitaire"]), float(r["total"]), r["username"],
               MODES_VENTE.get(r["mode"], "")]
              for r in rows]
    return classeur_excel("Ventes", "Historique des ventes",
                          ["N° vente", "Date", "Client", "Vaccin", "N° lot", "Quantité",
                           "Prix unitaire", "Total", "Vendeur", "Mode"],
                          lignes, [10, 20, 24, 26, 16, 12, 14, 14, 16, 20], "ventes",
                          colonnes_total=(6, 8))


# ---------------------------------------------------------------- Clients et ventes
@app.route("/clients", methods=["GET", "POST"])
@roles(*DROITS["clients_voir"])
def clients():
    if request.method == "POST":
        if not droit("clients_gerer"):
            flash("Action réservée à un autre rôle : l'ajout d'un client revient au responsable vente.", "danger")
            return redirect(url_for("clients"))
        vals, erreur = lire_client()
        if erreur:
            flash(erreur[0].upper() + erreur[1:], "danger")
        elif query("SELECT 1 FROM clients WHERE lower(nom)=lower(?)", (vals["nom"],), one=True):
            flash(f"Un client « {vals['nom']} » existe déjà.", "danger")
        else:
            execute(f"INSERT INTO clients({', '.join(vals)}) VALUES ({', '.join('?' for _ in vals)})",
                    tuple(vals.values()))
            audit(f"Ajout client {vals['nom']}")
            flash("Client ajouté.", "success")
        return redirect(url_for("clients"))
    return render_template("clients.html", clients=query("SELECT c.*, (SELECT COUNT(*) FROM ventes v WHERE v.client_id=c.id) AS nb_ventes,"
                                       " (SELECT COUNT(*) FROM commandes o WHERE o.client_id=c.id) AS nb_commandes"
                                       " FROM clients c ORDER BY c.nom"))


def etat_paiement(mode, total, paye, echeance):
    """(solde restant, état) : une vente au comptant est payée ; une vente à terme se suit jusqu'au solde."""
    if mode == "comptant":
        return 0, "payée"
    if mode != "terme":
        return 0, ""
    solde = max(0, total - paye)
    if solde < 0.005:
        return 0, "soldée"
    if echeance and echeance < date.today().isoformat():
        return solde, "en retard"
    return solde, "partielle" if paye > 0 else "à régler"


ETATS_IMPAYES = ("partielle", "à régler", "en retard")


@app.route("/ventes")
@roles(*DROITS["ventes_voir"])
def ventes():
    flt = args_filtres(*VENTES_FILTRES)
    statut = request.args.get("statut", "")
    where, args = clause_ventes(flt)
    liste = []
    for v in query("SELECT v.id, v.date, v.mode, v.echeance, c.nom AS client, u.username, v.commande_id,"
                   " (SELECT numero FROM commandes WHERE id=v.commande_id) AS commande_numero,"
                   " SUM(lv.quantite) AS qte,"
                   " SUM(lv.quantite*lv.prix_unitaire) AS total,"
                   " (SELECT COALESCE(SUM(p.montant), 0) FROM paiements p WHERE p.vente_id=v.id) AS paye"
                   + VENTES_FROM + where + " GROUP BY v.id ORDER BY v.id DESC", args):
        solde, etat = etat_paiement(v["mode"], v["total"], v["paye"], v["echeance"])
        if statut == "impayees" and etat not in ETATS_IMPAYES:
            continue
        liste.append(dict(v, solde=solde, etat=etat))
    return render_template("ventes.html", ventes=liste, flt=flt, fq=filtres_actifs(flt), statut=statut,
                           vaccins=query("SELECT id, nom FROM vaccins ORDER BY nom"),
                           vendeurs=query("SELECT id, username FROM users ORDER BY username"),
                           qte_total=sum(v["qte"] for v in liste),
                           montant_total=sum(v["total"] for v in liste),
                           reste_total=sum(v["solde"] for v in liste), MODES_VENTE=MODES_VENTE)


def charger_vente(vente_id):
    """Vente, lignes (par lot), lignes de facture (regroupées par vaccin et prix) et paiements."""
    v = query("SELECT v.*, c.nom AS client, c.type AS client_type, c.telephone AS client_tel,"
              " c.adresse AS client_adresse, COALESCE(u.code, u.username) AS username FROM ventes v"
              " JOIN clients c ON c.id=v.client_id JOIN users u ON u.id=v.user_id WHERE v.id=?", (vente_id,), one=True)
    if v is None:
        return None
    lignes = query("SELECT lv.quantite, lv.prix_unitaire, lv.quantite*lv.prix_unitaire AS montant,"
                   " va.nom AS vaccin, va.temp_min, va.temp_max, l.numero_lot, l.date_peremption"
                   " FROM lignes_vente lv JOIN lots l ON l.id=lv.lot_id"
                   " JOIN vaccins va ON va.id=l.vaccin_id WHERE lv.vente_id=? ORDER BY lv.id", (vente_id,))
    regroupees = query("SELECT va.nom AS vaccin, lv.prix_unitaire, SUM(lv.quantite) AS quantite,"
                       " SUM(lv.quantite*lv.prix_unitaire) AS montant FROM lignes_vente lv"
                       " JOIN lots l ON l.id=lv.lot_id JOIN vaccins va ON va.id=l.vaccin_id"
                       " WHERE lv.vente_id=? GROUP BY va.id, lv.prix_unitaire ORDER BY MIN(lv.id)", (vente_id,))
    paiements = query("SELECT p.*, COALESCE(u.code, u.username) AS username FROM paiements p LEFT JOIN users u ON u.id=p.user_id"
                      " WHERE p.vente_id=? ORDER BY p.id", (vente_id,))
    total = sum(l["montant"] for l in lignes)
    paye = sum(p["montant"] for p in paiements)
    solde, etat = etat_paiement(v["mode"], total, paye, v["echeance"])
    return {"v": v, "lignes": lignes, "regroupees": regroupees, "paiements": paiements, "total": total,
            "paye": paye, "solde": solde, "etat": etat, "numero": f"{vente_id:07d}",
            "adresse": v["adresse"] or v["client_adresse"] or ""}


@app.route("/ventes/<int:vente_id>")
@roles(*DROITS["ventes_voir"])
def vente_detail(vente_id):
    d = charger_vente(vente_id)
    if d is None:
        flash("Vente introuvable.", "danger")
        return redirect(url_for("ventes"))
    return render_template("vente_detail.html", MODES_VENTE=MODES_VENTE, MODES_PAIEMENT=MODES_PAIEMENT, **d)


@app.route("/ventes/<int:vente_id>/facture")
@roles(*DROITS["ventes_voir"])
def vente_facture(vente_id):
    d = charger_vente(vente_id)
    if d is None:
        flash("Vente introuvable.", "danger")
        return redirect(url_for("ventes"))
    return render_template(
        "facture_vente.html", lettres=nombre_en_lettres(d["total"]), vides=max(0, 14 - len(d["regroupees"])),
        date_vente=datetime.fromisoformat(d["v"]["date"]).strftime("%d/%m/%Y"), devise=DEVISE,
        imprime_le=datetime.now().strftime("%d/%m/%Y à %H:%M"), MODES_VENTE=MODES_VENTE,
        societe={"nom": ENTREPRISE_NOM, "adresse": ENTREPRISE_ADRESSE, "tel": ENTREPRISE_TEL}, **d)


@app.route("/ventes/<int:vente_id>/paiement", methods=["POST"])
@roles(*DROITS["paiements_saisir"])
def vente_paiement(vente_id):
    retour = redirect(url_for("vente_detail", vente_id=vente_id))
    d = charger_vente(vente_id)
    if d is None or d["v"]["mode"] != "terme":
        flash("Seules les ventes à terme se règlent par versements.", "danger")
        return retour
    montant = decimal(request.form.get("montant", ""))
    mode = request.form.get("mode_paiement", "")
    if not montant or montant <= 0:
        flash("Saisissez un montant supérieur à zéro.", "danger")
    elif montant > d["solde"] + 0.005:
        flash(f"Le montant dépasse le solde restant ({filtre_nombre(d['solde'])} {DEVISE}).", "danger")
    else:
        execute("INSERT INTO paiements(vente_id, montant, mode, date, user_id) VALUES (?,?,?,?,?)",
                (vente_id, montant, mode if mode in MODES_PAIEMENT else "espèces", now(), session["user"]["id"]))
        audit(f"Encaissement de {filtre_nombre(montant)} {DEVISE} sur la vente n°{d['numero']}")
        reste = d["solde"] - montant
        flash("Paiement enregistré." + (" La vente est soldée." if reste < 0.005 else
                                        f" Reste à payer : {filtre_nombre(reste)} {DEVISE}."), "success")
    return retour


def creances():
    """(reste à encaisser, nombre de ventes à terme en retard)."""
    reste = retard = 0
    for v in query("SELECT v.echeance,"
                   " COALESCE((SELECT SUM(lv.quantite*lv.prix_unitaire) FROM lignes_vente lv WHERE lv.vente_id=v.id), 0) AS total,"
                   " COALESCE((SELECT SUM(p.montant) FROM paiements p WHERE p.vente_id=v.id), 0) AS paye"
                   " FROM ventes v WHERE v.mode='terme'"):
        solde, etat = etat_paiement("terme", v["total"], v["paye"], v["echeance"])
        reste += solde
        retard += etat == "en retard"
    return reste, retard


def enregistrer_vente_caisse(mode, s):
    """Enregistre une vente de caisse (comptant ou à terme) : stock décrémenté sur le champ (FEFO).
    Renvoie (vente_id, erreur)."""
    uid, aujourd_hui = session["user"]["id"], date.today().isoformat()
    lignes = []
    for l in s["lignes"]:
        nom, q, p = re.sub(r"\s+", " ", l["nom"]).strip(), l["quantite"].strip(), l["prix"].strip()
        if not (nom or q or p):
            continue
        v = query("SELECT * FROM vaccins WHERE lower(nom)=lower(?) AND actif=1", (nom,), one=True) if nom else None
        if v is None:
            return None, f"Vaccin « {nom} » introuvable dans le catalogue." if nom else "Indiquez le nom du vaccin sur chaque ligne."
        qte = entier(q, 1)
        if qte is None:
            return None, f"Quantité invalide pour {v['nom']} (nombre entier supérieur à zéro)."
        prix = decimal(p) if p else v["prix_unitaire"]
        if prix is None:
            return None, f"Prix invalide pour {v['nom']}."
        if not prix:
            return None, f"Aucun prix pour {v['nom']} : saisissez-le sur la ligne (ou renseignez-le dans le catalogue)."
        lignes.append((v, qte, prix))
    if not lignes:
        return None, "Ajoutez au moins un vaccin à vendre."
    besoin = {}
    for v, q, _p in lignes:
        besoin[v["id"]] = (v["nom"], besoin.get(v["id"], ("", 0))[1] + q)
    _c = query("SELECT id FROM clients WHERE lower(nom)=lower(?)",
               (re.sub(r"\s+", " ", s["client_nom"]).strip()[:120] or "Client comptoir",), one=True)
    vendable = stocks_utilisables(_c["id"] if _c else None)
    manques = [f"{nom} : {q} demandé(s), {vendable.get(vid, 0)} disponible(s)"
               for vid, (nom, q) in besoin.items() if q > vendable.get(vid, 0)]
    if manques:
        return None, "Stock vendable insuffisant : " + " ; ".join(manques)
    total = sum(q * p for _v, q, p in lignes)
    nom_client = re.sub(r"\s+", " ", s["client_nom"]).strip()[:120]
    adresse = s["client_adresse"].strip()[:200]
    echeance, acompte = None, 0
    if mode == "terme":
        if not nom_client:
            return None, "Le nom du client est obligatoire pour une vente à terme."
        try:
            echeance = date.fromisoformat(s["echeance"])
        except ValueError:
            return None, "Indiquez la date d'échéance du paiement."
        if echeance < date.today():
            return None, "La date d'échéance ne peut pas être dans le passé."
        if s["acompte"].strip():
            acompte = decimal(s["acompte"])
            if acompte is None or acompte > total + 0.005:
                return None, "L'acompte doit être un nombre positif ne dépassant pas le total."
    mode_paiement = s["mode_paiement"] if s["mode_paiement"] in MODES_PAIEMENT else "espèces"
    con = db()
    try:
        nom_client = nom_client or "Client comptoir"
        c = con.execute("SELECT id, adresse FROM clients WHERE lower(nom)=lower(?)", (nom_client,)).fetchone()
        if c:
            client_id = c["id"]
            if adresse and not c["adresse"]:
                con.execute("UPDATE clients SET adresse=? WHERE id=?", (adresse, client_id))
        else:
            client_id = con.execute("INSERT INTO clients(nom, type, telephone, nature, adresse) VALUES (?,?,?,?,?)",
                                    (nom_client, "", s["client_tel"].strip()[:40], "particulier", adresse)).lastrowid
        vente_id = con.execute("INSERT INTO ventes(client_id, date, user_id, mode, echeance, adresse)"
                               " VALUES (?,?,?,?,?,?)",
                               (client_id, now(), uid, mode, echeance.isoformat() if echeance else None,
                                adresse or None)).lastrowid
        lots = {}
        mes_res = reservations_client(client_id)
        for v, qte, prix in lignes:
            if v["id"] not in lots:  # FEFO : le lot conforme qui périme en premier part en premier
                lots[v["id"]] = [dict(x, stock=dispo_pour(x, mes_res)) for x in query(
                    STOCK_SQL + " WHERE l.vaccin_id=? AND l.statut='conforme' AND l.date_peremption >= ?"
                    " ORDER BY l.date_peremption", (v["id"], aujourd_hui))]
            reste = qte
            for lot in lots[v["id"]]:
                prise = min(reste, lot["stock"])
                if prise <= 0:
                    continue
                con.execute("INSERT INTO lignes_vente(vente_id, lot_id, quantite, prix_unitaire) VALUES (?,?,?,?)",
                            (vente_id, lot["id"], prise, prix))
                con.execute("INSERT INTO mouvements(lot_id, type, quantite, motif, date, user_id, vente_id)"
                            " VALUES (?,?,?,?,?,?,?)",
                            (lot["id"], "SORTIE", prise, f"{MODES_VENTE[mode]} n°{vente_id:07d}", now(), uid, vente_id))
                consommer_reservation(con, lot["id"], client_id, prise)
                lot["stock"] -= prise
                reste -= prise
            if reste > 0:
                raise ValueError("stock insuffisant")
        encaisse = total if mode == "comptant" else acompte
        if encaisse > 0:
            con.execute("INSERT INTO paiements(vente_id, montant, mode, date, user_id) VALUES (?,?,?,?,?)",
                        (vente_id, encaisse, mode_paiement, now(), uid))
        con.commit()
    except ValueError:
        con.rollback()
        return None, "Vente annulée : le stock a changé pendant l'opération. Aucun mouvement n'a été enregistré."
    except Exception:
        con.rollback()
        raise
    audit(f"{MODES_VENTE[mode]} n°{vente_id:07d} : {filtre_nombre(total)} {DEVISE}, client {nom_client}")
    restant = stocks_utilisables()
    for vid, (nom, _q) in besoin.items():
        seuil = query("SELECT seuil_min FROM vaccins WHERE id=?", (vid,), one=True)["seuil_min"]
        if restant.get(vid, 0) < seuil:
            notifier_admins(f"Stock bas : {nom}", f"Après la vente n°{vente_id:07d}, il reste "
                            f"{restant.get(vid, 0)} unités (seuil minimal : {seuil}). Prévoir une commande.")
    return vente_id, None


@app.route("/ventes/caisse", methods=["GET", "POST"])
@roles(*DROITS["ventes_saisir"])
def caisse():
    f = request.form
    mode = f.get("mode") or request.args.get("mode") or "comptant"
    if mode not in ("comptant", "terme"):
        mode = "comptant"
    saisie = None
    if request.method == "POST":
        saisie = {k: f.get(k, "") for k in ("client_nom", "client_adresse", "client_tel", "echeance", "acompte",
                                            "mode_paiement")}
        saisie["lignes"] = [{"nom": n, "quantite": q, "prix": p} for n, q, p in
                            zip_longest(f.getlist("ligne_vaccin"), f.getlist("ligne_quantite"), f.getlist("ligne_prix"),
                                        fillvalue="")]
        vente_id, erreur = enregistrer_vente_caisse(mode, saisie)
        if not erreur:
            flash(f"{MODES_VENTE[mode]} enregistrée ; le stock a été décrémenté. Facture prête à imprimer.", "success")
            return redirect(url_for("vente_facture", vente_id=vente_id))
        flash(erreur, "danger")
    vendable = stocks_utilisables()
    catalogue = [{"nom": v["nom"], "prix": v["prix_unitaire"], "stock": vendable.get(v["id"], 0)}
                 for v in query("SELECT id, nom, prix_unitaire FROM vaccins WHERE actif=1 ORDER BY nom COLLATE NOCASE")]
    return render_template("caisse.html", mode=mode, saisie=saisie, catalogue=catalogue,
                           clients=query("SELECT nom FROM clients ORDER BY nom COLLATE NOCASE"),
                           MODES_PAIEMENT=MODES_PAIEMENT,
                           echeance_defaut=(date.today() + timedelta(days=30)).isoformat())


NIVEAUX_PURGE = (("ventes", "Ventes et commandes (ventes, paiements, commandes, factures, livraisons). "
                  "Le stock des lots est rétabli."),
                 ("stock", "Tout ce qui précède + lots, entrées/sorties et inventaires (le catalogue des vaccins est conservé)."),
                 ("tout", "Tout ce qui précède + clients."))


def compter_purge():
    def n(sql):
        return query(sql, one=True)[0]
    return {"ventes": n("SELECT COUNT(*) FROM ventes"), "commandes": n("SELECT COUNT(*) FROM commandes"),
            "factures": n("SELECT COUNT(*) FROM factures"), "lots": n("SELECT COUNT(*) FROM lots"),
            "inventaires": n("SELECT COUNT(*) FROM inventaires"), "clients": n("SELECT COUNT(*) FROM clients")}


@app.route("/donnees-essai", methods=["GET", "POST"])
@roles(*DROITS["reinitialiser"])
def donnees_essai():
    if request.method == "POST":
        niveau = request.form.get("niveau", "")
        if niveau not in dict(NIVEAUX_PURGE):
            flash("Choisissez ce qu'il faut supprimer.", "danger")
        elif request.form.get("confirmation", "").strip().upper() != "SUPPRIMER":
            flash("Pour confirmer, tapez le mot SUPPRIMER.", "danger")
        else:
            con = db()
            fichiers = []
            try:
                objets = ["commande"] + (["lot"] if niveau in ("stock", "tout") else [])
                for o in objets:
                    fichiers += [r["fichier"] for r in con.execute(
                        "SELECT fichier FROM pieces_jointes WHERE objet=?", (o,))]
                    con.execute("DELETE FROM pieces_jointes WHERE objet=?", (o,))
                for table in ("livraisons", "historique_commande", "lignes_facture", "factures", "paiements"):
                    con.execute(f"DELETE FROM {table}")
                con.execute("DELETE FROM mouvements WHERE vente_id IS NOT NULL")
                for table in ("lignes_vente", "ventes", "lignes_commande", "commandes"):
                    con.execute(f"DELETE FROM {table}")
                if niveau in ("stock", "tout"):
                    for table in ("lignes_inventaire", "inventaires", "mouvements", "lots"):
                        con.execute(f"DELETE FROM {table}")
                if niveau == "tout":
                    con.execute("DELETE FROM clients")
                con.commit()
            except Exception:
                con.rollback()
                raise
            for nom in fichiers:
                supprimer_fichier(nom)
            audit(f"Purge des données d'essai (niveau « {niveau} »)")
            flash("Données d'essai supprimées. Vous pouvez maintenant supprimer ou archiver les vaccins d'essai "
                  "depuis le catalogue.", "success")
            return redirect(url_for("donnees_essai"))
    return render_template("donnees_essai.html", niveaux=NIVEAUX_PURGE, nb=compter_purge())


@app.route("/ventes/nouvelle", methods=["GET", "POST"])
@login_required
def vente_nouvelle():
    return redirect(url_for("caisse") if droit("ventes_saisir") else url_for("ventes"))


# ---------------------------------------------------------------- Messagerie
@app.route("/messages", methods=["GET", "POST"])
@login_required
def messages():
    uid = session["user"]["id"]
    if request.method == "POST":
        f = request.form
        execute("INSERT INTO messages(expediteur_id,destinataire_id,sujet,corps,date)"
                " VALUES (?,?,?,?,?)", (uid, int(f["destinataire_id"]), f["sujet"], f["corps"], now()))
        flash("Message envoyé.", "success")
        return redirect(url_for("messages"))
    recus = query("SELECT m.*, u.username AS de FROM messages m JOIN users u ON u.id=m.expediteur_id"
                  " WHERE m.destinataire_id=? ORDER BY m.id DESC", (uid,))
    envoyes = query("SELECT m.*, u.username AS a FROM messages m JOIN users u ON u.id=m.destinataire_id"
                    " WHERE m.expediteur_id=? ORDER BY m.id DESC LIMIT 50", (uid,))
    users = query("SELECT id, username, role FROM users WHERE id<>? AND actif=1 ORDER BY username", (uid,))
    html = render_template("messages.html", recus=recus, envoyes=envoyes, users=users)
    execute("UPDATE messages SET lu=1 WHERE destinataire_id=?", (uid,))
    return html


# ---------------------------------------------------------------- Inventaire
@app.route("/inventaire")
@roles(*DROITS["inventaire_voir"])
def inventaires():
    liste = query("SELECT i.*, u.username FROM inventaires i JOIN users u ON u.id=i.user_id"
                  " ORDER BY i.id DESC")
    return render_template("inventaires.html", inventaires=liste)


@app.route("/inventaire/nouveau", methods=["POST"])
@roles(*DROITS["inventaire_compter"])
def inventaire_nouveau():
    inv_id = execute("INSERT INTO inventaires(date,user_id) VALUES (?,?)",
                     (now(), session["user"]["id"]))
    for l in query(STOCK_SQL + " ORDER BY l.vaccin_id, l.date_peremption"):
        db().execute("INSERT INTO lignes_inventaire(inventaire_id,lot_id,theorique) VALUES (?,?,?)",
                     (inv_id, l["id"], l["stock"]))
    db().commit()
    audit(f"Ouverture inventaire #{inv_id}")
    return redirect(url_for("inventaire_detail", inv_id=inv_id))


@app.route("/inventaire/<int:inv_id>", methods=["GET", "POST"])
@roles(*DROITS["inventaire_voir"])
def inventaire_detail(inv_id):
    inv = query("SELECT * FROM inventaires WHERE id=?", (inv_id,), one=True)
    if inv is None:
        return redirect(url_for("inventaires"))
    if request.method == "POST" and not inv["valide"]:
        valider = "valider" in request.form
        if valider and not droit("inventaire_valider"):
            flash("La validation d'un inventaire est réservée à l'administrateur.", "danger")
            return redirect(url_for("inventaire_detail", inv_id=inv_id))
        if not valider and not droit("inventaire_compter"):
            flash("La saisie du comptage est réservée au responsable stock.", "danger")
            return redirect(url_for("inventaire_detail", inv_id=inv_id))
        db().execute("UPDATE inventaires SET commentaire=? WHERE id=?",
                     (request.form.get("commentaire", "").strip()[:2000] or None, inv_id))
        if not valider:  # comptage (responsable stock)
            for li in query("SELECT * FROM lignes_inventaire WHERE inventaire_id=?", (inv_id,)):
                valeur = request.form.get(f"compte_{li['id']}", "").strip()
                if valeur == "":
                    continue
                compte = max(0, int(valeur))
                db().execute("UPDATE lignes_inventaire SET compte=?, ecart=? WHERE id=?",
                             (compte, compte - li["theorique"], li["id"]))
            audit(f"Comptage inventaire #{inv_id}")
            flash("Comptage enregistré. L'administrateur peut maintenant valider.", "success")
        else:  # validation (administrateur) : régularise les écarts saisis par le responsable stock
            for li in query("SELECT * FROM lignes_inventaire WHERE inventaire_id=?", (inv_id,)):
                if li["compte"] is None:
                    continue
                ecart = li["compte"] - li["theorique"]
                if ecart != 0:
                    db().execute("INSERT INTO mouvements(lot_id,type,quantite,motif,date,user_id)"
                                 " VALUES (?,?,?,?,?,?)",
                                 (li["lot_id"], "ENTREE" if ecart > 0 else "SORTIE", abs(ecart),
                                  f"Ajustement inventaire #{inv_id}", now(), session["user"]["id"]))
            db().execute("UPDATE inventaires SET valide=1 WHERE id=?", (inv_id,))
            audit(f"Validation inventaire #{inv_id}")
            flash("Inventaire validé ; écarts régularisés dans le stock.", "success")
        db().commit()
        return redirect(url_for("inventaire_detail", inv_id=inv_id))
    lignes = query("SELECT li.*, l.numero_lot, v.nom AS vaccin_nom,"
                   " (SELECT nom FROM emplacements WHERE id=l.emplacement_id) AS emplacement"
                   " FROM lignes_inventaire li JOIN lots l ON l.id=li.lot_id"
                   " JOIN vaccins v ON v.id=l.vaccin_id WHERE li.inventaire_id=?"
                   " ORDER BY v.nom, l.date_peremption", (inv_id,))
    return render_template("inventaire.html", inv=inv, lignes=lignes)


# ---------------------------------------------------------------- Journal d'audit
@app.route("/audit")
@roles(*DROITS["audit"])
def journal():
    flt = args_filtres("q", "utilisateur_id", "du", "au")
    where, args = "", []
    if flt["q"]:
        where += " AND (a.action LIKE ? OR u.username LIKE ?)"
        args += [f"%{flt['q']}%"] * 2
    if flt["utilisateur_id"].isdigit():
        where += " AND a.user_id=?"
        args.append(int(flt["utilisateur_id"]))
    if flt["du"]:
        where += " AND substr(a.date,1,10) >= ?"
        args.append(flt["du"])
    if flt["au"]:
        where += " AND substr(a.date,1,10) <= ?"
        args.append(flt["au"])
    base = " FROM audit a LEFT JOIN users u ON u.id=a.user_id WHERE 1=1" + where
    total = query("SELECT COUNT(*) AS n" + base, args, one=True)["n"]
    liste = query("SELECT a.*, u.username" + base + " ORDER BY a.id DESC LIMIT 300", args)
    return render_template("audit.html", entrees=liste, total=total, flt=flt,
                           users=query("SELECT id, username FROM users ORDER BY username"))


# ---------------------------------------------------------------- Gabarits HTML
BASE = """<!doctype html><html lang="fr"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="theme-color" content="#1d4310">
<title>UPVac - Stock vaccins</title>
<script>try{var t=localStorage.getItem('upvac_theme');if(t){document.documentElement.setAttribute('data-theme',t);}}catch(e){}</script>
<link rel="icon" type="image/png" href="{{ url_for('static', filename='favicon.png') }}">
<style>
/* ============================================================ Thème UPVac */
:root{
--vert:#3d9a1f;--vert-fonce:#2b7313;--vert-nuit:#173d0b;--vert-clair:#e6f4dc;--vert-pale:#f3f9ee;--titre:#173d0b;
--or:#e3a008;--or-clair:#fdf3d4;
--bleu:#2563eb;--bleu-clair:#e8f0fe;--orange:#d97706;--orange-clair:#fff4e0;--rouge:#d32f2f;--rouge-clair:#fdecec;
--fond:#f2f6ef;--surface:#fff;--surface-2:#f8fbf6;--survol:#edf6e6;--champ:#fff;--ligne:#ebf0e7;--piste:#e3ebdd;
--bord:#dde6d6;--bord-fort:#c3d0ba;--texte:#18230f;--texte-2:#56644f;--texte-3:#859180;
--verre:rgba(255,255,255,.86);--entete:linear-gradient(180deg,#2b7313,#22610e);
--g-grille:#e1e9db;--g-texte:#6b7865;--g-barre-1:#6cc43c;--g-barre-2:#2b7313;--g-ligne:#2563eb;--g-valeur:#173d0b;
--rayon:12px;--rayon-p:8px;
--ombre:0 1px 2px rgba(20,40,10,.05),0 2px 10px rgba(20,40,10,.06);
--ombre-forte:0 8px 28px rgba(20,40,10,.16);
--menu:264px;
--police:'Segoe UI Variable Text','Segoe UI',system-ui,-apple-system,Roboto,'Helvetica Neue',Arial,sans-serif}
*,*::before,*::after{box-sizing:border-box}
html{scroll-behavior:smooth}
body{font-family:var(--police);font-size:15px;line-height:1.5;margin:0;background:var(--fond);color:var(--texte);min-height:100vh;position:relative;display:flow-root;-webkit-font-smoothing:antialiased}
body::before{content:"";position:fixed;inset:0;z-index:0;pointer-events:none;
background:url('{{ url_for("static", filename="fond.png") }}') center 58%/min(52vw,560px) no-repeat;opacity:.045}
main,.pied{position:relative;z-index:1}
a{color:var(--lien,var(--vert-fonce));text-underline-offset:3px}
a:hover{color:var(--lien-survol,var(--vert-nuit))}
::selection{background:#cfe6bd}



/* ------------------------------------------------ Barre de navigation du haut */
.entete-app{position:sticky;top:0;z-index:50;background:#10300a;color:#fff;box-shadow:0 2px 12px rgba(0,0,0,.18)}
.entete-app .entete-barre{max-width:1340px;margin:0 auto;height:62px;padding:0 28px;display:flex;align-items:center;gap:20px}
.entete-app .brand{display:flex;align-items:center;gap:10px;color:#fff;text-decoration:none;flex:none}
.entete-app .brand img{height:38px;width:auto;background:#fff;border-radius:8px;padding:2px 4px}
.entete-app .brand b{display:block;font-size:17px;letter-spacing:.3px;line-height:1.1}
.entete-app .brand small{display:block;font-size:11px;color:#a9c49a}
.nav-principale{display:flex;align-items:center;gap:2px;height:100%}
.nav-principale .groupe{position:relative;height:100%;display:flex;align-items:center}
.entete-app .groupe-titre{position:relative;display:inline-flex;align-items:center;gap:8px;height:40px;padding:0 12px;background:transparent;color:#d3e2ca;border:0;box-shadow:none;border-radius:8px;font-size:14px;font-weight:600;text-decoration:none;cursor:pointer;white-space:nowrap}
.entete-app .groupe-titre:hover,.entete-app .groupe.ouvert>.groupe-titre{background:rgba(255,255,255,.09);color:#fff}
.entete-app .groupe-titre .ic{width:17px;height:17px;color:#93ad85}
.entete-app .groupe-titre .fl{width:14px;height:14px;opacity:.7;transition:transform .15s}
.entete-app .groupe.ouvert>.groupe-titre .fl{transform:rotate(180deg)}
.entete-app .groupe.actif>.groupe-titre{color:#fff}
.entete-app .groupe.actif>.groupe-titre .ic:not(.fl){color:var(--or)}
.entete-app .groupe.actif>.groupe-titre::after{content:"";position:absolute;left:12px;right:12px;bottom:-11px;height:3px;border-radius:3px 3px 0 0;background:var(--or)}
.deroulant{display:none;position:absolute;top:calc(100% - 6px);left:0;min-width:240px;background:var(--surface);border:1px solid var(--bord);border-radius:12px;box-shadow:var(--ombre-forte);padding:6px;z-index:60}
.groupe.ouvert>.deroulant{display:block}
@media(hover:hover) and (min-width:1001px){.nav-principale .groupe:hover>.deroulant{display:block}}
.deroulant a{display:flex;align-items:center;gap:10px;padding:9px 12px;border-radius:8px;color:var(--texte);text-decoration:none;font-size:14px;font-weight:500}
.deroulant a .i{display:inline-flex;color:var(--texte-3)}
.deroulant a:hover{background:var(--vert-pale);color:var(--texte)}
.deroulant a.actif{background:var(--vert-clair);color:var(--titre);font-weight:600}
.deroulant a.actif .i{color:var(--vert)}
.pastille-nb{margin-left:auto;background:var(--or);color:#1b1300;font-size:11px;font-weight:700;min-width:20px;height:20px;padding:0 6px;border-radius:10px;display:inline-flex;align-items:center;justify-content:center}
.groupe-titre .pastille-nb{margin-left:2px}
.entete-app .outils{margin-left:auto;display:flex;align-items:center;gap:6px}
.entete-app .jour{display:inline-flex;align-items:center;gap:6px;color:#a9c49a;font-size:12.5px;margin-right:6px;white-space:nowrap}
.entete-app .jour .ic{width:15px;height:15px}
.icone-btn{position:relative;display:inline-flex;align-items:center;justify-content:center;width:40px;height:40px;border-radius:10px;text-decoration:none;font-size:0;transition:background .15s}
.entete-app .icone-btn{color:#d3e2ca;background:transparent}
.entete-app .icone-btn:hover{background:rgba(255,255,255,.1);color:#fff}
.icone-btn .ic{width:19px;height:19px}
.icone-btn .nb{position:absolute;top:3px;right:2px;background:var(--rouge);color:#fff;font-size:10.5px;font-weight:700;min-width:18px;height:18px;border-radius:9px;padding:0 5px;display:flex;align-items:center;justify-content:center;border:2px solid #10300a}
.entete-app button.burger{display:none;background:transparent;border:1px solid rgba(255,255,255,.3);color:#fff;width:40px;height:40px;padding:0;border-radius:10px;box-shadow:none}
.entete-app button.burger .ic{width:20px;height:20px}
details.profil{position:relative}
details.profil summary{list-style:none;display:flex;align-items:center;gap:10px;cursor:pointer;padding:4px 10px 4px 4px;border-radius:24px;border:1px solid rgba(255,255,255,.16);background:rgba(255,255,255,.07);color:#fff;transition:box-shadow .15s}
details.profil summary::-webkit-details-marker{display:none}
details.profil summary:hover,details.profil[open] summary{box-shadow:0 0 0 3px rgba(255,255,255,.12)}
.avatar{width:32px;height:32px;border-radius:50%;background:linear-gradient(135deg,#f2c14e,#c8890a);color:#1b1300;font-weight:700;display:flex;align-items:center;justify-content:center;font-size:14px;text-transform:uppercase}
.profil .qui{line-height:1.15;white-space:nowrap}.profil .qui b{display:block;font-size:13px}.profil .qui small{font-size:11px;color:#a9c49a}
.profil .chevron .ic{width:14px;height:14px;color:#a9c49a}
.profil .menu{position:absolute;right:0;top:calc(100% + 10px);min-width:220px;background:var(--surface);border:1px solid var(--bord);border-radius:var(--rayon);box-shadow:var(--ombre-forte);padding:6px;z-index:60}
.profil .menu a{display:flex;gap:10px;align-items:center;padding:9px 12px;border-radius:8px;color:var(--texte);text-decoration:none;font-size:14px}
.profil .menu a:hover{background:var(--vert-pale)}
.profil .menu a .ic{color:var(--texte-3)}
.profil .menu hr{border:0;border-top:1px solid var(--bord);margin:6px 4px}
.profil .menu a.sortie,.profil .menu a.sortie .ic{color:var(--rouge)}
html[data-theme=sombre] .entete-app,html[data-theme=sombre] .entete-app .nav-principale{background:#0c1f08}
@media(max-width:1300px){.entete-app .jour{display:none}.entete-app .entete-barre{gap:12px}.entete-app .groupe-titre{padding:0 9px}}
@media(max-width:1000px){
.entete-app .entete-barre{padding:0 14px}
.entete-app button.burger{display:inline-flex}
.nav-principale{display:none;position:absolute;top:62px;left:0;right:0;height:auto;max-height:calc(100vh - 62px);overflow-y:auto;flex-direction:column;align-items:stretch;gap:0;background:#10300a;padding:6px 14px 18px;border-top:1px solid rgba(255,255,255,.1);box-shadow:0 12px 24px rgba(0,0,0,.25)}
.entete-app.ouvert .nav-principale{display:flex}
.nav-principale .groupe{height:auto;flex-direction:column;align-items:stretch}
.entete-app .groupe-titre{height:auto;justify-content:flex-start;padding:14px 4px 6px;font-size:11px;letter-spacing:1.1px;text-transform:uppercase;color:#8fae7c;cursor:default;background:transparent!important}
.entete-app .groupe-titre .ic,.entete-app .groupe.actif>.groupe-titre::after{display:none}
.entete-app a.groupe-titre{cursor:pointer;text-transform:none;letter-spacing:0;font-size:14px;font-weight:500;color:#d3e2ca;padding:11px 12px;margin-top:8px;border-top:1px solid rgba(255,255,255,.08);border-radius:0}
.entete-app a.groupe-titre .ic:not(.fl){display:inline-block;color:#93ad85}
.deroulant{display:block;position:static;min-width:0;background:transparent;border:0;box-shadow:none;padding:0}
.deroulant a{color:#d3e2ca;padding:11px 12px}
.deroulant a .i{color:#93ad85}
.deroulant a:hover{background:rgba(255,255,255,.06);color:#fff}
.deroulant a.actif{background:rgba(255,255,255,.1);color:#fff}
.deroulant a.actif .i{color:var(--or)}
.profil .qui,.profil .chevron{display:none}
details.profil summary{padding:3px}
}
@media(max-width:600px){.entete-app .brand small{display:none}}

/* ------------------------------------------------ Contenu */
main{max-width:1340px;margin:26px auto 10px;padding:0 28px}
body:not(.avec-menu) main{max-width:1100px}
h1{font-size:26px;line-height:1.2;font-weight:800;letter-spacing:-.01em;color:var(--titre);margin:4px 0 18px}
h2{font-size:18px;font-weight:700;color:var(--texte);margin:30px 0 12px}
h3{color:var(--titre)}
p{margin:10px 0}
hr{border:0;border-top:1px solid var(--bord)}
.pied{text-align:center;font-size:12px;color:var(--texte-3);padding:26px 10px 30px}

/* Tableaux */
table{width:100%;border-collapse:separate;border-spacing:0;background:var(--surface);font-size:14px;border:1px solid var(--bord);border-radius:var(--rayon);box-shadow:var(--ombre);overflow:hidden}
th{background:var(--entete);color:#fff;text-align:left;padding:11px 12px;font-size:12.5px;font-weight:700;letter-spacing:.3px;white-space:nowrap}
td{padding:10px 12px;border-bottom:1px solid var(--ligne);vertical-align:middle}
tr:last-child td{border-bottom:0}
main table:not(.fact-table):not(.bon-table) tr:nth-child(even) td{background:var(--surface-2)}
main table:not(.fact-table):not(.bon-table) tr:hover td{background:var(--survol)}
td a{font-weight:600}
.table-wrap{width:100%;overflow-x:auto;border:1px solid var(--bord);border-radius:var(--rayon);box-shadow:var(--ombre);background:var(--surface);margin:0 0 6px;-webkit-overflow-scrolling:touch}
.table-wrap>table{border:0;border-radius:0;box-shadow:none;overflow:visible}
td small{color:var(--texte-2)}
.num{text-align:right;font-variant-numeric:tabular-nums}

/* Formulaires */
form.card{background:var(--surface);padding:18px;border:1px solid var(--bord);border-radius:var(--rayon);box-shadow:var(--ombre);display:grid;
grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:14px;align-items:end;margin:6px 0 10px}
label{font-size:12.5px;font-weight:600;color:var(--texte-2);display:flex;flex-direction:column;gap:5px}
input,select,textarea{font:inherit;font-size:14px;padding:9px 11px;border:1px solid var(--bord-fort);border-radius:var(--rayon-p);background:var(--champ);color:var(--texte);transition:border-color .15s,box-shadow .15s;min-width:0}
textarea{resize:vertical}
input[type=checkbox],input[type=radio]{width:17px;height:17px;padding:0;accent-color:var(--vert);flex:none}
input[type=file]{padding:7px;background:var(--vert-pale);border-style:dashed}
input:hover,select:hover,textarea:hover{border-color:#a9b8a0}
input:focus,select:focus,textarea:focus{outline:none;border-color:var(--vert);box-shadow:0 0 0 3px rgba(73,141,30,.18)}
input[readonly],input:disabled,select:disabled{background:#f3f5f1;color:var(--texte-2)}
input::placeholder,textarea::placeholder{color:#9aa594}

/* Boutons */
button,.btn{display:inline-flex;align-items:center;justify-content:center;gap:6px;background:linear-gradient(180deg,#46a823,var(--vert-fonce));color:#fff;border:1px solid transparent;padding:9px 16px;border-radius:var(--rayon-p);cursor:pointer;font:inherit;font-size:14px;font-weight:600;line-height:1.2;box-shadow:0 1px 2px rgba(20,40,10,.15);transition:background .15s,box-shadow .15s,transform .05s;text-decoration:none;white-space:nowrap}
button:hover,.btn:hover{background:var(--vert-fonce);color:#fff}
button:active,.btn:active{transform:translateY(1px)}
button:focus-visible,a:focus-visible,summary:focus-visible{outline:3px solid rgba(73,141,30,.45);outline-offset:2px}
button.petit{padding:5px 11px;font-size:12.5px;border-radius:7px}
button.danger{background:var(--rouge)}button.danger:hover{background:#9b1c1c}
button.secondaire,.btn.secondaire{background:var(--surface);color:var(--vert-fonce);border:1px solid var(--vert)}
button.secondaire:hover,.btn.secondaire:hover{background:var(--vert);color:#fff}
.btn-export{display:inline-flex;align-items:center;gap:6px;padding:8px 14px;border:1px solid var(--vert);color:var(--vert-fonce);border-radius:var(--rayon-p);font-weight:600;font-size:13.5px;text-decoration:none;background:var(--surface);transition:background .15s}
.btn-export:hover{background:var(--vert);color:#fff}
form.en-ligne{display:inline-flex;gap:4px;margin:0 4px 0 0}

/* Messages flash et alertes */
.flash{display:flex;align-items:flex-start;gap:10px;padding:12px 14px;margin-bottom:10px;border-radius:10px;border:1px solid transparent;border-left-width:5px;font-size:14px;line-height:1.45}
.flash::before{flex:none;width:22px;height:22px;border-radius:50%;display:inline-flex;align-items:center;justify-content:center;font-size:12px;font-weight:800;color:#fff;margin-top:-1px}
.success{background:#e8f6e9}.danger{background:#fdecec}.warning{background:#fff6dc}
.flash.success{border-color:#bfe3c4;border-left-color:#2e7d32;color:#1b4d1f}.flash.success::before{content:"✓";background:#2e7d32}
.flash.danger{border-color:#f3c3c3;border-left-color:var(--rouge);color:#7a1717}.flash.danger::before{content:"!";background:var(--rouge)}
.flash.warning{border-color:#f2dc9c;border-left-color:var(--orange);color:#6b4300}.flash.warning::before{content:"!";background:var(--orange)}
.flash.info{background:var(--bleu-clair);border-color:#c6d8fb;border-left-color:var(--bleu);color:#1e3a8a}.flash.info::before{content:"i";background:var(--bleu)}
.flash .fermer{margin-left:auto;background:transparent;color:inherit;opacity:.55;box-shadow:none;padding:0 4px;font-size:18px;line-height:1}
.flash .fermer:hover{opacity:1;background:transparent;color:inherit}
.flashes{margin-bottom:6px}
.flashes .flash{animation:entree .25s ease-out;box-shadow:var(--ombre)}
@keyframes entree{from{opacity:0;transform:translateY(-6px)}to{opacity:1;transform:none}}

/* Badges */
.badge{display:inline-flex;align-items:center;gap:4px;padding:3px 10px;border-radius:999px;font-size:12px;font-weight:600;background:#e9ece6;color:#3b4636;white-space:nowrap;line-height:1.4}
.b-conforme,.b-disponible{background:#dcf5df;color:#166534}.b-vendu{background:#e9ebee;color:#4b5563}.b-réservé{background:#dbeafe;color:#1e40af}
.b-quarantaine,.b-rappelé{background:#fef1c7;color:#8a4b00}.b-périmé{background:#fde0e0;color:#9b1c1c}
.b-détruit{background:#dfe2e6;color:#333}.b-enregistrée{background:#dbeafe;color:#1e3a8a}.b-annulée{background:#f6dada;color:#7a1f1f}
.b-transmise{background:#e0e7ff;color:#3730a3}.b-facturée{background:#fef3c7;color:#92400e}.b-validée{background:#d1fae5;color:#065f46}
.b-livrée{background:#bbf7d0;color:#14532d}.b-archivée{background:#e5e7eb;color:#374151}.b-émise{background:#dbeafe;color:#1e3a8a}
.unread{font-weight:bold}
.unread td:first-child{box-shadow:inset 4px 0 0 var(--vert)}

/* Cartes indicateurs */
.cartes{display:grid;grid-template-columns:repeat(auto-fill,minmax(240px,1fr));gap:16px;margin:14px 0 24px}
.carte{--accent:var(--vert);--accent-clair:var(--vert-clair);position:relative;display:flex;align-items:center;gap:14px;background:var(--surface);border:1px solid var(--bord);border-radius:14px;padding:16px 18px;box-shadow:var(--ombre);overflow:hidden;color:inherit;text-decoration:none;transition:transform .15s,box-shadow .15s,border-color .15s}
.carte::before{content:"";position:absolute;left:0;top:0;bottom:0;width:4px;background:var(--accent)}
a.carte:hover{transform:translateY(-2px);box-shadow:var(--ombre-forte);border-color:var(--accent);color:inherit}
.carte .ico{flex:none;width:50px;height:50px;border-radius:12px;background:var(--accent-clair);display:flex;align-items:center;justify-content:center;font-size:24px}
.carte b{display:block;font-size:26px;line-height:1.1;font-weight:800;color:var(--texte);font-variant-numeric:tabular-nums}
.carte small{display:block;color:var(--texte-2);font-size:12.5px;margin-top:3px;line-height:1.35}
.carte .fleche{margin-left:auto;color:var(--texte-3);font-size:18px;transition:transform .15s}
a.carte:hover .fleche{transform:translateX(3px);color:var(--accent)}
.c-vert{--accent:var(--vert);--accent-clair:var(--vert-clair)}
.c-bleu{--accent:var(--bleu);--accent-clair:var(--bleu-clair)}
.c-orange{--accent:var(--orange);--accent-clair:#fde9c4;background:#fffbf3}.c-orange b{color:#9a5400}
.c-rouge{--accent:var(--rouge);--accent-clair:#f9d6d6;background:#fff8f8}.c-rouge b{color:var(--rouge)}
.rapport-carte{align-items:flex-start;flex-direction:column}
.rapport-carte small{display:block;margin:4px 0 10px;color:var(--texte-2)}
.rapport-carte label{margin-bottom:10px}
.rapport-carte .boutons{display:flex;gap:8px;flex-wrap:wrap}

/* Panneaux et grilles */
.deux-col{display:grid;grid-template-columns:3fr 2fr;gap:22px}
.deux-col.egal{grid-template-columns:1fr 1fr;margin-top:8px}
.deux-col.egal .panneau:only-child{grid-column:1/-1}
.panneau{background:var(--surface);border:1px solid var(--bord);border-radius:14px;padding:8px 18px 14px;box-shadow:var(--ombre)}
.panneau h2{font-size:15px;margin:12px 0 8px;color:var(--titre)}
@media(max-width:1100px){.deux-col,.deux-col.egal{grid-template-columns:1fr}}
.barre{background:var(--piste);border-radius:8px;height:9px;min-width:90px;overflow:hidden}
.rempli{height:100%;border-radius:8px;transition:width .6s ease}.rempli.ok{background:linear-gradient(90deg,#6bb33a,var(--vert))}.rempli.bas{background:linear-gradient(90deg,#e45a5a,var(--rouge))}
.mdp-box{background:#fffbe6;border:2px dashed #e8920c;padding:14px 16px;border-radius:10px;margin:12px 0}
.mdp-box code{font-size:22px;background:#fff;padding:3px 10px;border-radius:5px;letter-spacing:1.5px;user-select:all}

/* Filtres et recherche */
.filtres{display:flex;flex-wrap:wrap;gap:10px;align-items:flex-end;background:var(--surface);padding:14px;border:1px solid var(--bord);border-radius:var(--rayon);box-shadow:var(--ombre);margin:10px 0 12px}
.filtres input,.filtres select{padding:8px 10px;font-size:13.5px}
.filtres label{font-size:12px;color:var(--texte-2);display:flex;flex-direction:column;gap:3px}
.filtres label.case{flex-direction:row;align-items:center;gap:6px;font-size:13.5px;color:var(--texte);font-weight:500;padding-bottom:8px}
.filtres .grand{flex:1 1 240px}
.lien-reset{font-size:13px;color:var(--texte-2);align-self:center;padding:0 4px}
.compte{color:var(--texte-2);font-size:13.5px;margin:6px 0 12px;display:flex;flex-wrap:wrap;align-items:center;gap:10px}
input.recherche{width:100%;max-width:400px;margin:4px 0 12px;padding-left:12px}

/* Onglets */
.onglets{display:flex;gap:4px;margin:10px 0 16px;flex-wrap:wrap;background:var(--piste);padding:4px;border-radius:11px;width:fit-content;max-width:100%}
.onglets a{padding:8px 18px;border-radius:8px;color:var(--vert-nuit);text-decoration:none;font-weight:600;font-size:14px;transition:background .15s}
.onglets a:hover{background:rgba(255,255,255,.6)}
.onglets a.actif{background:var(--surface);color:var(--vert-fonce);box-shadow:0 1px 4px rgba(0,0,0,.12)}
.rapide{border:1px solid #bcd9a6;border-radius:var(--rayon);padding:4px 18px 14px;background:linear-gradient(180deg,#f4faee,#fff);margin-bottom:18px;box-shadow:var(--ombre)}
.rapide h2{margin:12px 0 4px}
.indice{font-size:12px;color:var(--texte-2);min-height:16px;grid-column:1/-1}.indice.alerte{color:#9b1c1c;font-weight:bold}
.total-gros{font-size:22px;font-weight:800;color:var(--vert-nuit)}

/* Documents imprimables : bon de livraison */
.actions-bon{max-width:820px;margin:0 auto 14px;display:flex;gap:14px;align-items:center;flex-wrap:wrap}
.actions-bon small{color:#667}
.bon{position:relative;max-width:820px;margin:0 auto;background:#fff;padding:28px 32px;border-radius:8px;box-shadow:0 2px 18px rgba(0,0,0,.13);overflow:hidden}
.bon .filigrane{position:absolute;left:50%;top:50%;width:68%;transform:translate(-50%,-50%);opacity:.07;pointer-events:none}
.bon-entete,.bon-infos,.bon-table,.bon-sign,.bon-pied{position:relative}
.bon-entete{display:flex;align-items:center;gap:18px;border-bottom:3px solid var(--vert);padding-bottom:14px}
.bon-logo{height:84px;width:auto}
.bon-soc{flex:1;font-size:13px;line-height:1.5}.bon-soc b{font-size:18px;color:var(--vert-nuit)}
.bon-titre{text-align:right;font-size:13px}.bon-titre h1{margin:0 0 4px;font-size:24px;letter-spacing:1px;color:var(--vert-fonce)}
.bon-titre .num{font-size:16px;font-weight:bold;color:#222}
.bon-infos{display:grid;grid-template-columns:1fr 1fr;gap:16px;margin:18px 0}
.bon-infos>div{border:1px solid #cfd8c8;border-radius:8px;padding:10px 14px;font-size:14px;line-height:1.5}
.bon-infos h3{margin:0 0 4px;font-size:12px;text-transform:uppercase;letter-spacing:.6px;color:var(--vert-fonce)}
.bon-table{box-shadow:none;background:transparent;border:0;border-radius:0;border-collapse:collapse;overflow:visible}
.bon-table td,.bon-table th{padding:8px 10px}
.bon-table td{border-bottom:1px solid #ddd}
.bon-table td small{color:#667}
.bon-table .num{text-align:right;white-space:nowrap}
.bon-table tfoot td{font-weight:bold;background:#e4efdb;border-top:2px solid var(--vert)}
.bon-sign{display:grid;grid-template-columns:1fr 1fr;gap:48px;margin-top:40px}
.bon-sign>div{border-top:1px solid #333;padding-top:6px;text-align:center;font-size:13px;height:90px}
.bon-pied{margin-top:20px;font-size:11px;color:#667;text-align:center;border-top:1px solid #dde5d6;padding-top:8px}

/* Documents imprimables : facture */
.fact{position:relative;max-width:780px;margin:0 auto;background:#fff;padding:26px 30px 18px;border-radius:8px;box-shadow:0 2px 18px rgba(0,0,0,.13);overflow:hidden;color:#111}
.fact .filigrane{position:absolute;left:50%;top:55%;width:60%;transform:translate(-50%,-50%);opacity:.06;pointer-events:none}
.fact>*{position:relative}
.fact-tete{display:flex;gap:18px;align-items:flex-start;justify-content:space-between;flex-wrap:wrap}
.fact-marque{text-align:center}.fact-marque img{height:92px;width:auto;display:block;margin:0 auto 4px}
.fact-marque b{display:block;font-size:17px;letter-spacing:.5px}.fact-marque span{font-size:14px}
.fact-cadre{flex:1;min-width:270px;max-width:380px;border:2px solid #333;border-radius:10px;padding:8px 12px;font-size:14px;line-height:2}
.fact-cadre .ecrit{border-bottom:1px dotted #555;display:inline-block;min-width:150px;font-weight:bold;padding:0 4px}
.fact-ligne{display:flex;align-items:center;gap:12px;margin-top:4px}
.fact-badge{background:#333;color:#fff;font-weight:bold;font-size:18px;padding:2px 16px;border-radius:6px;letter-spacing:1px}
.fact-table{width:100%;border-collapse:collapse;margin-top:16px;box-shadow:none;background:transparent;font-size:14px;border:0;border-radius:0;overflow:visible}
.fact-table th{background:#333;color:#fff;padding:6px 8px;border:2px solid #333;font-size:12px;letter-spacing:.5px}
.fact-table td{border:1px solid #444;padding:5px 8px;height:25px}
.fact-table .num{text-align:right;white-space:nowrap}
.fact-table tfoot td{font-weight:bold;border:2px solid #333;background:#f1f1f1}
.fact-lettres{margin:14px 0 2px;font-size:14px;line-height:1.9}.fact-lettres .ecrit{border-bottom:1px dotted #555;font-weight:bold;padding:0 4px}
.fact-paiement{font-size:12.5px;margin:4px 0 0;color:#333}
.fact-sign{display:flex;flex-direction:column;align-items:flex-end;gap:6px;margin:18px 6px 56px;font-weight:bold;font-size:13px}
.fact-pied{border-top:1px solid #999;padding-top:6px;font-size:11px;text-align:center;color:#333}
.tampon-annule{position:absolute;top:42%;left:50%;transform:translate(-50%,-50%) rotate(-18deg);font-size:84px;font-weight:bold;color:rgba(198,40,40,.28);border:8px solid rgba(198,40,40,.28);padding:0 24px;border-radius:12px;z-index:2;pointer-events:none}
@media(max-width:640px){.fact{padding:14px}.fact-table{font-size:12px}.fact-cadre{max-width:none}
.bon{padding:16px}.bon-entete{flex-wrap:wrap}.bon-infos,.bon-sign{grid-template-columns:1fr}.bon-table{font-size:12px}}

/* Commandes : saisie et circuit */
.bloc-cmd fieldset{border:1px solid var(--bord);border-radius:var(--rayon);padding:14px 16px;margin:14px 0;background:var(--surface);box-shadow:var(--ombre)}
.bloc-cmd legend{font-weight:700;color:var(--vert-fonce);padding:0 8px;font-size:15px}
.grille{display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:12px}
.grille label{display:flex;flex-direction:column;font-size:12.5px;color:var(--texte-2);gap:4px}
.table-lignes select{width:100%}.table-lignes td{padding:6px}
.table-lignes input.l-qte{width:90px}.table-lignes input.l-prix{width:120px}
.table-lignes .num{text-align:right;white-space:nowrap}
@media(max-width:700px){
.table-lignes,.table-lignes tbody{display:block;overflow:visible;border:0;box-shadow:none;background:transparent}
.table-lignes thead{display:none}
.table-lignes tr.ligne-cmd{display:grid;grid-template-columns:1fr 1fr auto;gap:8px;align-items:center;border:1px solid #cfd8c8;border-radius:8px;padding:8px;margin-bottom:8px;background:var(--surface)}
.table-lignes td{display:block;padding:0;border:0}
.table-lignes td:first-child{grid-column:1/-1}
.table-lignes td.l-montant{grid-column:1/3;text-align:left}
.table-lignes input.l-qte,.table-lignes input.l-prix{width:100%}
}
.etapes{list-style:none;display:flex;gap:8px;padding:0;margin:8px 0 16px;flex-wrap:wrap}
.etapes li{flex:1 1 110px;background:var(--surface);border:1px solid var(--bord);border-radius:12px;padding:10px 12px;font-size:12.5px;display:flex;flex-direction:column;gap:4px;box-shadow:var(--ombre)}
.etapes .pastille{width:26px;height:26px;border-radius:50%;background:#cfd8c8;color:#fff;display:inline-flex;align-items:center;justify-content:center;font-size:12.5px;font-weight:bold}
.etapes li.fait{border-color:#a9d18e;background:#f3f9ee}.etapes li.fait .pastille{background:var(--vert)}
.etapes li.courant{border-color:#e8920c;background:#fffaf0;box-shadow:0 0 0 3px #f8e1b5}.etapes li.courant .pastille{background:#e8920c}
.etapes small{color:var(--texte-2)}
.circuit{max-width:820px;margin:0 auto 14px}
.panneau-actions{display:flex;flex-wrap:wrap;gap:10px;align-items:center;margin:6px 0 4px}
.panneau-actions form{margin:0}
.renvoi{display:flex;gap:6px;flex-wrap:wrap}.renvoi input{min-width:260px}
.attente{margin:0;color:#7a5200}
.alerte-circuit{background:#fdecec;padding:10px 14px;border-radius:8px;margin:0;border-left:4px solid var(--rouge)}
ul.docs{list-style:none;padding:0;margin:0 0 10px}ul.docs li{padding:5px 0}

/* Tableau de bord */
.entete-page{display:flex;flex-wrap:wrap;align-items:flex-end;gap:14px 24px;margin:4px 0 20px}
.entete-page h1{margin:0}
.entete-page p{margin:4px 0 0;color:var(--texte-2)}
.entete-page .actions{margin-left:auto;display:flex;flex-wrap:wrap;gap:8px}
.section-titre{font-size:12px;font-weight:700;text-transform:uppercase;letter-spacing:1px;color:var(--texte-3);margin:22px 0 -4px}
.liste-alertes{max-height:360px;overflow-y:auto;padding-right:4px}
.resume-alertes{display:flex;gap:8px;flex-wrap:wrap;margin:0 0 12px}
.legende-graph{font-size:12px;color:var(--texte-2);margin:-4px 0 6px}

/* ------------------------------------------------ Connexion */
body.login{background:linear-gradient(135deg,#eef5e8 0%,#dfead5 100%)}
body.login::before{opacity:.10;background-position:right -8% center;background-size:min(70vw,780px)}
body.login main{max-width:1040px}
.login-wrap{min-height:calc(100vh - 110px);display:flex;align-items:center;justify-content:center;padding:20px 0}
.login-boite{display:grid;grid-template-columns:1.05fr 1fr;width:100%;max-width:940px;background:var(--surface);border-radius:20px;overflow:hidden;box-shadow:0 20px 60px rgba(29,67,16,.22)}
.login-marque{position:relative;padding:44px 40px;color:#fff;background:linear-gradient(150deg,#2f6b14 0%,#1d4310 60%,#132e08 100%);display:flex;flex-direction:column;justify-content:space-between;gap:28px;overflow:hidden}
.login-marque::after{content:"";position:absolute;right:-90px;bottom:-90px;width:300px;height:300px;border-radius:50%;background:rgba(255,255,255,.06)}
.login-marque::before{content:"";position:absolute;right:40px;top:-60px;width:160px;height:160px;border-radius:50%;background:rgba(255,255,255,.05)}
.login-marque img{width:120px;background:#fff;border-radius:14px;padding:8px 10px}
.login-marque h2{color:#fff;font-size:28px;margin:18px 0 6px;line-height:1.2}
.login-marque p{color:#cfe3c0;margin:0;font-size:15px}
.login-marque ul{list-style:none;padding:0;margin:0;display:grid;gap:10px;font-size:14px;color:#e4f0db}
.login-marque li{display:flex;gap:10px;align-items:center}
.login-marque li span{width:30px;height:30px;border-radius:8px;background:rgba(255,255,255,.12);display:inline-flex;align-items:center;justify-content:center}
.login-card{padding:44px 40px 34px;display:flex;flex-direction:column;justify-content:center}
.login-card h1{font-size:24px;margin:0 0 4px}
.login-card .sous{color:var(--texte-2);font-size:14px;margin:0 0 24px}
.login-card form{display:flex;flex-direction:column;gap:16px;text-align:left}
.login-card input{padding:12px 13px;font-size:15px}
.login-card button{padding:13px;font-size:15.5px;margin-top:4px}
.champ-mdp{position:relative;display:block}
.champ-mdp input{width:100%;padding-right:46px}
.champ-mdp button{position:absolute;right:5px;top:50%;transform:translateY(-50%);background:transparent;color:var(--texte-2);box-shadow:none;padding:6px 8px;margin:0;font-size:16px}
.champ-mdp button:hover{background:var(--vert-clair);color:var(--vert-nuit)}
.login-card .aide{font-size:12.5px;color:var(--texte-3);margin:18px 0 0;text-align:center}
@media(max-width:820px){.login-boite{grid-template-columns:1fr}.login-marque{padding:28px 26px}.login-marque ul{display:none}.login-card{padding:30px 26px}}

/* ------------------------------------------------ Responsive */
@media(max-width:1000px){
main{padding:0 14px;margin-top:18px}
}
@media(max-width:600px){h1{font-size:22px}.cartes{grid-template-columns:1fr 1fr;gap:10px}
.carte{padding:12px;gap:10px;flex-direction:column;align-items:flex-start}.carte .ico{width:40px;height:40px;font-size:20px}.carte b{font-size:21px}.carte .fleche{display:none}
.rapport-carte{grid-column:1/-1}}

/* ------------------------------------------------ Impression */
@media print{.entete-app,.no-print,.flash,.flashes,.pied,#inactif{display:none!important}
body,body.avec-menu{background:#fff!important;padding:0!important}body::before{display:none!important}
main{max-width:none;margin:0;padding:0}
table,.table-wrap{box-shadow:none!important}
.bon{box-shadow:none;border-radius:0;padding:0;max-width:none}
.fact{box-shadow:none;border-radius:0;padding:0;max-width:none}
th,.bon-table tfoot td,.bon-entete,.fact-table th,.fact-badge{-webkit-print-color-adjust:exact;print-color-adjust:exact}
.bon-table tr{break-inside:avoid}}
@page{size:A4;margin:14mm}
@media(prefers-reduced-motion:reduce){*{animation:none!important;transition:none!important;scroll-behavior:auto!important}}
/* ------------------------------------------------ En-têtes de page, titres, états vides */
main>h1:first-of-type,.entete-page h1{display:flex;align-items:center;gap:14px}
main>h1:first-of-type::before,.entete-page h1::before{content:var(--ico-page,"📄");flex:none;width:48px;height:48px;border-radius:14px;display:inline-flex;align-items:center;justify-content:center;font-size:24px;
background:linear-gradient(135deg,var(--vert-clair),var(--surface));border:1px solid var(--bord);box-shadow:var(--ombre)}
main>h1:first-of-type{padding-bottom:16px;border-bottom:1px solid var(--bord);margin-bottom:22px}
main>h2,.deux-col>div:not(.panneau)>h2{display:flex;align-items:center;gap:10px}
main>h2::before,.deux-col>div:not(.panneau)>h2::before{content:"";width:4px;height:18px;border-radius:3px;background:linear-gradient(180deg,var(--or),var(--vert));flex:none}
form.card{border-top:3px solid var(--vert)}
tr:nth-child(2):last-child>td[colspan]{text-align:center;padding:34px 16px;color:var(--texte-3);font-style:italic;background:var(--surface)!important}
tr:nth-child(2):last-child>td[colspan]::before{content:"📭";display:block;font-size:30px;font-style:normal;margin-bottom:6px;opacity:.8}

/* ------------------------------------------------ Graphiques */
.graph{display:block;width:100%;height:auto}
.graph .g-grille{stroke:var(--g-grille)}
.graph .g-axe{fill:var(--g-texte);font-size:11.5px}
.graph .g-lib{fill:var(--texte-2);font-size:12px;font-weight:600}
.graph .g-val{fill:var(--g-valeur);font-size:12px;font-weight:700}
.graph .g-vide{fill:var(--texte-3);font-size:13px}
.graph .g-point{fill:var(--surface);stroke:var(--g-ligne);stroke-width:3}
.graph .g-barre{transition:opacity .15s}.graph .g-barre:hover{opacity:.8}
.graph .g-point:hover{r:7}
.resume-graph{display:flex;gap:18px;flex-wrap:wrap;margin:-2px 0 8px;font-size:12.5px;color:var(--texte-2)}
.resume-graph b{display:block;font-size:20px;color:var(--texte);font-variant-numeric:tabular-nums}

/* ------------------------------------------------ Bouton de thème */
.theme-btn{font-size:18px;background:transparent;border:0;box-shadow:none;cursor:pointer;padding:0}
.theme-btn:hover{background:var(--vert-clair)}
.theme-btn .sombre-ico{display:none}
html[data-theme=sombre] .theme-btn .clair-ico{display:none}
html[data-theme=sombre] .theme-btn .sombre-ico{display:inline}
.login-theme{position:fixed;top:14px;right:14px;z-index:5;background:var(--surface);border:1px solid var(--bord)}

/* ------------------------------------------------ Mode sombre */
html[data-theme=sombre]{color-scheme:dark;
--vert:#4caf2a;--vert-fonce:#5cc236;--vert-nuit:#bfe6a8;--vert-clair:#1f3417;--vert-pale:#18261a;--titre:#cdeeb8;
--lien:#8fd66a;--lien-survol:#b5ec95;
--bleu:#5b8def;--bleu-clair:#172440;--orange:#f0a032;--orange-clair:#33260f;--rouge:#ef5350;--rouge-clair:#3a1a1a;--or:#f2c14e;--or-clair:#3a2f10;
--fond:#0e140e;--surface:#172017;--surface-2:#1a241a;--survol:#213021;--champ:#111911;--ligne:#232f23;--piste:#253225;
--bord:#2a382a;--bord-fort:#3b4d3b;--texte:#e4ecdf;--texte-2:#a7b6a1;--texte-3:#7b8a76;
--verre:rgba(18,26,18,.86);--entete:linear-gradient(180deg,#24521a,#1b4212);
--g-grille:#263326;--g-texte:#8d9c88;--g-barre-1:#7fd64e;--g-barre-2:#3f8f1f;--g-ligne:#6f9dff;--g-valeur:#d6f0c4;
--ombre:0 1px 2px rgba(0,0,0,.4),0 2px 10px rgba(0,0,0,.3);--ombre-forte:0 8px 28px rgba(0,0,0,.5)}
html[data-theme=sombre] body::before{display:none}
html[data-theme=sombre] button.secondaire,html[data-theme=sombre] .btn.secondaire,html[data-theme=sombre] .btn-export{color:var(--lien);border-color:#3f8f1f}
html[data-theme=sombre] button.secondaire:hover,html[data-theme=sombre] .btn.secondaire:hover,html[data-theme=sombre] .btn-export:hover{background:#2b7313;color:#fff}
html[data-theme=sombre] .success{background:#16301a}html[data-theme=sombre] .danger{background:#361a1a}html[data-theme=sombre] .warning{background:#33290f}
html[data-theme=sombre] .flash.success{border-color:#24502a;color:#b8e8bd}
html[data-theme=sombre] .flash.danger{border-color:#5a2626;color:#f5bcbc}
html[data-theme=sombre] .flash.warning{border-color:#5a4615;color:#f5dc9a}
html[data-theme=sombre] .flash.info{border-color:#24396a;color:#bcd0fb}
html[data-theme=sombre] .badge{background:#2a352a;color:#cfd8cb}
html[data-theme=sombre] .b-conforme,html[data-theme=sombre] .b-disponible,html[data-theme=sombre] .b-validée,html[data-theme=sombre] .b-livrée{background:#1b3b20;color:#9be3a6}
html[data-theme=sombre] .b-quarantaine,html[data-theme=sombre] .b-rappelé,html[data-theme=sombre] .b-facturée{background:#3a2e0f;color:#f3cf7a}
html[data-theme=sombre] .b-périmé,html[data-theme=sombre] .b-annulée{background:#421c1c;color:#f6a9a9}
html[data-theme=sombre] .b-réservé,html[data-theme=sombre] .b-enregistrée,html[data-theme=sombre] .b-émise,html[data-theme=sombre] .b-transmise{background:#1a2a4a;color:#a9c4fb}
html[data-theme=sombre] .b-vendu,html[data-theme=sombre] .b-archivée,html[data-theme=sombre] .b-détruit{background:#2a2f33;color:#c3c9ce}
html[data-theme=sombre] .c-orange{--accent-clair:#3a2c10;background:#1d1a10}html[data-theme=sombre] .c-orange b{color:#f3b45a}
html[data-theme=sombre] .c-rouge{--accent-clair:#3e1c1c;background:#201414}html[data-theme=sombre] .c-rouge b{color:#ff7a77}
html[data-theme=sombre] .rapide{background:linear-gradient(180deg,#18281a,var(--surface));border-color:#2f4a2a}
html[data-theme=sombre] .etapes li.fait{background:#18281a;border-color:#2f5a25}
html[data-theme=sombre] .etapes li.courant{background:#2a2312;box-shadow:0 0 0 3px #4a3a15}
html[data-theme=sombre] .alerte-circuit{background:#361a1a}
html[data-theme=sombre] .mdp-box{background:#2a2412}html[data-theme=sombre] .mdp-box code{background:#111911;color:#f3cf7a}
html[data-theme=sombre] body.login{background:linear-gradient(135deg,#0e140e,#142014)}
html[data-theme=sombre] .attente{color:#f3cf7a}
html[data-theme=sombre] .indice.alerte{color:#ff8a87}
html[data-theme=sombre] details.profil summary{background:var(--surface)}
html[data-theme=sombre] .actions-bon small{color:var(--texte-2)}
/* ------------------------------------------------ Finition professionnelle */
.ic{width:18px;height:18px;flex:none;vertical-align:-3px;display:inline-block}
button .ic,.btn .ic,.btn-export .ic{width:16px;height:16px;vertical-align:-3px}
a .ic{margin-right:2px}
body:not(.login)::before{display:none}
body{font-size:14.5px}
/* Menu latéral : sobre, icônes au trait, rubrique active soulignée d'or */
/* Barre du haut : fil d'Ariane */
/* Titres de page : icône de rubrique dans un pavé teinté */
main>h1:first-of-type::before,.entete-page h1::before{content:"";background:var(--ico-page) center/22px no-repeat,var(--vert-clair);border:0;box-shadow:none;width:42px;height:42px;border-radius:11px}
main>h1:first-of-type{font-size:24px;padding-bottom:14px}
.entete-page h1{font-size:24px}
main>h2,.deux-col>div:not(.panneau)>h2{font-size:16px;font-weight:650}
main>h2::before,.deux-col>div:not(.panneau)>h2::before{display:none}
.panneau h2{display:flex;align-items:center;gap:8px;font-size:14.5px;font-weight:650}
.panneau h2 .ic{color:var(--vert)}
/* Tableaux : en-tête discret, lignes aérées */
th{background:var(--surface-2);color:var(--texte-2);font-size:11.5px;font-weight:650;text-transform:uppercase;letter-spacing:.06em;padding:11px 14px;border-bottom:1px solid var(--bord)}
td{padding:11px 14px}
main table:not(.fact-table):not(.bon-table) tr:nth-child(even) td{background:transparent}
.bon-table th{background:var(--vert-fonce);color:#fff;text-transform:none;letter-spacing:.3px;font-size:12.5px}
tr:nth-child(2):last-child>td[colspan]::before{content:"";display:block;width:40px;height:40px;margin:0 auto 8px;opacity:1;
background:url('data:image/svg+xml,%3Csvg xmlns=%22http://www.w3.org/2000/svg%22 viewBox=%220 0 24 24%22 fill=%22none%22 stroke=%22%2398a592%22 stroke-width=%221.6%22 stroke-linecap=%22round%22 stroke-linejoin=%22round%22%3E%3Cpath d=%22M22 12h-6l-2 3h-4l-2-3H2%22/%3E%3Cpath d=%22M5.5 5.1 2 12v6a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2v-6l-3.5-6.9A2 2 0 0 0 16.8 4H7.2a2 2 0 0 0-1.7 1.1z%22/%3E%3C/svg%3E') center/contain no-repeat}
tr:nth-child(2):last-child>td[colspan]{font-style:normal}
/* Boutons : aplats nets */
button,.btn{background:var(--vert-fonce);box-shadow:0 1px 2px rgba(20,40,10,.18)}
button:hover,.btn:hover{background:#1f5a0c}
button.secondaire,.btn.secondaire,.btn-export{box-shadow:none;border-color:var(--bord-fort);color:var(--texte)}
button.secondaire:hover,.btn.secondaire:hover,.btn-export:hover{background:var(--surface-2);color:var(--texte);border-color:var(--texte-3)}
.btn-export .ic{color:var(--vert)}
/* Champs de recherche avec loupe */
.filtres input.grand,input.recherche{padding-left:36px;background:var(--champ) url('data:image/svg+xml,%3Csvg xmlns=%22http://www.w3.org/2000/svg%22 viewBox=%220 0 24 24%22 fill=%22none%22 stroke=%22%2398a592%22 stroke-width=%222%22 stroke-linecap=%22round%22%3E%3Ccircle cx=%2211%22 cy=%2211%22 r=%227%22/%3E%3Cpath d=%22m21 21-4.3-4.3%22/%3E%3C/svg%3E') 11px center/16px no-repeat}
form.card{border-top:1px solid var(--bord)}
/* Cartes indicateurs : sans barre latérale, icône teintée */
.carte::before{display:none}
.carte{border-radius:12px;padding:18px}
.carte .ico{width:46px;height:46px;border-radius:12px;color:var(--accent)}
.carte .ico .ic{width:22px;height:22px}
.carte b{font-size:25px;letter-spacing:-.01em}
.carte .fleche{font-size:0}
.carte .fleche::after{content:"";display:block;width:16px;height:16px;background:currentColor;
-webkit-mask:url('data:image/svg+xml,%3Csvg xmlns=%22http://www.w3.org/2000/svg%22 viewBox=%220 0 24 24%22 fill=%22none%22 stroke=%22black%22 stroke-width=%222.2%22 stroke-linecap=%22round%22 stroke-linejoin=%22round%22%3E%3Cpath d=%22m9 18 6-6-6-6%22/%3E%3C/svg%3E') center/contain no-repeat;
mask:url('data:image/svg+xml,%3Csvg xmlns=%22http://www.w3.org/2000/svg%22 viewBox=%220 0 24 24%22 fill=%22none%22 stroke=%22black%22 stroke-width=%222.2%22 stroke-linecap=%22round%22 stroke-linejoin=%22round%22%3E%3Cpath d=%22m9 18 6-6-6-6%22/%3E%3C/svg%3E') center/contain no-repeat}
.c-orange,.c-rouge{background:var(--surface)}
.c-orange{border-color:#f1d49b}.c-rouge{border-color:#f0bcbc}
a.carte:hover{transform:translateY(-1px)}
.rapport-carte b{display:flex;align-items:center;gap:8px}
.rapport-carte b .ic{color:var(--vert);width:20px;height:20px}
.section-titre{margin:26px 0 -2px}
@media(min-width:1001px){.entete-page~.cartes{grid-template-columns:repeat(3,1fr)}}
/* Badges avec pastille de couleur */
.badge::before{content:"";width:6px;height:6px;border-radius:50%;background:currentColor;opacity:.85}
.etapes .pastille .ic{width:14px;height:14px}
/* Connexion */
.login-marque li span{color:#d9ecc9}
.login-marque li span .ic{width:16px;height:16px}
.champ-mdp button{font-size:0;display:inline-flex}
.champ-mdp button .cacher,.champ-mdp button.visible .voir{display:none}
.champ-mdp button.visible .cacher{display:inline}
.login-theme .ic{width:18px;height:18px}
/* Liens de retour et d'action */
p>a:only-child{display:inline-flex;align-items:center;gap:6px;font-weight:600;text-decoration:none}
p>a:only-child:hover{text-decoration:underline}
html[data-theme=sombre] main>h1:first-of-type::before,html[data-theme=sombre] .entete-page h1::before{background:var(--ico-page-sombre) center/22px no-repeat,var(--vert-clair)}
html[data-theme=sombre] th{background:#1b261b}
html[data-theme=sombre] .c-orange{border-color:#5a4615}html[data-theme=sombre] .c-rouge{border-color:#5a2626}
html[data-theme=sombre] button,html[data-theme=sombre] .btn{background:#2f7d15}
html[data-theme=sombre] button:hover,html[data-theme=sombre] .btn:hover{background:#3a9419}
html[data-theme=sombre] button.secondaire,html[data-theme=sombre] .btn.secondaire,html[data-theme=sombre] .btn-export{background:transparent;color:var(--texte);border-color:var(--bord-fort)}
html[data-theme=sombre] button.danger{background:#b3261e}
html[data-theme=sombre] .theme-btn,html[data-theme=sombre] .flash .fermer,html[data-theme=sombre] .champ-mdp button,html[data-theme=sombre] button.burger{background:transparent}

@media print{:root,html[data-theme=sombre]{color-scheme:light;--surface:#fff;--surface-2:#fff;--texte:#18230f;--texte-2:#56644f;--titre:#173d0b;--bord:#dde6d6;--ligne:#ebf0e7;
--entete:#2b7313;--g-grille:#e1e9db;--g-texte:#6b7865;--g-valeur:#173d0b}}
</style></head>
<body class="{% if session.user %}avec-menu {% endif %}{% block bodyclass %}{% endblock %}">
{% macro lien(url, actif, ico, texte, nb=0) %}<a href="{{ url }}"{% if actif %} class="actif" aria-current="page"{% endif %}><span class="i">{{ ic(ico) }}</span><span>{{ texte }}</span>{% if nb %}<span class="pastille-nb">{{ nb }}</span>{% endif %}</a>{% endmacro %}
{% if session.user %}{% set r = session.user.role %}{% set ep = request.endpoint or '' %}
{% macro groupe(titre, ico, actif) %}<div class="groupe{% if actif %} actif{% endif %}"><button type="button" class="groupe-titre" aria-expanded="false">{{ ic(ico) }}<span>{{ titre }}</span><svg class="ic fl" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m6 9 6 6 6-6"/></svg></button><div class="deroulant">{{ caller() }}</div></div>{% endmacro %}
<header class="entete-app" id="entete">
<div class="entete-barre">
<a class="brand" href="{{ url_for('index') }}"><img src="{{ url_for('static', filename='logo.png') }}" alt="ISRA"><span><b>UPVac</b><small>Gestion des vaccins · ISRA</small></span></a>
<nav class="nav-principale" id="menu" aria-label="Menu principal">
{% call groupe('Pilotage', 'accueil', ep == 'index' or ep.startswith('rapport')) %}
{{ lien(url_for('index'), ep == 'index', 'accueil', 'Tableau de bord') }}
{% if droits.rapports_voir %}{{ lien(url_for('rapports'), ep.startswith('rapport'), 'graphique', 'Rapports') }}{% endif %}
{% endcall %}
{% call groupe('Stock', 'colis', ep.startswith('lot') or ep.startswith('vaccin') or ep.startswith('mouvement') or ep.startswith('inventaire') or ep.startswith('article')) %}
{{ lien(url_for('lots'), ep.startswith('lot') or ep.startswith('vaccin'), 'seringue', 'Vaccins & lots') }}
{% if droits.mouvements_voir %}{{ lien(url_for('mouvements'), ep.startswith('mouvement'), 'echange', 'Entrées / sorties') }}{% endif %}
{% if droits.inventaire_voir %}{{ lien(url_for('inventaires'), ep.startswith('inventaire'), 'inventaire', 'Inventaire') }}{% endif %}
{% if droits.articles_voir %}{{ lien(url_for('articles'), ep.startswith('article'), 'outils', 'Articles') }}{% endif %}
{% endcall %}
{% if droits.clients_voir or droits.commandes_voir or droits.ventes_voir or droits.ventes_saisir or droits.factures_voir %}
{% call groupe('Vente', 'panier', ep.startswith('caisse') or ep.startswith('commande') or ep.startswith('vente') or ep.startswith('facture') or ep.startswith('client')) %}
{% if droits.ventes_saisir %}{{ lien(url_for('caisse'), ep.startswith('caisse'), 'panier', 'Caisse') }}{% endif %}
{% if droits.commandes_voir %}{{ lien(url_for('commandes'), ep.startswith('commande'), 'recu', 'Commandes') }}{% endif %}
{% if droits.ventes_voir %}{{ lien(url_for('ventes'), ep.startswith('vente'), 'billets', 'Ventes') }}{% endif %}
{% if droits.factures_voir %}{{ lien(url_for('factures'), ep.startswith('facture'), 'fichier', 'Factures') }}{% endif %}
{% if droits.clients_voir %}{{ lien(url_for('clients'), ep.startswith('client'), 'utilisateurs', 'Clients') }}{% endif %}
{% endcall %}{% endif %}
<div class="groupe{% if ep.startswith('message') %} actif{% endif %}"><a class="groupe-titre" href="{{ url_for('messages') }}">{{ ic('mail') }}<span>Messagerie</span>{% if nb_non_lus %}<span class="pastille-nb">{{ nb_non_lus }}</span>{% endif %}</a></div>
{% if droits.referentiels_voir or droits.utilisateurs or droits.audit or droits.reinitialiser %}
{% call groupe('Administration', 'bouclier', ep.startswith('referentiel') or ep.startswith('ref_') or ep.startswith('utilisateur') or ep.startswith('email_') or ep == 'journal' or ep.startswith('donnees')) %}
{% if droits.referentiels_voir %}{{ lien(url_for('referentiels'), ep.startswith('referentiel') or ep.startswith('ref_'), 'dossier', 'Référentiels') }}{% endif %}
{% if droits.utilisateurs %}{{ lien(url_for('utilisateurs'), ep.startswith('utilisateur') or ep.startswith('email_'), 'bouclier', 'Utilisateurs') }}{% endif %}
{% if droits.audit %}{{ lien(url_for('journal'), ep == 'journal', 'historique', 'Audit') }}{% endif %}
{% if droits.reinitialiser %}{{ lien(url_for('donnees_essai'), ep.startswith('donnees'), 'fiole', "Données d'essai") }}{% endif %}
{% endcall %}{% endif %}
</nav>
<div class="outils">
<span class="jour">{{ ic('calendrier') }} {{ jour_fr }}</span>
<button type="button" class="icone-btn theme-btn" onclick="basculerTheme()" title="Mode clair / sombre" aria-label="Basculer le mode clair ou sombre"><span class="clair-ico">{{ ic('lune') }}</span><span class="sombre-ico">{{ ic('soleil') }}</span></button>
<a class="icone-btn" href="{{ url_for('messages') }}" title="Messagerie" aria-label="Messagerie{% if nb_non_lus %}, {{ nb_non_lus }} non lu(s){% endif %}">{{ ic('mail') }}{% if nb_non_lus %}<span class="nb">{{ nb_non_lus }}</span>{% endif %}</a>
<details class="profil"><summary><span class="avatar">{{ session.user.username[:1] }}</span><span class="qui"><b>{{ session.user.username }}</b><small>{{ r|role_lib }}</small></span><span class="chevron">{{ ic('chevron-bas') }}</span></summary>
<div class="menu">
<a href="{{ url_for('mon_compte') }}">{{ ic('utilisateur') }} Mon compte</a>
<a href="{{ url_for('mot_de_passe') }}">{{ ic('cle') }} Mot de passe</a>
<hr><a class="sortie" href="{{ url_for('logout') }}">{{ ic('sortie') }} Déconnexion</a>
</div></details>
<button type="button" class="burger" aria-label="Ouvrir le menu" aria-controls="menu" aria-expanded="false"
onclick="var o=document.getElementById('entete').classList.toggle('ouvert');this.setAttribute('aria-expanded',o)">{{ ic('menu') }}</button>
</div></div></header>{% else %}<button type="button" class="icone-btn theme-btn login-theme" onclick="basculerTheme()" title="Mode clair / sombre" aria-label="Basculer le mode clair ou sombre"><span class="clair-ico">{{ ic('lune') }}</span><span class="sombre-ico">{{ ic('soleil') }}</span></button>{% endif %}
<main style="{{ style_page }}">{% with msgs = get_flashed_messages(with_categories=true) %}{% if msgs %}<div class="flashes no-print" role="status">{% for cat, m in msgs %}
<div class="flash {{ cat }}"><span>{{ m }}</span><button type="button" class="fermer" aria-label="Fermer" onclick="this.parentNode.remove()">×</button></div>{% endfor %}</div>{% endif %}{% endwith %}
{% block content %}{% endblock %}</main>
<footer class="pied">UPVac · ISRA — Gestion de stock des vaccins · © {{ annee }}</footer>
<script>
(function(){
  function norm(s){return s.normalize('NFD').replace(/[\\u0300-\\u036f]/g,'').toLowerCase();}
  document.querySelectorAll('input[data-filtre]').forEach(function(inp){
    var table=document.getElementById(inp.dataset.filtre);
    if(!table){return;}
    inp.addEventListener('input',function(){
      var q=norm(inp.value.trim());
      table.querySelectorAll('tr').forEach(function(tr){
        if(!tr.querySelector('td')){return;}
        tr.style.display=norm(tr.textContent).indexOf(q)>-1?'':'none';
      });
    });
  });
  // tableaux larges : défilement horizontal propre au lieu de déborder de la page
  document.querySelectorAll('main table').forEach(function(t){
    if(t.closest('.fact,.bon,.table-wrap')||t.classList.contains('table-lignes')){return;}
    var w=document.createElement('div'); w.className='table-wrap';
    t.parentNode.insertBefore(w,t); w.appendChild(t);
  });
  // les messages de succès disparaissent seuls après quelques secondes
  document.querySelectorAll('.flashes .flash.success').forEach(function(f){
    setTimeout(function(){f.style.transition='opacity .4s';f.style.opacity='0';setTimeout(function(){f.remove();},450);},6000);
  });
  // fermeture du menu mobile et du menu profil
  // menus déroulants de la barre du haut : ouverture au clic (souris ou écran tactile)
  var groupes=document.querySelectorAll('.nav-principale .groupe');
  function fermerTout(sauf){groupes.forEach(function(g){if(g!==sauf){g.classList.remove('ouvert');var b=g.querySelector('button.groupe-titre');if(b){b.setAttribute('aria-expanded','false');}}});}
  document.querySelectorAll('.nav-principale button.groupe-titre').forEach(function(b){
    b.addEventListener('click',function(e){e.stopPropagation();var g=b.parentNode;fermerTout(g);
      var o=g.classList.toggle('ouvert');b.setAttribute('aria-expanded',o);});
  });
  document.addEventListener('keydown',function(e){
    if(e.key==='Escape'){fermerTout(null);var t=document.getElementById('entete');if(t){t.classList.remove('ouvert');}
      document.querySelectorAll('details.profil[open]').forEach(function(d){d.removeAttribute('open');});}
  });
  document.addEventListener('click',function(e){
    if(!e.target.closest('.nav-principale')){fermerTout(null);}
    document.querySelectorAll('details.profil[open]').forEach(function(d){if(!d.contains(e.target)){d.removeAttribute('open');}});
  });
  window.basculerTheme=function(){
    var h=document.documentElement, s=h.getAttribute('data-theme')==='sombre'?'clair':'sombre';
    h.setAttribute('data-theme',s); try{localStorage.setItem('upvac_theme',s);}catch(e){}
  };
})();
</script>
{% if session.user %}
<div id="inactif" style="display:none;position:fixed;left:50%;bottom:24px;transform:translateX(-50%);z-index:9999;background:#8a1c1c;color:#fff;padding:12px 18px;border-radius:10px;box-shadow:0 8px 28px rgba(0,0,0,.35);font-size:14px;max-width:90%;text-align:center">
Sans activité, vous allez être déconnecté dans <b id="inactif-sec">60</b> s. Bougez la souris ou touchez l'écran pour rester connecté.</div>
<script>
(function(){
  var MAX={{ delai_inactivite }}*60000, AVERT=60000, CLE='gestvac_activite', derniere=Date.now(), dernierPing=Date.now();
  var boite=document.getElementById('inactif'), sec=document.getElementById('inactif-sec');
  function lire(){try{return parseInt(localStorage.getItem(CLE)||'0',10);}catch(e){return 0;}}
  function noter(){
    var t=Date.now(); if(t-derniere<1000){return;}
    derniere=t; try{localStorage.setItem(CLE,String(t));}catch(e){}
  }
  ['mousemove','mousedown','keydown','scroll','touchstart','click'].forEach(function(e){
    document.addEventListener(e,noter,{passive:true,capture:true});
  });
  try{localStorage.setItem(CLE,String(derniere));}catch(e){}
  setInterval(function(){
    var t=Date.now(), act=Math.max(derniere,lire()), inactif=t-act;
    if(inactif>=MAX){window.location.href="{{ url_for('logout') }}?expire=1";return;}
    if(inactif>=MAX-AVERT){sec.textContent=Math.ceil((MAX-inactif)/1000);boite.style.display='block';}
    else{boite.style.display='none';}
    // tant que l'utilisateur est actif, on prolonge la session côté serveur toutes les 4 minutes
    if(inactif<MAX-AVERT && t-dernierPing>240000){
      dernierPing=t; fetch("{{ url_for('session_ping') }}",{credentials:'same-origin'}).catch(function(){});
    }
  },1000);
})();
</script>
{% endif %}
</body></html>"""

LOGIN = """{% extends 'base.html' %}{% block bodyclass %}login{% endblock %}{% block content %}
<div class="login-wrap"><div class="login-boite">
<div class="login-marque">
<div><img src="{{ url_for('static', filename='logo.png') }}" alt="Logo ISRA - UPVac">
<h2>GESVac</h2><p>Plateforme de gestion des vaccins de l'UPVac · ISRA</p></div>
<ul>
<li><span>{{ ic('seringue') }}</span> Stock des lots et alertes de péremption</li>
<li><span>{{ ic('recu') }}</span> Commandes, ventes et facturation</li>
<li><span>{{ ic('graphique') }}</span> Rapports mensuels et annuels</li>
</ul>
</div>
<div class="login-card">
<h1>Connexion</h1>
<p class="sous">Gestion de stock · Commande · Vente</p>
<form method="post">
<label>Utilisateur<input name="username" required autofocus autocomplete="username" placeholder="Votre identifiant"></label>
<label>Mot de passe<span class="champ-mdp"><input name="password" id="mdp" type="password" required autocomplete="current-password" placeholder="••••••••">
<button type="button" aria-label="Afficher le mot de passe" title="Afficher / masquer" onclick="var i=document.getElementById('mdp');var v=i.type==='password';i.type=v?'text':'password';this.classList.toggle('visible',v);this.setAttribute('aria-label',v?'Masquer le mot de passe':'Afficher le mot de passe')"><span class="voir">{{ ic('oeil') }}</span><span class="cacher">{{ ic('oeil-barre') }}</span></button></span></label>
<button>Se connecter</button></form>
<p class="aide">Mot de passe oublié ? Contactez l'administrateur de la plateforme.</p>
</div></div></div>
{% endblock %}"""

INDEX = """{% extends 'base.html' %}{% block content %}
<div class="entete-page">
<div><h1>Tableau de bord</h1><p>Bonjour <b>{{ session.user.username }}</b>, voici la situation du stock et de l'activité.</p></div>
<div class="actions no-print">
{% if droits.ventes_saisir %}<a class="btn" href="{{ url_for('caisse') }}">{{ ic('panier') }} Nouvelle vente</a>{% endif %}
{% if droits.commandes_saisir %}<a class="btn secondaire" href="{{ url_for('commande_nouvelle') }}">{{ ic('recu') }} Nouvelle commande</a>{% endif %}
{% if peut_gerer %}<a class="btn secondaire" href="{{ url_for('lots') }}">{{ ic('colis') }} Réception de lot</a>{% endif %}
{% if droits.rapports_voir %}<a class="btn secondaire" href="{{ url_for('rapports') }}">{{ ic('graphique') }} Rapports</a>{% endif %}
</div></div>

<div class="section-titre">Stock</div>
<div class="cartes">
<a class="carte c-vert" href="{{ url_for('lots', stock=1) }}"><span class="ico">{{ ic('seringue') }}</span><div><b>{{ stats.doses|nombre }}</b><small>Doses vendables en stock</small></div><span class="fleche">›</span></a>
<a class="carte c-bleu" href="{{ url_for('lots', stock=1) }}"><span class="ico">{{ ic('colis') }}</span><div><b>{{ stats.lots }}</b><small>Lots en stock · {{ stats.nb_vaccins }} vaccin(s) au catalogue</small></div><span class="fleche">›</span></a>
<a class="carte {{ 'c-rouge' if stats.perimes else 'c-vert' }}" href="{{ url_for('lots', delai='perimes', stock=1) }}"><span class="ico">{{ ic('interdit') }}</span><div><b>{{ stats.perimes }}</b><small>Lot(s) périmé(s) avec stock</small></div><span class="fleche">›</span></a>
<a class="carte {{ 'c-orange' if stats.proches else 'c-vert' }}" href="{{ url_for('lots', delai='30', stock=1) }}"><span class="ico">{{ ic('sablier') }}</span><div><b>{{ stats.proches }}</b><small>Lot(s) expirant sous 30 jours</small></div><span class="fleche">›</span></a>
<a class="carte {{ 'c-orange' if stats.bas else 'c-vert' }}" href="#stock-vaccins"><span class="ico">{{ ic('baisse') }}</span><div><b>{{ stats.bas }}</b><small>Vaccin(s) sous le seuil minimal</small></div><span class="fleche">›</span></a>
{% if droits.articles_voir %}<a class="carte {{ 'c-orange' if stats.art_bas else 'c-vert' }}" href="{{ url_for('articles', etat='bas') }}"><span class="ico">{{ ic('outils') }}</span><div><b>{{ stats.art_bas }}</b><small>Article(s) sous le seuil minimal</small></div><span class="fleche">›</span></a>{% endif %}
</div>

<div class="section-titre">Activité</div>
<div class="cartes">
<a class="carte {{ 'c-rouge' if stats.alertes else 'c-vert' }}" href="#alertes"><span class="ico">{{ ic('cloche') }}</span><div><b>{{ stats.alertes }}</b><small>Alerte(s) en cours</small></div><span class="fleche">›</span></a>
{% if droits.commandes_voir %}<a class="carte {{ 'c-orange' if stats.commandes else 'c-bleu' }}" href="{{ url_for('commandes', a_traiter=1) }}"><span class="ico">{{ ic('recu') }}</span><div><b>{{ stats.commandes }}</b><small>{{ stats.commandes_libelle }}</small></div><span class="fleche">›</span></a>{% endif %}
{% if droits.ventes_voir %}<a class="carte c-bleu" href="{{ url_for('ventes', du=stats.debut_mois) }}"><span class="ico">{{ ic('panier') }}</span><div><b>{{ stats.ventes }}</b><small>Vente(s) ce mois · {{ stats.montant }} {{ devise }}</small></div><span class="fleche">›</span></a>
<a class="carte {{ 'c-orange' if stats.nb_retard else 'c-bleu' }}" href="{{ url_for('ventes', mode='terme', statut='impayees') }}"><span class="ico">{{ ic('carte') }}</span><div><b>{{ stats.a_encaisser }}</b><small>{{ devise }} à encaisser (ventes à terme){% if stats.nb_retard %} · {{ stats.nb_retard }} en retard{% endif %}</small></div><span class="fleche">›</span></a>{% endif %}
<a class="carte {{ 'c-orange' if stats.non_lus else 'c-bleu' }}" href="{{ url_for('messages') }}"><span class="ico">{{ ic('mail') }}</span><div><b>{{ stats.non_lus }}</b><small>Message(s) non lu(s)</small></div><span class="fleche">›</span></a>
</div>

<div class="panneau" id="alertes" style="scroll-margin-top:80px">
<h2>{{ ic('cloche') }} Alertes</h2>
{% set nb_danger = alertes|selectattr(0, 'equalto', 'danger')|list|length %}
{% if alertes %}<div class="resume-alertes">
{% if nb_danger %}<span class="badge b-périmé">{{ nb_danger }} critique(s)</span>{% endif %}
{% if alertes|length - nb_danger %}<span class="badge b-quarantaine">{{ alertes|length - nb_danger }} à surveiller</span>{% endif %}
</div>{% endif %}
<div class="liste-alertes">
{% for niveau, texte in alertes|sort(attribute=0) %}<div class="flash {{ niveau }}"><span>{{ texte }}</span></div>
{% else %}<div class="flash success"><span>Aucune alerte : tout est en ordre.</span></div>{% endfor %}
</div></div>

<div class="deux-col egal" style="margin-top:22px">
<div class="panneau"><h2>{{ ic('hausse') }} Évolution du stock</h2><p class="legende-graph">Doses en stock en fin de mois, 6 derniers mois</p>
<div class="resume-graph"><span><b>{{ resume_graph.stock_fin }}</b>doses fin de mois</span>
{% if resume_graph.stock_var %}<span><b style="color:{{ 'var(--vert)' if resume_graph.stock_var > 0 else 'var(--rouge)' }}">{{ '▲' if resume_graph.stock_var > 0 else '▼' }} {{ resume_graph.stock_var|abs|nombre }}</b>sur le dernier mois</span>{% endif %}</div>
{{ graphique_stock }}</div>
{% if droits.ventes_voir %}<div class="panneau"><h2>{{ ic('graphique') }} Doses vendues par mois</h2><p class="legende-graph">Quantités vendues, 6 derniers mois</p>
<div class="resume-graph"><span><b>{{ resume_graph.ventes_total }}</b>doses sur 6 mois</span><span><b>{{ resume_graph.ventes_moy }}</b>en moyenne / mois</span></div>
{{ graphique_ventes }}</div>{% endif %}
</div>

<div class="deux-col">
<div id="stock-vaccins" style="scroll-margin-top:80px"><h2>Stock vendable par vaccin</h2>
<table><tr><th>Vaccin</th><th class="num">Stock / seuil</th><th>Niveau</th><th>État</th></tr>
{% for v in vaccins %}<tr><td><b>{{ v.nom }}</b></td><td class="num">{{ v.total|nombre }} / {{ v.seuil|nombre }}</td>
<td><div class="barre" title="{{ v.pct }} % du seuil minimal"><div class="rempli {{ 'bas' if v.bas else 'ok' }}" style="width:{{ v.pct }}%"></div></div></td>
<td>{% if v.bas %}<span class="badge b-périmé">Stock bas</span>{% else %}<span class="badge b-conforme">OK</span>{% endif %}</td></tr>
{% else %}<tr><td colspan="4">Aucun vaccin au catalogue.</td></tr>{% endfor %}</table></div>

<div><h2>Prochaines péremptions</h2>
<table><tr><th>Vaccin / lot</th><th>Date</th><th>Reste</th></tr>
{% for p in prochaines %}<tr><td><b>{{ p.vaccin }}</b><br><small>Lot {{ p.lot }} · {{ p.stock|nombre }} en stock</small></td>
<td>{{ p.date|date_fr }}</td>
<td><span class="badge {{ 'b-périmé' if p.niveau == 'danger' else 'b-quarantaine' if p.niveau == 'warning' else 'b-conforme' }}">{{ p.jours }} j</span></td></tr>
{% else %}<tr><td colspan="3">Aucun lot en stock.</td></tr>{% endfor %}</table></div>
</div>
{% endblock %}"""

VACCINS = """{% extends 'base.html' %}{% block content %}
<h1>Catalogue des vaccins</h1>
{% if droits.vaccins_gerer %}<form class="card" method="post">
<label>Nom<input name="nom" required></label>
<label>Type<select name="type"><option>viral</option><option>bactérien</option>
<option>vivant atténué</option><option>inactivé</option></select></label>
<label>Espèce cible<input name="espece"></label>
<label>Fabricant<input name="fabricant"></label>
<label>Doses / flacon<input name="doses" type="number" min="1" value="1"></label>
<label>Temp. min (°C)<input name="temp_min" type="number" step="0.1" value="2"></label>
<label>Temp. max (°C)<input name="temp_max" type="number" step="0.1" value="8"></label>
<label>Seuil minimal<input name="seuil_min" type="number" min="0" value="0"></label>
<label>Prix unitaire ({{ devise }})<input name="prix_unitaire" type="text" inputmode="decimal" value="0"></label>
<button>Ajouter</button></form>{% endif %}
<h2>Liste</h2><input class="recherche" data-filtre="t-vaccins" placeholder="Rechercher un vaccin (nom, espèce, fabricant)…">
<p class="compte">{% if archives %}<a href="{{ url_for('vaccins') }}">Masquer les vaccins archivés</a>{% else %}<a href="{{ url_for('vaccins', archives=1) }}">Afficher les vaccins archivés</a>{% endif %}</p>
<table id="t-vaccins"><tr><th>Nom</th><th>Type</th><th>Espèce</th><th>Fabricant</th><th>Doses/flacon</th>
<th>Prix unitaire</th><th>Conservation</th><th>Seuil</th><th>Stock</th><th>Vendable</th><th>Actions</th></tr>
{% for v in vaccins %}<tr><td><a href="{{ url_for('vaccin_detail', vid=v.id) }}">{{ v.nom }}</a>{% if not v.actif %} <span class="badge b-quarantaine">Archivé</span>{% endif %}</td><td>{{ v.type }}</td><td>{{ v.espece or '' }}</td><td>{{ v.fabricant or '' }}</td>
<td>{{ v.doses_par_flacon }}</td><td>{{ v.prix_unitaire|nombre if v.prix_unitaire else '—' }}</td><td>{{ v.temp_min }} à {{ v.temp_max }} °C</td><td>{{ v.seuil_min }}</td><td>{{ v.stock_total }}</td><td>{{ v.vendable }}</td>
<td>{% if droits.vaccins_gerer %}{% if not v.actif %}
<form method="post" action="{{ url_for('vaccin_archiver', vid=v.id) }}" class="en-ligne"><button class="petit">Restaurer</button></form>
{% elif v.stock_total == 0 %}
<form method="post" action="{{ url_for('vaccin_archiver', vid=v.id) }}" class="en-ligne"
onsubmit='return confirm({{ ("Archiver « " ~ v.nom ~ " » ? Il disparaîtra des listes et des alertes (restaurable).")|tojson }})'><button class="petit">Archiver</button></form>
{% endif %}{% endif %}
{% if droits.supprimer %}{% if v.nb_ventes == 0 %}
<form method="post" action="{{ url_for('vaccin_supprimer', vid=v.id) }}" class="en-ligne"
onsubmit='return confirm({{ ("Supprimer définitivement « " ~ v.nom ~ " » ?" ~ ((" Seront aussi supprimés : " ~ v.nb_lots ~ " lot(s) et tous leurs mouvements.") if v.nb_lots else "") ~ " Action irréversible.")|tojson }})'><button class="petit danger">Supprimer</button></form>
{% else %}<small>Déjà vendu</small>{% endif %}{% endif %}</td></tr>
{% else %}<tr><td colspan="11">Aucun vaccin.</td></tr>{% endfor %}
</table>{% endblock %}"""

LOTS = """{% extends 'base.html' %}{% block content %}
<h1>Vaccin</h1>
{% if droits.vaccins_voir %}<p><a href="{{ url_for('vaccins') }}">{{ ic('livre') }} Catalogue des vaccins et prix unitaires</a></p>{% endif %}
{% if peut_gerer %}<form class="card" method="post" enctype="multipart/form-data">
<label>Nom du vaccin<input name="vaccin_nom" id="lot-vaccin" list="liste-vaccins" required maxlength="120" autocomplete="off" placeholder="Taper ou choisir le vaccin"></label>
<datalist id="liste-vaccins">{% for v in vaccins %}<option value="{{ v.nom }}">{% endfor %}</datalist>
<label>N° de lot<input name="numero_lot" required maxlength="60"></label>
<label>Quantité reçue<input name="quantite" type="number" min="1" required></label>
<label>Provenance<select name="provenance" required><option value="">— Choisir —</option>{% for x in fournisseurs %}<option value="{{ x.nom }}">{{ x.nom }}</option>{% endfor %}</select></label>
<label>Emplacement<select name="emplacement_id" required><option value="">— Choisir —</option>{% for x in emplacements %}<option value="{{ x.id }}">{{ x.nom }}</option>{% endfor %}</select></label>
<label>Date de fabrication<input name="date_fabrication" type="date" required></label>
<label>Date de péremption<input name="date_peremption" type="date" required></label>
<label>Prix unitaire ({{ devise }})<input name="prix_unitaire" id="lot-prix" type="text" inputmode="decimal" placeholder="Rempli automatiquement"></label>
<div id="lot-nouveau" style="display:none">
<label>Nouveau vaccin : type<select name="type"><option value="">— Choisir —</option>{% for t in types_vaccin %}<option>{{ t }}</option>{% endfor %}</select></label>
<label>Seuil minimal d'alerte<input name="seuil_min" type="number" min="0" value="0"></label></div>
<label>Fiche de fabrication (facultatif)<input type="file" name="fiche_fichier" accept=".pdf,.doc,.docx,.xls,.xlsx,.png,.jpg,.jpeg"></label>
<label>Bon de livraison (facultatif)<input type="file" name="bl_fichier" accept=".pdf,.doc,.docx,.xls,.xlsx,.png,.jpg,.jpeg"></label>
<button>Enregistrer la réception</button></form>
<script>
(function(){
  var cat={{ catalogue_js|tojson }}, nom=document.getElementById('lot-vaccin'), prix=document.getElementById('lot-prix'),
      nouveau=document.getElementById('lot-nouveau'), touche=false;
  prix.addEventListener('input',function(){touche=true;});
  function maj(){
    var v=cat[nom.value.trim().toLowerCase()];
    nouveau.style.display=(!v&&nom.value.trim())?'contents':'none';
    if(v&&!touche){prix.value=v.prix?String(v.prix).replace('.',','):'';}
  }
  nom.addEventListener('input',maj); nom.addEventListener('change',maj); maj();
})();
</script>{% endif %}
<h2>Stock par lot (tri : péremption la plus proche)</h2>
<form class="filtres" method="get" action="{{ url_for('lots') }}">
<input class="grand" name="q" value="{{ flt.q }}" placeholder="Lot, vaccin, emplacement, provenance…">
<select name="vaccin_id"><option value="">Tous les vaccins</option>{% for v in vaccins_tous %}<option value="{{ v.id }}" {% if flt.vaccin_id == v.id|string %}selected{% endif %}>{{ v.nom }}</option>{% endfor %}</select>
<select name="statut"><option value="">Tous les statuts</option>{% for s in STATUTS_LOT %}<option {% if flt.statut == s %}selected{% endif %}>{{ s }}</option>{% endfor %}</select>
<select name="delai"><option value="">Toutes péremptions</option>
<option value="perimes" {% if flt.delai == 'perimes' %}selected{% endif %}>Déjà périmés</option>
<option value="30" {% if flt.delai == '30' %}selected{% endif %}>Expirent sous 30 j</option>
<option value="60" {% if flt.delai == '60' %}selected{% endif %}>Expirent sous 60 j</option>
<option value="90" {% if flt.delai == '90' %}selected{% endif %}>Expirent sous 90 j</option></select>
<label>Péremption du<input type="date" name="du" value="{{ flt.du }}"></label>
<label>au<input type="date" name="au" value="{{ flt.au }}"></label>
<label class="case"><input type="checkbox" name="stock" value="1" {% if flt.stock == '1' %}checked{% endif %}> En stock seulement</label>
<button>Filtrer</button><a class="lien-reset" href="{{ url_for('lots') }}">Réinitialiser</a></form>
<p class="compte">{{ lots|length }} lot(s){% if fq %} · filtres actifs{% endif %}
&nbsp;<a class="btn-export" href="{{ url_for('export_stock', **fq) }}">{{ ic('telecharger') }} Exporter en Excel</a></p>
<table><tr><th>Nom du vaccin</th><th>N° lot</th><th>Quantité reçue</th><th>Disponible</th><th>Provenance</th><th>Fabrication</th><th>Péremption</th><th>Jours</th>
<th>Emplacement</th><th>Témoins</th><th>Détruites</th><th>Statut</th><th></th></tr>
{% for l in lots %}<tr><td>{{ l.vaccin_nom }}</td><td>{{ l.numero_lot }}</td><td>{{ l.recu }}</td><td><b>{{ l.stock }}</b></td>
<td>{{ l.fournisseur_nom or '' }}</td><td>{{ l.date_fabrication }}</td><td>{{ l.date_peremption }}</td>
<td>{% if l.jours < 0 %}<span class="badge b-périmé">périmé</span>{% elif l.jours <= 30 %}<span class="badge b-quarantaine">{{ l.jours }} j</span>{% else %}{{ l.jours }}{% endif %}</td>
<td>{{ l.emplacement_nom or '' }}</td><td>{{ l.temoins }}</td><td>{{ l.detruites }}</td>
<td><span class="badge b-{{ l|statut_lot }}">{{ l|statut_lot }}</span></td>
<td><a href="{{ url_for('lot_detail', lot_id=l.id) }}">Détail</a></td></tr>
{% else %}<tr><td colspan="13">Aucun lot ne correspond à la recherche.</td></tr>{% endfor %}
</table>{% endblock %}"""

LOT = """{% extends 'base.html' %}{% block content %}
<h1>Lot de vaccin {{ lot.numero_lot }} · {{ lot.vaccin_nom }}</h1>
<p>Fabrication : {{ lot.date_fabrication }} · Péremption : {{ lot.date_peremption }}
({{ jours }} j) · Provenance : {{ lot.fournisseur_nom or '—' }} · Emplacement : {{ lot.emplacement_nom or '—' }}<br>
Disponible : <b>{{ lot.stock }}</b> · Réservées : <b>{{ lot.reserve }}</b> · Témoins : <b>{{ lot.temoins }}</b> · Détruites : <b>{{ lot.detruites }}</b><br>
Statut : <span class="badge b-{{ lot|statut_lot }}">{{ lot|statut_lot }}</span></p>
{% if peut_gerer %}<form class="card" method="post">
<label>Changer l'état du lot<select name="statut">{% for s in STATUTS %}
<option {% if s == lot.statut %}selected{% endif %}>{{ s }}</option>{% endfor %}</select></label>
<button>Mettre à jour</button></form>
<h2>Témoins et destructions</h2>
<form class="card" method="post" action="{{ url_for('lot_temoins', lot_id=lot.id) }}">
<label>Témoins à mettre de côté<input name="quantite" type="number" min="1" max="{{ lot.stock }}" required></label>
<label>Motif (facultatif)<input name="motif" maxlength="200" placeholder="Contrôle qualité"></label>
<button>Mettre de côté</button></form>
<form class="card" method="post" action="{{ url_for('lot_destruction', lot_id=lot.id) }}"
onsubmit="return confirm('Enregistrer cette destruction ? Les doses seront retirées du stock disponible.')">
<label>Quantité détruite<input name="quantite" type="number" min="1" max="{{ lot.stock }}" required></label>
<label>Motif (obligatoire)<input name="motif" maxlength="200" required placeholder="Périmé, casse, rupture de chaîne du froid…"></label>
<button class="danger">Enregistrer la destruction</button></form>{% endif %}
{% if droits.supprimer %}{% if clients|length == 0 %}
<form method="post" action="{{ url_for('lot_supprimer', lot_id=lot.id) }}" class="en-ligne"
onsubmit='return confirm({{ ("Supprimer définitivement le lot " ~ lot.numero_lot ~ " et ses " ~ mouvements|length ~ " mouvement(s) ? Action irréversible.")|tojson }})'><button class="danger">{{ ic('poubelle') }} Supprimer ce lot</button></form>
{% else %}<p><small>Ce lot a déjà été vendu : il ne peut pas être supprimé (changez son statut si nécessaire).</small></p>{% endif %}{% endif %}
{% if droits.pj_fournisseur_voir %}{% from 'pieces.html' import bloc_pieces %}
<h2>Documents (fiche de fabrication, bon de livraison)</h2>
{{ bloc_pieces('lot', lot.id, pieces, droits.pj_fournisseur_gerer, droits.pj_fournisseur_gerer or droits.supprimer, types_pj, TYPES_DOC) }}{% endif %}
<h2>Traçabilité : clients livrés</h2>
<table><tr><th>Client</th><th>Téléphone</th><th>Date</th><th>Quantité</th></tr>
{% for c in clients %}<tr><td>{{ c.nom }}</td><td>{{ c.telephone }}</td><td>{{ c.date }}</td><td>{{ c.quantite }}</td></tr>
{% else %}<tr><td colspan="4">Aucune vente pour ce lot.</td></tr>{% endfor %}</table>
<h2>Mouvements</h2>
<table><tr><th>Date</th><th>Type</th><th>Quantité</th><th>Motif</th><th>Utilisateur</th></tr>
{% for m in mouvements %}<tr><td>{{ m.date|replace('T', ' ') }}</td><td>{{ m.type|type_mvt(m.nature) }}</td><td>{{ m.quantite }}</td>
<td>{{ m.motif }}</td><td>{{ m.username }}</td></tr>{% endfor %}</table>{% endblock %}"""

MOUVEMENTS = """{% extends 'base.html' %}{% block content %}
<h1>Entrées / sorties de stock</h1>
{% if droits.mouvements_saisir %}<form class="card" method="post">
<label>Lot<select name="lot_id">{% for l in lots %}<option value="{{ l.id }}">{{ l.vaccin_nom }} · {{ l.numero_lot }} (stock {{ l.stock }}{% if l.reserve %}, dont {{ l.reserve }} réservé(s){% endif %})</option>{% endfor %}</select></label>
<label>Type<select name="type" id="mv-type"><option value="ENTREE">Entrée</option><option value="SORTIE">Sortie</option></select></label>
<label>Quantité<input name="quantite" type="number" min="1" required></label>
<label>Motif<select name="motif" id="mv-motif" required></select></label>
<button>Enregistrer</button></form>
<script>
(function(){
  var motifs={ENTREE:{{ MOTIFS_ENTREE|tojson }},SORTIE:{{ MOTIFS_SORTIE|tojson }}},
      t=document.getElementById('mv-type'), m=document.getElementById('mv-motif');
  function maj(){m.innerHTML='';motifs[t.value].forEach(function(x){var o=document.createElement('option');o.textContent=x;m.appendChild(o);});}
  t.addEventListener('change',maj);maj();
})();
</script>{% endif %}
<h2 id="reservations">Réservations</h2>
<p><small>Réserver des doses pour une structure : elles ne sont plus proposées aux autres clients à la vente ni à la livraison.
La vente au client concerné utilise sa réservation. Seul le CSA peut réserver ou annuler une réservation.</small></p>
{% if droits.reservations_gerer %}<form class="card" method="post" action="{{ url_for('mouvement_reservation') }}">
<label>Vaccin<select name="lot_id" required>{% for l in lots if l.statut == 'conforme' and l.stock - l.reserve > 0 %}<option value="{{ l.id }}">{{ l.vaccin_nom }} · {{ l.numero_lot }} (non réservé : {{ l.stock - l.reserve }})</option>{% endfor %}</select></label>
<label>Client / structure<select name="client_id" required><option value="">— Choisir —</option>{% for c in clients %}<option value="{{ c.id }}">{{ c.nom }}</option>{% endfor %}</select></label>
<label>Quantité à réserver<input name="quantite" type="number" min="1" required></label>
<label>Note (facultatif)<input name="note" maxlength="200" placeholder="Ex. campagne de vaccination, commande ferme"></label>
<button>Réserver</button></form>{% endif %}
<table><tr><th>Date</th><th>Vaccin</th><th>N° de lot</th><th>Client / structure</th><th>Qté réservée</th><th>Note</th><th>Par</th>{% if droits.reservations_gerer %}<th></th>{% endif %}</tr>
{% for r in reservations %}<tr><td>{{ r.date|replace('T', ' ') }}</td><td>{{ r.vaccin_nom }}</td><td>{{ r.numero_lot }}</td><td>{{ r.client }}</td><td>{{ r.quantite }}</td><td>{{ r.note or '' }}</td><td>{{ r.username or '' }}</td>
{% if droits.reservations_gerer %}<td><form method="post" action="{{ url_for('mouvement_reservation_annuler', rid=r.id) }}" class="en-ligne" onsubmit="return confirm('Annuler cette réservation ?')"><button class="petit danger">Annuler</button></form></td>{% endif %}</tr>
{% else %}<tr><td colspan="8">Aucune réservation en cours.</td></tr>{% endfor %}</table>
<h2>Mouvements</h2>
<form class="filtres" method="get" action="{{ url_for('mouvements') }}">
<input class="grand" name="q" value="{{ flt.q }}" placeholder="Vaccin, lot, motif, utilisateur…">
<select name="type"><option value="">Entrées et sorties</option>
<option value="ENTREE" {% if flt.type == 'ENTREE' %}selected{% endif %}>Entrées</option>
<option value="SORTIE" {% if flt.type == 'SORTIE' %}selected{% endif %}>Sorties</option></select>
<select name="nature"><option value="">Tous les motifs</option>
<option value="DETRUIT" {% if flt.nature == 'DETRUIT' %}selected{% endif %}>Destructions</option>
<option value="TEMOIN" {% if flt.nature == 'TEMOIN' %}selected{% endif %}>Témoins</option></select>
<select name="vaccin_id"><option value="">Tous les vaccins</option>{% for v in vaccins %}<option value="{{ v.id }}" {% if flt.vaccin_id == v.id|string %}selected{% endif %}>{{ v.nom }}</option>{% endfor %}</select>
<label>Du<input type="date" name="du" value="{{ flt.du }}"></label>
<label>Au<input type="date" name="au" value="{{ flt.au }}"></label>
<button>Filtrer</button><a class="lien-reset" href="{{ url_for('mouvements') }}">Réinitialiser</a></form>
<p class="compte">{{ total }} mouvement(s){% if total > 200 %} · les 200 plus récents sont affichés (l'export contient tout){% endif %}{% if fq %} · filtres actifs{% endif %}
&nbsp;<a class="btn-export" href="{{ url_for('export_mouvements', **fq) }}">{{ ic('telecharger') }} Exporter en Excel</a></p>
<table><tr><th>Date</th><th>Vaccin</th><th>Lot</th><th>Type</th><th>Qté</th><th>Motif</th><th>Utilisateur</th></tr>
{% for m in mouvements %}<tr><td>{{ m.date }}</td><td>{{ m.vaccin_nom }}</td><td>{{ m.numero_lot }}</td>
<td>{{ m.type|type_mvt(m.nature) }}</td><td>{{ m.quantite }}</td><td>{{ m.motif }}</td><td>{{ m.username }}</td></tr>
{% else %}<tr><td colspan="7">Aucun mouvement ne correspond à la recherche.</td></tr>{% endfor %}
</table>{% endblock %}"""

CLIENTS = """{% extends 'base.html' %}{% block content %}
<h1>Clients</h1>
{% if droits.clients_gerer %}<form class="card" method="post">
<label>Nom<input name="nom" required maxlength="120"></label>
<label>Profil<select name="nature" required><option value="">—</option><option>entreprise</option><option>particulier</option></select></label>
<label>Type<select name="type"><option>éleveur</option><option>vétérinaire</option><option>structure</option></select></label>
<label>Téléphone<input name="telephone" maxlength="40"></label>
<label>E-mail<input name="email" type="email" maxlength="120"></label>
<label>Adresse<input name="adresse" maxlength="200"></label>
<button>Ajouter</button></form>{% endif %}
<h2>Liste</h2><input class="recherche" data-filtre="t-clients" placeholder="Rechercher un client…">
<table id="t-clients"><tr><th>Nom</th><th>Profil</th><th>Type</th><th>Téléphone</th><th>Commandes</th><th>Ventes</th>{% if droits.supprimer %}<th>Actions</th>{% endif %}</tr>
{% for c in clients %}<tr><td><a href="{{ url_for('client_fiche', cid=c.id) }}">{{ c.nom }}</a></td><td>{{ c.nature or '' }}</td><td>{{ c.type or '' }}</td><td>{{ c.telephone or '' }}</td><td>{{ c.nb_commandes }}</td><td>{{ c.nb_ventes }}</td>
{% if droits.supprimer %}<td>{% if c.nb_ventes == 0 and c.nb_commandes == 0 %}
<form method="post" action="{{ url_for('client_supprimer', cid=c.id) }}" class="en-ligne"
onsubmit='return confirm({{ ("Supprimer définitivement le client « " ~ c.nom ~ " » ?")|tojson }})'><button class="petit danger">Supprimer</button></form>
{% else %}<small>Historique conservé</small>{% endif %}</td>{% endif %}</tr>{% endfor %}
</table>{% endblock %}"""

CLIENT_FICHE = """{% extends 'base.html' %}{% block content %}
<h1>{{ c.nom }}</h1>
<p><a href="{{ url_for('clients') }}">{{ ic('gauche') }} Clients</a></p>
{% if droits.clients_gerer %}<form class="card" method="post">
<label>Nom<input name="nom" required maxlength="120" value="{{ c.nom }}"></label>
<label>Profil<select name="nature" required><option value="">—</option>{% for x in ('entreprise', 'particulier') %}<option {% if c.nature == x %}selected{% endif %}>{{ x }}</option>{% endfor %}</select></label>
<label>Type<select name="type">{% for x in ('éleveur', 'vétérinaire', 'structure') %}<option {% if c.type == x %}selected{% endif %}>{{ x }}</option>{% endfor %}</select></label>
<label>Téléphone<input name="telephone" maxlength="40" value="{{ c.telephone or '' }}"></label>
<label>E-mail<input name="email" type="email" maxlength="120" value="{{ c.email or '' }}"></label>
<label>Adresse<input name="adresse" maxlength="200" value="{{ c.adresse or '' }}"></label>
<button>Enregistrer</button></form>
{% else %}<p>Profil : <b>{{ c.nature or '—' }}</b> · Type : <b>{{ c.type or '—' }}</b> · Téléphone : <b>{{ c.telephone or '—' }}</b> · E-mail : <b>{{ c.email or '—' }}</b> · Adresse : <b>{{ c.adresse or '—' }}</b></p>{% endif %}
<h2>Commandes</h2>
<table><tr><th>N°</th><th>Date</th><th>Statut</th><th>Total</th></tr>
{% for o in commandes %}<tr><td><a href="{{ url_for('commande_detail', cmd_id=o.id) }}">{{ o.numero }}</a></td><td>{{ o.date|replace('T', ' ') }}</td>
<td><span class="badge b-{{ o.statut }}">{{ o.statut }}</span></td><td>{{ o.total|nombre }} {{ devise }}</td></tr>
{% else %}<tr><td colspan="4">Aucune commande.</td></tr>{% endfor %}</table>
{% endblock %}"""

VENTES = """{% extends 'base.html' %}{% block content %}
<h1>Ventes</h1>{% if droits.ventes_saisir %}<p><a href="{{ url_for('caisse') }}"><button>{{ ic('panier') }} Nouvelle vente (caisse)</button></a></p>{% endif %}
<div class="onglets">
<a href="{{ url_for('ventes') }}" class="{{ 'actif' if not flt.mode and not statut }}">Toutes</a>
<a href="{{ url_for('ventes', mode='comptant') }}" class="{{ 'actif' if flt.mode == 'comptant' }}">Vente au comptant</a>
<a href="{{ url_for('ventes', mode='terme') }}" class="{{ 'actif' if flt.mode == 'terme' and not statut }}">Vente à terme</a>
<a href="{{ url_for('ventes', mode='terme', statut='impayees') }}" class="{{ 'actif' if statut == 'impayees' }}">À encaisser</a></div>
<form class="filtres" method="get" action="{{ url_for('ventes') }}">
<input class="grand" name="q" value="{{ flt.q }}" placeholder="Client, vendeur ou n° de vente…">
<select name="mode"><option value="">Tous les modes</option>{% for k, lib in MODES_VENTE.items() %}<option value="{{ k }}" {% if flt.mode == k %}selected{% endif %}>{{ lib }}</option>{% endfor %}</select>
<select name="vaccin_id"><option value="">Tous les vaccins</option>{% for v in vaccins %}<option value="{{ v.id }}" {% if flt.vaccin_id == v.id|string %}selected{% endif %}>{{ v.nom }}</option>{% endfor %}</select>
<select name="vendeur_id"><option value="">Tous les vendeurs</option>{% for u in vendeurs %}<option value="{{ u.id }}" {% if flt.vendeur_id == u.id|string %}selected{% endif %}>{{ u.username }}</option>{% endfor %}</select>
<label>Du<input type="date" name="du" value="{{ flt.du }}"></label>
<label>Au<input type="date" name="au" value="{{ flt.au }}"></label>
<button>Filtrer</button><a class="lien-reset" href="{{ url_for('ventes') }}">Réinitialiser</a></form>
<p class="compte">{{ ventes|length }} vente(s) · {{ qte_total }} dose(s) · montant {{ '%.0f'|format(montant_total) }}{% if reste_total %} · reste à encaisser {{ '%.0f'|format(reste_total) }}{% endif %}{% if fq or statut %} · filtres actifs{% endif %}
&nbsp;<a class="btn-export" href="{{ url_for('export_ventes', **fq) }}">{{ ic('telecharger') }} Exporter en Excel</a></p>
<table><tr><th>N°</th><th>Date</th><th>Client</th><th>Mode</th><th>Quantité</th><th>Total</th><th>Paiement</th><th>Vendeur</th><th>Documents</th></tr>
{% for v in ventes %}<tr><td><a href="{{ url_for('vente_detail', vente_id=v.id) }}">{{ '%07d'|format(v.id) }}</a></td><td>{{ v.date|replace('T', ' ') }}</td><td>{{ v.client }}</td>
<td>{{ MODES_VENTE[v.mode] }}{% if v.commande_id %}<br><a href="{{ url_for('commande_detail', cmd_id=v.commande_id) }}"><small>{{ v.commande_numero }}</small></a>{% endif %}</td>
<td>{{ v.qte }}</td><td>{{ '%.0f'|format(v.total) }}</td>
<td>{% if v.etat %}{% set cl = {'payée':'conforme','soldée':'conforme','partielle':'quarantaine','à régler':'quarantaine','en retard':'périmé'}[v.etat] %}<span class="badge b-{{ cl }}">{{ v.etat }}</span>{% if v.solde %}<br><small>reste {{ '%.0f'|format(v.solde) }}{% if v.echeance %} · éch. {{ v.echeance|date_fr }}{% endif %}</small>{% endif %}{% endif %}</td>
<td>{{ v.username }}</td>
<td><a href="{{ url_for('vente_facture', vente_id=v.id) }}">{{ ic('recu') }} Facture</a> · <a href="{{ url_for('vente_bon', vente_id=v.id) }}">{{ ic('imprimante') }} Bon</a></td></tr>
{% else %}<tr><td colspan="9">Aucune vente ne correspond à la recherche.</td></tr>{% endfor %}</table>{% endblock %}"""

CAISSE = r"""{% extends 'base.html' %}{% block content %}
<h1>Caisse</h1>
<datalist id="liste-vaccins">{% for v in catalogue %}<option value="{{ v.nom }}">{% endfor %}</datalist>
<datalist id="liste-clients">{% for c in clients %}<option value="{{ c.nom }}">{% endfor %}</datalist>
<div class="onglets">
<a href="{{ url_for('caisse', mode='comptant') }}" class="{{ 'actif' if mode == 'comptant' }}">Vente au comptant</a>
<a href="{{ url_for('caisse', mode='terme') }}" class="{{ 'actif' if mode == 'terme' }}">Vente à terme</a></div>
<p class="compte">{% if mode == 'comptant' %}Vente au comptant : tapez le nom du vaccin et la quantité, le prix unitaire et le montant total s'affichent tout seuls. Le client paie tout de suite, la vente est soldée et le stock diminue immédiatement. Le nom du client est facultatif.
{% else %}Vente à terme : le client emporte les vaccins et paie plus tard. Le stock diminue immédiatement ; les versements se suivent ensuite dans la fiche de la vente.{% endif %}</p>
{% macro ligne(l) %}<tr class="ligne-cmd">
<td><input name="ligne_vaccin" class="l-nom" list="liste-vaccins" autocomplete="off" placeholder="Nom du vaccin" value="{{ l.nom|default('') }}"><div class="indice l-info"></div></td>
<td><input name="ligne_quantite" type="number" min="1" class="l-qte" placeholder="Quantité" value="{{ l.quantite|default('') }}"></td>
<td><input name="ligne_prix" type="text" inputmode="decimal" class="l-prix" placeholder="Auto" value="{{ l.prix|default('') }}"></td>
<td class="num l-montant">0</td>
<td><button type="button" class="petit danger l-suppr" title="Retirer la ligne">{{ ic('croix') }}</button></td></tr>{% endmacro %}
<form method="post" class="bloc-cmd" id="principal">
<input type="hidden" name="mode" value="{{ mode }}">
<fieldset><legend>Client{% if mode == 'comptant' %} (facultatif){% endif %}</legend>
<div class="grille">
<label>Nom du client<input name="client_nom" list="liste-clients" maxlength="120" autocomplete="off" {% if mode == 'terme' %}required{% endif %} value="{{ saisie.client_nom if saisie else '' }}" placeholder="{{ 'Nom du client' if mode == 'terme' else 'Client comptoir' }}"></label>
<label>Adresse<input name="client_adresse" maxlength="200" value="{{ saisie.client_adresse if saisie else '' }}"></label>
{% if mode == 'terme' %}<label>Téléphone<input name="client_tel" maxlength="40" value="{{ saisie.client_tel if saisie else '' }}"></label>{% endif %}
</div></fieldset>
<fieldset><legend>Vaccins vendus</legend>
<table class="table-lignes"><thead><tr><th>Nom du vaccin</th><th>Quantité</th><th>Prix unitaire ({{ devise }})</th><th>Montant</th><th></th></tr></thead>
<tbody id="lignes-cmd">{% if saisie and saisie.lignes %}{% for l in saisie.lignes %}{{ ligne(l) }}{% endfor %}{% else %}{{ ligne({}) }}{% endif %}</tbody></table>
<p><button type="button" id="ajout-ligne" class="petit">+ Ajouter un vaccin</button>
&nbsp;&nbsp;<span class="total-gros">Total : <span id="total-cmd">0</span> {{ devise }}</span></p></fieldset>
<fieldset><legend>{{ 'Paiement' if mode == 'comptant' else 'Conditions de paiement' }}</legend><div class="grille">
{% if mode == 'comptant' %}<label>Mode de paiement<select name="mode_paiement">{% for m in MODES_PAIEMENT %}<option {% if saisie and saisie.mode_paiement == m %}selected{% endif %}>{{ m }}</option>{% endfor %}</select></label>
{% else %}<label>Échéance (date limite de paiement)<input type="date" name="echeance" required value="{{ saisie.echeance if saisie and saisie.echeance else echeance_defaut }}"></label>
<label>Acompte versé maintenant (facultatif)<input name="acompte" type="text" inputmode="decimal" value="{{ saisie.acompte if saisie else '' }}"></label>
<label>Mode de paiement de l'acompte<select name="mode_paiement">{% for m in MODES_PAIEMENT %}<option {% if saisie and saisie.mode_paiement == m %}selected{% endif %}>{{ m }}</option>{% endfor %}</select></label>{% endif %}
</div></fieldset>
<p><button>{{ 'Encaisser et valider la vente' if mode == 'comptant' else 'Valider la vente à terme' }}</button></p>
<p><small>Le stock est décrémenté automatiquement selon la règle FEFO (lots conformes et non périmés, péremption la plus proche d'abord). Une facture imprimable est générée.</small></p>
</form>
<template id="modele-ligne">{{ ligne({}) }}</template>
<script>
(function(){
  var CAT={}; {{ catalogue|tojson }}.forEach(function(v){CAT[v.nom.toLowerCase()]=v;});
  function nombre(v){return parseFloat(String(v).replace(',', '.').replace(/ /g,''))||0;}
  function fr(n){return n.toLocaleString('fr-FR');}
  function trouve(nom){return CAT[String(nom).trim().toLowerCase()];}
  function info(el,v,qte){
    if(!el){return;}
    if(!v){el.textContent='';el.className=el.className.replace(' alerte','');return;}
    var txt='Disponible : '+fr(v.stock)+(v.prix?'':' · aucun prix au catalogue');
    var alerte=qte>v.stock;
    if(alerte){txt+=' — quantité demandée supérieure au stock !';}
    el.textContent=txt; el.className='indice'+(alerte?' alerte':'')+(el.classList.contains('l-info')?' l-info':'');
  }
  /* Formulaire complet */
  var corps=document.getElementById('lignes-cmd'), modele=document.getElementById('modele-ligne');
  function recalc(){
    var total=0;
    corps.querySelectorAll('tr.ligne-cmd').forEach(function(tr){
      var q=nombre(tr.querySelector('.l-qte').value), m=q*nombre(tr.querySelector('.l-prix').value);
      tr.querySelector('.l-montant').textContent=fr(m); total+=m;
      info(tr.querySelector('.l-info'),trouve(tr.querySelector('.l-nom').value),q);
    });
    document.getElementById('total-cmd').textContent=fr(total);
  }
  corps.addEventListener('input',function(e){
    if(e.target.classList.contains('l-prix')){e.target.dataset.touche='1';}
    if(e.target.classList.contains('l-nom')){
      var p=e.target.closest('tr').querySelector('.l-prix'), v=trouve(e.target.value);
      if(v&&!p.dataset.touche){p.value=v.prix?String(v.prix).replace('.',','):'';}
    }
    recalc();
  });
  corps.addEventListener('change',function(e){
    if(e.target.classList.contains('l-nom')){
      var p=e.target.closest('tr').querySelector('.l-prix'), v=trouve(e.target.value);
      if(v){p.dataset.touche='';p.value=v.prix?String(v.prix).replace('.',','):p.value;}
      recalc();
    }
  });
  corps.addEventListener('click',function(e){
    if(e.target.classList.contains('l-suppr')){
      var tr=e.target.closest('tr');
      if(corps.querySelectorAll('tr.ligne-cmd').length>1){tr.remove();}
      else{tr.querySelectorAll('input').forEach(function(i){i.value='';});}
      recalc();
    }
  });
  document.getElementById('ajout-ligne').addEventListener('click',function(){corps.appendChild(modele.content.cloneNode(true));});
  recalc();
  var premier=corps.querySelector('.l-nom'); if(premier&&!premier.value){premier.focus();}
})();
</script>
{% endblock %}"""

VENTE_DETAIL = r"""{% extends 'base.html' %}{% block content %}
<h1>Vente n°{{ numero }} · {{ MODES_VENTE[v.mode] }}</h1>
<p><a href="{{ url_for('ventes') }}">{{ ic('gauche') }} Retour aux ventes</a> · <a href="{{ url_for('vente_facture', vente_id=v.id) }}">{{ ic('recu') }} Facture imprimable</a> · <a href="{{ url_for('vente_bon', vente_id=v.id) }}">{{ ic('imprimante') }} Bon de vente (avec lots)</a></p>
<div class="cartes">
<div class="carte c-bleu"><span class="ico">{{ ic('recu') }}</span><div><b>{{ total|nombre }}</b><small>Total ({{ devise }})</small></div></div>
{% if v.mode == 'terme' %}<div class="carte c-vert"><span class="ico">{{ ic('billets') }}</span><div><b>{{ paye|nombre }}</b><small>Déjà payé</small></div></div>
<div class="carte {{ 'c-rouge' if etat == 'en retard' else 'c-orange' if solde else 'c-vert' }}"><span class="ico">{{ ic('sablier') }}</span><div><b>{{ solde|nombre }}</b><small>Reste à payer · {{ etat }}{% if v.echeance %} · échéance {{ v.echeance|date_fr }}{% endif %}</small></div></div>
{% else %}<div class="carte c-vert"><span class="ico">{{ ic('valide') }}</span><div><b>{{ etat or '—' }}</b><small>Paiement</small></div></div>{% endif %}
</div>
<p>Client : <b>{{ v.client }}</b>{% if adresse %} · {{ adresse }}{% endif %}{% if v.client_tel %} · Tél : {{ v.client_tel }}{% endif %}<br>
Date : {{ v.date|replace('T', ' ') }} · Vendeur : {{ v.username }}</p>
<h2>Vaccins vendus</h2>
<table><tr><th>Vaccin</th><th>N° lot</th><th>Péremption</th><th>Quantité</th><th>Prix unitaire</th><th>Montant</th></tr>
{% for l in lignes %}<tr><td>{{ l.vaccin }}</td><td>{{ l.numero_lot }}</td><td>{{ l.date_peremption|date_fr }}</td><td>{{ l.quantite }}</td><td>{{ l.prix_unitaire|nombre }}</td><td>{{ l.montant|nombre }}</td></tr>{% endfor %}</table>
{% if v.mode in ('terme', 'comptant') %}<h2>Paiements</h2>
<table><tr><th>Date</th><th>Montant</th><th>Mode</th><th>Encaissé par</th></tr>
{% for p in paiements %}<tr><td>{{ p.date|replace('T', ' ') }}</td><td>{{ p.montant|nombre }} {{ devise }}</td><td>{{ p.mode or '' }}</td><td>{{ p.username or '' }}</td></tr>
{% else %}<tr><td colspan="4">Aucun paiement enregistré.</td></tr>{% endfor %}</table>
{% if v.mode == 'terme' and solde and droits.paiements_saisir %}<h2>Enregistrer un versement</h2>
<form class="card" method="post" action="{{ url_for('vente_paiement', vente_id=v.id) }}">
<label>Montant ({{ devise }})<input name="montant" type="text" inputmode="decimal" required placeholder="Max. {{ solde|nombre }}"></label>
<label>Mode de paiement<select name="mode_paiement">{% for m in MODES_PAIEMENT %}<option>{{ m }}</option>{% endfor %}</select></label>
<button>Enregistrer le versement</button></form>{% endif %}{% endif %}
{% endblock %}"""

FACTURE_VENTE = r"""{% extends 'base.html' %}{% block content %}
<div class="no-print actions-bon">
<button onclick="window.print()">{{ ic('imprimante') }} Imprimer la facture</button>
<a href="{{ url_for('vente_detail', vente_id=v.id) }}">{{ ic('gauche') }} Détail de la vente</a> · <a href="{{ url_for('ventes') }}">Toutes les ventes</a>
<small>Astuce : choisissez « Enregistrer au format PDF » dans la fenêtre d'impression pour l'envoyer au client.</small>
</div>
<div class="fact">
<img class="filigrane" src="{{ url_for('static', filename='fond.png') }}" alt="">
<div class="fact-tete">
<div class="fact-marque"><img src="{{ url_for('static', filename='logo.png') }}" alt="ISRA"><b>{{ societe.nom|upper }}</b><span>Service Commercial</span></div>
<div class="fact-cadre">
<div>Date : <span class="ecrit">{{ date_vente }}</span></div>
<div>Client : <span class="ecrit">{{ v.client }}</span></div>
<div>Adresse : <span class="ecrit">{{ adresse }}</span></div>
<div class="fact-ligne"><span class="fact-badge">FACTURE</span><span>N° <b>{{ numero }}</b></span></div>
</div></div>
<table class="fact-table">
<tr><th style="width:15%">QUANTITÉ</th><th>DÉSIGNATION</th><th style="width:16%">P. UNITAIRE</th><th style="width:19%">P. TOTAL</th></tr>
{% for l in regroupees %}<tr><td class="num">{{ l.quantite|nombre }}</td><td>{{ l.vaccin }}</td><td class="num">{{ l.prix_unitaire|nombre }}</td><td class="num">{{ l.montant|nombre }}</td></tr>{% endfor %}
{% for _ in range(vides) %}<tr><td></td><td></td><td></td><td></td></tr>{% endfor %}
<tfoot><tr><td colspan="3" class="num">TOTAL ({{ devise }})</td><td class="num">{{ total|nombre }}</td></tr></tfoot>
</table>
<p class="fact-lettres"><b>Arrêté la présente à la somme de</b> <span class="ecrit">{{ lettres }} francs CFA</span></p>
<p class="fact-paiement">{{ MODES_VENTE[v.mode] }}{% if v.mode == 'comptant' %} · payée{% elif v.mode == 'terme' %} · échéance {{ v.echeance|date_fr }}{% if paye %} · acompte versé : {{ paye|nombre }} {{ devise }}{% endif %} · reste à payer : {{ solde|nombre }} {{ devise }}{% endif %}</p>
<div class="fact-sign"><span>Le Chef de l'Unité P.O</span><span>Le Chef du Service Administratif</span></div>
<div class="fact-pied">{{ societe.nom|upper }} — PRODUCTION DE VACCINS, {{ societe.adresse }} · Tél : {{ societe.tel }}<br>Facture éditée le {{ imprime_le }} par {{ session.user.code or session.user.username }}</div>
</div>
{% endblock %}"""

DONNEES_ESSAI = """{% extends 'base.html' %}{% block content %}
<h1>Supprimer les données d'essai</h1>
<p class="compte">Réservé à l'administrateur. Sert à effacer les ventes et achats faits pour tester la plateforme, avant la mise en service.
Les comptes utilisateurs, le catalogue des vaccins, les référentiels et le journal d'audit ne sont jamais touchés.</p>
<div class="cartes">
<div class="carte c-bleu"><span class="ico">{{ ic('panier') }}</span><div><b>{{ nb.ventes }}</b><small>Vente(s)</small></div></div>
<div class="carte c-bleu"><span class="ico">{{ ic('recu') }}</span><div><b>{{ nb.commandes }}</b><small>Commande(s) · {{ nb.factures }} facture(s)</small></div></div>
<div class="carte c-bleu"><span class="ico">{{ ic('colis') }}</span><div><b>{{ nb.lots }}</b><small>Lot(s) · {{ nb.inventaires }} inventaire(s)</small></div></div>
<div class="carte c-bleu"><span class="ico">{{ ic('utilisateurs') }}</span><div><b>{{ nb.clients }}</b><small>Client(s)</small></div></div></div>
<form class="card" method="post" style="display:block;max-width:760px"
onsubmit="return confirm('Cette suppression est définitive. Continuer ?')">
<p><b>Que faut-il supprimer ?</b></p>
{% for cle, lib in niveaux %}<label style="flex-direction:row;align-items:flex-start;gap:8px;font-size:14px;color:#222;margin:8px 0">
<input type="radio" name="niveau" value="{{ cle }}" {% if loop.first %}checked{% endif %} style="margin-top:3px"> <span>{{ lib }}</span></label>{% endfor %}
<label>Pour confirmer, tapez le mot SUPPRIMER<input name="confirmation" autocomplete="off" required></label>
<button class="danger">Supprimer définitivement</button></form>
<p><small>Après la purge, les vaccins d'essai n'ont plus de ventes : le bouton « Supprimer » réapparaît dans le catalogue.</small></p>
{% endblock %}"""

MESSAGES = """{% extends 'base.html' %}{% block content %}
<h1>Messagerie interne</h1>
<form class="card" method="post">
<label>Destinataire<select name="destinataire_id">{% for u in users %}<option value="{{ u.id }}">{{ u.username }} ({{ u.role|role_lib }})</option>{% endfor %}</select></label>
<label>Sujet<input name="sujet" required></label>
<label style="grid-column:1/-1">Message<textarea name="corps" rows="3"></textarea></label>
<button>Envoyer</button></form>
<h2>Boîte de réception</h2>
<table><tr><th>Date</th><th>De</th><th>Sujet</th><th>Message</th></tr>
{% for m in recus %}<tr class="{% if not m.lu %}unread{% endif %}"><td>{{ m.date }}</td><td>{{ m.de }}</td>
<td>{{ m.sujet }}</td><td>{{ m.corps }}</td></tr>{% else %}<tr><td colspan="4">Aucun message.</td></tr>{% endfor %}</table>
<h2>Messages envoyés</h2>
<table><tr><th>Date</th><th>À</th><th>Sujet</th></tr>
{% for m in envoyes %}<tr><td>{{ m.date }}</td><td>{{ m.a }}</td><td>{{ m.sujet }}</td></tr>{% endfor %}</table>{% endblock %}"""

INVENTAIRES = """{% extends 'base.html' %}{% block content %}
<h1>Inventaires</h1>
{% if droits.inventaire_compter %}<form method="post" action="{{ url_for('inventaire_nouveau') }}"><button>Démarrer un nouvel inventaire</button></form>{% endif %}
<h2>Historique</h2><input class="recherche" data-filtre="t-inv" placeholder="Rechercher un inventaire…">
<table id="t-inv"><tr><th>N°</th><th>Date</th><th>Responsable</th><th>État</th><th></th></tr>
{% for i in inventaires %}<tr><td>{{ i.id }}</td><td>{{ i.date }}</td><td>{{ i.username }}</td>
<td>{{ 'Validé' if i.valide else 'En cours' }}</td>
<td><a href="{{ url_for('inventaire_detail', inv_id=i.id) }}">Ouvrir</a></td></tr>{% endfor %}</table>{% endblock %}"""

INVENTAIRE = """{% extends 'base.html' %}{% block content %}
<h1>Inventaire n°{{ inv.id }} {% if inv.valide %}(validé){% endif %}</h1>
<form method="post"><table><tr><th>Vaccin</th><th>Lot</th><th>Emplacement</th><th>Stock théorique</th>
<th>Stock compté</th><th>Écart</th></tr>
{% for l in lignes %}<tr><td>{{ l.vaccin_nom }}</td><td>{{ l.numero_lot }}</td><td>{{ l.emplacement }}</td>
<td>{{ l.theorique }}</td>
<td>{% if inv.valide or not droits.inventaire_compter %}{{ l.compte if l.compte is not none }}{% else %}<input type="number" min="0" name="compte_{{ l.id }}" value="{{ l.compte if l.compte is not none }}" style="width:90px">{% endif %}</td>
<td>{{ l.ecart if l.ecart is not none }}</td></tr>{% endfor %}</table>
<h2>Commentaire</h2>
{% if inv.valide or not (droits.inventaire_compter or droits.inventaire_valider) %}<p>{{ inv.commentaire or '—' }}</p>
{% else %}<textarea name="commentaire" rows="4" maxlength="2000" style="width:100%" placeholder="Observations sur l'inventaire : écarts constatés, causes, remarques…">{{ inv.commentaire or '' }}</textarea>{% endif %}
{% if not inv.valide %}<p>{% if droits.inventaire_compter %}<button>Enregistrer le comptage</button>{% endif %}
{% if droits.inventaire_valider %}<button name="valider" value="1" onclick="return confirm('Valider cet inventaire et régulariser les écarts dans le stock ?')">Valider et régulariser les écarts</button>
{% else %}<small>Seul l'administrateur peut valider l'inventaire.</small>{% endif %}</p>{% endif %}</form>{% endblock %}"""

AUDIT = """{% extends 'base.html' %}{% block content %}
<h1>Journal d'audit</h1>
<form class="filtres" method="get" action="{{ url_for('journal') }}">
<input class="grand" name="q" value="{{ flt.q }}" placeholder="Action ou utilisateur…">
<select name="utilisateur_id"><option value="">Tous les utilisateurs</option>{% for u in users %}<option value="{{ u.id }}" {% if flt.utilisateur_id == u.id|string %}selected{% endif %}>{{ u.username }}</option>{% endfor %}</select>
<label>Du<input type="date" name="du" value="{{ flt.du }}"></label>
<label>Au<input type="date" name="au" value="{{ flt.au }}"></label>
<button>Filtrer</button><a class="lien-reset" href="{{ url_for('journal') }}">Réinitialiser</a></form>
<p class="compte">{{ total }} entrée(s){% if total > 300 %} · les 300 plus récentes sont affichées{% endif %}</p>
<table><tr><th>Date</th><th>Utilisateur</th><th>Action</th></tr>
{% for a in entrees %}<tr><td>{{ a.date|replace('T', ' ') }}</td><td>{{ a.username }}</td><td>{{ a.action }}</td></tr>
{% else %}<tr><td colspan="3">Aucune entrée ne correspond à la recherche.</td></tr>{% endfor %}
</table>{% endblock %}"""

MOTDEPASSE = """{% extends 'base.html' %}{% block content %}
<h1>Changer mon mot de passe</h1>
<form class="card" method="post" style="max-width:420px">
<label>Mot de passe actuel<input name="actuel" type="password" required autocomplete="current-password"></label>
<label>Nouveau mot de passe (8 caractères minimum)<input name="nouveau" type="password" required minlength="8" autocomplete="new-password"></label>
<label>Confirmer le nouveau mot de passe<input name="confirmation" type="password" required minlength="8" autocomplete="new-password"></label>
<button>Enregistrer</button></form>
{% endblock %}"""

UTILISATEURS = """{% extends 'base.html' %}{% block content %}
<h1>Gestion des utilisateurs</h1>
{% if mdp %}<div class="mdp-box">{{ ic('cle') }} Compte <b>{{ mdp.username }}</b> · mot de passe temporaire :
<code>{{ mdp.mdp }}</code><br><small>Notez-le maintenant : il ne sera plus affiché. L'utilisateur devra
en choisir un nouveau à sa première connexion.</small></div>{% endif %}
<form class="card" method="post" action="{{ url_for('utilisateur_nouveau') }}">
<label>Nom d'utilisateur<input name="username" required minlength="3" maxlength="30" autocomplete="off"
placeholder="ex. Mr Sow"></label>
<label>Rôle<select name="role" required><option value="">— Choisir un rôle —</option>{% for r in ROLES %}<option value="{{ r }}">{{ r|role_lib }}</option>{% endfor %}</select></label>
<label>E-mail (facultatif)<input name="email" type="email" maxlength="120" placeholder="prenom.nom@exemple.sn"></label>
<button>Créer le compte</button></form>
<p><a href="{{ url_for('email_parametres') }}">{{ ic('mail') }} Paramètres des notifications par e-mail</a></p>
<p><small>Tout nouveau compte reçoit le mot de passe standard Vaccin@2027 ; l'utilisateur doit le changer à sa première connexion.</small></p>
<h2>Comptes</h2>
<table><tr><th>Utilisateur</th><th>Code</th><th>Rôle</th><th>E-mail</th><th>État</th><th>Dernière connexion</th><th>Actions</th></tr>
{% for u in users %}<tr>
<td>{{ u.username }}{% if u.id == moi %} <small>(vous)</small>{% endif %}</td><td><b>{{ u.code or '—' }}</b></td>
<td>{% if u.id == moi %}{{ u.role|role_lib }}{% else %}
<form method="post" action="{{ url_for('utilisateur_role', uid=u.id) }}" class="en-ligne">
<select name="role">{% for r in ROLES %}<option value="{{ r }}" {% if r == u.role %}selected{% endif %}>{{ r|role_lib }}</option>{% endfor %}</select>
<button class="petit">OK</button></form>{% endif %}</td>
<td><form method="post" action="{{ url_for('utilisateur_email', uid=u.id) }}" class="en-ligne">
<input name="email" type="email" maxlength="120" value="{{ u.email or '' }}" placeholder="—" style="width:190px"><button class="petit">OK</button></form></td>
<td>{% if u.bloque %}<span class="badge b-périmé">Bloqué</span>{% elif u.actif %}<span class="badge b-conforme">Actif</span>{% else %}<span class="badge b-périmé">Désactivé</span>{% endif %}
{% if u.doit_changer_mdp %}<span class="badge b-quarantaine">mot de passe temporaire</span>{% endif %}</td>
<td>{{ (u.derniere or '—')|replace('T', ' ') }}</td>
<td>{% if u.id != moi %}
{% if u.bloque %}<form method="post" action="{{ url_for('utilisateur_debloquer', uid=u.id) }}" class="en-ligne"><button class="petit">{{ ic('cadenas-ouvert') }} Débloquer</button></form>{% endif %}
<form method="post" action="{{ url_for('utilisateur_reinit', uid=u.id) }}" class="en-ligne"
onsubmit="return confirm('Réinitialiser le mot de passe de {{ u.username }} ?')"><button class="petit">Réinitialiser</button></form>
<form method="post" action="{{ url_for('utilisateur_etat', uid=u.id) }}" class="en-ligne"
onsubmit="return confirm('{{ 'Désactiver' if u.actif else 'Réactiver' }} le compte {{ u.username }} ?')">
<button class="petit {{ 'danger' if u.actif }}">{{ 'Désactiver' if u.actif else 'Réactiver' }}</button></form>
<form method="post" action="{{ url_for('utilisateur_supprimer', uid=u.id) }}" class="en-ligne"
onsubmit="return confirm('Supprimer définitivement le compte {{ u.username }} ? Action irréversible.')"><button class="petit danger">Supprimer</button></form>
{% else %}<small>—</small>{% endif %}</td></tr>{% endfor %}</table>
<p><small>Après {{ max_echecs }} tentatives de connexion échouées, un compte est bloqué : seul l'administrateur peut le débloquer.
Un compte ne peut être supprimé que s'il n'a encore aucune opération enregistrée ; sinon, désactivez-le pour conserver l'historique.
Le code (GS01, RV01…) remplace le nom sur les documents imprimés.</small></p>
{% endblock %}"""

VENTE_BON = """{% extends 'base.html' %}{% block content %}
<div class="no-print actions-bon">
<button onclick="window.print()">{{ ic('imprimante') }} Imprimer le bon</button>
<a href="{{ url_for('ventes') }}">{{ ic('gauche') }} Retour aux ventes</a>
<small>Astuce : dans la fenêtre d'impression, choisissez « Enregistrer au format PDF » pour l'envoyer au client.</small>
</div>
<div class="bon">
<img class="filigrane" src="{{ url_for('static', filename='fond.png') }}" alt="">
<div class="bon-entete">
<img class="bon-logo" src="{{ url_for('static', filename='logo.png') }}" alt="Logo">
<div class="bon-soc"><b>{{ societe.nom }}</b>
{% if societe.adresse %}<br>{{ societe.adresse }}{% endif %}
{% if societe.tel %}<br>Tél : {{ societe.tel }}{% endif %}
{% if societe.email %}<br>{{ societe.email }}{% endif %}</div>
<div class="bon-titre"><h1>BON DE VENTE</h1><div class="num">N° {{ numero }}</div><div>Date : {{ date_vente }}</div></div>
</div>
<div class="bon-infos">
<div><h3>Client</h3><b>{{ v.client }}</b>{% if v.client_type %}<br>{{ v.client_type }}{% endif %}
{% if v.client_tel %}<br>Tél : {{ v.client_tel }}{% endif %}</div>
<div><h3>Vendeur</h3><b>{{ v.username }}</b><br>Vente enregistrée le {{ date_vente }}</div>
</div>
<table class="bon-table">
<tr><th>Désignation</th><th>N° de lot</th><th>Péremption</th><th class="num">Quantité</th>
<th class="num">Prix unitaire ({{ devise }})</th><th class="num">Montant ({{ devise }})</th></tr>
{% for l in lignes %}<tr><td>{{ l.vaccin }}<br><small>Conservation : {{ l.temp_min|nombre }} à {{ l.temp_max|nombre }} °C</small></td>
<td>{{ l.numero_lot }}</td><td>{{ l.date_peremption|date_fr }}</td><td class="num">{{ l.quantite }}</td>
<td class="num">{{ l.prix_unitaire|nombre }}</td><td class="num">{{ l.montant|nombre }}</td></tr>{% endfor %}
<tfoot><tr><td colspan="3">TOTAL</td><td class="num">{{ qte }}</td><td></td><td class="num">{{ total|nombre }} {{ devise }}</td></tr></tfoot>
</table>
<div class="bon-sign"><div>Le vendeur<br><small>(nom et signature)</small></div><div>Le client<br><small>(nom, date et signature)</small></div></div>
<div class="bon-pied">{{ societe.nom }} · Bon n° {{ numero }} · Édité le {{ imprime_le }} par {{ session.user.code or session.user.username }}</div>
</div>
{% endblock %}"""

REF_HUB = """{% extends 'base.html' %}{% block content %}
<h1>Référentiels</h1>
<p class="compte">Les listes de base utilisées dans toute la plateforme. Une valeur modifiée ici est mise à jour partout.</p>
<div class="cartes">
{% for c in cartes %}<a class="carte c-vert" href="{{ url_for('ref_liste', cle=c.cle) }}" style="text-decoration:none;color:inherit">
<span class="ico">{{ ic(c.ico) }}</span><div><b>{{ c.n }}</b><small>{{ c.titre }} · {{ c.desc }}</small></div></a>{% endfor %}
{% if droits.clients_voir %}<a class="carte c-bleu" href="{{ url_for('clients') }}" style="text-decoration:none;color:inherit">
<span class="ico">{{ ic('utilisateurs') }}</span><div><b>{{ nb_clients }}</b><small>Clients · gérés dans la page Clients</small></div></a>{% endif %}
</div>
{% endblock %}"""

REF_LISTE = """{% extends 'base.html' %}{% block content %}
<h1>{{ conf.titre }}</h1>
<p><a href="{{ url_for('referentiels') }}">{{ ic('gauche') }} Référentiels</a></p>
{% if droits.referentiels_gerer %}<form class="card" method="post">
{% for nom, libelle, requis in conf.champs %}<label>{{ libelle }}<input name="{{ nom }}" {% if requis %}required{% endif %} maxlength="200"></label>
{% endfor %}<button>Ajouter</button></form>{% endif %}
<input class="recherche" data-filtre="t-ref" placeholder="Rechercher…">
<p class="compte">{{ lignes|length }} élément(s) ·
{% if archives %}<a href="{{ url_for('ref_liste', cle=cle) }}">Masquer les archivés</a>{% else %}<a href="{{ url_for('ref_liste', cle=cle, archives=1) }}">Afficher les archivés</a>{% endif %}</p>
<table id="t-ref"><tr>{% for nom, libelle, requis in conf.champs %}<th>{{ libelle }}</th>{% endfor %}
<th>Utilisé par</th><th>État</th><th>Actions</th></tr>
{% for r in lignes %}<tr>
{% for nom, libelle, requis in conf.champs %}<td>{% if loop.first %}<a href="{{ url_for('ref_edit', cle=cle, rid=r.id) }}">{{ r[nom] }}</a>{% else %}{{ r[nom] or '' }}{% endif %}</td>{% endfor %}
<td>{{ r.nb_usages }} {{ conf.usage_label }}</td>
<td>{% if r.actif %}<span class="badge b-conforme">Actif</span>{% else %}<span class="badge b-quarantaine">Archivé</span>{% endif %}</td>
<td><a href="{{ url_for('ref_edit', cle=cle, rid=r.id) }}">{% if droits.referentiels_gerer %}Modifier{% else %}Voir{% endif %}</a>
{% if droits.referentiels_gerer %}<form method="post" action="{{ url_for('ref_archiver', cle=cle, rid=r.id) }}" class="en-ligne"><button class="petit">{{ 'Archiver' if r.actif else 'Restaurer' }}</button></form>{% endif %}
{% if droits.supprimer and r.nb_usages == 0 %}<form method="post" action="{{ url_for('ref_supprimer', cle=cle, rid=r.id) }}" class="en-ligne"
onsubmit='return confirm({{ ("Supprimer définitivement « " ~ r.nom ~ " » ?")|tojson }})'><button class="petit danger">Supprimer</button></form>{% endif %}</td></tr>
{% else %}<tr><td colspan="{{ conf.champs|length + 3 }}">Aucun élément.</td></tr>{% endfor %}
</table>{% endblock %}"""

REF_EDIT = """{% extends 'base.html' %}{% block content %}
<h1>{{ conf.titre }} · {{ r.nom }}</h1>
<p><a href="{{ url_for('ref_liste', cle=cle) }}">{{ ic('gauche') }} {{ conf.titre }}</a></p>
<form class="card" method="post">
{% for nom, libelle, requis in conf.champs %}<label>{{ libelle }}<input name="{{ nom }}" value="{{ r[nom] or '' }}" {% if requis %}required{% endif %} maxlength="200" {% if not droits.referentiels_gerer %}readonly{% endif %}></label>
{% endfor %}{% if droits.referentiels_gerer %}<button>Enregistrer</button>{% endif %}</form>
<p class="compte">Utilisé par {{ r.nb_usages }} {{ conf.usage_label }} · {% if r.actif %}actif{% else %}archivé{% endif %}</p>
{% endblock %}"""

ARTICLES = """{% extends 'base.html' %}{% block content %}
<h1>Articles (stock général)</h1>
{% if droits.articles_gerer %}<form class="card" method="post" action="{{ url_for('articles') }}">
<label>Nom<input name="nom" required maxlength="120"></label>
<label>Référence<input name="reference" maxlength="60"></label>
<label>Catégorie<select name="categorie_id" required><option value="">—</option>{% for x in categories %}<option value="{{ x.id }}">{{ x.nom }}</option>{% endfor %}</select></label>
<label>Unité<select name="unite_id" required><option value="">—</option>{% for x in unites %}<option value="{{ x.id }}">{{ x.nom }}</option>{% endfor %}</select></label>
<label>Fournisseur<select name="fournisseur_id" ><option value="">—</option>{% for x in fournisseurs %}<option value="{{ x.id }}">{{ x.nom }}</option>{% endfor %}</select></label>
<label>Emplacement<select name="emplacement_id" ><option value="">—</option>{% for x in emplacements %}<option value="{{ x.id }}">{{ x.nom }}</option>{% endfor %}</select></label>
<label>Seuil minimal<input name="seuil_min" type="number" min="0" value="0"></label>
<label>Stock initial (facultatif)<input name="stock_initial" type="number" min="0"></label>
<button>Ajouter l'article</button>
<p style="grid-column:1/-1;margin:0"><small>Il manque une catégorie, une unité, un fournisseur ou un emplacement ? Ajoutez-le dans les
<a href="{{ url_for('referentiels') }}">Référentiels</a>.</small></p></form>{% endif %}
<h2>Liste</h2>
<form class="filtres" method="get" action="{{ url_for('articles') }}">
<input class="grand" name="q" value="{{ flt.q }}" placeholder="Nom ou référence…">
<select name="categorie_id"><option value="">Toutes les catégories</option>{% for x in categories %}<option value="{{ x.id }}" {% if flt.categorie_id == x.id|string %}selected{% endif %}>{{ x.nom }}</option>{% endfor %}</select>
<select name="fournisseur_id"><option value="">Tous les fournisseurs</option>{% for x in fournisseurs %}<option value="{{ x.id }}" {% if flt.fournisseur_id == x.id|string %}selected{% endif %}>{{ x.nom }}</option>{% endfor %}</select>
<select name="emplacement_id"><option value="">Tous les emplacements</option>{% for x in emplacements %}<option value="{{ x.id }}" {% if flt.emplacement_id == x.id|string %}selected{% endif %}>{{ x.nom }}</option>{% endfor %}</select>
<select name="etat"><option value="">Tous les états</option><option value="bas" {% if flt.etat == 'bas' %}selected{% endif %}>Stock bas seulement</option></select>
<label class="case"><input type="checkbox" name="archives" value="1" {% if flt.archives == '1' %}checked{% endif %}> Inclure les archivés</label>
<button>Filtrer</button><a class="lien-reset" href="{{ url_for('articles') }}">Réinitialiser</a></form>
<p class="compte">{{ articles|length }} article(s){% if fq %} · filtres actifs{% endif %}
&nbsp;<a class="btn-export" href="{{ url_for('export_articles', **fq) }}">{{ ic('telecharger') }} Exporter en Excel</a></p>
<table><tr><th>Article</th><th>Catégorie</th><th>Unité</th><th>Fournisseur</th><th>Emplacement</th><th>Stock</th><th>Seuil</th><th>État</th></tr>
{% for a in articles %}<tr><td><a href="{{ url_for('article_detail', aid=a.id) }}">{{ a.nom }}</a>{% if a.reference %}<br><small>Réf. {{ a.reference }}</small>{% endif %}</td>
<td>{{ a.categorie_nom }}</td><td>{{ a.unite_nom }}</td><td>{{ a.fournisseur_nom or '' }}</td><td>{{ a.emplacement_nom or '' }}</td>
<td><b>{{ a.stock }}</b></td><td>{{ a.seuil_min }}</td>
<td>{% if not a.actif %}<span class="badge b-quarantaine">Archivé</span>{% elif a.stock < a.seuil_min %}<span class="badge b-périmé">Stock bas</span>{% else %}<span class="badge b-conforme">OK</span>{% endif %}</td></tr>
{% else %}<tr><td colspan="8">Aucun article ne correspond.</td></tr>{% endfor %}
</table>{% endblock %}"""

ARTICLE = """{% extends 'base.html' %}{% block content %}
<h1>{{ a.nom }}{% if not a.actif %} <span class="badge b-quarantaine">Archivé</span>{% endif %}</h1>
<p><a href="{{ url_for('articles') }}">{{ ic('gauche') }} Articles</a></p>
<div class="cartes">
<div class="carte {{ 'c-rouge' if a.stock < a.seuil_min else 'c-vert' }}"><span class="ico">{{ ic('outils') }}</span><div><b>{{ a.stock }}</b><small>{{ a.unite_nom }} en stock</small></div></div>
<div class="carte c-bleu"><span class="ico">{{ ic('baisse') }}</span><div><b>{{ a.seuil_min }}</b><small>Seuil minimal{% if a.stock < a.seuil_min %} · <em>stock bas</em>{% endif %}</small></div></div>
</div>
{% if droits.articles_mouvements and a.actif %}<h2>Enregistrer un mouvement</h2>
<form class="card" method="post" action="{{ url_for('article_mouvement', aid=a.id) }}" enctype="multipart/form-data">
<label>Type<select name="nature" required><option value="">—</option>{% for k, v in NATURES.items() %}<option value="{{ k }}">{{ v }}</option>{% endfor %}</select></label>
<label>Quantité<input name="quantite" type="number" min="1" required></label>
<label>Sens (ajustement seulement)<select name="sens"><option value="+">+ (ajouter)</option><option value="-">− (retirer)</option></select></label>
<label>Motif (obligatoire pour sortie et ajustement)<input name="motif" maxlength="200"></label>
{% if droits.pj_fournisseur_gerer %}<label>Facture fournisseur (facultatif)<input type="file" name="facture_fichier" accept=".pdf,.doc,.docx,.xls,.xlsx,.png,.jpg,.jpeg"></label>
<label>Bon de livraison fournisseur (facultatif)<input type="file" name="bl_fichier" accept=".pdf,.doc,.docx,.xls,.xlsx,.png,.jpg,.jpeg"></label>{% endif %}
<button>Enregistrer</button></form>{% endif %}
<h2>Informations</h2>
{% if droits.articles_gerer %}<form class="card" method="post">
<label>Nom<input name="nom" required maxlength="120" value="{{ a.nom }}"></label>
<label>Référence<input name="reference" maxlength="60" value="{{ a.reference or '' }}"></label>
<label>Catégorie<select name="categorie_id" required>{% for x in categories %}<option value="{{ x.id }}" {% if x.id == a.categorie_id %}selected{% endif %}>{{ x.nom }}</option>{% endfor %}</select></label>
<label>Unité<select name="unite_id" required>{% for x in unites %}<option value="{{ x.id }}" {% if x.id == a.unite_id %}selected{% endif %}>{{ x.nom }}</option>{% endfor %}</select></label>
<label>Fournisseur<select name="fournisseur_id"><option value="">—</option>{% for x in fournisseurs %}<option value="{{ x.id }}" {% if x.id == a.fournisseur_id %}selected{% endif %}>{{ x.nom }}</option>{% endfor %}</select></label>
<label>Emplacement<select name="emplacement_id"><option value="">—</option>{% for x in emplacements %}<option value="{{ x.id }}" {% if x.id == a.emplacement_id %}selected{% endif %}>{{ x.nom }}</option>{% endfor %}</select></label>
<label>Seuil minimal<input name="seuil_min" type="number" min="0" value="{{ a.seuil_min }}"></label>
<label>Description<input name="description" maxlength="300" value="{{ a.description or '' }}"></label>
<button>Enregistrer les modifications</button></form>
<form method="post" action="{{ url_for('article_archiver', aid=a.id) }}" class="en-ligne"
onsubmit='return confirm({{ (("Restaurer" if not a.actif else "Archiver") ~ " « " ~ a.nom ~ " » ?")|tojson }})'><button class="petit">{{ 'Restaurer' if not a.actif else 'Archiver' }}</button></form>
{% else %}<p>Catégorie : <b>{{ a.categorie_nom }}</b> · Unité : <b>{{ a.unite_nom }}</b> · Fournisseur : <b>{{ a.fournisseur_nom or '—' }}</b> · Emplacement : <b>{{ a.emplacement_nom or '—' }}</b>{% if a.reference %} · Réf. <b>{{ a.reference }}</b>{% endif %}</p>{% endif %}
{% if droits.supprimer %}<form method="post" action="{{ url_for('article_supprimer', aid=a.id) }}" class="en-ligne"
onsubmit='return confirm({{ ("Supprimer définitivement « " ~ a.nom ~ " » et son historique ? Action irréversible.")|tojson }})'><button class="petit danger">Supprimer</button></form>{% endif %}
<h2>Historique des mouvements</h2>
<table><tr><th>Date</th><th>Type</th><th>Quantité</th><th>Stock après</th><th>Motif</th><th>Utilisateur</th><th>Documents</th></tr>
{% for m in historique %}<tr><td>{{ m.date|replace('T', ' ') }}</td><td>{{ NATURES.get(m.nature, m.nature) }}</td>
<td>{{ '+' if m.delta > 0 }}{{ m.delta }}</td><td>{{ m.solde }}</td><td>{{ m.motif or '' }}</td><td>{{ m.username or '' }}</td>
<td>{% for p in m.docs %}<a href="{{ url_for('piece_telecharger', pid=p.id) }}" title="{{ p.nom_original }}">{{ ic('trombone') }} {{ TYPES_DOC[p.type_doc] }}</a>{% if not loop.last %}<br>{% endif %}{% endfor %}</td></tr>
{% else %}<tr><td colspan="7">Aucun mouvement enregistré.</td></tr>{% endfor %}
</table>{% endblock %}"""

VACCIN = """{% extends 'base.html' %}{% block content %}
<h1>{{ v.nom }}{% if not v.actif %} <span class="badge b-quarantaine">Archivé</span>{% endif %}</h1>
<p><a href="{{ url_for('vaccins') }}">{{ ic('gauche') }} Catalogue des vaccins</a> · <a href="{{ url_for('lots') }}">Lots</a></p>
<div class="cartes">
<div class="carte {{ 'c-rouge' if vendable < v.seuil_min else 'c-vert' }}"><span class="ico">{{ ic('seringue') }}</span><div><b>{{ vendable }}</b><small>Disponible à la vente</small></div></div>
<div class="carte c-bleu"><span class="ico">{{ ic('colis') }}</span><div><b>{{ stock_total }}</b><small>Stock total (tous statuts)</small></div></div>
<div class="carte c-bleu"><span class="ico">{{ ic('fiole') }}</span><div><b>{{ temoins }}</b><small>Témoins mis de côté</small></div></div>
<div class="carte c-bleu"><span class="ico">{{ ic('poubelle') }}</span><div><b>{{ detruites }}</b><small>Doses détruites</small></div></div>
<div class="carte c-bleu"><span class="ico">{{ ic('baisse') }}</span><div><b>{{ v.seuil_min }}</b><small>Seuil minimal</small></div></div>
</div>
<h2>Fiche du vaccin</h2>
{% if droits.vaccins_gerer %}<form class="card" method="post">
<label>Nom<input name="nom" required maxlength="120" value="{{ v.nom }}"></label>
<label>Type<select name="type">{% for t in types %}<option {% if t == v.type %}selected{% endif %}>{{ t }}</option>{% endfor %}</select></label>
<label>Espèce cible<input name="espece" value="{{ v.espece or '' }}"></label>
<label>Fabricant<input name="fabricant" value="{{ v.fabricant or '' }}"></label>
<label>Doses / flacon<input name="doses" type="number" min="1" value="{{ v.doses_par_flacon }}"></label>
<label>Temp. min (°C)<input name="temp_min" type="number" step="0.1" value="{{ v.temp_min }}"></label>
<label>Temp. max (°C)<input name="temp_max" type="number" step="0.1" value="{{ v.temp_max }}"></label>
<label>Seuil minimal<input name="seuil_min" type="number" min="0" value="{{ v.seuil_min }}"></label>
<label>Prix unitaire ({{ devise }})<input name="prix_unitaire" type="text" inputmode="decimal" value="{{ v.prix_unitaire|nombre if v.prix_unitaire else 0 }}"></label>
<button>Enregistrer</button></form>
{% else %}<p>Type : <b>{{ v.type }}</b> · Espèce : <b>{{ v.espece or '—' }}</b> · Fabricant : <b>{{ v.fabricant or '—' }}</b> ·
Doses par flacon : <b>{{ v.doses_par_flacon }}</b> · Prix unitaire : <b>{{ v.prix_unitaire|nombre }} {{ devise }}</b> · Conservation : <b>{{ v.temp_min }} à {{ v.temp_max }} °C</b></p>{% endif %}
<h2>Lots de ce vaccin</h2>
<table><tr><th>N° lot</th><th>Péremption</th><th>Jours</th><th>Disponible</th><th>Témoins</th><th>Détruites</th><th>Statut</th></tr>
{% for l in lots %}<tr><td><a href="{{ url_for('lot_detail', lot_id=l.id) }}">{{ l.numero_lot }}</a></td><td>{{ l.date_peremption }}</td>
<td>{% if l.jours < 0 %}<span class="badge b-périmé">périmé</span>{% elif l.jours <= 30 %}<span class="badge b-quarantaine">{{ l.jours }} j</span>{% else %}{{ l.jours }}{% endif %}</td>
<td>{{ l.stock }}</td><td>{{ l.temoins }}</td><td>{{ l.detruites }}</td><td><span class="badge b-{{ l.statut }}">{{ l.statut }}</span></td></tr>
{% else %}<tr><td colspan="7">Aucun lot pour ce vaccin.</td></tr>{% endfor %}</table>
<h2>Fiches techniques</h2>
{% if droits.vaccins_gerer %}<form class="card" method="post" action="{{ url_for('fiche_ajouter', vid=v.id) }}" enctype="multipart/form-data">
<label>Titre<input name="titre" maxlength="120" placeholder="Notice du fabricant"></label>
<label>Version<input name="version" maxlength="40" placeholder="v2, 2026…"></label>
<label>Fichier (PDF, Word, Excel, image · 10 Mo max)<input type="file" name="fichier" required accept=".pdf,.doc,.docx,.xls,.xlsx,.png,.jpg,.jpeg"></label>
<button>Ajouter la fiche</button></form>{% endif %}
<table><tr><th>Titre</th><th>Version</th><th>Fichier</th><th>Ajoutée le</th><th>Par</th><th></th></tr>
{% for f in fiches %}<tr><td>{{ f.titre }}</td><td>{{ f.version or '' }}</td>
<td><a href="{{ url_for('fiche_telecharger', fid=f.id) }}">{{ ic('fichier') }} {{ f.nom_original }}</a> <small>({{ (f.taille / 1024)|round(0)|int }} Ko)</small></td>
<td>{{ f.date|replace('T', ' ') }}</td><td>{{ f.username or '' }}</td>
<td>{% if droits.vaccins_gerer %}<form method="post" action="{{ url_for('fiche_supprimer', fid=f.id) }}" class="en-ligne"
onsubmit='return confirm({{ ("Supprimer la fiche « " ~ f.titre ~ " » ?")|tojson }})'><button class="petit danger">Supprimer</button></form>{% endif %}</td></tr>
{% else %}<tr><td colspan="6">Aucune fiche technique.</td></tr>{% endfor %}</table>
{% endblock %}"""

COMMANDES = """{% extends 'base.html' %}{% block content %}
<h1>Commandes clients</h1>
{% if droits.commandes_saisir %}<p><a href="{{ url_for('commande_nouvelle') }}"><button>Nouvelle commande</button></a></p>{% endif %}
<form class="filtres" method="get" action="{{ url_for('commandes') }}">
<input class="grand" name="q" value="{{ flt.q }}" placeholder="N° de commande ou client…">
<select name="statut"><option value="">Tous les statuts</option>{% for st in statuts %}<option {% if flt.statut == st %}selected{% endif %}>{{ st }}</option>{% endfor %}</select>
<label>Du<input type="date" name="du" value="{{ flt.du }}"></label>
<label>Au<input type="date" name="au" value="{{ flt.au }}"></label>
<label class="case"><input type="checkbox" name="a_traiter" value="1" {% if flt.a_traiter == '1' %}checked{% endif %}> À traiter par moi</label>
<label class="case"><input type="checkbox" name="archives" value="1" {% if flt.archives == '1' %}checked{% endif %}> Inclure les archivées</label>
<button>Filtrer</button><a class="lien-reset" href="{{ url_for('commandes') }}">Réinitialiser</a></form>
<p class="compte">{{ commandes|length }} commande(s) · total hors annulées : <b>{{ total|nombre }} {{ devise }}</b>{% if fq %} · filtres actifs{% endif %}
&nbsp;<a class="btn-export" href="{{ url_for('export_commandes', **fq) }}">{{ ic('telecharger') }} Exporter en Excel</a></p>
<table><tr><th>N°</th><th>Date</th><th>Client</th><th>Lignes</th><th>Total</th><th>Statut</th><th>Créée par</th></tr>
{% for o in commandes %}<tr><td><a href="{{ url_for('commande_detail', cmd_id=o.id) }}">{{ o.numero }}</a></td>
<td>{{ o.date|replace('T', ' ') }}</td><td>{{ o.client_nom }}{% if o.client_nature %}<br><small>{{ o.client_nature }}</small>{% endif %}</td>
<td>{{ o.nb_lignes }}</td><td>{{ o.total|nombre }} {{ devise }}</td>
<td><span class="badge b-{{ o.statut }}">{{ o.statut }}</span></td><td>{{ o.username or '' }}</td></tr>
{% else %}<tr><td colspan="7">Aucune commande ne correspond.</td></tr>{% endfor %}
</table>{% endblock %}"""

COMMANDE_FORM = """{% extends 'base.html' %}{% block content %}
{% macro ligne(l, vaccins) %}<tr class="ligne-cmd">
<td><select name="ligne_vaccin" class="l-vaccin"><option value="">— Vaccin —</option>{% for v in vaccins %}<option value="{{ v.id }}" data-prix="{{ v.dernier_prix }}" {% if l.vaccin_id|string == v.id|string %}selected{% endif %}>{{ v.nom }} (vendable : {{ v.vendable }})</option>{% endfor %}</select></td>
<td><input name="ligne_quantite" type="number" min="1" class="l-qte" placeholder="Quantité" value="{{ l.quantite|default('') }}"></td>
<td><input name="ligne_prix" type="text" inputmode="decimal" class="l-prix" placeholder="Prix unitaire" value="{{ l.prix|default('') }}"></td>
<td class="num l-montant">0</td>
<td><button type="button" class="petit danger l-suppr" title="Retirer la ligne">{{ ic('croix') }}</button></td></tr>{% endmacro %}
<h1>{% if cmd %}Modifier la commande {{ cmd.numero }}{% else %}Nouvelle commande{% endif %}</h1>
<p><a href="{{ url_for('commande_detail', cmd_id=cmd.id) if cmd else url_for('commandes') }}">{{ ic('gauche') }} Retour</a></p>
<form method="post" class="bloc-cmd">
<fieldset><legend>Client</legend>
<div class="grille"><label>Client existant<select name="client_id" id="client-select"><option value="">Nouveau client (à saisir ci-dessous)</option>
{% for c in clients %}<option value="{{ c.id }}" {% if saisie and saisie.client_id == c.id|string %}selected{% endif %}>{{ c.nom }}{% if c.nature %} ({{ c.nature }}){% endif %}</option>{% endfor %}</select></label></div>
{% set n = (saisie.nouveau if saisie else {}) or {} %}
<div id="nouveau-client" class="grille" style="margin-top:10px">
<label>Nom du nouveau client<input name="nouveau_nom" maxlength="120" value="{{ n.nom|default('') }}"></label>
<label>Nature<select name="nouveau_nature"><option value="">—</option>{% for x in natures_client %}<option {% if n.nature == x %}selected{% endif %}>{{ x }}</option>{% endfor %}</select></label>
<label>Type<select name="nouveau_type">{% for x in types_client %}<option {% if n.type == x %}selected{% endif %}>{{ x }}</option>{% endfor %}</select></label>
<label>Téléphone<input name="nouveau_telephone" maxlength="40" value="{{ n.telephone|default('') }}"></label>
<label>E-mail<input name="nouveau_email" type="email" maxlength="120" value="{{ n.email|default('') }}"></label>
<label>Adresse<input name="nouveau_adresse" maxlength="200" value="{{ n.adresse|default('') }}"></label></div></fieldset>
<fieldset><legend>Lignes de la commande</legend>
<table class="table-lignes"><thead><tr><th>Vaccin</th><th>Quantité</th><th>Prix unitaire ({{ devise }})</th><th>Montant</th><th></th></tr></thead>
<tbody id="lignes-cmd">{% if saisie and saisie.lignes %}{% for l in saisie.lignes %}{{ ligne(l, vaccins) }}{% endfor %}{% else %}{{ ligne({}, vaccins) }}{% endif %}</tbody></table>
<p><button type="button" id="ajout-ligne" class="petit">+ Ajouter une ligne</button>
&nbsp;&nbsp;<b>Total : <span id="total-cmd">0</span> {{ devise }}</b></p></fieldset>
<fieldset><legend>Livraison et remarques</legend>
<div class="grille"><label>Date de livraison souhaitée (facultatif)<input type="date" name="date_souhaitee" value="{{ saisie.date_souhaitee if saisie else '' }}"></label>
<label>Remarques<textarea name="notes" rows="2" maxlength="500">{{ saisie.notes if saisie else '' }}</textarea></label></div></fieldset>
<p><button>{% if cmd %}Enregistrer les modifications{% else %}Enregistrer la commande{% endif %}</button></p>
</form>
<template id="modele-ligne">{{ ligne({}, vaccins) }}</template>
<script>
(function(){
  var corps=document.getElementById('lignes-cmd'), modele=document.getElementById('modele-ligne');
  var sel=document.getElementById('client-select'), bloc=document.getElementById('nouveau-client');
  function nombre(v){return parseFloat(String(v).replace(',', '.').replace(/ /g,''))||0;}
  function recalc(){
    var total=0;
    corps.querySelectorAll('tr.ligne-cmd').forEach(function(tr){
      var m=nombre(tr.querySelector('.l-qte').value)*nombre(tr.querySelector('.l-prix').value);
      tr.querySelector('.l-montant').textContent=m.toLocaleString('fr-FR');
      total+=m;
    });
    document.getElementById('total-cmd').textContent=total.toLocaleString('fr-FR');
  }
  function client(){bloc.style.display=sel.value===''?'grid':'none';}
  corps.addEventListener('input',recalc);
  corps.addEventListener('change',function(e){
    if(e.target.classList.contains('l-vaccin')){
      var tr=e.target.closest('tr'), prix=tr.querySelector('.l-prix'), opt=e.target.options[e.target.selectedIndex];
      if(prix.value.trim()===''&&opt&&opt.dataset.prix){prix.value=opt.dataset.prix;}
      recalc();
    }
  });
  corps.addEventListener('click',function(e){
    if(e.target.classList.contains('l-suppr')){
      if(corps.querySelectorAll('tr.ligne-cmd').length>1){e.target.closest('tr').remove();}
      else{e.target.closest('tr').querySelectorAll('input').forEach(function(i){i.value='';});}
      recalc();
    }
  });
  document.getElementById('ajout-ligne').addEventListener('click',function(){corps.appendChild(modele.content.cloneNode(true));});
  sel.addEventListener('change',client);
  client(); recalc();
})();
</script>
{% endblock %}"""

COMMANDE = """{% extends 'base.html' %}{% block content %}
<div class="no-print actions-bon">
<button onclick="window.print()">{{ ic('imprimante') }} Imprimer</button>
<a href="{{ url_for('commandes') }}">{{ ic('gauche') }} Retour aux commandes</a>
{% if act.modifier %}<a href="{{ url_for('commande_modifier', cmd_id=cmd.id) }}"><button type="button">{{ ic('crayon') }} Modifier</button></a>{% endif %}
{% if act.annuler %}<form method="post" action="{{ url_for('commande_annuler', cmd_id=cmd.id) }}" onsubmit="return confirm('Annuler cette commande ?')"><button class="danger">Annuler la commande</button></form>{% endif %}
</div>
<div class="no-print circuit">
{% if cmd.statut == 'annulée' %}<p class="alerte-circuit">{{ ic('interdit') }} Cette commande est annulée.</p>
{% else %}<ol class="etapes">{% for e in etapes %}<li class="{{ e.etat }}"><span class="pastille">{% if e.etat == 'fait' %}{{ ic('coche') }}{% else %}{{ loop.index }}{% endif %}</span><b>{{ e.libelle }}</b><small>{{ e.acteur }}</small></li>{% endfor %}</ol>{% endif %}
<div class="panneau-actions">
{% if act.transmettre %}<form method="post" action="{{ url_for('commande_transmettre', cmd_id=cmd.id) }}" onsubmit="return confirm('Transmettre cette commande au responsable stock ? Elle ne sera plus modifiable.')"><button>{{ ic('envoyer') }} Transmettre pour contrôle</button></form>{% endif %}
{% if act.facturer %}<form method="post" action="{{ url_for('commande_facturer', cmd_id=cmd.id) }}" onsubmit="return confirm('Les quantités sont-elles contrôlées ? La facture va être générée.')"><button>{{ ic('recu') }} Contrôler et générer la facture</button></form>{% endif %}
{% if act.valider %}<form method="post" action="{{ url_for('commande_valider', cmd_id=cmd.id) }}" onsubmit="return confirm('Valider cette vente ?')"><button>{{ ic('valide') }} Valider la vente</button></form>{% endif %}
{% if act.livrer %}<form method="post" action="{{ url_for('commande_livrer', cmd_id=cmd.id) }}" onsubmit="return confirm('Livrer cette commande ? Le stock sera décrémenté (le lot qui expire en premier est livré en premier).')"><button>{{ ic('colis') }} Livrer et déstocker</button></form>{% endif %}
{% if act.archiver %}<form method="post" action="{{ url_for('commande_archiver', cmd_id=cmd.id) }}" onsubmit="return confirm('Archiver ce dossier ?')"><button>{{ ic('archive') }} Archiver le dossier</button></form>{% endif %}
{% if act.renvoyer %}<form method="post" action="{{ url_for('commande_renvoyer', cmd_id=cmd.id) }}" class="renvoi">
<input name="motif" required maxlength="300" placeholder="Motif du renvoi (obligatoire)"><button class="danger">{{ ic('retour') }} Renvoyer pour correction</button></form>{% endif %}
{% if attente %}<p class="attente">{{ ic('sablier') }} En attente de : <b>{{ attente }}</b></p>{% endif %}
</div>
</div>
<div class="bon">
<img class="filigrane" src="{{ url_for('static', filename='fond.png') }}" alt="">
<div class="bon-entete">
<img class="bon-logo" src="{{ url_for('static', filename='logo.png') }}" alt="Logo">
<div class="bon-soc"><b>{{ societe.nom }}</b>
{% if societe.adresse %}<br>{{ societe.adresse }}{% endif %}{% if societe.tel %}<br>Tél : {{ societe.tel }}{% endif %}{% if societe.email %}<br>{{ societe.email }}{% endif %}</div>
<div class="bon-titre"><h1>BON DE COMMANDE</h1><div class="num">N° {{ cmd.numero }}</div><div>Date : {{ date_cmd }}</div>
<div><span class="badge b-{{ cmd.statut }}">{{ cmd.statut }}</span></div></div>
</div>
<div class="bon-infos">
<div><h3>Client</h3><b>{{ client.nom }}</b>{% if client.nature %} <small>({{ client.nature }})</small>{% endif %}
{% if client.type %}<br>{{ client.type }}{% endif %}{% if client.telephone %}<br>Tél : {{ client.telephone }}{% endif %}
{% if client.email %}<br>{{ client.email }}{% endif %}{% if client.adresse %}<br>{{ client.adresse }}{% endif %}</div>
<div><h3>Commande</h3>Enregistrée par <b>{{ cmd.username or '—' }}</b><br>Date de livraison souhaitée : <b>{{ cmd.date_souhaitee|date_fr if cmd.date_souhaitee else '—' }}</b>
{% if cmd.notes %}<br>Remarques : {{ cmd.notes }}{% endif %}</div>
</div>
<table class="bon-table">
<tr><th>Désignation</th><th class="num">Quantité</th><th class="num">Prix unitaire ({{ devise }})</th><th class="num">Montant ({{ devise }})</th><th class="no-print">Disponibilité actuelle</th></tr>
{% for l in lignes %}<tr><td>{{ l.vaccin_nom }}<br><small>Conservation : {{ l.temp_min|nombre }} à {{ l.temp_max|nombre }} °C</small></td>
<td class="num">{{ l.quantite }}</td><td class="num">{{ l.prix_unitaire|nombre }}</td><td class="num">{{ l.montant|nombre }}</td>
<td class="no-print">{% if cmd.statut in ('enregistrée', 'transmise', 'facturée', 'validée') %}{% if l.insuffisant %}<span class="badge b-périmé">{{ ic('alerte') }} stock vendable : {{ l.vendable }}</span>{% else %}<span class="badge b-conforme">OK (vendable : {{ l.vendable }})</span>{% endif %}{% endif %}</td></tr>{% endfor %}
<tfoot><tr><td>TOTAL</td><td class="num">{{ lignes|sum(attribute='quantite') }}</td><td></td><td class="num">{{ cmd.total|nombre }} {{ devise }}</td><td class="no-print"></td></tr></tfoot>
</table>
<div class="bon-sign"><div>Le responsable vente<br><small>(nom et signature)</small></div><div>Le client<br><small>(nom, date et signature)</small></div></div>
<div class="bon-pied">{{ societe.nom }} · Commande {{ cmd.numero }} · Édité le {{ imprime_le }} par {{ session.user.username }}</div>
</div>
<div class="no-print">
<h2>Documents liés</h2>
<ul class="docs">
{% for f in factures %}<li>{{ ic('recu') }} Facture <a href="{{ url_for('facture_detail', fid=f.id) }}">{{ f.numero }}</a> <span class="badge b-{{ f.statut }}">{{ f.statut }}</span></li>{% endfor %}
{% if livraison %}<li>{{ ic('colis') }} Bordereau de livraison <a href="{{ url_for('livraison_detail', liv_id=livraison.id) }}">{{ livraison.numero }}</a></li>
{% if droits.ventes_voir %}<li>{{ ic('panier') }} <a href="{{ url_for('vente_bon', vente_id=livraison.vente_id) }}">Bon de vente n°{{ livraison.vente_id }}</a></li>{% endif %}{% endif %}
{% if not factures and not livraison %}<li>Aucun document pour l'instant : la facture est générée après le contrôle du responsable stock.</li>{% endif %}
</ul>
{% if droits.pj_commande_voir %}{% from 'pieces.html' import bloc_pieces %}
<h2>Pièces jointes (bon de livraison signé, facture signée…)</h2>
{{ bloc_pieces('commande', cmd.id, pieces, droits.pj_commande_gerer, droits.pj_commande_gerer or droits.supprimer, types_pj, TYPES_DOC) }}{% endif %}
<h2>Historique</h2>
<table><tr><th>Date</th><th>Action</th><th>Statut</th><th>Par</th><th>Motif</th></tr>
{% for h in historique %}<tr><td>{{ h.date|replace('T', ' ') }}</td><td>{{ h.action }}</td><td><span class="badge b-{{ h.statut_apres }}">{{ h.statut_apres }}</span></td>
<td>{{ h.username or '' }}{% if h.role %} <small>({{ h.role|role_lib }})</small>{% endif %}</td><td>{{ h.motif or '' }}</td></tr>{% endfor %}
</table>
</div>
{% endblock %}"""

FACTURES = """{% extends 'base.html' %}{% block content %}
<h1>Factures</h1>
<form class="filtres" method="get" action="{{ url_for('factures') }}">
<input class="grand" name="q" value="{{ flt.q }}" placeholder="N° de facture, de commande ou client…">
<select name="statut"><option value="">Tous les statuts</option><option {% if flt.statut == 'émise' %}selected{% endif %}>émise</option><option {% if flt.statut == 'annulée' %}selected{% endif %}>annulée</option></select>
<label>Du<input type="date" name="du" value="{{ flt.du }}"></label><label>Au<input type="date" name="au" value="{{ flt.au }}"></label>
<button>Filtrer</button><a class="lien-reset" href="{{ url_for('factures') }}">Réinitialiser</a></form>
<p class="compte">{{ factures|length }} facture(s) · total des factures émises : <b>{{ total|nombre }} {{ devise }}</b>{% if fq %} · filtres actifs{% endif %}
&nbsp;<a class="btn-export" href="{{ url_for('export_factures', **fq) }}">{{ ic('telecharger') }} Exporter en Excel</a></p>
<table><tr><th>N°</th><th>Date</th><th>Commande</th><th>Client</th><th>Total</th><th>Statut</th><th>Validation CSA</th></tr>
{% for f in factures %}<tr><td><a href="{{ url_for('facture_detail', fid=f.id) }}">{{ f.numero }}</a></td><td>{{ f.date|replace('T', ' ') }}</td>
<td><a href="{{ url_for('commande_detail', cmd_id=f.commande_id) }}">{{ f.commande_numero }}</a></td><td>{{ f.client_nom }}</td>
<td>{{ f.total|nombre }} {{ devise }}</td><td><span class="badge b-{{ f.statut }}">{{ f.statut }}</span></td>
<td>{% if f.validee_le %}{{ f.validee_le|dt_fr }}{% else %}<small>en attente</small>{% endif %}</td></tr>
{% else %}<tr><td colspan="7">Aucune facture ne correspond.</td></tr>{% endfor %}
</table>{% endblock %}"""

FACTURE = """{% extends 'base.html' %}{% block content %}
<div class="no-print actions-bon"><button onclick="window.print()">{{ ic('imprimante') }} Imprimer</button>
<a href="{{ url_for('commande_detail', cmd_id=f.commande_id) }}">{{ ic('gauche') }} Commande {{ f.commande_numero }}</a>
<a href="{{ url_for('factures') }}">Toutes les factures</a></div>
<div class="bon">
<img class="filigrane" src="{{ url_for('static', filename='fond.png') }}" alt="">
{% if f.statut == 'annulée' %}<div class="tampon-annule">ANNULÉE</div>{% endif %}
<div class="bon-entete">
<img class="bon-logo" src="{{ url_for('static', filename='logo.png') }}" alt="Logo">
<div class="bon-soc"><b>{{ societe.nom }}</b>
{% if societe.adresse %}<br>{{ societe.adresse }}{% endif %}{% if societe.tel %}<br>Tél : {{ societe.tel }}{% endif %}{% if societe.email %}<br>{{ societe.email }}{% endif %}</div>
<div class="bon-titre"><h1>FACTURE</h1><div class="num">N° {{ f.numero }}</div><div>Date : {{ date_f }}</div><div>Commande : {{ f.commande_numero }}</div></div>
</div>
<div class="bon-infos">
<div><h3>Facturé à</h3><b>{{ client.nom }}</b>{% if client.nature %} <small>({{ client.nature }})</small>{% endif %}
{% if client.telephone %}<br>Tél : {{ client.telephone }}{% endif %}{% if client.email %}<br>{{ client.email }}{% endif %}{% if client.adresse %}<br>{{ client.adresse }}{% endif %}</div>
<div><h3>Contrôle et validation</h3>Contrôlée par <b>{{ f.username or '—' }}</b> (responsable stock)<br>
{% if valideur %}Validée par <b>{{ valideur.username }}</b> ({{ valideur.role|role_lib }})<br><small>le {{ f.validee_le|dt_fr }}</small>{% else %}Validation CSA : <b>en attente</b>{% endif %}</div>
</div>
<table class="bon-table">
<tr><th>Désignation</th><th class="num">Quantité</th><th class="num">Prix unitaire ({{ devise }})</th><th class="num">Montant ({{ devise }})</th></tr>
{% for l in lignes %}<tr><td>{{ l.designation }}</td><td class="num">{{ l.quantite }}</td><td class="num">{{ l.prix_unitaire|nombre }}</td><td class="num">{{ l.montant|nombre }}</td></tr>{% endfor %}
<tfoot><tr><td>TOTAL À PAYER</td><td class="num">{{ lignes|sum(attribute='quantite') }}</td><td></td><td class="num">{{ f.total|nombre }} {{ devise }}</td></tr></tfoot>
</table>
<div class="bon-pied">{{ societe.nom }} · Facture {{ f.numero }} · Édité le {{ imprime_le }} par {{ session.user.username }}</div>
</div>
{% endblock %}"""

LIVRAISON = """{% extends 'base.html' %}{% block content %}
<div class="no-print actions-bon"><button onclick="window.print()">{{ ic('imprimante') }} Imprimer</button>
<a href="{{ url_for('commande_detail', cmd_id=liv.commande_id) }}">{{ ic('gauche') }} Commande {{ liv.commande_numero }}</a></div>
<div class="bon">
<img class="filigrane" src="{{ url_for('static', filename='fond.png') }}" alt="">
<div class="bon-entete">
<img class="bon-logo" src="{{ url_for('static', filename='logo.png') }}" alt="Logo">
<div class="bon-soc"><b>{{ societe.nom }}</b>
{% if societe.adresse %}<br>{{ societe.adresse }}{% endif %}{% if societe.tel %}<br>Tél : {{ societe.tel }}{% endif %}{% if societe.email %}<br>{{ societe.email }}{% endif %}</div>
<div class="bon-titre"><h1>BORDEREAU DE LIVRAISON</h1><div class="num">N° {{ liv.numero }}</div><div>Date : {{ date_liv }}</div><div>Commande : {{ liv.commande_numero }}</div></div>
</div>
<div class="bon-infos">
<div><h3>Livré à</h3><b>{{ client.nom }}</b>{% if client.nature %} <small>({{ client.nature }})</small>{% endif %}
{% if client.telephone %}<br>Tél : {{ client.telephone }}{% endif %}{% if client.adresse %}<br>{{ client.adresse }}{% endif %}</div>
<div><h3>Livraison</h3>Préparée par <b>{{ liv.username or '—' }}</b><br>Chaîne du froid à respecter pendant le transport</div>
</div>
<table class="bon-table">
<tr><th>Désignation</th><th>N° de lot</th><th>Péremption</th><th class="num">Quantité livrée</th></tr>
{% for l in lignes %}<tr><td>{{ l.vaccin }}<br><small>Conservation : {{ l.temp_min|nombre }} à {{ l.temp_max|nombre }} °C</small></td>
<td>{{ l.numero_lot }}</td><td>{{ l.date_peremption|date_fr }}</td><td class="num">{{ l.quantite }}</td></tr>{% endfor %}
<tfoot><tr><td colspan="3">TOTAL</td><td class="num">{{ lignes|sum(attribute='quantite') }}</td></tr></tfoot>
</table>
<div class="bon-sign"><div>Le responsable stock<br><small>(nom et signature)</small></div><div>Le client<br><small>(réception : nom, date et signature)</small></div></div>
<div class="bon-pied">{{ societe.nom }} · Bordereau {{ liv.numero }} · Édité le {{ imprime_le }} par {{ session.user.username }}</div>
</div>
{% endblock %}"""

PIECES = """{% macro bloc_pieces(objet, oid, pieces, peut_ajouter, peut_retirer, types, libelles) %}
<table><tr><th>Type</th><th>Titre</th><th>Fichier</th><th>Ajouté</th><th></th></tr>
{% for p in pieces %}<tr><td>{{ libelles[p.type_doc] }}</td><td>{{ p.titre }}</td>
<td><a href="{{ url_for('piece_telecharger', pid=p.id) }}">{{ ic('trombone') }} {{ p.nom_original }}</a> <small>({{ (p.taille / 1024)|round(0)|int }} Ko)</small></td>
<td>{{ p.date|dt_fr }}<br><small>{{ p.username or '' }}</small></td>
<td>{% if peut_retirer %}<form method="post" action="{{ url_for('piece_supprimer', pid=p.id) }}" class="en-ligne"
onsubmit='return confirm({{ ("Supprimer le document « " ~ p.titre ~ " » ?")|tojson }})'><button class="petit danger">Supprimer</button></form>{% endif %}</td></tr>
{% else %}<tr><td colspan="5">Aucun document joint.</td></tr>{% endfor %}</table>
{% if peut_ajouter %}<form class="card" method="post" action="{{ url_for('piece_ajouter', objet=objet, oid=oid) }}" enctype="multipart/form-data">
<label>Type de document<select name="type_doc" required>{% for t in types %}<option value="{{ t }}">{{ libelles[t] }}</option>{% endfor %}</select></label>
<label>Titre (facultatif)<input name="titre" maxlength="120" placeholder="N° de facture, référence…"></label>
<label>Fichier (PDF, Word, Excel, image · 10 Mo max)<input type="file" name="fichier" required accept=".pdf,.doc,.docx,.xls,.xlsx,.png,.jpg,.jpeg"></label>
<button>Joindre le document</button></form>{% endif %}
{% endmacro %}"""

RAPPORTS = """{% extends 'base.html' %}{% block content %}
<h1>Rapports</h1>
<p class="compte">Les rapports reprennent les données de la plateforme au moment de leur génération. Le rapport mensuel est
<b>archivé automatiquement</b> et consultable ci-dessous.</p>
<div class="cartes" style="grid-template-columns:repeat(auto-fit,minmax(min(460px,100%),1fr))">
<form class="carte c-vert rapport-carte" method="post" action="{{ url_for('rapport_mensuel_generer') }}"><div style="width:100%">
<b style="font-size:17px">{{ ic('calendrier') }} Rapport mensuel</b><small>Mouvements, livraisons, chiffre d'affaires, destructions, articles, lots à surveiller.</small>
<label>Mois<input name="mois" type="month" value="{{ mois_defaut }}" required pattern="[0-9]{4}-[0-9]{2}" placeholder="2026-10"></label>
<label class="case" style="flex-direction:row;align-items:center;gap:6px"><input type="checkbox" name="envoyer" value="1"> Envoyer aussi par e-mail aux abonnés</label>
<div class="boutons"><button>Générer et archiver (PDF)</button>
<button class="secondaire" formmethod="get" formaction="{{ url_for('rapport_excel', genre='mensuel') }}">Excel</button></div></div></form>
<form class="carte c-bleu rapport-carte" method="get" action="{{ url_for('rapport_pdf', genre='annuel') }}"><div style="width:100%">
<b style="font-size:17px">{{ ic('calendrier') }} Rapport annuel</b><small>Évolution mois par mois et totaux de l'année.</small>
<label>Année<input name="annee" type="number" min="2000" max="2100" value="{{ annee_defaut }}" required></label>
<div class="boutons"><button>PDF</button><button class="secondaire" formaction="{{ url_for('rapport_excel', genre='annuel') }}">Excel</button></div></div></form>
<form class="carte c-bleu rapport-carte" method="get" action="{{ url_for('rapport_pdf', genre='type') }}"><div style="width:100%">
<b style="font-size:17px">{{ ic('fiole') }} Rapport par type de vaccin</b><small>Viral, bactérien, vivant atténué, inactivé : stock, livraisons, destructions, chiffre d'affaires.</small>
<div class="grille"><label>Du<input type="date" name="du" value="{{ du_defaut }}" required></label><label>Au<input type="date" name="au" value="{{ au_defaut }}" required></label></div>
<div class="boutons"><button>PDF</button><button class="secondaire" formaction="{{ url_for('rapport_excel', genre='type') }}">Excel</button></div></div></form>
<form class="carte c-vert rapport-carte" method="get" action="{{ url_for('rapport_pdf', genre='global') }}"><div style="width:100%">
<b style="font-size:17px">{{ ic('graphique') }} Rapport global</b><small>Situation du jour : stocks, alertes, lots à surveiller, commandes, cumul depuis le début.</small>
<div class="boutons" style="margin-top:34px"><button>PDF</button><button class="secondaire" formaction="{{ url_for('rapport_excel', genre='global') }}">Excel</button></div></div></form>
</div>
<h2 id="archives">Archives des rapports mensuels</h2>
<input class="recherche" data-filtre="t-archives" placeholder="Rechercher (mois, année…)">
<table id="t-archives"><tr><th>Période</th><th>Rapport</th><th>Généré le</th><th>Origine</th><th>Par</th><th>Taille</th><th></th></tr>
{% for r in archives %}<tr><td>{{ r.periode }}</td><td>{{ r.titre }}</td><td>{{ r.date|dt_fr }}</td>
<td>{% if r.origine == 'auto' %}<span class="badge b-conforme">Automatique</span>{% else %}<span class="badge b-enregistrée">Manuel</span>{% endif %}</td>
<td>{{ r.username or 'système' }}</td><td>{{ (r.taille / 1024)|round(0)|int }} Ko</td>
<td><a href="{{ url_for('rapport_archive_telecharger', rid=r.id) }}">{{ ic('fichier') }} Télécharger</a>
{% if droits.email_config %}<form method="post" action="{{ url_for('rapport_archive_envoyer', rid=r.id) }}" class="en-ligne"
onsubmit="return confirm('Envoyer ce rapport par e-mail aux abonnés ?')"><button class="petit">{{ ic('mail') }} Envoyer</button></form>{% endif %}
{% if droits.supprimer %}<form method="post" action="{{ url_for('rapport_archive_supprimer', rid=r.id) }}" class="en-ligne"
onsubmit='return confirm({{ ("Supprimer le rapport « " ~ r.titre ~ " » de l'archive ?")|tojson }})'><button class="petit danger">Supprimer</button></form>{% endif %}</td></tr>
{% else %}<tr><td colspan="7">Aucun rapport archivé pour l'instant. Le rapport d'un mois est archivé automatiquement dès le mois suivant.</td></tr>{% endfor %}
</table>{% endblock %}"""

EMAIL_PARAMETRES = """{% extends 'base.html' %}{% block content %}
<h1>Notifications par e-mail</h1>
<p><a href="{{ url_for('utilisateurs') }}">{{ ic('gauche') }} Utilisateurs</a></p>
{% if not pret %}<div class="flash warning">Les e-mails sont <b>désactivés</b> ou incomplets : renseignez le serveur d'envoi ci-dessous et cochez « Activer ».</div>
{% else %}<div class="flash success">L'envoi d'e-mails est <b>actif</b> : alerte quotidienne et rapports mensuels.</div>{% endif %}
<form class="card" method="post">
<label class="case" style="grid-column:1/-1;flex-direction:row;align-items:center;gap:6px;font-size:14px"><input type="checkbox" name="email_actif" value="1" {% if p.email_actif == '1' %}checked{% endif %}> Activer l'envoi d'e-mails (alertes quotidiennes et rapports mensuels)</label>
<label>Serveur d'envoi (SMTP)<input name="smtp_hote" value="{{ p.smtp_hote }}" placeholder="mail.votre-domaine.sn"></label>
<label>Port<input name="smtp_port" value="{{ p.smtp_port }}" inputmode="numeric"></label>
<label>Sécurité<select name="smtp_securite"><option value="starttls" {% if p.smtp_securite == 'starttls' %}selected{% endif %}>STARTTLS (port 587)</option><option value="ssl" {% if p.smtp_securite == 'ssl' %}selected{% endif %}>SSL/TLS (port 465)</option><option value="aucune" {% if p.smtp_securite == 'aucune' %}selected{% endif %}>Aucune (déconseillé)</option></select></label>
<label>Utilisateur SMTP<input name="smtp_utilisateur" value="{{ p.smtp_utilisateur }}" autocomplete="off"></label>
<label>Mot de passe SMTP<input name="smtp_mot_de_passe" type="password" autocomplete="new-password" placeholder="{% if mdp_env %}fourni par l'environnement du serveur{% elif mdp_enregistre %}déjà enregistré : laisser vide pour le conserver{% endif %}"></label>
<label>Adresse d'expédition<input name="email_expediteur" type="email" value="{{ p.email_expediteur }}" placeholder="alertes@votre-domaine.sn"></label>
<label>Nom affiché<input name="email_nom" value="{{ p.email_nom }}"></label>
<label>Adresse du site (pour les liens)<input name="url_site" value="{{ p.url_site }}" placeholder="https://stock.votre-domaine.sn"></label>
<button>Enregistrer</button></form>
<p><small>Le mot de passe SMTP n'est jamais affiché. Pour plus de sécurité, il peut être fourni par la variable d'environnement
<code>UPVAC_SMTP_PASSWORD</code> du serveur : il n'est alors pas lu dans la base. Utilisez une boîte d'envoi dédiée.</small></p>
<h2>Envoyer un e-mail de test</h2>
<form method="post" action="{{ url_for('email_test') }}"><p>Destinataire : <b>{{ mon_email or '(aucune adresse : renseignez-la dans « Mon compte »)' }}</b>
&nbsp;<button {% if not pret or not mon_email %}disabled{% endif %}>Envoyer le test</button></p></form>
<h2>Qui reçoit quoi ?</h2>
<p class="compte">Alertes quotidiennes : stocks bas et lots à surveiller, pour les rôles qui consultent le stock. Rapports mensuels : pour les rôles qui consultent les rapports.
Chaque utilisateur choisit ses notifications dans « Mon compte ».</p>
<table><tr><th>Utilisateur</th><th>Rôle</th><th>E-mail</th><th>Alertes</th><th>Rapports</th></tr>
{% for a in abonnes %}<tr><td>{{ a.username }}</td><td>{{ a.role|role_lib }}</td><td>{{ a.email }}</td>
<td>{% if a.role in roles_alertes %}{{ 'oui' if a.notif_alertes else 'non' }}{% else %}<small>sans objet</small>{% endif %}</td>
<td>{% if a.role in roles_rapports %}{{ 'oui' if a.notif_rapports else 'non' }}{% else %}<small>sans objet</small>{% endif %}</td></tr>
{% else %}<tr><td colspan="5">Aucun utilisateur n'a encore d'adresse e-mail.</td></tr>{% endfor %}</table>
<h2>Journal des 50 derniers envois</h2>
<table><tr><th>Date</th><th>Destinataire</th><th>Objet</th><th>Type</th><th>Résultat</th></tr>
{% for j in journal %}<tr><td>{{ j.date|replace('T', ' ') }}</td><td>{{ j.destinataire }}</td><td>{{ j.sujet }}</td><td>{{ j.type }}</td>
<td>{% if j.statut == 'envoyé' %}<span class="badge b-conforme">envoyé</span>{% else %}<span class="badge b-périmé">erreur</span><br><small>{{ j.erreur }}</small>{% endif %}</td></tr>
{% else %}<tr><td colspan="5">Aucun e-mail envoyé pour l'instant.</td></tr>{% endfor %}</table>
{% endblock %}"""

MON_COMPTE = """{% extends 'base.html' %}{% block content %}
<h1>Mon compte</h1>
<form class="card" method="post">
<label>Nom d'utilisateur<input value="{{ u.username }}" disabled></label>
<label>Rôle<input value="{{ u.role|role_lib }}" disabled></label>
<label>Mon adresse e-mail<input name="email" type="email" maxlength="120" value="{{ u.email or '' }}" placeholder="prenom.nom@exemple.sn"></label>
{% if droits.vaccins_voir %}<label class="case" style="flex-direction:row;align-items:center;gap:6px;font-size:14px;color:#222"><input type="checkbox" name="notif_alertes" value="1" {% if u.notif_alertes %}checked{% endif %}> Recevoir l'alerte quotidienne (stocks bas, lots à surveiller)</label>{% endif %}
{% if droits.rapports_voir %}<label class="case" style="flex-direction:row;align-items:center;gap:6px;font-size:14px;color:#222"><input type="checkbox" name="notif_rapports" value="1" {% if u.notif_rapports %}checked{% endif %}> Recevoir le rapport mensuel par e-mail</label>{% endif %}
<button>Enregistrer</button></form>
{% if not pret %}<p><small>Les envois d'e-mails ne sont pas encore activés sur cette plateforme : vos choix seront pris en compte dès leur activation.</small></p>{% endif %}
<p><a href="{{ url_for('mot_de_passe') }}">Changer mon mot de passe</a></p>
{% endblock %}"""

app.jinja_loader = DictLoader({
    "base.html": BASE, "login.html": LOGIN, "index.html": INDEX, "vaccins.html": VACCINS,
    "lots.html": LOTS, "lot.html": LOT, "mouvements.html": MOUVEMENTS, "clients.html": CLIENTS,
    "donnees_essai.html": DONNEES_ESSAI, "ventes.html": VENTES, "caisse.html": CAISSE, "vente_detail.html": VENTE_DETAIL, "facture_vente.html": FACTURE_VENTE, "messages.html": MESSAGES,
    "mot_de_passe.html": MOTDEPASSE, "inventaires.html": INVENTAIRES, "inventaire.html": INVENTAIRE, "audit.html": AUDIT, "utilisateurs.html": UTILISATEURS, "vente_bon.html": VENTE_BON, "referentiels.html": REF_HUB, "email_parametres.html": EMAIL_PARAMETRES, "mon_compte.html": MON_COMPTE, "rapports.html": RAPPORTS, "pieces.html": PIECES, "commandes.html": COMMANDES, "factures.html": FACTURES, "facture.html": FACTURE, "livraison.html": LIVRAISON,
    "commande_form.html": COMMANDE_FORM, "commande.html": COMMANDE, "client_fiche.html": CLIENT_FICHE, "vaccin.html": VACCIN, "articles.html": ARTICLES, "article.html": ARTICLE,
    "ref_liste.html": REF_LISTE, "ref_edit.html": REF_EDIT,
})

if __name__ != "__main__":
    init_db()   # hébergement WSGI (PythonAnywhere, cPanel…) : crée/met à jour la base à l'import

if __name__ == "__main__":
    init_db()
    if len(sys.argv) > 1 and sys.argv[1] == "tache-quotidienne":
        # À lancer chaque jour depuis le planificateur de tâches (cron) de l'hébergeur :
        #   python app.py tache-quotidienne
        with app.test_request_context():
            rapports_crees, mails_lances = tache_quotidienne()
        print(f"Rapports mensuels archivés : {rapports_crees} · e-mails d'alerte envoyés : {mails_lances}")
        sys.exit(0)
    if len(sys.argv) > 2 and sys.argv[1] == "debloquer":
        # Secours si le seul administrateur s'est bloqué :  python app.py debloquer admin
        con = sqlite3.connect(DB_PATH)
        n = con.execute("UPDATE users SET echecs=0, bloque=0 WHERE lower(username)=lower(?)", (sys.argv[2],)).rowcount
        con.commit()
        print(f"Compte « {sys.argv[2]} » débloqué." if n else "Aucun compte à ce nom.")
        sys.exit(0)
    # Mode debug uniquement si UPVAC_DEBUG=1 (jamais en production)
    # Port d'écoute : 5000 par défaut ; changer avec  --port 8080  ou la variable UPVAC_PORT
    port = int(os.environ.get("UPVAC_PORT", "5000"))
    if "--port" in sys.argv:
        port = int(sys.argv[sys.argv.index("--port") + 1])
    if "--reseau" in sys.argv:
        # Mise en service sur le réseau local :  python app.py --reseau   (accès : http://IP-DU-PC:5000)
        if os.name == "nt":
            import ctypes   # empêche la mise en veille automatique de Windows tant que le serveur tourne
            ctypes.windll.kernel32.SetThreadExecutionState(0x80000001)
        try:
            from waitress import serve
            print(f"UPVAC en service sur le réseau, port {port} (Ctrl+C pour arrêter)")
            serve(app, host="0.0.0.0", port=port, threads=8)
        except ImportError:
            app.run(host="0.0.0.0", port=port)
        sys.exit(0)
    app.run(port=port, debug=os.environ.get("UPVAC_DEBUG") == "1")
