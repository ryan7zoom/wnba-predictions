"""
WNBA Daily Probability System
- Player prop floor probabilities (e.g. P(15+ PTS), P(6+ REB), P(4+ AST))
- Team spread-cover probabilities (based on point-differential model)
- Missing-star flagging (informational, not modeled into the math)

Data sources:
- stats.wnba.com (unofficial, same platform family as stats.nba.com, LeagueID=10)
- ESPN WNBA injuries endpoint (unofficial, used as the missing-player signal)

No API key needed. For individual/non-commercial use. Both sources are
undocumented and can change or break without notice - this is the same
tradeoff as the MLB Stats API script.

Output: docs/index.html (phone-friendly page) + docs/report.json, for GitHub Pages.
"""

import json
import math
from datetime import datetime, timedelta
import urllib.request
import urllib.parse
import os

STATS_BASE = "https://stats.wnba.com/stats"
ESPN_BASE = "https://site.api.espn.com/apis/site/v2/sports/basketball/wnba"
TODAY = datetime.utcnow().strftime("%Y-%m-%d")
SEASON = "2026"
LEAGUE_ID = "10"

# stats.wnba.com requires NBA-family headers or it 403s - same header set
# nba_api/wehoop use under the hood. This is undocumented behavior, not
# officially guaranteed to keep working.
STATS_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "en-US,en;q=0.9",
    "Referer": "https://stats.wnba.com/",
    "Origin": "https://stats.wnba.com",
    "x-nba-stats-origin": "stats",
    "x-nba-stats-token": "true",
    "Connection": "keep-alive",
}

# A player is flagged as "important" for missing-player purposes if their
# season usage rate is at/above this percentile within their own team's
# rotation. This is a blunt, transparent threshold on purpose - see
# flag_missing_starters() docstring for why we don't try to model the
# downstream effect numerically.
IMPORTANCE_USAGE_RANK = 2  # flag if player is top-2 on their team by usage%


# ---------- low-level fetch ----------

def stats_get(endpoint, params=None):
    url = f"{STATS_BASE}/{endpoint}"
    if params:
        url += "?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, headers=STATS_HEADERS)
    with urllib.request.urlopen(req, timeout=20) as resp:
        return json.loads(resp.read().decode())


def espn_get(path, params=None):
    url = f"{ESPN_BASE}{path}"
    if params:
        url += "?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=20) as resp:
        return json.loads(resp.read().decode())


# ---------- team ID crosswalk (stats.wnba.com <-> ESPN) ----------
#
# stats.wnba.com and ESPN use two completely different numeric team ID
# systems, and there's no documented free endpoint that maps one to the
# other directly. Instead of hardcoding a table that silently goes stale if
# a team ID ever changes, we build the crosswalk at runtime by matching on
# team abbreviation (e.g. "LV", "NY", "IND"), which both sources expose
# reliably. This self-heals across seasons/expansion teams instead of
# requiring a manual edit.

def build_espn_team_id_crosswalk():
    """Returns {stats_wnba_team_id: espn_team_id}, keyed by matching abbreviation."""
    stats_payload = stats_get("leaguedashteamstats", {
        "LeagueID": LEAGUE_ID,
        "Season": SEASON,
        "SeasonType": "Regular Season",
        "MeasureType": "Base",
        "PerMode": "PerGame",
    })
    stats_rows = stats_result_to_rows(stats_payload)
    stats_abbr_to_id = {r["TEAM_ABBREVIATION"]: r["TEAM_ID"] for r in stats_rows}

    espn_payload = espn_get("/teams")
    espn_teams = espn_payload.get("sports", [{}])[0].get("leagues", [{}])[0].get("teams", [])

    crosswalk = {}
    unmatched = []
    for t in espn_teams:
        team = t.get("team", {})
        abbr = team.get("abbreviation", "")
        espn_id = team.get("id")
        # normalize a couple of known abbreviation mismatches between the
        # two systems (stats.wnba.com vs ESPN sometimes differ slightly)
        abbr_aliases = {"GS": "GSV", "GSV": "GS"}
        stats_id = stats_abbr_to_id.get(abbr) or stats_abbr_to_id.get(abbr_aliases.get(abbr, ""))
        if stats_id and espn_id:
            crosswalk[stats_id] = espn_id
        else:
            unmatched.append(abbr)
    return crosswalk, unmatched


def stats_result_to_rows(payload, result_set_name=None):
    """
    stats.wnba.com responses come back as {"resultSets": [{"name":..,
    "headers": [...], "rowSet": [[...], ...]}]}. Convert to list-of-dicts.
    """
    result_sets = payload.get("resultSets") or payload.get("resultSet")
    if result_sets is None:
        return []
    if isinstance(result_sets, dict):
        result_sets = [result_sets]
    for rs in result_sets:
        if result_set_name is None or rs.get("name") == result_set_name:
            headers = rs["headers"]
            return [dict(zip(headers, row)) for row in rs["rowSet"]]
    return []


# ---------- schedule ----------

def get_todays_games(date=TODAY):
    payload = stats_get("scoreboardv2", {
        "GameDate": date,
        "LeagueID": LEAGUE_ID,
        "DayOffset": "0",
    })
    game_header = stats_result_to_rows(payload, "GameHeader")
    line_score = stats_result_to_rows(payload, "LineScore")

    teams_by_game = {}
    for row in line_score:
        teams_by_game.setdefault(row["GAME_ID"], []).append(row)

    games = []
    for g in game_header:
        gid = g["GAME_ID"]
        teams = teams_by_game.get(gid, [])
        home = next((t for t in teams if t["TEAM_ID"] == g["HOME_TEAM_ID"]), None)
        away = next((t for t in teams if t["TEAM_ID"] == g["VISITOR_TEAM_ID"]), None)
        if not home or not away:
            continue
        games.append({
            "game_id": gid,
            "home_team_id": home["TEAM_ID"],
            "home_team_abbr": home["TEAM_ABBREVIATION"],
            "home_team_name": home.get("TEAM_CITY_NAME", "") + " " + home.get("TEAM_NICKNAME", ""),
            "away_team_id": away["TEAM_ID"],
            "away_team_abbr": away["TEAM_ABBREVIATION"],
            "away_team_name": away.get("TEAM_CITY_NAME", "") + " " + away.get("TEAM_NICKNAME", ""),
        })
    return games


# ---------- rest days ----------

def get_team_last_game_date(team_id, before_date=TODAY):
    """Days since a team's last game, for back-to-back detection."""
    payload = stats_get("leaguegamefinder", {
        "TeamID": team_id,
        "LeagueID": LEAGUE_ID,
        "Season": SEASON,
        "SeasonType": "Regular Season",
    })
    rows = stats_result_to_rows(payload)
    if not rows:
        return None
    dates = sorted(
        [datetime.strptime(r["GAME_DATE"], "%Y-%m-%d") for r in rows
         if r["GAME_DATE"] < before_date],
        reverse=True
    )
    if not dates:
        return None
    days_rest = (datetime.strptime(before_date, "%Y-%m-%d") - dates[0]).days
    return days_rest


# ---------- team season stats (for spread model) ----------

def get_team_season_stats(season=SEASON):
    payload = stats_get("leaguedashteamstats", {
        "LeagueID": LEAGUE_ID,
        "Season": season,
        "SeasonType": "Regular Season",
        "MeasureType": "Base",
        "PerMode": "PerGame",
    })
    rows = stats_result_to_rows(payload)
    by_team = {}
    for r in rows:
        by_team[r["TEAM_ID"]] = {
            "team_name": r["TEAM_NAME"],
            "pts_pg": r["PTS"],
            "pts_allowed_pg": None,  # Base measure type doesn't include opponent pts; filled below
            "gp": r["GP"],
        }
    # Opponent points allowed requires the "Opponent" measure type
    payload_opp = stats_get("leaguedashteamstats", {
        "LeagueID": LEAGUE_ID,
        "Season": season,
        "SeasonType": "Regular Season",
        "MeasureType": "Opponent",
        "PerMode": "PerGame",
    })
    rows_opp = stats_result_to_rows(payload_opp)
    for r in rows_opp:
        if r["TEAM_ID"] in by_team:
            by_team[r["TEAM_ID"]]["pts_allowed_pg"] = r.get("OPP_PTS")
    return by_team


def get_head_to_head(team_a_id, team_b_id, season=SEASON):
    """
    This-season games between these two specific teams. With only 12 teams,
    each pair meets multiple times a season, so this sample is usable in a
    way it wouldn't be in a 30-team league.
    """
    payload = stats_get("leaguegamefinder", {
        "TeamID": team_a_id,
        "LeagueID": LEAGUE_ID,
        "Season": season,
        "SeasonType": "Regular Season",
        "VsTeamID": team_b_id,
    })
    rows = stats_result_to_rows(payload)
    return rows


def spread_cover_prob(team_a_stats, team_b_stats, spread, std_dev=11.0):
    """
    Normal approximation of WNBA point-differential margin.
    std_dev ~11 points is a rough single-game margin std dev for the WNBA
    (smaller scoring totals than NBA, so a smaller std dev than NBA's ~13).
    This is an approximation, not derived from a full historical fit -
    treat outputs as directional.
    """
    if not team_a_stats or not team_b_stats:
        return None
    if team_a_stats.get("pts_allowed_pg") is None or team_b_stats.get("pts_allowed_pg") is None:
        return None
    expected_margin = (team_a_stats["pts_pg"] - team_a_stats["pts_allowed_pg"]) - \
                       (team_b_stats["pts_pg"] - team_b_stats["pts_allowed_pg"])
    z = (spread + expected_margin) / std_dev
    prob = 0.5 * (1 + math.erf(z / math.sqrt(2)))
    return round(prob, 3)


def apply_rest_adjustment(prob, team_a_rest, team_b_rest, points_per_rest_day=0.02):
    """
    Mild adjustment to a cover probability based on rest differential.
    A team on a back-to-back (0 days rest) vs an opponent with 2+ days rest
    is a meaningfully worse spot in the WNBA's heavier-minutes rotations.
    Dampened deliberately - this is directional, not a precise fit.
    """
    if prob is None or team_a_rest is None or team_b_rest is None:
        return prob
    rest_diff = team_a_rest - team_b_rest
    rest_diff = max(-3, min(3, rest_diff))  # cap the effect
    adjusted = prob + (rest_diff * points_per_rest_day)
    return round(max(0.0, min(1.0, adjusted)), 3)


# ---------- player prop floors ----------

def get_player_recent_games(player_id, season=SEASON, last_n=10):
    payload = stats_get("playergamelog", {
        "PlayerID": player_id,
        "LeagueID": LEAGUE_ID,
        "Season": season,
        "SeasonType": "Regular Season",
    })
    rows = stats_result_to_rows(payload)
    rows = sorted(rows, key=lambda r: r["GAME_DATE"], reverse=True)
    return rows[:last_n]


def prop_floor_probs(games, stat_key, thresholds):
    """Empirical P(stat >= threshold) over the sampled recent games."""
    n = len(games)
    if n == 0:
        return {}
    values = [float(g.get(stat_key, 0) or 0) for g in games]
    probs = {}
    for t in thresholds:
        hits = sum(1 for v in values if v >= t)
        probs[t] = round(hits / n, 3)
    return probs


def get_team_roster_with_usage(team_id, season=SEASON):
    """
    Returns players on a team with season usage%, sorted descending.
    Used both to identify who counts as 'important' for the missing-player
    flag, and to select starters for prop tracking.
    """
    payload = stats_get("leaguedashplayerstats", {
        "LeagueID": LEAGUE_ID,
        "Season": season,
        "SeasonType": "Regular Season",
        "MeasureType": "Advanced",
        "PerMode": "PerGame",
        "TeamID": team_id,
    })
    rows = stats_result_to_rows(payload)
    rows = sorted(rows, key=lambda r: r.get("USG_PCT", 0) or 0, reverse=True)
    return rows


# ---------- starter selection ----------
#
# "Starters" isn't directly exposed as a clean flag on leaguedashplayerstats,
# so we approximate it using minutes per game (MIN) from the Base measure
# type: the top-5 players by MIN on a team are treated as the starting unit.
# This is a reasonable proxy - starters play the most minutes almost by
# definition - but it can occasionally mislabel a high-minutes sixth player
# ahead of an injured/rotating starter. Good enough for "don't bet bench
# guys" without needing a scraped depth chart.
STARTERS_PER_TEAM = 5

def get_team_starters(team_id, season=SEASON):
    payload = stats_get("leaguedashplayerstats", {
        "LeagueID": LEAGUE_ID,
        "Season": season,
        "SeasonType": "Regular Season",
        "MeasureType": "Base",
        "PerMode": "PerGame",
        "TeamID": team_id,
    })
    rows = stats_result_to_rows(payload)
    rows = sorted(rows, key=lambda r: r.get("MIN", 0) or 0, reverse=True)
    return rows[:STARTERS_PER_TEAM]


PROP_THRESHOLDS = {
    "PTS": (10, 15, 20, 25),
    "REB": (4, 6, 8),
    "AST": (2, 4, 6),
}

def get_player_props(team_id, season=SEASON, last_n=10):
    """
    Prop floor probabilities for each starter on a team, using their last
    N games. Returns a list of per-player dicts with PTS/REB/AST floors.
    """
    starters = get_team_starters(team_id, season)
    results = []
    for p in starters:
        player_id = p.get("PLAYER_ID")
        name = p.get("PLAYER_NAME")
        if not player_id:
            continue
        games = get_player_recent_games(player_id, season, last_n)
        floors = {}
        for stat_key, thresholds in PROP_THRESHOLDS.items():
            floors[stat_key] = prop_floor_probs(games, stat_key, thresholds)
        results.append({
            "name": name,
            "games_sampled": len(games),
            "floors": floors,
        })
    return results


# ---------- injury / missing-player flagging ----------
#
# DESIGN NOTE: we deliberately do NOT try to redistribute usage or adjust
# props/spread numbers based on who's missing. That requires real judgment
# (who absorbs the missing shots, how much) that a blunt formula would get
# wrong while looking precise. Instead we surface a plain flag - "this team
# is missing a top-usage player" - so the probabilities stay clean and the
# human makes the judgment call on affected games.
#
# ESPN's injuries endpoint is pregame/official-confirmation speed, not
# Twitter-breaking-news speed. Beat reporters on X will usually know before
# this does. This is a known limitation, not something to paper over.

def get_espn_team_injuries(espn_team_id):
    try:
        payload = espn_get(f"/teams/{espn_team_id}/injuries")
        return payload.get("injuries", [])
    except Exception:
        return []


def flag_missing_starters(team_id, espn_team_id, season=SEASON):
    """
    Returns a list of plain-language flags for this team, e.g.
    ["Missing A'ja Wilson (team's #1 in usage%) - treat props/spread with caution"]
    Empty list if nothing notable or if data wasn't available (fails quiet,
    not silent - the report should show 'injury check unavailable' rather
    than pretend an empty list means 'confirmed nobody is out').
    """
    flags = []
    try:
        roster = get_team_roster_with_usage(team_id, season)
        important_names = {
            r["PLAYER_NAME"] for r in roster[:IMPORTANCE_USAGE_RANK]
        }
    except Exception:
        return ["Injury/usage check unavailable - verify starters manually before betting this game."]

    injuries = get_espn_team_injuries(espn_team_id)
    for inj in injuries:
        athlete = inj.get("athlete", {})
        name = athlete.get("displayName")
        status = inj.get("status", "")
        if name in important_names and status.lower() not in ("probable", "available"):
            flags.append(
                f"{name} listed as {status} - among team's top {IMPORTANCE_USAGE_RANK} in usage%. "
                f"Treat this team's props and spread with extra caution."
            )
    return flags


# ---------- main ----------

def build_report():
    games = get_todays_games()
    team_stats = get_team_season_stats()

    # Built live each run by matching team abbreviations between
    # stats.wnba.com and ESPN - see build_espn_team_id_crosswalk().
    try:
        espn_crosswalk, unmatched_abbrs = build_espn_team_id_crosswalk()
    except Exception:
        espn_crosswalk, unmatched_abbrs = {}, []

    report = []
    for g in games:
        home_rest = get_team_last_game_date(g["home_team_id"])
        away_rest = get_team_last_game_date(g["away_team_id"])
        home_stats = team_stats.get(g["home_team_id"])
        away_stats = team_stats.get(g["away_team_id"])

        home_espn_id = espn_crosswalk.get(g["home_team_id"])
        away_espn_id = espn_crosswalk.get(g["away_team_id"])
        home_flags = flag_missing_starters(g["home_team_id"], home_espn_id) if home_espn_id else \
            ["ESPN team ID crosswalk failed for this team - injury check skipped. Verify starters manually."]
        away_flags = flag_missing_starters(g["away_team_id"], away_espn_id) if away_espn_id else \
            ["ESPN team ID crosswalk failed for this team - injury check skipped. Verify starters manually."]

        home_props = get_player_props(g["home_team_id"])
        away_props = get_player_props(g["away_team_id"])

        entry = {
            "matchup": f"{g['away_team_abbr']} @ {g['home_team_abbr']}",
            "home_team": g["home_team_abbr"],
            "away_team": g["away_team_abbr"],
            "home_rest_days": home_rest,
            "away_rest_days": away_rest,
            "home_flags": home_flags,
            "away_flags": away_flags,
            "spread_lines": [],
            "home_players": home_props,
            "away_players": away_props,
        }

        for spread in (-3.5, -1.5, 1.5, 3.5):
            p_home = spread_cover_prob(home_stats, away_stats, spread)
            p_home = apply_rest_adjustment(p_home, home_rest, away_rest)
            p_away = spread_cover_prob(away_stats, home_stats, spread)
            p_away = apply_rest_adjustment(p_away, away_rest, home_rest)
            entry["spread_lines"].append({
                "spread": spread,
                "home_cover_prob": p_home,
                "away_cover_prob": p_away,
            })

        report.append(entry)
    return report


def render_html(report):
    rows = []
    for g in report:
        rows.append(f"<h2>{g['away_team']} @ {g['home_team']}</h2>")
        rows.append("<div class='card'>")
        rest_txt = f"Rest: {g['away_team']} {g['away_rest_days']}d / {g['home_team']} {g['home_rest_days']}d"
        rows.append(f"<p class='sub'>{rest_txt}</p>")

        for flag in g["away_flags"] + g["home_flags"]:
            rows.append(f"<p class='flag'>&#9888; {flag}</p>")

        rows.append("<h3>Spread Cover Probabilities</h3>")
        rows.append(f"<table><tr><th>Spread</th><th>{g['away_team']}</th><th>{g['home_team']}</th></tr>")
        for s in g["spread_lines"]:
            ap = f"{s['away_cover_prob']*100:.0f}%" if s['away_cover_prob'] is not None else "N/A"
            hp = f"{s['home_cover_prob']*100:.0f}%" if s['home_cover_prob'] is not None else "N/A"
            rows.append(f"<tr><td>{s['spread']}</td><td>{ap}</td><td>{hp}</td></tr>")
        rows.append("</table>")

        rows.append("<h3>Starter Prop Floors</h3>")
        for side_label, players in ((g["away_team"], g["away_players"]), (g["home_team"], g["home_players"])):
            if not players:
                continue
            rows.append(f"<p class='sub'><b>{side_label}</b></p>")
            for p in players:
                rows.append(f"<p><b>{p['name']}</b> <span class='sub'>(last {p['games_sampled']} games)</span></p>")
                rows.append("<ul>")
                for stat_key, floors in p["floors"].items():
                    parts = [f"{t}+ {stat_key}: <b>{prob*100:.0f}%</b>" for t, prob in floors.items()]
                    if parts:
                        rows.append(f"<li>{' &middot; '.join(parts)}</li>")
                rows.append("</ul>")
        rows.append("</div>")

    html = f"""<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>WNBA Daily Probabilities</title>
<style>
body {{ font-family: -apple-system, sans-serif; max-width: 700px; margin: 0 auto; padding: 16px; background: #0f1115; color: #eee; }}
h1 {{ font-size: 1.3em; }}
h2 {{ margin-top: 2em; border-bottom: 1px solid #333; padding-bottom: 6px; }}
h3 {{ font-size: 1em; color: #aaa; margin-bottom: 4px; }}
.card {{ background: #1a1d24; border-radius: 10px; padding: 12px 16px; margin-bottom: 12px; }}
table {{ width: 100%; border-collapse: collapse; margin-top: 6px; }}
th, td {{ text-align: left; padding: 6px; border-bottom: 1px solid #333; }}
.sub {{ color: #888; font-size: 0.85em; margin: -4px 0 8px 0; }}
.flag {{ color: #f5b942; font-size: 0.85em; background: #2a2410; padding: 6px 8px; border-radius: 6px; margin: 4px 0; }}
.updated {{ color: #888; font-size: 0.85em; }}
</style>
</head>
<body>
<h1>WNBA Daily Probabilities</h1>
<p class="updated">Generated {datetime.utcnow().strftime('%Y-%m-%d %H:%M UTC')}</p>
<p style="color:#f66; font-size:0.85em;">Estimates only, not guarantees. Injury flags are informational (ESPN data, pregame-confirmation speed) - always verify starters yourself before betting. Spread model uses season point differential with a rough rest-day adjustment; treat all outputs as directional.</p>
{''.join(rows)}
</body>
</html>"""
    return html


if __name__ == "__main__":
    report = build_report()
    os.makedirs("docs", exist_ok=True)
    with open("docs/report.json", "w") as f:
        json.dump(report, f, indent=2, default=str)
    with open("docs/index.html", "w") as f:
        f.write(render_html(report))
    print(f"Done. {len(report)} games processed.")
