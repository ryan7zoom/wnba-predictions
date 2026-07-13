"""
WNBA Daily Probability System
- Player prop floor probabilities for starters (e.g. P(15+ PTS), P(6+ REB), P(4+ AST))
- Team spread-cover probabilities (based on point-differential model)
- Missing-star flagging (informational, not modeled into the math)

Data source: ESPN's public site.api.espn.com endpoints (unofficial/undocumented,
but widely used and reliable - same platform wehoop's espn_wnba_* functions use).

stats.wnba.com was tried first but hangs on direct API calls even from a normal
residential connection (confirmed by hand, not just from GitHub Actions), so this
version uses ESPN exclusively for everything - schedule, team stats, rosters,
player game logs, and injuries - instead of mixing two sources.

No API key needed. For individual/non-commercial use. This is still an
undocumented API and can change or break without notice.

Output: docs/index.html (phone-friendly page) + docs/report.json, for GitHub Pages.
"""

import json
import math
import time
from datetime import datetime, timedelta
import urllib.request
import urllib.parse
import urllib.error
import os

# The scoreboard's "today" is computed from local time at a fixed UTC+6
# offset, rather than raw UTC, so late-evening runs still pull the games
# still upcoming locally rather than jumping ahead to the next UTC calendar
# day. This offset is applied silently and isn't shown anywhere in the UI.
LOCAL_UTC_OFFSET_HOURS = 6

def local_now():
    return datetime.utcnow() + timedelta(hours=LOCAL_UTC_OFFSET_HOURS)

ESPN_SITE_BASE = "https://site.api.espn.com/apis/site/v2/sports/basketball/wnba"
ESPN_WEB_BASE = "https://site.web.api.espn.com/apis/site/v2/sports/basketball/wnba"
ESPN_COMMON_BASE = "https://site.web.api.espn.com/apis/common/v3/sports/basketball/wnba"
ESPN_CORE_BASE = "https://sports.core.api.espn.com/v2/sports/basketball/leagues/wnba"
TODAY = local_now().strftime("%Y%m%d")
SEASON = 2026

STARTERS_PER_TEAM = 5
PROP_GAMES_SAMPLE = 10
PROP_THRESHOLDS = {
    "points": (10, 15, 20, 25),
    "rebounds": (4, 6, 8),
    "assists": (2, 4, 6),
}

REQUEST_DELAY_SECONDS = 0.4
MAX_RETRIES = 3
RETRY_BACKOFF_SECONDS = 4


# ---------- low-level fetch ----------

def _fetch_with_retry(url, timeout=20):
    req = urllib.request.Request(url, headers={
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
        "Accept": "application/json",
    })
    last_error = None
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                data = json.loads(resp.read().decode())
            time.sleep(REQUEST_DELAY_SECONDS)
            return data
        except (urllib.error.URLError, TimeoutError, ConnectionError) as e:
            last_error = e
            if attempt < MAX_RETRIES:
                time.sleep(RETRY_BACKOFF_SECONDS * attempt)
    raise last_error


def espn_site_get(path, params=None):
    url = f"{ESPN_SITE_BASE}{path}"
    if params:
        url += "?" + urllib.parse.urlencode(params)
    return _fetch_with_retry(url)


def espn_web_get(path, params=None):
    url = f"{ESPN_WEB_BASE}{path}"
    if params:
        url += "?" + urllib.parse.urlencode(params)
    return _fetch_with_retry(url)


def espn_common_get(path, params=None):
    url = f"{ESPN_COMMON_BASE}{path}"
    if params:
        url += "?" + urllib.parse.urlencode(params)
    return _fetch_with_retry(url)


def espn_core_get(url_or_path, params=None):
    url = url_or_path if url_or_path.startswith("http") else f"{ESPN_CORE_BASE}{url_or_path}"
    if params:
        url += "?" + urllib.parse.urlencode(params)
    return _fetch_with_retry(url)


# ---------- teams ----------

def get_all_teams():
    payload = espn_site_get("/teams")
    teams_raw = payload.get("sports", [{}])[0].get("leagues", [{}])[0].get("teams", [])
    teams = []
    for t in teams_raw:
        team = t.get("team", {})
        teams.append({
            "id": team.get("id"),
            "abbreviation": team.get("abbreviation"),
            "display_name": team.get("displayName"),
        })
    return teams


# ---------- schedule ----------

def get_todays_games():
    """
    ESPN's scoreboard 'dates' parameter buckets games by ESPN's own internal
    scheduling day, which does not reliably align with any specific
    requester's local calendar day - a 7 AM local game can land under a
    different ESPN-side date than expected. Instead of trusting a single
    date guess, we pull a window (yesterday, today, tomorrow in local terms)
    and filter every event by its actual kickoff timestamp compared to the
    local "now" - keeping anything from the start of local today through
    the end of local today, plus anything already in progress.
    """
    local_today = local_now().replace(hour=0, minute=0, second=0, microsecond=0)
    local_tomorrow_start = local_today + timedelta(days=1)

    dates_to_query = [
        (local_today - timedelta(days=1)).strftime("%Y%m%d"),
        local_today.strftime("%Y%m%d"),
        local_tomorrow_start.strftime("%Y%m%d"),
    ]

    seen_event_ids = set()
    games = []
    for date_str in dates_to_query:
        try:
            payload = espn_site_get("/scoreboard", {"dates": date_str})
        except Exception:
            continue
        for e in payload.get("events", []):
            event_id = e.get("id")
            if not event_id or event_id in seen_event_ids:
                continue

            event_date_raw = e.get("date")
            if not event_date_raw:
                continue
            try:
                # ESPN event dates are UTC (Z suffix) - convert to local
                # before comparing against the local-day window.
                event_dt_utc = datetime.strptime(event_date_raw, "%Y-%m-%dT%H:%M%z")
                event_dt_local = event_dt_utc.replace(tzinfo=None) + timedelta(hours=LOCAL_UTC_OFFSET_HOURS)
            except ValueError:
                try:
                    event_dt_utc = datetime.strptime(event_date_raw, "%Y-%m-%dT%H:%M:%SZ")
                    event_dt_local = event_dt_utc + timedelta(hours=LOCAL_UTC_OFFSET_HOURS)
                except ValueError:
                    continue

            comp = e.get("competitions", [{}])[0]
            status_state = comp.get("status", {}).get("type", {}).get("state")  # 'pre','in','post'

            is_todays_local_date = local_today <= event_dt_local < local_tomorrow_start
            is_in_progress = status_state == "in"
            if not (is_todays_local_date or is_in_progress):
                continue

            competitors = comp.get("competitors", [])
            home = next((c for c in competitors if c.get("homeAway") == "home"), None)
            away = next((c for c in competitors if c.get("homeAway") == "away"), None)
            if not home or not away:
                continue

            seen_event_ids.add(event_id)
            games.append({
                "event_id": event_id,
                "home_team_id": home["team"]["id"],
                "home_team_abbr": home["team"].get("abbreviation"),
                "home_team_name": home["team"].get("displayName") or home["team"].get("abbreviation"),
                "away_team_id": away["team"]["id"],
                "away_team_abbr": away["team"].get("abbreviation"),
                "away_team_name": away["team"].get("displayName") or away["team"].get("abbreviation"),
            })
    return games


# ---------- rest days & team season stats ----------
#
# ESPN's dedicated team-statistics endpoint (sports.core.api.espn.com/.../
# statistics) is widely reported as unreliable for some sports - either
# missing fields or returning all zeros. Rather than depend on it, we derive
# points-for/points-against directly from each team's completed games via
# the schedule endpoint, which is verified-working (same call already used
# for rest-day calculation, so this doesn't add extra requests).

def get_team_schedule_events(team_id, season=SEASON):
    payload = espn_site_get(f"/teams/{team_id}/schedule", {"season": season})
    return payload.get("events", [])


def get_days_rest(team_id, before_date_str=TODAY, season=SEASON):
    events = get_team_schedule_events(team_id, season)
    dates = []
    for e in events:
        try:
            dt = datetime.strptime(e["date"][:10], "%Y-%m-%d")
        except (KeyError, ValueError):
            continue
        if dt < datetime.strptime(before_date_str, "%Y%m%d"):
            dates.append(dt)
    if not dates:
        return None
    before_date = datetime.strptime(before_date_str, "%Y%m%d")
    return (before_date - max(dates)).days


def get_team_season_stats(team_id, season=SEASON):
    """
    Points for/against per game, computed from this team's completed games
    this season (via the schedule endpoint's per-event score data), not
    from ESPN's separate team-statistics endpoint - that endpoint is known
    to be unreliable/empty for some sports. Returns None if no completed
    games are found yet.
    """
    events = get_team_schedule_events(team_id, season)
    pts_for, pts_against, games_counted = 0, 0, 0

    for e in events:
        comp = e.get("competitions", [{}])[0]
        if not comp.get("status", {}).get("type", {}).get("completed"):
            continue
        competitors = comp.get("competitors", [])
        this_team = next((c for c in competitors if str(c.get("team", {}).get("id")) == str(team_id)), None)
        opponent = next((c for c in competitors if str(c.get("team", {}).get("id")) != str(team_id)), None)
        if not this_team or not opponent:
            continue
        try:
            pts_for += int(this_team.get("score", {}).get("value", this_team.get("score")))
            pts_against += int(opponent.get("score", {}).get("value", opponent.get("score")))
            games_counted += 1
        except (TypeError, ValueError):
            continue

    if games_counted == 0:
        return None
    return {
        "pts_pg": round(pts_for / games_counted, 2),
        "pts_allowed_pg": round(pts_against / games_counted, 2),
        "games_counted": games_counted,
    }


def spread_cover_prob(team_a_stats, team_b_stats, spread, std_dev=11.0):
    """
    Normal approximation of WNBA point-differential margin.
    std_dev ~11 points is a rough single-game margin std dev for the WNBA -
    an approximation, not derived from a full historical fit. Treat outputs
    as directional, not precise.
    """
    if not team_a_stats or not team_b_stats:
        return None
    expected_margin = (team_a_stats["pts_pg"] - team_a_stats["pts_allowed_pg"]) - \
                       (team_b_stats["pts_pg"] - team_b_stats["pts_allowed_pg"])
    z = (spread + expected_margin) / std_dev
    prob = 0.5 * (1 + math.erf(z / math.sqrt(2)))
    return round(prob, 3)


def apply_rest_adjustment(prob, team_a_rest, team_b_rest, points_per_rest_day=0.02):
    """
    Mild adjustment based on rest differential. A team on a back-to-back
    (0 days rest) vs a well-rested opponent is a meaningfully worse spot in
    the WNBA's heavier-minutes rotations. Dampened deliberately - directional,
    not a precise fit.
    """
    if prob is None or team_a_rest is None or team_b_rest is None:
        return prob
    rest_diff = max(-3, min(3, team_a_rest - team_b_rest))
    adjusted = prob + (rest_diff * points_per_rest_day)
    return round(max(0.0, min(1.0, adjusted)), 3)


# ---------- roster / starters ----------
#
# Earlier version ranked starters by fetching every roster player's season
# stats individually (~15 calls per team) just to sort by minutes. That was
# too slow - with retries/delays across ~15 teams x ~15 players it blew past
# the workflow's 10-minute timeout. This version instead pulls the box score
# of the team's most recent completed game, where ESPN explicitly marks each
# player as a starter (starter: true/false) - one call per team instead of
# fifteen.

def get_team_last_completed_event_id(team_id, season=SEASON):
    payload = espn_site_get(f"/teams/{team_id}/schedule", {"season": season})
    events = payload.get("events", [])
    completed = [
        e for e in events
        if e.get("competitions", [{}])[0].get("status", {}).get("type", {}).get("completed")
    ]
    if not completed:
        return None
    completed.sort(key=lambda e: e.get("date", ""))
    return completed[-1].get("id")


def get_team_starters(team_id, season=SEASON):
    """
    Returns up to STARTERS_PER_TEAM players who started the team's most
    recent completed game, via that game's box score. Falls back to an
    empty list (rather than guessing) if no completed game is found yet
    this season or the box score doesn't include starter flags.
    """
    event_id = get_team_last_completed_event_id(team_id, season)
    if not event_id:
        return []

    try:
        payload = espn_web_get("/summary", {"event": event_id})
    except Exception:
        return []

    starters = []
    for team_box in payload.get("boxscore", {}).get("players", []):
        if str(team_box.get("team", {}).get("id")) != str(team_id):
            continue
        for stat_group in team_box.get("statistics", []):
            for athlete_entry in stat_group.get("athletes", []):
                if not athlete_entry.get("starter"):
                    continue
                athlete = athlete_entry.get("athlete", {})
                starters.append({
                    "id": athlete.get("id"),
                    "name": athlete.get("displayName") or athlete.get("fullName"),
                })
    return starters[:STARTERS_PER_TEAM]


VS_OPPONENT_MAX_AGE_DAYS = 365  # hard cutoff - per design decision, a
# meeting older than this isn't shown at all, rather than being averaged in
# alongside recent games as if it reflects current form.
VS_OPPONENT_MAX_GAMES = 2  # only the most recent 2 meetings, not a full history

def get_recent_vs_opponent(athlete_id, opponent_team_id, season=SEASON, today_str=None):
    """
    Returns up to VS_OPPONENT_MAX_GAMES most recent games this player has
    played against a specific opponent, restricted to a hard cutoff of
    VS_OPPONENT_MAX_GAMES days old. If nothing qualifies, returns an empty
    list with a reason string explaining why (no meetings at all vs. only
    stale ones) - the caller should show that reason rather than silently
    displaying nothing.
    """
    if today_str is None:
        today_str = TODAY
    today = datetime.strptime(today_str, "%Y%m%d")

    all_games = get_player_recent_gamelog(athlete_id, season, all_games=True)
    vs_this_opponent = [g for g in all_games if g.get("opponent_team_id") == str(opponent_team_id)]

    if not vs_this_opponent:
        return {"games": [], "reason": "No meetings found vs this opponent this season."}

    recent_enough = []
    for g in vs_this_opponent:
        if not g.get("date"):
            continue
        try:
            game_date = datetime.strptime(g["date"][:10], "%Y-%m-%d")
        except ValueError:
            continue
        age_days = (today - game_date).days
        if 0 <= age_days <= VS_OPPONENT_MAX_AGE_DAYS:
            recent_enough.append((age_days, g))

    if not recent_enough:
        return {"games": [], "reason": f"Only meetings vs this opponent are older than "
                                        f"{VS_OPPONENT_MAX_AGE_DAYS} days - not shown as current form."}

    recent_enough.sort(key=lambda x: x[0])  # most recent (smallest age) first
    return {"games": [g for _, g in recent_enough[:VS_OPPONENT_MAX_GAMES]], "reason": None}


# ---------- player prop floors ----------

def get_player_recent_gamelog(athlete_id, season=SEASON, last_n=PROP_GAMES_SAMPLE, all_games=False):
    """
    Returns up to last_n most recent games as dicts of:
      {"stats": {stat-name -> value}, "date": ISO date str or None,
       "opponent_team_id": str or None}

    Set all_games=True to get the full season's games (used for vs-opponent
    filtering) instead of just the last N (used for general prop floors).

    NOTE: earlier version matched category events to the top-level "events"
    dict by raw eventId, but that lookup silently failed on every game
    (likely an int-vs-string key mismatch between the two payload sections),
    producing 0 games for every player with no error. This version
    normalizes IDs to strings before matching, and also checks for stats
    embedded directly on the category event as a fallback, in case the
    separate top-level "events" section isn't populated for some athletes.
    """
    try:
        payload = espn_common_get(f"/athletes/{athlete_id}/gamelog", {"season": season})
    except Exception:
        return []

    events_section = payload.get("events", {})
    # normalize to a str-keyed dict regardless of whether ESPN returns a
    # dict-of-events or a list-of-events for this athlete
    events_by_id = {}
    if isinstance(events_section, dict):
        events_by_id = {str(k): v for k, v in events_section.items()}
    elif isinstance(events_section, list):
        events_by_id = {str(e.get("id")): e for e in events_section if e.get("id")}

    names = payload.get("names", [])  # stat column names, aligned to each event's "stats" list
    season_types = payload.get("seasonTypes", [])

    game_entries = []
    for st in season_types:
        for cat in st.get("categories", []):
            for evt in cat.get("events", []):
                gid = str(evt.get("eventId") or evt.get("id") or "")
                matched = events_by_id.get(gid, {})

                stat_values = evt.get("stats") or matched.get("stats")
                if not stat_values:
                    continue
                stat_map = dict(zip(names, stat_values))

                # Opponent/date usually live on the top-level matched event
                # object, not inside the stat-name/value pair, since those
                # are metadata rather than a stat column.
                opponent_id = None
                opponent_ref = matched.get("opponent") or evt.get("opponent")
                if isinstance(opponent_ref, dict):
                    opponent_id = str(opponent_ref.get("id")) if opponent_ref.get("id") else None
                game_date = matched.get("gameDate") or evt.get("gameDate")

                game_entries.append({
                    "sort_key": game_date or gid,
                    "date": game_date,
                    "opponent_team_id": opponent_id,
                    "stats": stat_map,
                })

    game_entries.sort(key=lambda x: str(x["sort_key"]))
    if all_games:
        return game_entries
    return game_entries[-last_n:] if game_entries else []
    games = [g[1] for g in game_entries]
    return games[-last_n:] if games else []


# ESPN's gamelog "names" labels for a given stat aren't fully confirmed
# ahead of time (undocumented API) - "points" and "assists" matched
# correctly, but "rebounds" was returning 0% across the board, meaning the
# real label differs (likely "REB", "rebounds" split into
# offensive/defensive, or a different casing). Rather than guess a single
# label a third time, we try a list of plausible aliases per stat, and for
# rebounds specifically, also try summing offensive + defensive rebound
# fields in case ESPN doesn't expose a combined total.
STAT_KEY_ALIASES = {
    "points": ["points", "PTS", "pts"],
    "rebounds": ["rebounds", "REB", "reb", "totalRebounds"],
    "assists": ["assists", "AST", "ast"],
    "minutes": ["minutes", "MIN", "min"],
}
REBOUND_SPLIT_ALIASES = [
    ("offensiveRebounds", "defensiveRebounds"),
    ("OREB", "DREB"),
    ("oreb", "dreb"),
]

MINUTES_CHANGE_THRESHOLD = 0.15  # flag if most recent game's minutes are
# 15%+ above OR below this player's own average over the sampled games -
# a real, honestly-derived signal (not a proxy for usage%, which needs
# possession data we don't have access to for free).

def detect_minutes_change(games):
    """
    Compares the most recent game's minutes to this player's own average
    over the sampled games (excluding that most recent game, so it's not
    comparing a game to an average that includes itself). Returns a dict
    with the recent/average minutes and whether it's a notable increase
    or decrease, or None if minutes data wasn't found or there's too
    little history to compare against.
    """
    if len(games) < 2:
        return None
    minutes_vals = []
    for g in games:
        v = _extract_stat_value(g, "minutes")
        if v is not None:
            minutes_vals.append(v)
    if len(minutes_vals) < 2:
        return None

    most_recent = minutes_vals[-1]
    prior_avg = sum(minutes_vals[:-1]) / len(minutes_vals[:-1])
    if prior_avg == 0:
        return None

    pct_change = (most_recent - prior_avg) / prior_avg
    return {
        "most_recent_minutes": round(most_recent, 1),
        "prior_avg_minutes": round(prior_avg, 1),
        "pct_change": round(pct_change, 3),
        "is_notable_bump": pct_change >= MINUTES_CHANGE_THRESHOLD,
        "is_notable_drop": pct_change <= -MINUTES_CHANGE_THRESHOLD,
    }



def _extract_stat_value(game_entry, stat_key):
    """
    Looks up a stat's value in a single game entry's stats dict, trying
    known aliases first, then falling back to summing an offensive+defensive
    rebound split if the stat is rebounds and no combined field was found.
    Returns None (not 0) if nothing matched, so callers can distinguish
    "genuinely zero rebounds that game" from "we never found the field."
    """
    stats = game_entry.get("stats", {})
    for alias in STAT_KEY_ALIASES.get(stat_key, [stat_key]):
        if alias in stats:
            try:
                return float(stats[alias])
            except (TypeError, ValueError):
                continue
    if stat_key == "rebounds":
        for off_key, def_key in REBOUND_SPLIT_ALIASES:
            if off_key in stats and def_key in stats:
                try:
                    return float(stats[off_key]) + float(stats[def_key])
                except (TypeError, ValueError):
                    continue
    return None


def prop_floor_probs(games, stat_key, thresholds):
    """Empirical P(stat >= threshold) over the sampled recent games."""
    n = len(games)
    if n == 0:
        return {}
    values = []
    matched_any = False
    for g in games:
        v = _extract_stat_value(g, stat_key)
        if v is not None:
            matched_any = True
            values.append(v)
        else:
            values.append(0.0)
    if not matched_any:
        # None of the alias attempts found this stat anywhere in the
        # sampled games - return empty rather than a confident-looking 0%
        # for every threshold, since that's a data problem, not a real floor.
        return {}
    probs = {}
    for t in thresholds:
        hits = sum(1 for v in values if v >= t)
        probs[t] = round(hits / n, 3)
    return probs


_gamelog_debug_printed = False
_names_debug_printed = False

def get_player_props(team_id, opponent_team_id=None, season=SEASON, team_injured_names=None):
    global _gamelog_debug_printed, _names_debug_printed
    starters = get_team_starters(team_id, season)
    team_injured_names = team_injured_names or set()
    results = []
    for p in starters:
        games = get_player_recent_gamelog(p["id"], season)

        if games and not _names_debug_printed:
            _names_debug_printed = True
            print(f"DEBUG sample game entry for {p['name']}'s most recent game: {games[-1]}")

        if len(games) == 0 and not _gamelog_debug_printed:
            _gamelog_debug_printed = True
            try:
                raw = espn_common_get(f"/athletes/{p['id']}/gamelog", {"season": season})
                print(f"DEBUG gamelog for {p['name']} (id={p['id']}) returned 0 games. "
                      f"Top-level keys: {list(raw.keys())}")
                if raw.get("seasonTypes"):
                    st0 = raw["seasonTypes"][0]
                    print(f"DEBUG seasonTypes[0] keys: {list(st0.keys())}")
                    if st0.get("categories"):
                        cat0 = st0["categories"][0]
                        print(f"DEBUG categories[0] keys: {list(cat0.keys())}")
                        if cat0.get("events"):
                            print(f"DEBUG first event sample: {cat0['events'][0]}")
            except Exception as debug_err:
                print(f"DEBUG gamelog fetch itself failed: {debug_err}")

        floors = {}
        for stat_key, thresholds in PROP_THRESHOLDS.items():
            floors[stat_key] = prop_floor_probs(games, stat_key, thresholds)

        vs_opponent = None
        if opponent_team_id:
            vs_opponent = get_recent_vs_opponent(p["id"], opponent_team_id, season)

        minutes_change = detect_minutes_change(games)
        # Only claim a connection to a specific teammate's absence when that
        # teammate is ALSO in this game's confirmed injury flags - otherwise
        # we just report the minutes change itself without inventing a cause.
        minutes_note = None
        if minutes_change and minutes_change["is_notable_bump"]:
            if team_injured_names:
                minutes_note = (
                    f"Playing more than usual lately ({minutes_change['most_recent_minutes']} min "
                    f"vs {minutes_change['prior_avg_minutes']} min average) - team is missing "
                    f"{', '.join(sorted(team_injured_names))}, which may explain the increased role."
                )
            else:
                minutes_note = (
                    f"Playing more than usual lately ({minutes_change['most_recent_minutes']} min "
                    f"vs {minutes_change['prior_avg_minutes']} min average) - reason unconfirmed, "
                    f"worth checking team news before relying on the floors above."
                )
        elif minutes_change and minutes_change["is_notable_drop"]:
            minutes_note = (
                f"Playing less than usual lately ({minutes_change['most_recent_minutes']} min "
                f"vs {minutes_change['prior_avg_minutes']} min average) - could be a minor injury, "
                f"rotation change, or blowout garbage time. Worth checking team news before "
                f"relying on the floors above, since a reduced role lowers them."
            )

        results.append({
            "name": p["name"],
            "games_sampled": len(games),
            "floors": floors,
            "vs_opponent": vs_opponent,
            "minutes_note": minutes_note,
        })
    return results


# ---------- injury / missing-player flagging ----------
#
# DESIGN NOTE: we deliberately do NOT try to redistribute usage or adjust
# props/spread numbers based on who's missing. That requires real judgment
# (who absorbs the missing shots, how much) that a blunt formula would get
# wrong while looking precise. Instead we surface a plain flag - "this team
# is missing a top scorer" - so the probabilities stay clean and the human
# makes the judgment call on affected games.
#
# ESPN's injuries endpoint is pregame/official-confirmation speed, not
# Twitter-breaking-news speed. Beat reporters on X will usually know before
# this does. This is a known limitation, not something to paper over.

def get_team_injuries(team_id):
    try:
        payload = espn_site_get(f"/teams/{team_id}/injuries")
        return payload.get("injuries", [])
    except Exception:
        return None  # None = check failed; [] = check succeeded, nobody out


def flag_missing_starters(team_id, season=SEASON):
    """Returns (flags, injured_starter_names) - the names set lets other
    parts of the report (like the minutes-bump note) reference confirmed
    injuries without duplicating the injury lookup."""
    starters = get_team_starters(team_id, season)
    if not starters:
        return (["Starter lineup unavailable (no completed game yet this season, or box score data missing) - verify starters manually before betting this game."], set())
    starter_names = {p["name"] for p in starters}

    injuries = get_team_injuries(team_id)
    if injuries is None:
        return (["Injury check unavailable - verify starters manually before betting this game."], set())

    flags = []
    injured_starter_names = set()
    for inj in injuries:
        athlete = inj.get("athlete", {})
        name = athlete.get("displayName") or athlete.get("fullName")
        status = inj.get("status", "")
        if name in starter_names and status.lower() not in ("probable", "active", "available"):
            flags.append(
                f"{name} listed as {status} - started the team's most recent game. "
                f"Treat this team's props and spread with extra caution."
            )
            injured_starter_names.add(name)
    return (flags, injured_starter_names)


# ---------- main ----------

def build_report():
    games = get_todays_games()
    report = []

    for g in games:
        home_id, away_id = g["home_team_id"], g["away_team_id"]

        home_rest = get_days_rest(home_id)
        away_rest = get_days_rest(away_id)
        home_stats = get_team_season_stats(home_id)
        away_stats = get_team_season_stats(away_id)

        home_flags, home_injured_names = flag_missing_starters(home_id)
        away_flags, away_injured_names = flag_missing_starters(away_id)

        home_props = get_player_props(home_id, opponent_team_id=away_id, team_injured_names=home_injured_names)
        away_props = get_player_props(away_id, opponent_team_id=home_id, team_injured_names=away_injured_names)

        entry = {
            "matchup": f"{g['away_team_name']} @ {g['home_team_name']}",
            "home_team": g["home_team_abbr"],
            "away_team": g["away_team_abbr"],
            "home_team_full": g["home_team_name"],
            "away_team_full": g["away_team_name"],
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


def format_display_date(date_input):
    """
    Formats a date as 'dd MMM yy' (e.g. '12 Dec 25') for display, per
    requested UI convention. Accepts either a datetime object or an
    ISO-ish date string (YYYY-MM-DD...). Returns the original string
    unchanged if it can't be parsed, rather than failing the whole render.
    """
    if isinstance(date_input, datetime):
        dt = date_input
    else:
        try:
            dt = datetime.strptime(str(date_input)[:10], "%Y-%m-%d")
        except (ValueError, TypeError):
            return str(date_input)
    return dt.strftime("%d %b %y")


def render_html(report):
    rows = []
    for g in report:
        rows.append(f"<h2>{g['away_team_full']} @ {g['home_team_full']}</h2>")
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

                vs_opp = p.get("vs_opponent")
                if vs_opp:
                    if vs_opp["games"]:
                        lines = []
                        for g_entry in vs_opp["games"]:
                            date_str = format_display_date(g_entry.get("date"))
                            pts = _extract_stat_value(g_entry, "points")
                            reb = _extract_stat_value(g_entry, "rebounds")
                            ast = _extract_stat_value(g_entry, "assists")
                            pts_s = f"{pts:.0f}" if pts is not None else "?"
                            reb_s = f"{reb:.0f}" if reb is not None else "?"
                            ast_s = f"{ast:.0f}" if ast is not None else "?"
                            lines.append(f"{date_str}: {pts_s} pts / {reb_s} reb / {ast_s} ast")
                        rows.append(f"<p class='sub'>vs this opponent (last {len(vs_opp['games'])}, "
                                    f"within {VS_OPPONENT_MAX_AGE_DAYS} days): {' | '.join(lines)}</p>")
                    else:
                        rows.append(f"<p class='sub'>vs this opponent: {vs_opp['reason']}</p>")

                if p.get("minutes_note"):
                    rows.append(f"<p class='flag'>&#9888; {p['minutes_note']}</p>")
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
<p class="updated">Generated {format_display_date(local_now())} {local_now().strftime('%H:%M')}</p>
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

    # Quick self-check printed to the Actions log, so a broken data source
    # is visible immediately instead of only showing up as an empty-looking
    # page later.
    games_with_spread_data = sum(
        1 for g in report if any(s["home_cover_prob"] is not None for s in g["spread_lines"])
    )
    games_with_props = sum(1 for g in report if g["home_players"] or g["away_players"])
    print(f"Done. {len(report)} games processed.")
    print(f"  Spread data available for {games_with_spread_data}/{len(report)} games.")
    print(f"  Player props available for {games_with_props}/{len(report)} games.")
    if len(report) > 0 and games_with_spread_data == 0:
        print("  WARNING: no spread data on any game - check get_team_season_stats() field names.")
    if len(report) > 0 and games_with_props == 0:
        print("  WARNING: no player props on any game - check get_player_recent_gamelog() field names.")
