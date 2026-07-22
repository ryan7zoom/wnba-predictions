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
print(f"DEBUG local_now={local_now()} TODAY={TODAY}")
SEASON = 2026

STARTERS_PER_TEAM = 5
PROP_GAMES_SAMPLE = 10
# Only used now as the list of stat keys to compute. The actual threshold
# values are no longer fixed - prop_floor_probs() builds a band centered on
# each player's own recent average (see THRESHOLD_BAND_BELOW/ABOVE above),
# so a real bookmaker line is far more likely to exist for whatever gets
# picked here, instead of a blanket 10+/15+/20+/25+ that's trivial for a
# 25-PPG star and irrelevant for a 6-PPG bench piece.
PROP_THRESHOLDS = {
    "points": None,
    "rebounds": None,
    "assists": None,
    "threes": None,
    "pra": None,
}

# The "medium" threshold per stat is used for the Top Performers ranking -
# not the easiest bar (near-certain, uninformative, ~1.01-odds territory)
# and not the hardest (~coinflip territory), but the one in between that
# still says something real about a player's floor. For a 4-tier stat
# (points) that's index 1 (15+); for a 3-tier stat that's index 1 (the
# middle value) too.
MEDIUM_THRESHOLD_INDEX = 1

TOP_PERFORMERS_COUNT = 10
TOP_PERFORMERS_MIN_GAMES = 5  # don't rank anyone with too small a sample

CONFIDENCE_THRESHOLD = 0.80  # only picks at/above this become eligible for bet builders
TOP_PICKS_LIMIT = 8


POINTS_STAT_KEY = "points"
TREND_ONLY_STAT_KEYS = ("rebounds", "assists", "pra", "threes")

# Weighting for the points ranking score below. Own hit-rate is the
# foundation (a player has to actually be hitting the line); head-to-head
# and opponent-defense are real but secondary signals layered on top, not
# separate rankings of their own - a player with a great hit-rate but a
# tough opponent should still generally outrank a mediocre hit-rate against
# a weak opponent, so these are additive nudges (fractions of the hit-rate
# scale), not multipliers that could flip the order entirely.
POINTS_H2H_BONUS = 0.05          # hit the line in her most recent head-to-head
POINTS_OPP_ALLOWING_BONUS = 0.05  # opponent's recent points-allowed trend is up (easier matchup)
POINTS_OPP_WEAK_DEFENSE_BONUS = 0.05  # opponent ranks in the bottom half of the league defensively

# Same idea, applied to rebounds/assists/pra now that they have real
# opponent-allowed and own-offense data behind them instead of being
# footnotes. Kept at the same weight as the points bonuses for consistency.
TREND_H2H_BONUS = 0.05
TREND_OPP_ALLOWING_BONUS = 0.05
TREND_OWN_OFFENSE_BONUS = 0.05

def _points_score_for_player(p, side_label, side_full, opponent_full, g):
    """
    Builds the 4-factor points candidate for a single player, or None if
    she doesn't have a qualifying points floor. The 4 factors:
      1. Her own hit-rate on the medium points threshold (the base score)
      2. Whether she hit that same line in her most recent head-to-head
      3. Whether the opponent has recently been allowing more points than
         their season average (a trending-easier matchup)
      4. Whether the opponent ranks in the bottom half of the league on
         defense over the last 10 games (a weak-defense matchup, not just
         a recent blip)
    Only points gets this treatment - rebounds/assists/threes don't have
    opponent-allowed data behind them (see TREND_ONLY_STAT_KEYS below).
    """
    floors = p["floors"].get(POINTS_STAT_KEY, {})
    if not floors:
        return None
    sorted_thresholds = sorted(floors.keys())
    idx = min(MEDIUM_THRESHOLD_INDEX, len(sorted_thresholds) - 1)
    medium_t = sorted_thresholds[idx]
    hit_rate = floors.get(medium_t)
    if hit_rate is None:
        return None

    score = hit_rate
    reasons = []

    # Factor 2: head-to-head
    h2h_hit = False
    vs_opp = p.get("vs_opponent")
    if vs_opp and vs_opp.get("games"):
        most_recent_vs_opp = vs_opp["games"][-1]
        v = _extract_stat_value(most_recent_vs_opp, POINTS_STAT_KEY)
        if v is not None and v >= medium_t:
            h2h_hit = True
            score += POINTS_H2H_BONUS
            n_h2h = len(vs_opp["games"])
            reasons.append(f"hit {medium_t}+ points in her last {'meeting' if n_h2h == 1 else f'{n_h2h} meetings'} vs {opponent_full}")

    # Factor 3: opponent recently allowing more points than their own season average
    opp_allowing_more = False
    recent_def = p.get("opponent_recent_defense")
    if recent_def and recent_def["pct_change"] > 0:
        opp_allowing_more = True
        score += POINTS_OPP_ALLOWING_BONUS
        reasons.append(f"{opponent_full} has allowed {recent_def['pct_change'] * 100:.0f}% more points than "
                        f"their season average over their last {recent_def['games_counted']} games")

    # Factor 4: opponent's league-wide defensive rank, bottom half = weak D
    opp_weak_defense = False
    opp_rank = p.get("opponent_league_rank")
    if opp_rank and opp_rank["teams_ranked"] >= 2:
        if opp_rank["def_rank"] > (opp_rank["teams_ranked"] + 1) / 2:
            opp_weak_defense = True
            score += POINTS_OPP_WEAK_DEFENSE_BONUS
            reasons.append(f"{opponent_full} ranks #{opp_rank['def_rank']} of {opp_rank['teams_ranked']} in defense "
                            f"over the last 10 games")

    return {
        "name": p["name"],
        "team": side_full,
        "matchup": f"{side_full} vs {opponent_full}",
        "opponent_full": opponent_full,
        "stat_key": POINTS_STAT_KEY,
        "threshold": medium_t,
        "hit_rate": hit_rate,
        "score": round(score, 4),
        "games_sampled": p["games_sampled"],
        "vs_opp_aligned": h2h_hit,
        "opp_allowing_more": opp_allowing_more,
        "opp_weak_defense": opp_weak_defense,
        "reasons": reasons,
    }


def build_top_points_performers(report):
    """
    Points-only Top Performers list, scored on all 4 factors (own hit-rate,
    head-to-head, opponent recent points-allowed trend, opponent
    league-wide defensive rank) - see _points_score_for_player. This is
    the strongest section since points is the only stat with real
    opponent-defense data behind it.
    """
    candidates = []
    for g in report:
        for side_label, side_full, opponent_full, players in (
            (g["away_team"], g["away_team_full"], g["home_team_full"], g["away_players"]),
            (g["home_team"], g["home_team_full"], g["away_team_full"], g["home_players"]),
        ):
            for p in players:
                if p["games_sampled"] < TOP_PERFORMERS_MIN_GAMES:
                    continue
                candidate = _points_score_for_player(p, side_label, side_full, opponent_full, g)
                if candidate:
                    candidates.append(candidate)

    candidates.sort(key=lambda c: c["score"], reverse=True)
    return candidates[:TOP_PERFORMERS_COUNT]


def build_top_trend_performers(report):
    """
    Rebounds/assists/PRA/threes Top Performers list. Now scored the same
    way as points: her own hit-rate is the foundation, with real bonuses
    layered on top for:
      - opponent allowing more of this stat than usual lately (only for
        rebounds/assists/pra, which now have opponent-allowed data - see
        get_team_recent_allowed_reb_ast)
      - her own team's offense trending up recently (own_recent_offense)
      - hitting the same mark in her most recent head-to-head
    Threes still only gets the hit-rate + head-to-head factors, since
    there's no reliable opponent-allowed-threes signal being tracked.

    If the opponent's allowed-stat number is flagged volatile (swings a
    lot game to game - see ALLOWED_STAT_VOLATILITY_RATIO), the bonus is
    NOT applied even if the average looks favorable, since a volatile
    average isn't a trustworthy signal for any single game.
    """
    candidates = []
    for g in report:
        for side_label, side_full, opponent_full, players in (
            (g["away_team"], g["away_team_full"], g["home_team_full"], g["away_players"]),
            (g["home_team"], g["home_team_full"], g["away_team_full"], g["home_players"]),
        ):
            for p in players:
                if p["games_sampled"] < TOP_PERFORMERS_MIN_GAMES:
                    continue
                best_for_player = None
                for stat_key in TREND_ONLY_STAT_KEYS:
                    floors = p["floors"].get(stat_key, {})
                    if not floors:
                        continue
                    sorted_thresholds = sorted(floors.keys())
                    idx = min(MEDIUM_THRESHOLD_INDEX, len(sorted_thresholds) - 1)
                    medium_t = sorted_thresholds[idx]
                    hit_rate = floors.get(medium_t)
                    if hit_rate is None:
                        continue

                    score = hit_rate
                    reasons = []

                    # Opponent-allowed bonus (rebounds/assists/pra only)
                    opp_allowed_more = False
                    allowed_note = p.get("opponent_allowed_reb_ast")
                    if allowed_note and stat_key in ("rebounds", "assists", "pra"):
                        if stat_key == "rebounds" and not allowed_note["rebounds_volatile"]:
                            opp_allowed_more = True
                        elif stat_key == "assists" and not allowed_note["assists_volatile"]:
                            opp_allowed_more = True
                        elif stat_key == "pra" and not allowed_note["rebounds_volatile"] and not allowed_note["assists_volatile"]:
                            opp_allowed_more = True
                        if opp_allowed_more:
                            score += TREND_OPP_ALLOWING_BONUS
                            reasons.append(
                                f"{opponent_full} has been allowing {allowed_note['rebounds_allowed_pg']} reb "
                                f"and {allowed_note['assists_allowed_pg']} ast per game lately"
                            )

                    # Own-team offense trending up (applies to all trend stats)
                    own_off = p.get("own_recent_offense")
                    if own_off and own_off.get("is_notable") and own_off["pct_change"] > 0:
                        score += TREND_OWN_OFFENSE_BONUS
                        reasons.append(
                            f"{side_full} has scored {own_off['pct_change']*100:.0f}% more than their season "
                            f"average over their last {own_off['games_counted']} games"
                        )

                    if best_for_player is None or score > best_for_player["score"]:
                        best_for_player = {
                            "stat_key": stat_key,
                            "threshold": medium_t,
                            "hit_rate": hit_rate,
                            "score": round(score, 4),
                            "reasons": reasons,
                        }
                if not best_for_player:
                    continue

                vs_opp_aligned = False
                vs_opp = p.get("vs_opponent")
                if vs_opp and vs_opp.get("games"):
                    most_recent_vs_opp = vs_opp["games"][-1]
                    v = _extract_stat_value(most_recent_vs_opp, best_for_player["stat_key"])
                    if v is not None and v >= best_for_player["threshold"]:
                        vs_opp_aligned = True
                        best_for_player["score"] += TREND_H2H_BONUS
                        n_h2h = len(vs_opp["games"])
                        best_for_player["reasons"].append(
                            f"hit {best_for_player['threshold']}+ {STAT_DISPLAY_NAMES.get(best_for_player['stat_key'])} "
                            f"in her last {'meeting' if n_h2h == 1 else f'{n_h2h} meetings'} vs {opponent_full}"
                        )

                candidates.append({
                    "name": p["name"],
                    "team": side_full,
                    "matchup": f"{side_full} vs {opponent_full}",
                    "opponent_full": opponent_full,
                    "stat_key": best_for_player["stat_key"],
                    "threshold": best_for_player["threshold"],
                    "hit_rate": best_for_player["hit_rate"],
                    "score": best_for_player["score"],
                    "games_sampled": p["games_sampled"],
                    "vs_opp_aligned": vs_opp_aligned,
                    "reasons": best_for_player["reasons"],
                })

    candidates.sort(key=lambda c: c["score"], reverse=True)
    return candidates[:TOP_PERFORMERS_COUNT]



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

    date_a = (local_today - timedelta(days=1)).strftime("%Y%m%d")
    date_b = local_today.strftime("%Y%m%d")
    date_c = local_tomorrow_start.strftime("%Y%m%d")
    dates_to_query = [date_a, date_b, date_c]

    seen_event_ids = set()
    games = []
    all_events = []
    any_events_seen = False
    for date_str in dates_to_query:
        try:
            payload = espn_site_get("/scoreboard", {"dates": date_str})
        except Exception as e:
            print(f"WARNING: scoreboard fetch failed for dates={date_str}: {e}")
            continue
        events = payload.get("events", [])
        print(f"DEBUG single-date query dates={date_str} -> {len(events)} events")
        if events:
            any_events_seen = True
        all_events.extend(events)

    # ESPN's single-date scoreboard bucket can come back HTTP 200 with an
    # empty events list even on a date that genuinely has games (a known
    # quirk of this undocumented endpoint - it's not a network/auth error,
    # so the try/except above never catches it). If ALL three single-date
    # calls came back empty, fall back to the range-query syntax
    # (dates=YYYYMMDD-YYYYMMDD), which ESPN's own scoreboard UI uses
    # internally and doesn't appear to hit the same empty-bucket issue.
    if not any_events_seen:
        range_param = f"{date_a}-{date_c}"
        print(f"WARNING: all single-date queries returned 0 events - retrying with range dates={range_param}")
        try:
            range_payload = espn_site_get("/scoreboard", {"dates": range_param})
            range_events = range_payload.get("events", [])
            print(f"DEBUG range query dates={range_param} -> {len(range_events)} events")
            all_events.extend(range_events)
        except Exception as e:
            print(f"WARNING: range scoreboard fetch failed for dates={range_param}: {e}")

    for e in all_events:
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
            print(f"DEBUG get_todays_games returning {len(games)} games: {[g['away_team_abbr']+'@'+g['home_team_abbr'] for g in games]}")
    return games


# ---------- rest days & team season stats ----------
#
# ESPN's dedicated team-statistics endpoint (sports.core.api.espn.com/.../
# statistics) is widely reported as unreliable for some sports - either
# missing fields or returning all zeros. Rather than depend on it, we derive
# points-for/points-against directly from each team's completed games via
# the schedule endpoint, which is verified-working (same call already used
# for rest-day calculation, so this doesn't add extra requests).

_SCHEDULE_CACHE = {}  # team_id -> events list, cleared per run via clear_schedule_cache()

def get_team_schedule_events(team_id, season=SEASON):
    cache_key = (str(team_id), season)
    if cache_key in _SCHEDULE_CACHE:
        return _SCHEDULE_CACHE[cache_key]
    payload = espn_site_get(f"/teams/{team_id}/schedule", {"season": season})
    events = payload.get("events", [])
    _SCHEDULE_CACHE[cache_key] = events
    return events


def clear_schedule_cache():
    _SCHEDULE_CACHE.clear()


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


RECENT_DEFENSE_GAMES_SAMPLE = 5
RECENT_DEFENSE_NOTABLE_PCT = 0.10  # flag when last-5 points-allowed is
# 10%+ above (or below) the season average - same "plain fact, not a
# weighted probability boost" pattern as the minutes-bump note.

def get_team_recent_defense(team_id, season=SEASON):
    """
    Points allowed over this team's last RECENT_DEFENSE_GAMES_SAMPLE
    completed games, using the same schedule-events source as
    get_team_season_stats (no new requests - this is a filtering change,
    not a new data source). Returns None if there aren't enough completed
    games yet this season.
    """
    events = get_team_schedule_events(team_id, season)
    completed = []
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
            pts_against = int(opponent.get("score", {}).get("value", opponent.get("score")))
        except (TypeError, ValueError):
            continue
        completed.append({"date": e.get("date", ""), "pts_against": pts_against})

    if not completed:
        return None
    completed.sort(key=lambda x: x["date"])
    last_n = completed[-RECENT_DEFENSE_GAMES_SAMPLE:]
    if not last_n:
        return None

    recent_avg = sum(g["pts_against"] for g in last_n) / len(last_n)
    return {
        "recent_pts_allowed_pg": round(recent_avg, 1),
        "games_counted": len(last_n),
    }


def build_recent_defense_note(recent_defense, season_stats, opponent_team_full=None):
    """
    Combines a team's recent (last-5) points-allowed with their season
    average into a display-ready dict: both numbers, plus whether the
    deviation is notable (10%+). Returns None if either input is missing,
    or if there aren't enough games to make the comparison meaningful.
    """
    if not recent_defense or not season_stats:
        return None
    if recent_defense["games_counted"] < 2:
        return None

    recent = recent_defense["recent_pts_allowed_pg"]
    season_avg = season_stats["pts_allowed_pg"]
    if season_avg == 0:
        return None

    pct_change = (recent - season_avg) / season_avg
    return {
        "opponent_team_full": opponent_team_full,
        "recent_pts_allowed_pg": recent,
        "season_pts_allowed_pg": season_avg,
        "games_counted": recent_defense["games_counted"],
        "pct_change": round(pct_change, 3),
        "is_notable": abs(pct_change) >= RECENT_DEFENSE_NOTABLE_PCT,
    }


# ---------- team's own recent scoring (mirror of recent defense above) ----------
#
# Same rationale as get_team_recent_defense: is this team's own scoring
# trending above/below their season average lately? Useful both for team
# total-points bets and as context for player props (a team scoring more
# as a whole tends to lift individual player floors too).

def get_team_recent_offense(team_id, season=SEASON):
    """
    Points scored over this team's last RECENT_DEFENSE_GAMES_SAMPLE
    completed games. Reuses get_team_schedule_events (cached per run), so
    this adds no new network calls beyond what's already fetched.
    """
    events = get_team_schedule_events(team_id, season)
    completed = []
    for e in events:
        comp = e.get("competitions", [{}])[0]
        if not comp.get("status", {}).get("type", {}).get("completed"):
            continue
        competitors = comp.get("competitors", [])
        this_team = next((c for c in competitors if str(c.get("team", {}).get("id")) == str(team_id)), None)
        if not this_team:
            continue
        try:
            pts_for = int(this_team.get("score", {}).get("value", this_team.get("score")))
        except (TypeError, ValueError):
            continue
        completed.append({"date": e.get("date", ""), "pts_for": pts_for})

    if not completed:
        return None
    completed.sort(key=lambda x: x["date"])
    last_n = completed[-RECENT_DEFENSE_GAMES_SAMPLE:]
    if not last_n:
        return None

    recent_avg = sum(g["pts_for"] for g in last_n) / len(last_n)
    return {
        "recent_pts_for_pg": round(recent_avg, 1),
        "games_counted": len(last_n),
    }


def build_recent_offense_note(recent_offense, season_stats, team_full=None):
    """
    Combines a team's recent (last-5) points-scored with their season
    average, same shape/rules as build_recent_defense_note. team_full here
    is the team's OWN name (not an opponent's) - this note describes what
    a team itself is doing, so it's attached to that team's own players.
    """
    if not recent_offense or not season_stats:
        return None
    if recent_offense["games_counted"] < 2:
        return None

    recent = recent_offense["recent_pts_for_pg"]
    season_avg = season_stats["pts_pg"]
    if season_avg == 0:
        return None

    pct_change = (recent - season_avg) / season_avg
    return {
        "team_full": team_full,
        "recent_pts_for_pg": recent,
        "season_pts_for_pg": season_avg,
        "games_counted": recent_offense["games_counted"],
        "pct_change": round(pct_change, 3),
        "is_notable": abs(pct_change) >= RECENT_DEFENSE_NOTABLE_PCT,
    }


# ---------- opponent-allowed rebounds & assists (team level) ----------
#
# Points-allowed above only needs each game's final score, which is on
# the schedule endpoint for free. Rebounds/assists allowed aren't on the
# schedule endpoint at all - they only exist in each game's box score, so
# this section fetches the box score (/summary?event=) for a team's last
# few completed games and sums BOTH teams' player lines from it: the
# opponent's own total (their own rebounding/passing output) and this
# team's total (rebounds/assists this team allowed that game).
#
# This is a real per-game fetch, unlike the points-allowed reuse above,
# so it's kept to a small game sample to avoid hammering the API.
OPP_ALLOWED_GAMES_SAMPLE = 5

# How much game-to-game swing counts as "volatile" for a team's allowed
# stat - if the highest and lowest games in the sample differ by more
# than this fraction of the average, we flag it as an unreliable signal
# rather than a dependable "weak defense" read.
ALLOWED_STAT_VOLATILITY_RATIO = 0.35


def _team_boxscore_totals(team_id, event_id):
    """
    Sums one team's player-level rebounds/assists for a single completed
    game, using the same /summary boxscore endpoint and athlete-loop shape
    already proven working in get_team_starters. Returns None if the box
    score doesn't have this team's player stats for some reason (e.g. data
    gap), rather than guessing zero.
    """
    try:
        payload = espn_web_get("/summary", {"event": event_id})
    except Exception:
        return None

    totals = {"rebounds": 0.0, "assists": 0.0, "found": False}
    for team_box in payload.get("boxscore", {}).get("players", []):
        if str(team_box.get("team", {}).get("id")) != str(team_id):
            continue
        for stat_group in team_box.get("statistics", []):
            for athlete_entry in stat_group.get("athletes", []):
                totals["found"] = True
                v_reb = _extract_stat_value(athlete_entry, "rebounds")
                v_ast = _extract_stat_value(athlete_entry, "assists")
                if v_reb is not None:
                    totals["rebounds"] += v_reb
                if v_ast is not None:
                    totals["assists"] += v_ast
    return totals if totals["found"] else None


def get_team_recent_allowed_reb_ast(team_id, season=SEASON, n=OPP_ALLOWED_GAMES_SAMPLE):
    """
    For a team's last n completed games, fetches each game's box score and
    sums the OPPONENT's rebounds/assists in that game - i.e. how many
    rebounds/assists this team allowed. Also keeps the per-game values (not
    just the average) so we can measure how much they swing game to game,
    for the volatility flag below.

    Returns None if no completed games with usable box scores were found.
    """
    events = get_team_schedule_events(team_id, season)
    completed = []
    for e in events:
        comp = e.get("competitions", [{}])[0]
        if not comp.get("status", {}).get("type", {}).get("completed"):
            continue
        competitors = comp.get("competitors", [])
        opponent = next((c for c in competitors if str(c.get("team", {}).get("id")) != str(team_id)), None)
        if not opponent:
            continue
        opp_id = opponent.get("team", {}).get("id")
        if not opp_id:
            continue
        completed.append({"date": e.get("date", ""), "event_id": e.get("id"), "opp_id": opp_id})

    if not completed:
        return None
    completed.sort(key=lambda x: x["date"])
    last_n = completed[-n:]

    reb_allowed_games = []
    ast_allowed_games = []
    for g in last_n:
        totals = _team_boxscore_totals(g["opp_id"], g["event_id"])
        if totals is None:
            continue
        reb_allowed_games.append(totals["rebounds"])
        ast_allowed_games.append(totals["assists"])

    if not reb_allowed_games:
        return None

    return {
        "rebounds_allowed_games": reb_allowed_games,
        "assists_allowed_games": ast_allowed_games,
        "rebounds_allowed_pg": round(sum(reb_allowed_games) / len(reb_allowed_games), 1),
        "assists_allowed_pg": round(sum(ast_allowed_games) / len(ast_allowed_games), 1),
        "games_counted": len(reb_allowed_games),
    }


def _stat_volatility_flag(values, avg):
    """
    Plain check: does this team's allowed stat swing wildly game to game,
    or is it fairly consistent? If the gap between her best and worst game
    in the sample is large relative to the average, the "this opponent
    allows a lot" read is a lot less trustworthy for any single game -
    it might just be an average built from two very different nights,
    exactly like a team allowing 90 one night and 75 the next.
    """
    if not values or avg == 0:
        return {"is_volatile": False, "spread": 0.0}
    spread = (max(values) - min(values)) / avg
    return {"is_volatile": spread >= ALLOWED_STAT_VOLATILITY_RATIO, "spread": round(spread, 2)}


def build_allowed_reb_ast_note(allowed_data, opponent_team_full=None):
    """
    Display-ready summary of what this opponent allows in rebounds and
    assists, plus a plain volatility flag for each. Returns None if there
    isn't enough data to say anything meaningful yet.
    """
    if not allowed_data or allowed_data["games_counted"] < 2:
        return None

    reb_vol = _stat_volatility_flag(allowed_data["rebounds_allowed_games"], allowed_data["rebounds_allowed_pg"])
    ast_vol = _stat_volatility_flag(allowed_data["assists_allowed_games"], allowed_data["assists_allowed_pg"])

    return {
        "opponent_team_full": opponent_team_full,
        "rebounds_allowed_pg": allowed_data["rebounds_allowed_pg"],
        "assists_allowed_pg": allowed_data["assists_allowed_pg"],
        "games_counted": allowed_data["games_counted"],
        "rebounds_volatile": reb_vol["is_volatile"],
        "assists_volatile": ast_vol["is_volatile"],
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


# ---------- league-wide rolling rankings (last 10 games) ----------
#
# Separate window from the last-5 "recent defense/offense vs season avg"
# notes above - 10 games gives a steadier sample for ranking every team
# against each other, whereas the 5-game notes are meant to catch a sharp
# recent swing. Computed once per report run (not per-game) and cached,
# since every team in the league needs to be ranked regardless of how many
# games are on today's slate.

LEAGUE_RANKING_GAMES_SAMPLE = 10
_LEAGUE_RANKINGS_CACHE = None  # populated by get_league_rankings(), cleared per run

def _team_last_n_pts(team_id, season=SEASON, n=LEAGUE_RANKING_GAMES_SAMPLE):
    """Returns (pts_for_pg, pts_against_pg) over this team's last n completed
    games, or (None, None) if there's no completed-game data yet."""
    events = get_team_schedule_events(team_id, season)
    completed = []
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
            pts_for = int(this_team.get("score", {}).get("value", this_team.get("score")))
            pts_against = int(opponent.get("score", {}).get("value", opponent.get("score")))
        except (TypeError, ValueError):
            continue
        completed.append({"date": e.get("date", ""), "pts_for": pts_for, "pts_against": pts_against})

    if not completed:
        return None, None
    completed.sort(key=lambda x: x["date"])
    last_n = completed[-n:]
    if not last_n:
        return None, None
    pts_for_pg = sum(g["pts_for"] for g in last_n) / len(last_n)
    pts_against_pg = sum(g["pts_against"] for g in last_n) / len(last_n)
    return round(pts_for_pg, 1), round(pts_against_pg, 1)


def get_league_rankings(season=SEASON, force_refresh=False, team_ids=None):
    """
    Ranks teams by points-for and points-against over their last
    LEAGUE_RANKING_GAMES_SAMPLE completed games. Returns a dict keyed by
    team_id (str):
      {"off_rank": int, "def_rank": int, "recent_pts_for_pg": float,
       "recent_pts_against_pg": float, "teams_ranked": int}
    off_rank 1 = highest scoring, def_rank 1 = fewest points allowed (best
    defense). A team with too few completed games to compute is omitted
    from the ranking (not assigned a fake rank).

    team_ids: if given, only ranks these teams against each other (e.g.
    just today's playing teams) instead of fetching the entire league -
    this is what keeps the API call count down to roughly one schedule
    fetch per playing team, rather than one per team in the league.
    "teams_ranked" and every rank in the result reflect the size of this
    scoped set, so a rank like "#1 of 4" means best of only today's teams,
    not the full league. Defaults to the full league if not given.

    Cached per run since it's identical for a given team_ids set regardless
    of which specific game is being processed - call clear_schedule_cache()
    (or start a fresh process) between runs on different days. The cache is
    keyed by the exact team_ids requested, so calling with a different set
    of teams within the same run will compute fresh rather than reusing a
    stale scoped result.
    """
    global _LEAGUE_RANKINGS_CACHE
    cache_key = tuple(sorted(str(t) for t in team_ids)) if team_ids else None
    if _LEAGUE_RANKINGS_CACHE is not None and not force_refresh:
        cached_key, cached_result = _LEAGUE_RANKINGS_CACHE
        if cached_key == cache_key:
            return cached_result

    if team_ids:
        teams = [{"id": t} for t in team_ids]
    else:
        teams = get_all_teams()

    computed = []
    for t in teams:
        pts_for_pg, pts_against_pg = _team_last_n_pts(t["id"], season)
        if pts_for_pg is None:
            continue
        computed.append({
            "team_id": str(t["id"]),
            "recent_pts_for_pg": pts_for_pg,
            "recent_pts_against_pg": pts_against_pg,
        })

    if not computed:
        _LEAGUE_RANKINGS_CACHE = (cache_key, {})
        return {}

    by_offense = sorted(computed, key=lambda x: x["recent_pts_for_pg"], reverse=True)
    by_defense = sorted(computed, key=lambda x: x["recent_pts_against_pg"])  # fewest allowed = best = rank 1

    off_rank_by_id = {row["team_id"]: i + 1 for i, row in enumerate(by_offense)}
    def_rank_by_id = {row["team_id"]: i + 1 for i, row in enumerate(by_defense)}

    result = {}
    for row in computed:
        tid = row["team_id"]
        result[tid] = {
            "off_rank": off_rank_by_id[tid],
            "def_rank": def_rank_by_id[tid],
            "recent_pts_for_pg": row["recent_pts_for_pg"],
            "recent_pts_against_pg": row["recent_pts_against_pg"],
            "teams_ranked": len(computed),
        }
    _LEAGUE_RANKINGS_CACHE = (cache_key, result)
    return result


def clear_league_rankings_cache():
    global _LEAGUE_RANKINGS_CACHE
    _LEAGUE_RANKINGS_CACHE = None


# ---------- home/away splits ----------
#
# Some teams/players perform meaningfully differently at home vs on the
# road. This reuses the same schedule-events data already fetched for rest
# days/season stats (no new calls at the team level). Uses ALL completed
# games this season for each split, not just a last-N window - home/away
# splits need a decent sample size to mean anything, and a team is
# typically only home or away for roughly half its games, so restricting
# to "last 10" would often leave too few of one type to be meaningful.

HOME_AWAY_MIN_GAMES = 2  # below this, don't claim a split means anything

def get_team_home_away_split(team_id, season=SEASON):
    """
    Returns {"home": {...}, "away": {...}} with pts_for_pg/pts_against_pg/
    games_counted for each split, using ALL of this team's completed games
    this season. A split is omitted (not included in the dict) if it has
    fewer than HOME_AWAY_MIN_GAMES games.
    """
    events = get_team_schedule_events(team_id, season)
    splits = {"home": [], "away": []}
    for e in events:
        comp = e.get("competitions", [{}])[0]
        if not comp.get("status", {}).get("type", {}).get("completed"):
            continue
        competitors = comp.get("competitors", [])
        this_team = next((c for c in competitors if str(c.get("team", {}).get("id")) == str(team_id)), None)
        opponent = next((c for c in competitors if str(c.get("team", {}).get("id")) != str(team_id)), None)
        if not this_team or not opponent:
            continue
        home_away = this_team.get("homeAway")
        if home_away not in ("home", "away"):
            continue
        try:
            pts_for = int(this_team.get("score", {}).get("value", this_team.get("score")))
            pts_against = int(opponent.get("score", {}).get("value", opponent.get("score")))
        except (TypeError, ValueError):
            continue
        splits[home_away].append({"pts_for": pts_for, "pts_against": pts_against})

    result = {}
    for side in ("home", "away"):
        games = splits[side]
        if len(games) < HOME_AWAY_MIN_GAMES:
            continue
        result[side] = {
            "pts_for_pg": round(sum(g["pts_for"] for g in games) / len(games), 1),
            "pts_against_pg": round(sum(g["pts_against"] for g in games) / len(games), 1),
            "games_counted": len(games),
        }
    return result if result else None


def get_player_home_away_split(games, team_schedule_events, stat_key):
    """
    Splits a player's sampled games (from get_player_recent_gamelog) into
    home/away buckets for a given stat, by matching each game's date
    against the team's schedule events (which carry the homeAway flag) -
    the player gamelog endpoint itself doesn't expose home/away directly,
    so this joins the two data sources by date.

    Returns {"home": {"avg": float, "games_counted": int},
             "away": {...}} - a split is omitted if it has fewer than
    HOME_AWAY_MIN_GAMES games or no games matched a schedule date at all.
    """
    # Build a date -> competitors lookup from the team's schedule. The
    # actual home/away side for THIS team gets resolved per-game below
    # (by matching against the opponent_team_id on the player's game
    # entry), since a bare date key alone doesn't tell us which competitor
    # is "this team" vs the opponent.
    date_to_home_away = {}
    for e in team_schedule_events:
        comp = e.get("competitions", [{}])[0]
        competitors = comp.get("competitors", [])
        date_key = (e.get("date") or "")[:10]
        if date_key:
            date_to_home_away[date_key] = competitors

    buckets = {"home": [], "away": []}
    for g in games:
        game_date = (g.get("date") or "")[:10]
        if not game_date or game_date not in date_to_home_away:
            continue
        value = _extract_stat_value(g, stat_key)
        if value is None:
            continue
        competitors = date_to_home_away[game_date]
        # Determine this game's homeAway by finding which competitor is
        # NOT the opponent listed on the player's game entry.
        opp_id = g.get("opponent_team_id")
        this_team_entry = next(
            (c for c in competitors if str(c.get("team", {}).get("id")) != str(opp_id)), None
        )
        if not this_team_entry or this_team_entry.get("homeAway") not in ("home", "away"):
            continue
        buckets[this_team_entry["homeAway"]].append(value)

    result = {}
    for side in ("home", "away"):
        vals = buckets[side]
        if len(vals) < HOME_AWAY_MIN_GAMES:
            continue
        result[side] = {"avg": round(sum(vals) / len(vals), 1), "games_counted": len(vals)}
    return result if result else None


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
    "threes": ["threePointFieldGoalsMade", "3PM", "threesMade", "fg3m"],
}
# ESPN sometimes reports threes as a combined "made-attempted" string (e.g.
# "3-7") under a field like "threePointFieldGoalsMade-threePointFieldGoalsAttempted"
# or "3PT", rather than a separate made-only numeric field. Tried as a
# fallback if none of the plain numeric aliases above are found.
THREES_COMBINED_ALIASES = ["threePointFieldGoalsMade-threePointFieldGoalsAttempted", "3PT", "fg3"]
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



RETURN_FROM_ABSENCE_MIN_MINUTES = 3  # a game with fewer than this many
# minutes played is treated as "effectively did not play" for the purposes
# of this heuristic (covers true DNPs plus token appearances).
RETURN_FROM_ABSENCE_LOOKBACK_GAMES = 10  # how far back to scan for a gap
RETURN_FROM_ABSENCE_FLAG_RECENT_GAMES = 2  # flag the most recent N games
# back from an absence, not just the single game immediately after - a
# player's conditioning/rhythm often takes more than one game to return.

def detect_recent_return_from_absence(games):
    """
    HEURISTIC, NOT A CONFIRMED INJURY STATUS. Free data sources here don't
    include an actual injury/DNP feed with reasons - this only looks at
    whether a player logged near-zero minutes in a recent game and then
    came back with real minutes, which could mean injury, illness, a
    coach's decision (rest, rotation, benching), or a personal matter.
    Always says "apparent absence" and "verify before relying on this",
    never claims to know the cause.

    Returns None if no such pattern is found in the last
    RETURN_FROM_ABSENCE_LOOKBACK_GAMES games, or a dict describing the most
    recent gap otherwise:
      {"absence_game_date": str or None, "games_since_absence": int,
       "games_sampled": int}
    """
    if len(games) < 2:
        return None

    recent = games[-RETURN_FROM_ABSENCE_LOOKBACK_GAMES:]
    minutes_by_index = []
    for g in recent:
        v = _extract_stat_value(g, "minutes")
        minutes_by_index.append(v)  # keep None as a placeholder to preserve ordering

    if all(v is None for v in minutes_by_index):
        return None

    # Walk backward from the most recent game to find the closest prior gap
    # (a near-zero-minutes game) that's since been followed by real minutes.
    last_idx = len(recent) - 1
    if minutes_by_index[last_idx] is None or minutes_by_index[last_idx] < RETURN_FROM_ABSENCE_MIN_MINUTES:
        return None  # she's IN the apparent absence right now, not returning from one

    for i in range(last_idx - 1, -1, -1):
        v = minutes_by_index[i]
        if v is not None and v < RETURN_FROM_ABSENCE_MIN_MINUTES:
            games_since = last_idx - i
            if games_since > RETURN_FROM_ABSENCE_FLAG_RECENT_GAMES:
                return None  # gap is too far back to still be "recent"
            return {
                "absence_game_date": recent[i].get("date"),
                "games_since_absence": games_since,
                "games_sampled": len(recent),
            }
    return None


def _extract_stat_value(game_entry, stat_key):
    """
    Looks up a stat's value in a single game entry's stats dict, trying
    known aliases first, then falling back to summing an offensive+defensive
    rebound split if the stat is rebounds and no combined field was found.
    Returns None (not 0) if nothing matched, so callers can distinguish
    "genuinely zero rebounds that game" from "we never found the field."

    "pra" is a combined stat (points + rebounds + assists in that single
    game) rather than a field ESPN provides directly, so it's built here
    by calling this same function recursively for its three parts. If any
    of the three is missing for that game, pra is also None for that game
    rather than silently treating a missing stat as zero.
    """
    if stat_key == "pra":
        pts = _extract_stat_value(game_entry, "points")
        reb = _extract_stat_value(game_entry, "rebounds")
        ast = _extract_stat_value(game_entry, "assists")
        if pts is None or reb is None or ast is None:
            return None
        return pts + reb + ast

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
    if stat_key == "threes":
        for alias in THREES_COMBINED_ALIASES:
            if alias in stats:
                raw = str(stats[alias])
                if "-" in raw:
                    made_part = raw.split("-")[0]
                    try:
                        return float(made_part)
                    except (TypeError, ValueError):
                        continue
    return None


# Number of rungs per stat, and where the player's own average sits among
# them. RUNGS_ABOVE_AVG rungs sit above the average, the rest sit below
# it. Matches the requested shape: mostly sub-average lines (for real
# granularity below the "obvious" bar) plus exactly one rung above avg.
#   20 PPG example: 12, 15, 18, 20, 22  -> 3 below, avg, 1 above (5 rungs)
#    8 PPG example: 3, 5, 7, 8, 10      -> 3 below, avg, 1 above (5 rungs)
RUNG_COUNT = {
    "points": 5,
    "rebounds": 4,
    "assists": 3,
    "threes": 3,
    "pra": 5,
}
RUNGS_ABOVE_AVG = 1

# Step between rungs scales with the player's average rather than being a
# flat league-wide number, so a 22-PPG star and a 6-PPG bench piece each
# get gaps that look like real, postable bookmaker lines instead of the
# same fixed increment applied to both. STEP_FRACTION is roughly "how many
# rungs it'd take to span the full average" (avg / STEP_FRACTION), floored
# at STEP_MIN so low-average stats don't collapse every rung onto one number.
STEP_FRACTION = {
    "points": 7,
    "rebounds": 5,
    "assists": 4,
    "threes": 3,
    "pra": 8,
}
STEP_MIN = {
    "points": 2,
    "rebounds": 1,
    "assists": 1,
    "threes": 1,
    "pra": 2,
}

# Lowest threshold that's still a plausible real-world bookmaker line for
# this stat - keeps the bottom rung from going so low it's meaningless
# (e.g. "1+ points") even for a very low-average player.
THRESHOLD_MIN_FLOOR = {
    "points": 3,
    "rebounds": 2,
    "assists": 1,
    "threes": 0,
    "pra": 8,
}


def _build_player_thresholds(avg, stat_key):
    """
    Builds a descending-then-one-above band of thresholds centered on a
    player's own recent average for this stat: mostly rungs below the
    average (for granularity under the "obvious" line) plus one rung
    above it, with the gap between rungs scaling with the average itself.

    Example (points, avg=20): 12, 15, 18, 20, 22
    Example (points, avg=8):  3, 5, 7, 8, 10
    """
    rung_count = RUNG_COUNT.get(stat_key, 4)
    above = min(RUNGS_ABOVE_AVG, rung_count - 1)
    below = rung_count - 1 - above
    min_floor = THRESHOLD_MIN_FLOOR.get(stat_key, 1)

    step_fraction = STEP_FRACTION.get(stat_key, 5)
    step_min = STEP_MIN.get(stat_key, 1)
    base_step = max(step_min, round(avg / step_fraction))

    center = max(min_floor, round(avg))

    # Steps shrink as they approach the average (wider gaps far below,
    # tighter gaps close to it) - matches 12,15,18,20,22 (steps 3,3,2,2)
    # and 3,5,7,8,10 (steps 2,2,1,2) rather than one flat step throughout.
    # The rung closest to the average uses a step one smaller than the
    # base step (floored at step_min); all farther rungs use the base step.
    thresholds = []
    t = center
    for i in range(below, 0, -1):
        near_avg = (i == 1)
        this_step = max(step_min, base_step - 1) if near_avg else base_step
        t = t - this_step
        thresholds.insert(0, t)
    thresholds.append(center)
    thresholds += [center + base_step * i for i in range(1, above + 1)]

    # Clamp to the floor and de-dupe (small averages can otherwise repeat
    # the same rung), preserving ascending order.
    thresholds = sorted(set(t for t in thresholds if t >= min_floor))

    # If clamping collapsed rungs below the target count, pad upward from
    # the top so the player still gets a full set of lines.
    while len(thresholds) < rung_count:
        thresholds.append(thresholds[-1] + base_step)

    return tuple(thresholds)


def prop_floor_probs(games, stat_key, thresholds=None):
    """
    Empirical P(stat >= threshold) over the sampled recent games.

    If thresholds isn't given explicitly, build a player-specific band
    centered on her own recent average for this stat via
    _build_player_thresholds(), so the lines surfaced are ones a book
    would plausibly post for HER specifically - not a blanket threshold
    that's the same for a 22-PPG scorer and a 6-PPG bench piece.
    """
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

    if thresholds is None:
        avg = sum(values) / len(values)
        thresholds = _build_player_thresholds(avg, stat_key)

    probs = {}
    for t in thresholds:
        hits = sum(1 for v in values if v >= t)
        probs[t] = round(hits / n, 3)
    return probs


_gamelog_debug_printed = False
_names_debug_printed = False

def get_player_props(team_id, opponent_team_id=None, season=SEASON, team_injured_names=None,
                      opponent_recent_defense_note=None, own_recent_offense_note=None,
                      opponent_allowed_reb_ast_note=None,
                      team_schedule_events=None, opponent_league_rank=None):
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
        for stat_key in PROP_THRESHOLDS:
            floors[stat_key] = prop_floor_probs(games, stat_key)

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

        return_from_absence = detect_recent_return_from_absence(games)
        return_from_absence_note = None
        if return_from_absence:
            games_since = return_from_absence["games_since_absence"]
            recency = "her most recent game" if games_since == 1 else f"{games_since} games ago"
            return_from_absence_note = (
                f"Apparent absence detected: logged well below normal minutes in a recent game, "
                f"then returned with real minutes as of {recency}. Cause is unconfirmed (could be "
                f"injury, illness, rest, or a coaching decision) - verify her status before relying "
                f"on the floors above, since a still-limited role would lower them."
            )

        home_away_split = None
        if team_schedule_events:
            home_away_split = get_player_home_away_split(games, team_schedule_events, "points")

        results.append({
            "name": p["name"],
            "games_sampled": len(games),
            "floors": floors,
            "recent_games": games,
            "vs_opponent": vs_opponent,
            "minutes_note": minutes_note,
            "opponent_recent_defense": opponent_recent_defense_note,
            "opponent_allowed_reb_ast": opponent_allowed_reb_ast_note,
            "own_recent_offense": own_recent_offense_note,
            "opponent_league_rank": opponent_league_rank,
            "return_from_absence_note": return_from_absence_note,
            "home_away_points_split": home_away_split,
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
    # Clear per-run caches so a fresh workflow run doesn't reuse stale data
    # from a previous invocation of the same long-lived process (harmless
    # no-op for a fresh process, but keeps behavior correct either way).
    clear_schedule_cache()
    clear_league_rankings_cache()

    games = get_todays_games()
    report = []

    # Rank every team in the league against each other (not just today's
    # playing teams) so "#2 in offense" means #2 in the whole league, the
    # way that phrase normally reads - not #2 out of just today's 4 teams.
    # Costs more API calls (one schedule fetch per team in the league) than
    # scoping to today's slate would, but avoids a confusing/misleading
    # ranking number.
    league_rankings = get_league_rankings()

    for g in games:
        home_id, away_id = g["home_team_id"], g["away_team_id"]

        home_rest = get_days_rest(home_id)
        away_rest = get_days_rest(away_id)
        home_stats = get_team_season_stats(home_id)
        away_stats = get_team_season_stats(away_id)

        # Each note describes a team's OWN recent defense, labeled with that
        # team's OWN name. Which side it gets attached to (as the opponent's
        # defense, for a given player) is decided below when building props.
        home_recent_defense = build_recent_defense_note(get_team_recent_defense(home_id), home_stats, g["home_team_name"])
        away_recent_defense = build_recent_defense_note(get_team_recent_defense(away_id), away_stats, g["away_team_name"])

        # Same pattern as recent defense above, but for a team's OWN
        # scoring - attached to that team's OWN players (not the opponent's),
        # since it's context on how the player's own offense is trending.
        home_recent_offense = build_recent_offense_note(get_team_recent_offense(home_id), home_stats, g["home_team_name"])
        away_recent_offense = build_recent_offense_note(get_team_recent_offense(away_id), away_stats, g["away_team_name"])

        # Rebounds/assists allowed - real fetch (box scores, not the free
        # schedule-endpoint reuse the points version gets), so this is
        # kept to a small recent-game sample. Same "labeled with that
        # team's own name" pattern as recent defense above.
        home_allowed_reb_ast = build_allowed_reb_ast_note(get_team_recent_allowed_reb_ast(home_id), g["home_team_name"])
        away_allowed_reb_ast = build_allowed_reb_ast_note(get_team_recent_allowed_reb_ast(away_id), g["away_team_name"])

        home_flags, home_injured_names = flag_missing_starters(home_id)
        away_flags, away_injured_names = flag_missing_starters(away_id)

        home_schedule_events = get_team_schedule_events(home_id)
        away_schedule_events = get_team_schedule_events(away_id)

        # Each side's players face the OPPONENT's defense, so the note
        # attached to a player is the opponent's recent-defense numbers,
        # their OWN team's recent offense note, and the opponent's
        # league-wide defensive rank (how good the opponent is at
        # defending, in league-wide context - not just this one matchup).
        home_props = get_player_props(home_id, opponent_team_id=away_id, team_injured_names=home_injured_names,
                                       opponent_recent_defense_note=away_recent_defense,
                                       own_recent_offense_note=home_recent_offense,
                                       opponent_allowed_reb_ast_note=away_allowed_reb_ast,
                                       team_schedule_events=home_schedule_events,
                                       opponent_league_rank=league_rankings.get(str(away_id)))
        away_props = get_player_props(away_id, opponent_team_id=home_id, team_injured_names=away_injured_names,
                                       opponent_recent_defense_note=home_recent_defense,
                                       own_recent_offense_note=away_recent_offense,
                                       opponent_allowed_reb_ast_note=home_allowed_reb_ast,
                                       team_schedule_events=away_schedule_events,
                                       opponent_league_rank=league_rankings.get(str(home_id)))

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
            "home_league_rank": league_rankings.get(str(home_id)),
            "away_league_rank": league_rankings.get(str(away_id)),
            "home_team_split": get_team_home_away_split(home_id),
            "away_team_split": get_team_home_away_split(away_id),
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


def _prob_bar(label, prob, color):
    """Renders a labeled horizontal fill-bar for a probability, the page's
    signature element - makes 'which side is favored' readable at a glance
    instead of requiring the reader to compare two numbers in a table."""
    if prob is None:
        return f"""<div class="pbar-row">
            <span class="pbar-label">{label}</span>
            <div class="pbar-track"><div class="pbar-fill pbar-na"></div></div>
            <span class="pbar-value pbar-na-text">N/A</span>
        </div>"""
    pct = prob * 100
    return f"""<div class="pbar-row">
        <span class="pbar-label">{label}</span>
        <div class="pbar-track"><div class="pbar-fill" style="width:{pct:.0f}%; background:{color};"></div></div>
        <span class="pbar-value">{pct:.0f}%</span>
    </div>"""


STAT_DISPLAY_NAMES = {"points": "PTS", "rebounds": "REB", "assists": "AST", "threes": "3PM", "pra": "PRA"}

def _render_top_points_performers(top_points):
    if not top_points:
        return ""
    items = []
    for rank, tp in enumerate(top_points, start=1):
        pct = tp["hit_rate"] * 100
        reason_html = ""
        if tp["reasons"]:
            reason_items = "".join(f"<li>{r}</li>" for r in tp["reasons"])
            reason_html = f'<ul class="tp-reasons">{reason_items}</ul>'
        items.append(f"""
        <div class="tp-card">
          <div class="tp-rank">{rank}</div>
          <div class="tp-body">
            <p class="tp-name">{tp['name']} <span class="tp-team">{tp['team']}</span></p>
            <p class="tp-matchup">vs {tp['opponent_full']}</p>
            <div class="tp-stat-row">
              <span class="tp-stat-badge">{tp['threshold']}+ Points</span>
              <span class="tp-hit-rate">{pct:.0f}% <span class="tp-hit-rate-label">hit rate</span></span>
              <span class="tp-games">last {tp['games_sampled']} games</span>
            </div>
            {reason_html}
          </div>
        </div>""")
    return f"""
    <section class="top-performers">
      <h2 class="tp-heading">Today's Top Points Performers</h2>
      <p class="tp-subheading">Points is the only stat with opponent-defense data behind it, so this list weighs 4 things: her own hit rate on a medium-difficulty line, whether she hit it in her last head-to-head vs this opponent, whether the opponent has recently been allowing more points than usual, and whether the opponent ranks weak defensively over their last 10 games.</p>
      <div class="tp-grid">
        {''.join(items)}
      </div>
    </section>"""


def _render_top_trend_performers(top_trends):
    if not top_trends:
        return ""
    items = []
    for rank, tp in enumerate(top_trends, start=1):
        stat_label = STAT_DISPLAY_NAMES.get(tp["stat_key"], tp["stat_key"].upper())
        pct = tp["hit_rate"] * 100
        boost = '<span class="boost-tag">&#9733; matches recent vs opponent</span>' if tp["vs_opp_aligned"] else ""
        reasons_html = ""
        if tp.get("reasons"):
            reasons_html = '<ul class="tp-reasons">' + "".join(f"<li>{r}</li>" for r in tp["reasons"]) + "</ul>"
        items.append(f"""
        <div class="tp-card">
          <div class="tp-rank">{rank}</div>
          <div class="tp-body">
            <p class="tp-name">{tp['name']} <span class="tp-team">{tp['team']}</span></p>
            <p class="tp-matchup">vs {tp['opponent_full']}</p>
            <div class="tp-stat-row">
              <span class="tp-stat-badge">{tp['threshold']}+ {stat_label}</span>
              <span class="tp-hit-rate">{pct:.0f}% <span class="tp-hit-rate-label">hit rate</span></span>
              <span class="tp-games">last {tp['games_sampled']} games</span>
            </div>
            {boost}
            {reasons_html}
          </div>
        </div>""")
    return f"""
    <section class="top-performers">
      <h2 class="tp-heading">Today's Top Rebounds/Assists/PRA/3PM Trends</h2>
      <p class="tp-subheading">Rebounds, assists, and PRA (points+rebounds+assists combined) now factor in how many of these the opponent has actually been allowing lately, plus whether her own team's offense is trending up - not just her own hit rate. Threes still only uses her own hit rate and head-to-head, since there's no reliable opponent-allowed-threes signal being tracked yet.</p>
      <div class="tp-grid">
        {''.join(items)}
      </div>
    </section>"""



# --- Bet Builder pick-quality rules (plain-English version) ---
#
# A "safe" pick now needs to pass TWO checks, not one:
#   1. Hit rate check (old rule) - she's cleared this mark often recently.
#   2. Real-line check (new rule) - the mark itself is a number a
#      bookmaker would actually list, not a joke floor near zero that
#      everyone clears every night (this is what was causing things like
#      "0+ threes" to show up as a "pick").
#
# On top of that, every pick also gets a comfort check (see
# _closest_call_margin below): did she clear the mark with room to spare,
# or was she barely scraping over it? A high hit rate with a lot of
# barely-cleared games is NOT the same as a safe pick - that's exactly
# the Lacan/Reese pattern (looks safe on paper, misses when one bad
# shooting night happens).
#
# MIN_BETTABLE_THRESHOLD = the lowest number per stat that's still a real
# betting line. Anything below this is thrown out even at 100% hit rate.
MIN_BETTABLE_THRESHOLD = {
    "points": 6,
    "rebounds": 3,
    "assists": 2,
    "threes": 1,
    "pra": 12,
}

# A game counts as a "close call" if she landed at the threshold or up to
# 2 above it - i.e. she cleared it, but barely.
CLOSE_CALL_WINDOW = 2

# If 40%+ of her recent games were close calls on this exact mark, we
# label the pick "thin margin" instead of treating it the same as a
# comfortable pick.
THIN_MARGIN_RATIO = 0.4


def _closest_call_margin(games, stat_key, threshold):
    """
    Plain-English safety check: out of her recent games, how many times
    did she barely clear this line (land within CLOSE_CALL_WINDOW points
    above it) instead of clearing it with real room to spare?

    A player can have a great hit rate (say 9 of her last 10 games) and
    still be a bad bet if most of those clears were by 1-2 points - one
    slightly-worse shooting night and she misses. This function is what
    catches that, instead of only looking at the hit rate number.
    """
    values = []
    for g in games:
        v = _extract_stat_value(g, stat_key)
        values.append(v if v is not None else 0.0)
    if not values:
        return None

    close_calls = sum(1 for v in values if threshold <= v <= threshold + CLOSE_CALL_WINDOW)
    return {
        "close_calls": close_calls,
        "games_checked": len(values),
        "worst_game": min(values),
    }


def _lowest_safe_threshold(prob_dict, min_confidence=CONFIDENCE_THRESHOLD, stat_key=None):
    """
    Given a {threshold: prob} dict, returns the LOWEST threshold whose
    prob still clears min_confidence AND is a real, bookmaker-sized
    number (see MIN_BETTABLE_THRESHOLD). This is the fix for picks like
    "0+ threes" - technically a 100% hit rate, but too low a number for
    any book to actually offer, so it's not a usable bet and no longer
    qualifies here.
    """
    if not prob_dict:
        return None
    min_bettable = MIN_BETTABLE_THRESHOLD.get(stat_key, 1)
    eligible = [
        (t, p) for t, p in prob_dict.items()
        if p is not None and p >= min_confidence and t >= min_bettable
    ]
    if not eligible:
        return None
    t, p = min(eligible, key=lambda x: x[0])
    return {"threshold": t, "prob": p}


def extract_top_picks(report, min_confidence=CONFIDENCE_THRESHOLD, limit=TOP_PICKS_LIMIT):
    """
    Bet Builder pick extractor. A pick has to pass THREE checks now,
    not one:
      1. Hit rate check: she's cleared this mark often enough recently.
      2. Real-line check: the mark is a number a book would actually
         post, not a near-zero floor that's meaningless as a bet.
      3. Comfort check: most of her recent games clear the mark with real
         room to spare, not by barely scraping over it. Picks that fail
         this get a plain "thin margin" warning and get sorted lower,
         instead of being shown as if they're just as safe as the rest.

    Picks are grouped by game, and a game is only included if it has at
    least 2 qualifying picks, since the point of this section is bet
    builders (same-game parlays), which need 2+ legs from the same game
    to combine.

    This reflects the model's own math only - it has not been backtested
    against real settled results, so "safe" here means "the model is very
    consistent about this," not "guaranteed to hit."

    Returns a list of game-groups: [{"matchup": ..., "picks": [...]}, ...],
    sorted by each game's best single pick probability, highest first, and
    capped at `limit` games (not `limit` picks).
    """
    games = []

    for g in report:
        matchup = f'{g["away_team_full"]} @ {g["home_team_full"]}'
        game_picks = []

        # --- player prop floors (points, rebounds, assists, threes) ---
        for side_label, players in (
            (g["away_team"], g["away_players"]),
            (g["home_team"], g["home_players"]),
        ):
            for p in players:
                recent_games = p.get("recent_games") or []

                for stat_key, floors in p["floors"].items():
                    best = _lowest_safe_threshold(floors, min_confidence, stat_key=stat_key)
                    if not best:
                        continue

                    stat_label = STAT_DISPLAY_NAMES.get(stat_key, stat_key)
                    reasons = [f"hit this mark in {round(best['prob']*100)}% of her last {p['games_sampled']} games"]

                    # Comfort check: is she clearing this with room to
                    # spare, or scraping over it most nights?
                    is_thin_margin = False
                    if recent_games:
                        margin_info = _closest_call_margin(recent_games, stat_key, best["threshold"])
                        if margin_info and margin_info["games_checked"] > 0:
                            close_ratio = margin_info["close_calls"] / margin_info["games_checked"]
                            if close_ratio >= THIN_MARGIN_RATIO:
                                is_thin_margin = True
                                reasons.append(
                                    f"THIN MARGIN: she barely cleared this mark (within {CLOSE_CALL_WINDOW}) in "
                                    f"{margin_info['close_calls']} of her last {margin_info['games_checked']} games - "
                                    f"one slightly-worse game and this misses"
                                )
                            else:
                                reasons.append("usually clears this with real room to spare, not just barely")

                    vs_opp = p.get("vs_opponent")
                    if vs_opp and vs_opp.get("games"):
                        most_recent_vs_opp = vs_opp["games"][-1]
                        v = _extract_stat_value(most_recent_vs_opp, stat_key)
                        if v is not None and v >= best["threshold"]:
                            reasons.append(f"also hit {best['threshold']}+ {stat_label} in her last meeting vs this opponent")

                    game_picks.append({
                        "type": stat_label,
                        "player": p["name"],
                        "team_context": matchup,
                        "pick_label": f'{best["threshold"]}+ {stat_label}',
                        "prob": best["prob"],
                        "reasons": reasons,
                        "thin_margin": is_thin_margin,
                    })

        # --- team spread covers (best line per team, not every threshold) ---
        best_spread_per_team = {}
        for s in g.get("spread_lines", []):
            for side_label, side_full, prob in (
                (g["away_team"], g["away_team_full"], s.get("away_cover_prob")),
                (g["home_team"], g["home_team_full"], s.get("home_cover_prob")),
            ):
                if prob is not None and prob >= min_confidence:
                    key = side_label
                    candidate = {
                        "type": "Spread",
                        "player": side_full,
                        "team_context": matchup,
                        "pick_label": f'{s["spread"]:+} spread',
                        "prob": prob,
                        "reasons": [f"model favors {side_full} to cover {s['spread']:+} today"],
                        "thin_margin": False,
                    }
                    if key not in best_spread_per_team or prob > best_spread_per_team[key]["prob"]:
                        best_spread_per_team[key] = candidate
        game_picks.extend(best_spread_per_team.values())

        # Bet builder requirement: need 2+ picks from this game, or it's not
        # useful for combining legs - drop games with only 0 or 1 qualifying pick.
        if len(game_picks) >= 2:
            # Comfortable picks (not thin margin) sort first, then by
            # probability within each group - so the safest legs to
            # actually combine show up at the top of each game block.
            game_picks.sort(key=lambda x: (x["thin_margin"], -x["prob"]))
            games.append({
                "matchup": matchup,
                "best_prob": game_picks[0]["prob"],
                "picks": game_picks,
            })

    games.sort(key=lambda x: x["best_prob"], reverse=True)
    return games[:limit]


def _render_top_picks(games):
    """
    Renders the Top Picks section as bet-builder groups: one block per
    game, each containing 2+ qualifying picks (spread cover and/or player
    prop floors) that can be combined into a same-game parlay / bet
    builder. Games sorted by their best single pick's probability,
    highest first. Empty state shown honestly if no game had 2+
    qualifying picks today.
    """
    if not games:
        return """
    <section class="top-picks">
      <h2 class="top-picks-title">Today's Bet Builders</h2>
      <p class="top-picks-sub">No game had at least two picks clear our confidence bar today - that happens on days with tougher matchups. Check the full game breakdowns below instead.</p>
    </section>"""

    game_blocks = []
    for game in games:
        rows = []
        for pk in game["picks"]:
            pct = pk["prob"] * 100
            reasons_html = ""
            if pk.get("reasons"):
                reasons_html = '<ul class="pick-reasons">' + "".join(f"<li>{r}</li>" for r in pk["reasons"]) + "</ul>"
            thin_badge = ""
            card_class = "pick-card"
            if pk.get("thin_margin"):
                card_class += " pick-card-thin"
                thin_badge = '<span class="thin-margin-badge">THIN MARGIN</span>'
            rows.append(f"""
          <div class="{card_class}">
            <div class="pick-card-top">
              <span class="pick-type">{pk["type"]}</span>
              <span class="pick-prob">{pct:.0f}%</span>
            </div>
            <p class="pick-player">{pk["player"]} {thin_badge}</p>
            <p class="pick-line">{pk["pick_label"]}</p>
            {reasons_html}
          </div>""")

        game_blocks.append(f"""
      <div class="bed-builder-group">
        <h3 class="bed-builder-label">Bet Builder: {game["matchup"]}</h3>
        <div class="pick-grid">
          {''.join(rows)}
        </div>
      </div>""")

    return f"""
    <section class="top-picks">
      <h2 class="top-picks-title">Today's Bet Builders</h2>
      <p class="top-picks-sub">2+ picks per game to combine into a parlay. Every pick shown here already
      cleared a high hit-rate bar AND is a real number a bookmaker would actually list (no more joke
      lines like "0+ threes"). Picks marked <strong>THIN MARGIN</strong> still passed the hit-rate bar,
      but she's usually barely scraping over that number rather than clearing it comfortably — treat
      those as the first legs to cut if you want a safer combo. Model math, NOT a guarantee.</p>
      {''.join(game_blocks)}
    </section>"""


def render_html(report):
    top_picks = extract_top_picks(report)
    top_picks_html = _render_top_picks(top_picks)
    top_points = build_top_points_performers(report)
    top_trends = build_top_trend_performers(report)
    cards = []
    for g in report:
        block = []
        block.append(f'<section class="matchup-card">')
        block.append(f'<div class="matchup-header">')
        block.append(f'<div class="court-line"></div>')
        block.append(f'<h2>{g["away_team_full"]} <span class="at-sign">@</span> {g["home_team_full"]}</h2>')
        rest_txt = f'{g["away_team"]} rest {g["away_rest_days"]}d &middot; {g["home_team"]} rest {g["home_rest_days"]}d'
        block.append(f'<p class="rest-line">{rest_txt}</p>')

        away_rank = g.get("away_league_rank")
        home_rank = g.get("home_league_rank")
        away_split = g.get("away_team_split")
        home_split = g.get("home_team_split")

        team_bullets = []
        for team_abbr, team_full, rank, split in (
            (g["away_team"], g["away_team_full"], away_rank, away_split),
            (g["home_team"], g["home_team_full"], home_rank, home_split),
        ):
            lines = []
            if rank:
                lines.append(f'{team_full} was #{rank["off_rank"]} in offense and #{rank["def_rank"]} in '
                              f'defense out of {rank["teams_ranked"]} teams in the league, over the last 10 games.')
            if split:
                for side_key, side_label in (("home", "at home"), ("away", "on the road")):
                    s = split.get(side_key)
                    if s:
                        lines.append(f'{team_full} scored {s["pts_for_pg"]:.1f} and allowed {s["pts_against_pg"]:.1f} '
                                      f'points per game {side_label} this season ({s["games_counted"]} games).')
            if lines:
                team_bullets.append((team_abbr, lines))

        if team_bullets:
            block.append('<ul class="matchup-facts">')
            for _abbr, lines in team_bullets:
                for line in lines:
                    block.append(f'<li>{line}</li>')
            block.append('</ul>')
        block.append('</div>')

        flags = g["away_flags"] + g["home_flags"]
        if flags:
            block.append('<div class="flag-stack">')
            for flag in flags:
                block.append(f'<div class="flag-chip">&#9888; {flag}</div>')
            block.append('</div>')

        block.append('<h3 class="section-label">Spread Cover</h3>')
        block.append('<div class="spread-block">')
        for s in g["spread_lines"]:
            block.append(f'<div class="spread-row-group">')
            block.append(f'<span class="spread-num">{s["spread"]:+}</span>')
            block.append(_prob_bar(g["away_team"], s["away_cover_prob"], "var(--teal)"))
            block.append(_prob_bar(g["home_team"], s["home_cover_prob"], "var(--orange)"))
            block.append('</div>')
        block.append('</div>')

        block.append('<h3 class="section-label">Starter Prop Floors</h3>')
        for side_label, side_full, players in (
            (g["away_team"], g["away_team_full"], g["away_players"]),
            (g["home_team"], g["home_team_full"], g["home_players"]),
        ):
            if not players:
                continue
            block.append(f'<div class="team-group">')
            block.append(f'<p class="team-sublabel">{side_label}</p>')
            for p in players:
                block.append('<div class="player-block">')
                block.append(f'<p class="player-name">{p["name"]} <span class="player-team">({side_full})</span> '
                             f'<span class="games-sampled">last {p["games_sampled"]} games</span></p>')
                for stat_key, floors in p["floors"].items():
                    if not floors:
                        continue
                    block.append('<div class="stat-group">')
                    block.append(f'<span class="stat-group-label">{STAT_DISPLAY_NAMES.get(stat_key, stat_key)}</span>')
                    block.append('<div class="pill-row">')
                    for t, prob in floors.items():
                        pct = prob * 100
                        tier = "pill-hot" if pct >= 70 else ("pill-warm" if pct >= 40 else "pill-cool")
                        block.append(f'<span class="pill {tier}">{t}+ &middot; {pct:.0f}%</span>')
                    block.append('</div>')
                    block.append('</div>')

                recent_def = p.get("opponent_recent_defense")
                if recent_def:
                    sign = "+" if recent_def["pct_change"] >= 0 else ""
                    pct_txt = f"{sign}{recent_def['pct_change'] * 100:.0f}%"
                    opp_name = recent_def.get("opponent_team_full") or "Opponent"
                    def_txt = (f"{opp_name} allowed {recent_def['recent_pts_allowed_pg']:.1f} points per "
                               f"game on average over their last {recent_def['games_counted']} games "
                               f"(season avg {recent_def['season_pts_allowed_pg']:.1f}, {pct_txt})")
                    if recent_def["is_notable"]:
                        block.append(f'<div class="flag-chip flag-chip-inline">&#9888; {def_txt}</div>')
                    else:
                        block.append(f'<p class="vs-opp-line">{def_txt}</p>')

                opp_rank = p.get("opponent_league_rank")
                if opp_rank:
                    opp_name = (recent_def or {}).get("opponent_team_full") or "Opponent"
                    rank_txt = (f"{opp_name} ranks #{opp_rank['def_rank']} in defense out of "
                                f"{opp_rank['teams_ranked']} teams in the league, over the last 10 games.")
                    block.append(f'<p class="vs-opp-line">{rank_txt}</p>')

                vs_opp = p.get("vs_opponent")
                if vs_opp:
                    if vs_opp["games"]:
                        lines = []
                        for g_entry in vs_opp["games"]:
                            date_str = format_display_date(g_entry.get("date"))
                            pts = _extract_stat_value(g_entry, "points")
                            reb = _extract_stat_value(g_entry, "rebounds")
                            ast = _extract_stat_value(g_entry, "assists")
                            tpm = _extract_stat_value(g_entry, "threes")
                            pts_s = f"{pts:.0f}" if pts is not None else "?"
                            reb_s = f"{reb:.0f}" if reb is not None else "?"
                            ast_s = f"{ast:.0f}" if ast is not None else "?"
                            tpm_s = f"{tpm:.0f}" if tpm is not None else "?"
                            lines.append(f"{date_str}: {pts_s}p/{reb_s}r/{ast_s}a/{tpm_s}3pm")
                        block.append(f'<p class="vs-opp-line">vs opponent (last {len(vs_opp["games"])}, '
                                     f'&lt;{VS_OPPONENT_MAX_AGE_DAYS}d): {" &middot; ".join(lines)}</p>')
                    else:
                        block.append(f'<p class="vs-opp-line vs-opp-empty">vs opponent: {vs_opp["reason"]}</p>')

                own_off = p.get("own_recent_offense")
                if own_off:
                    sign = "+" if own_off["pct_change"] >= 0 else ""
                    pct_txt = f"{sign}{own_off['pct_change'] * 100:.0f}%"
                    team_name = own_off.get("team_full") or side_full
                    off_txt = (f"{team_name} scored {own_off['recent_pts_for_pg']:.1f} points per game "
                               f"on average over their last {own_off['games_counted']} games "
                               f"(season avg {own_off['season_pts_for_pg']:.1f}, {pct_txt})")
                    if own_off["is_notable"]:
                        block.append(f'<div class="flag-chip flag-chip-inline">&#9888; {off_txt}</div>')
                    else:
                        block.append(f'<p class="vs-opp-line">{off_txt}</p>')

                home_away_split = p.get("home_away_points_split")
                if home_away_split:
                    split_parts = []
                    for side_key in ("home", "away"):
                        s = home_away_split.get(side_key)
                        if s:
                            split_parts.append(f'{side_key}: {s["avg"]:.1f} pts/g ({s["games_counted"]}g)')
                    if split_parts:
                        block.append(f'<p class="vs-opp-line">Points, home/away split: {" &middot; ".join(split_parts)}</p>')

                if p.get("return_from_absence_note"):
                    block.append(f'<div class="flag-chip flag-chip-inline">&#9888; {p["return_from_absence_note"]}</div>')

                if p.get("minutes_note"):
                    block.append(f'<div class="flag-chip flag-chip-inline">&#9888; {p["minutes_note"]}</div>')
                block.append('</div>')
            block.append('</div>')
        block.append('</section>')
        cards.append("".join(block))

    html = f"""<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>WNBA Daily Probabilities</title>
<style>
:root {{
  --bg: #0B1120;
  --card: #131B2E;
  --card-border: #1F2A44;
  --orange: #E8630A;
  --teal: #2DD4BF;
  --amber: #F5A623;
  --text: #F7F8FA;
  --text-dim: #AEB8CC;
  --h1-accent: #ffb35c;
  --disclaimer-text: #E39A9A;
  --disclaimer-bg: rgba(232, 99, 10, 0.08);
  --disclaimer-border: rgba(232, 99, 10, 0.2);
  --flag-bg: rgba(245, 166, 35, 0.12);
  --flag-border: rgba(245, 166, 35, 0.35);
  --row-tint: rgba(255,255,255,0.02);
  --track-bg: rgba(255,255,255,0.08);
  --pill-hot-bg: rgba(45, 212, 191, 0.16);
  --pill-hot-text: #5eead4;
  --pill-hot-border: rgba(45, 212, 191, 0.4);
  --pill-warm-bg: rgba(232, 99, 10, 0.16);
  --pill-warm-text: #ffab6b;
  --pill-warm-border: rgba(232, 99, 10, 0.4);
  --pill-cool-bg: rgba(255,255,255,0.04);
  --pill-cool-text: #9AA5BC;
  --pill-cool-border: rgba(255,255,255,0.10);
}}
@media (prefers-color-scheme: light) {{
  :root {{
    --bg: #F7F8FA;
    --card: #FFFFFF;
    --card-border: #E2E6ED;
    --orange: #D4560A;
    --teal: #0D9488;
    --amber: #B8730E;
    --text: #1A2233;
    --text-dim: #64708A;
    --h1-accent: #E8630A;
    --disclaimer-text: #A8391F;
    --disclaimer-bg: rgba(212, 86, 10, 0.06);
    --disclaimer-border: rgba(212, 86, 10, 0.18);
    --flag-bg: rgba(184, 115, 14, 0.08);
    --flag-border: rgba(184, 115, 14, 0.3);
    --row-tint: rgba(20, 30, 50, 0.02);
    --track-bg: rgba(20, 30, 50, 0.08);
    --pill-hot-bg: rgba(13, 148, 136, 0.1);
    --pill-hot-text: #0D9488;
    --pill-hot-border: rgba(13, 148, 136, 0.3);
    --pill-warm-bg: rgba(212, 86, 10, 0.1);
    --pill-warm-text: #B8480E;
    --pill-warm-border: rgba(212, 86, 10, 0.3);
    --pill-cool-bg: rgba(20, 30, 50, 0.03);
    --pill-cool-text: #7A879E;
    --pill-cool-border: rgba(20, 30, 50, 0.08);
  }}
}}
* {{ box-sizing: border-box; }}
body {{
  font-family: -apple-system, "Segoe UI", sans-serif;
  max-width: 720px;
  margin: 0 auto;
  padding: 16px;
  background: var(--bg);
  color: var(--text);
}}
h1 {{
  font-family: "Arial Narrow", "Oswald", -apple-system, sans-serif;
  font-weight: 800;
  font-size: 1.9em;
  letter-spacing: 0.02em;
  text-transform: uppercase;
  margin: 4px 0 2px;
  background: linear-gradient(90deg, var(--orange), var(--h1-accent));
  -webkit-background-clip: text;
  background-clip: text;
  -webkit-text-fill-color: transparent;
}}
.updated {{ color: var(--text-dim); font-size: 0.82em; margin: 0 0 10px; }}
.disclaimer {{
  color: var(--disclaimer-text);
  font-size: 0.78em;
  background: var(--disclaimer-bg);
  border: 1px solid var(--disclaimer-border);
  border-radius: 8px;
  padding: 10px 12px;
  margin-bottom: 22px;
  line-height: 1.5;
}}

.matchup-card {{
  background: var(--card);
  border: 1px solid var(--card-border);
  border-radius: 14px;
  padding: 0 0 22px;
  margin-bottom: 28px;
  overflow: hidden;
}}
.matchup-header {{ padding: 20px 20px 12px; }}
.court-line {{
  height: 3px;
  width: 100%;
  background: linear-gradient(90deg, var(--orange), var(--teal));
  margin: -1px -1px 16px -1px;
  width: calc(100% + 2px);
}}
.matchup-header h2 {{
  font-family: "Arial Narrow", "Oswald", -apple-system, sans-serif;
  font-weight: 700;
  font-size: 1.25em;
  letter-spacing: 0.01em;
  margin: 0;
  line-height: 1.3;
  color: var(--text);
}}
.at-sign {{ color: var(--text-dim); font-weight: 400; }}
.rest-line {{ color: var(--text-dim); font-size: 0.82em; margin: 8px 0 0; }}
.matchup-facts {{ list-style: none; margin: 10px 0 0; padding: 0; }}
.matchup-facts li {{ color: var(--text-dim); font-size: 0.82em; line-height: 1.5; margin: 6px 0 0; padding-left: 14px; position: relative; }}
.matchup-facts li::before {{ content: "\\2022"; position: absolute; left: 0; color: var(--teal); }}

.flag-stack {{ padding: 0 20px; display: flex; flex-direction: column; gap: 8px; margin-bottom: 18px; }}
.flag-chip {{
  color: var(--amber);
  background: var(--flag-bg);
  border: 1px solid var(--flag-border);
  border-radius: 8px;
  padding: 10px 12px;
  font-size: 0.82em;
  line-height: 1.5;
}}
.flag-chip-inline {{ margin: 12px 0 0; }}

.section-label {{
  color: var(--text-dim);
  font-size: 0.72em;
  text-transform: uppercase;
  letter-spacing: 0.1em;
  font-weight: 700;
  padding: 0 20px;
  margin: 26px 0 12px;
}}

.spread-block {{ padding: 0 20px; display: flex; flex-direction: column; gap: 12px; }}
.spread-row-group {{
  background: var(--row-tint);
  border: 1px solid var(--card-border);
  border-radius: 10px;
  padding: 10px 12px 12px;
}}
.spread-num {{
  display: block;
  font-weight: 700;
  font-size: 0.85em;
  color: var(--text-dim);
  margin-bottom: 8px;
}}
.pbar-row {{ display: flex; align-items: center; gap: 8px; margin: 6px 0; }}
.pbar-label {{ width: 34px; font-size: 0.78em; color: var(--text-dim); font-weight: 600; flex-shrink: 0; }}
.pbar-track {{ flex: 1; height: 8px; background: var(--track-bg); border-radius: 4px; overflow: hidden; }}
.pbar-fill {{ height: 100%; border-radius: 4px; }}
.pbar-na {{ width: 0%; }}
.pbar-value {{ width: 38px; text-align: right; font-size: 0.82em; font-weight: 700; flex-shrink: 0; color: var(--text); }}
.pbar-na-text {{ color: var(--text-dim); font-weight: 400; }}

.team-group {{
  margin: 0 0 24px;
  padding-bottom: 4px;
}}
.team-group + .team-group {{
  border-top: 2px solid var(--card-border);
  padding-top: 18px;
}}
.team-sublabel {{
  padding: 0 20px;
  color: var(--text-dim);
  font-size: 0.72em;
  text-transform: uppercase;
  letter-spacing: 0.08em;
  font-weight: 700;
  margin: 22px 0 10px;
}}
.team-sublabel:first-of-type {{ margin-top: 4px; }}
.player-team {{ color: var(--text-dim); font-weight: 500; font-size: 0.85em; }}

.player-block {{
  padding: 14px 20px 16px;
  border-top: 1px solid var(--card-border);
}}
.player-block:first-of-type {{ border-top: none; padding-top: 0; }}
.player-name {{ font-size: 0.98em; font-weight: 700; margin: 0 0 10px; color: var(--text); }}
.games-sampled {{ color: var(--text-dim); font-weight: 400; font-size: 0.82em; }}

.stat-group {{ margin-bottom: 10px; }}
.stat-group-label {{
  display: block;
  color: var(--text-dim);
  font-size: 0.68em;
  text-transform: uppercase;
  letter-spacing: 0.08em;
  font-weight: 700;
  margin-bottom: 6px;
}}
.pill-row {{ display: flex; flex-wrap: wrap; gap: 8px; }}
.pill {{
  font-size: 0.74em;
  font-weight: 700;
  padding: 5px 10px;
  border-radius: 20px;
  white-space: nowrap;
  letter-spacing: 0.01em;
}}
.pill-hot {{ background: var(--pill-hot-bg); color: var(--pill-hot-text); border: 1px solid var(--pill-hot-border); }}
.pill-warm {{ background: var(--pill-warm-bg); color: var(--pill-warm-text); border: 1px solid var(--pill-warm-border); }}
.pill-cool {{ background: var(--pill-cool-bg); color: var(--pill-cool-text); border: 1px solid var(--pill-cool-border); }}

.vs-opp-line {{ color: var(--text-dim); font-size: 0.78em; margin: 12px 0 0; line-height: 1.6; }}
.vs-opp-empty {{ font-style: italic; }}

.top-performers {{ margin-bottom: 32px; }}
.tp-heading {{
  font-family: "Arial Narrow", "Oswald", -apple-system, sans-serif;
  font-weight: 800;
  font-size: 1.15em;
  letter-spacing: 0.01em;
  color: var(--text);
  margin: 0 0 6px;
}}
.tp-subheading {{ color: var(--text-dim); font-size: 0.8em; line-height: 1.5; margin: 0 0 18px; }}
.tp-grid {{ display: flex; flex-direction: column; gap: 12px; }}
.tp-card {{
  display: flex;
  gap: 14px;
  background: var(--card);
  border: 1px solid var(--card-border);
  border-radius: 12px;
  padding: 14px 16px;
}}
.tp-rank {{
  flex-shrink: 0;
  width: 26px;
  height: 26px;
  border-radius: 50%;
  background: linear-gradient(135deg, var(--orange), var(--teal));
  color: #0B1120;
  font-weight: 800;
  font-size: 0.82em;
  display: flex;
  align-items: center;
  justify-content: center;
}}
.tp-body {{ flex: 1; min-width: 0; }}
.tp-name {{ font-weight: 700; font-size: 0.98em; margin: 0 0 2px; color: var(--text); }}
.tp-team {{ color: var(--text-dim); font-weight: 500; font-size: 0.85em; }}
.tp-matchup {{ color: var(--text-dim); font-size: 0.8em; margin: 0 0 10px; }}
.tp-stat-row {{ display: flex; flex-wrap: wrap; align-items: center; gap: 10px; }}
.tp-stat-badge {{
  background: var(--pill-hot-bg);
  color: var(--pill-hot-text);
  border: 1px solid var(--pill-hot-border);
  font-weight: 700;
  font-size: 0.78em;
  padding: 4px 10px;
  border-radius: 20px;
}}
.tp-hit-rate {{ font-weight: 800; font-size: 1em; color: var(--text); }}
.tp-hit-rate-label {{ font-weight: 400; font-size: 0.75em; color: var(--text-dim); }}
.tp-games {{ color: var(--text-dim); font-size: 0.78em; }}
.boost-tag {{
  display: inline-block;
  margin-top: 10px;
  color: var(--amber);
  font-size: 0.76em;
  font-weight: 600;
}}
.tp-reasons {{ list-style: none; margin: 10px 0 0; padding: 0; }}
.tp-reasons li {{ color: var(--text-dim); font-size: 0.78em; line-height: 1.5; margin: 4px 0 0; padding-left: 14px; position: relative; }}
.tp-reasons li::before {{ content: "\\2022"; position: absolute; left: 0; color: var(--teal); }}

.top-picks {{
  background: var(--card);
  border: 1px solid var(--card-border);
  border-radius: 14px;
  padding: 20px 18px;
  margin-bottom: 22px;
}}
.top-picks-title {{ font-size: 1.1em; font-weight: 800; margin: 0 0 4px; color: var(--text); }}
.top-picks-sub {{ font-size: 0.78em; color: var(--text-dim); line-height: 1.5; margin: 0 0 14px; }}
.pick-grid {{ display: flex; flex-direction: column; gap: 10px; }}
.bed-builder-group {{ margin-bottom: 20px; }}
.bed-builder-group:last-child {{ margin-bottom: 0; }}
.bed-builder-label {{
  font-size: 0.85em;
  font-weight: 700;
  color: var(--teal);
  margin: 0 0 10px;
}}
.pick-card {{
  background: var(--track-bg);
  border: 1px solid var(--card-border);
  border-radius: 10px;
  padding: 12px 14px;
}}
.pick-card-thin {{
  border: 1px solid var(--amber, #f5a623);
  background: rgba(245, 166, 35, 0.06);
}}
.thin-margin-badge {{
  display: inline-block;
  background: var(--amber, #f5a623);
  color: #0B1120;
  font-size: 0.65em;
  font-weight: 800;
  letter-spacing: 0.03em;
  padding: 2px 7px;
  border-radius: 10px;
  margin-left: 6px;
  vertical-align: middle;
}}
.pick-card-top {{ display: flex; justify-content: space-between; align-items: center; margin-bottom: 6px; }}
.pick-type {{
  font-size: 0.68em;
  font-weight: 700;
  letter-spacing: 0.04em;
  text-transform: uppercase;
  color: var(--text-dim);
}}
.pick-prob {{ font-size: 1.1em; font-weight: 800; color: var(--teal); }}
.pick-player {{ font-size: 0.98em; font-weight: 700; color: var(--text); margin: 0 0 2px; }}
.pick-line {{ font-size: 0.88em; font-weight: 600; color: var(--orange); margin: 0 0 2px; }}
.pick-context {{ font-size: 0.75em; color: var(--text-dim); margin: 0; }}
.pick-reasons {{
  margin: 8px 0 0;
  padding: 0 0 0 16px;
  list-style: disc;
  font-size: 0.75em;
  color: var(--text-dim);
  line-height: 1.5;
}}
.pick-reasons li {{ margin: 2px 0; }}

.tab-nav {{
  display: grid;
  grid-template-columns: repeat(3, 1fr);
  gap: 10px;
  padding: 0 20px;
  margin: 18px 0 4px;
}}
.tab-card {{
  background: var(--card-bg, #131a2b);
  border: 1px solid rgba(255,255,255,0.08);
  border-radius: 12px;
  padding: 14px 10px;
  display: flex;
  flex-direction: column;
  align-items: center;
  text-align: center;
  gap: 4px;
  cursor: pointer;
  font-family: inherit;
  color: var(--text, #e8ecf4);
}}
.tab-card-title {{
  font-size: 0.95em;
  font-weight: 800;
}}
.tab-card-sub {{
  font-size: 0.68em;
  color: var(--text-dim, #8892a6);
  line-height: 1.3;
}}
.tab-card.active {{
  border-color: var(--teal, #2dd4bf);
  background: rgba(45, 212, 191, 0.08);
}}
.tab-card.active .tab-card-title {{ color: var(--teal, #2dd4bf); }}
.tab-panel {{ display: none; }}
.tab-panel.active {{ display: block; }}
</style>
</head>
<body>
<h1>WNBA Daily Probabilities</h1>

<p class="updated">Generated {format_display_date(local_now())} {local_now().strftime('%H:%M')}</p>
<p class="disclaimer">Estimates only, NOT guarantees — verify starters and lines yourself before betting.</p>

<div class="tab-nav">
  <button class="tab-card active" data-tab="tab-builders" onclick="showTab('tab-builders', this)">
    <span class="tab-card-title">Bet Builders</span>
    <span class="tab-card-sub">Same-game parlay picks</span>
  </button>
  <button class="tab-card" data-tab="tab-toppicks" onclick="showTab('tab-toppicks', this)">
    <span class="tab-card-title">Top Picks</span>
    <span class="tab-card-sub">Points, rebounds, assists, 3PM trends</span>
  </button>
  <button class="tab-card" data-tab="tab-everything" onclick="showTab('tab-everything', this)">
    <span class="tab-card-title">All Games</span>
    <span class="tab-card-sub">Spreads &amp; full prop breakdowns</span>
  </button>
</div>

<div id="tab-builders" class="tab-panel active">
{top_picks_html}
</div>

<div id="tab-toppicks" class="tab-panel">
{_render_top_points_performers(top_points)}
{_render_top_trend_performers(top_trends)}
</div>

<div id="tab-everything" class="tab-panel">
{''.join(cards)}
</div>

<script>
function showTab(id, btn) {{
  document.querySelectorAll('.tab-panel').forEach(function(p) {{ p.classList.remove('active'); }});
  document.querySelectorAll('.tab-card').forEach(function(c) {{ c.classList.remove('active'); }});
  document.getElementById(id).classList.add('active');
  btn.classList.add('active');
  window.scrollTo({{ top: 0, behavior: 'instant' }});
}}
</script>
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
    if len(report) == 0:
        print("WARNING: 0 games in report - scoreboard fetch may have failed for all dates queried (check WARNING lines above).")
    print(f"Done. {len(report)} games processed.")
    print(f"  Spread data available for {games_with_spread_data}/{len(report)} games.")
    print(f"  Player props available for {games_with_props}/{len(report)} games.")
    if len(report) > 0 and games_with_spread_data == 0:
        print("  WARNING: no spread data on any game - check get_team_season_stats() field names.")
    if len(report) > 0 and games_with_props == 0:
        print("  WARNING: no player props on any game - check get_player_recent_gamelog() field names.")
