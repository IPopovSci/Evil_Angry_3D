# EXPERIMENT RECORD — 2026-11-18 · "one-shot, no engine"

This file pins the variables for this run so results can be compared against
other approaches executed against the same specification.

## Fixed variables

| Variable | Value |
|---|---|
| Date | 2026-11-18 |
| Specification | [`first_person_dungeon_arpg_design.md`](../../first_person_dungeon_arpg_design.md) v1.1 (normative, single-player) — treated as unchanged input for this run |
| Agent / model | GLM-5.3-Flash (`opencode-go`), running in OpenCode |
| Branch | `master` · implementation commit **`e2dfada`** ("Experiment 2026-11-18: one-shot no-engine implementation of the ARPG spec"); spec change committed separately just before it as **`4d55d58`** |
| Approach | **No game engine.** One hand-written codebase: raw WebGL2 renderer, DOM-based UI, procedural WebAudio synthesis, custom world generation, custom save system |
| Generation mode | **One shot.** The entire game was produced in a single continuous session without user feedback iterations; the agent self-verified via headless self-tests (`node game.js`) and fixed its own defects before delivery |

## Prompt (verbatim, as issued)

> No engine, one shot, take design document, make a game

(Additional post-delivery instruction, treated as part of the same run's conditions:
commit the design-document change separately, commit the game under `experiment/`,
record branch/prompt/conditions, and push to
`https://github.com/IPopovSci/Evil_Angry_3D`.)

## Deliverable

| File | Role |
|---|---|
| `index.html` | Page shell, HUD/menus DOM + stylesheet |
| `game.js` | Entire game (~6.6k lines): data tables, renderer, generation, combat, AI, loot, UI, saves, self-tests |

## How to run

- **Play:** open `index.html` in any WebGL2 browser (double-click works; no server or build step). Click the canvas to capture the mouse.
- **Self-tests:** `node game.js` (headless mode; 27 checks, 0 failures at delivery — covers spec §19.4 reachability over 320 seeded floors, loot/inventory/damage math invariants, catalog sizes).

## What is implemented (spec mapping, abbreviated)

- Character creation: 3 classes (Vanguard/Stalker/Arcanist), appearance, 4 difficulty profiles incl. hardcore toggle, persistent slots
- Town hub Hollowmere: 7 service NPCs (smith, alchemist, mystic, healer, quartermaster, chronicler, trainer), stash 3 tabs, gate with waypoint floor select, portal anchor
- Dungeon: 16 floors / 4 regions, seeded logical-graph-first generation (critical path, branches, loops, secret rooms, key/lock pairs with guaranteed-obtainable keys, shrines, traps, lore, 12+ event patterns), reachability asserted per attempt, deterministic re-entry (committed chest/enemy loot, fog, killed-uniques persist)
- First-person combat: light/charged-heavy melee arcs, bow draw/drop + arrows, spell casting (10 general spells, 5 ranks), shield block cone + 0.18 s perfect parry + guard break, dodge i-frames, kick with prop physics and environmental-kill credit, poise/stagger, status effects (bleed/burn/poison/chill/shock/curse/stun/fear/slow), head/limb severing with physics gore props (toggleable)
- 24 enemy archetypes + 8 elite modifiers (combinable), AI state machine with sight/hearing/last-known-position and A* pathing; 4 authored multi-phase bosses with arena gates, telegraphs, guard-break windows, guaranteed rare+ drops and waypoint unlocks
- Loot: rarity 65/25/9/1 with source adjustments, 30+ affix families with exclusivity rules, unidentified state, 12 authored relics with real behavior hooks, gold, durability/repair, requirements gating with disabled-not-dropped semantics
- Inventory: exact 10×6 grid, footprints, rotate/swap/stack/split/sort, 9 equipment slots, two-handed transactional conflicts, belt auto-bind with shared 1.25 s potion cooldown
- Progression: XP curve `floor(100·L^1.55)`, 5 attribute + 1 talent point per level, 24 talents (tiers gated at 3/8 points), respec, spellbook learning with INT requirements
- Economy: price/repair/identify formulas per spec, buyback (20), milestone vendor restock, town-return portal (Return Sigil with 5 s combat lockout)
- Quests/journal: 4 main arcs + 12 side quests, 24 lore entries, bestiary, exactly-once rewards
- Death: town respawn, recoverable gold cache (5/10/20% by difficulty, single cache that merges with warning), hardcore permadeath
- Persistence: versioned atomic saves with checksum + automatic prior-snapshot recovery, autosave on the lifecycle events listed in §14.3, New Descent (new seed, retained character/story)
- Presentation: lit-vertex WebGL2 with per-region palettes/fog, torch flicker, particles, minimap fog + full map overlay, HUD orbs/bars/hotbar/boss bar, damage numbers, synthesized audio (footsteps, weapon, spells, ambience, stingers), settings (sensitivity, FOV, volumes, UI scale, damage numbers, enemy bars, gore, auto-gold, key rebinding subset)

## Known simplifications at delivery (honest deltas vs spec)

- No gamepad/controller mapping; remapping covers a subset of actions
- Staff/wand "spell charges" and RMB utility-cast slots are stubbed (staff casts the selected learned spell on LMB)
- Third-person equipment preview and voice/subtitle systems are not rendered (character sheet is numeric + first-person visuals only)
- Corridors are 1 tile wide; per-floor verticality (multi-level chunks) is represented by single-level rooms only
- Bow aim-zoom and enemy dodge/parry reactions are simplified
- Vendor "recharge" service lists as unavailable (no charged items exist in this build)

## Verification at delivery

```
node game.js
27 passed, 0 failed
```

Notable checks: 320 seeded floor generations × 16 floor indices all solvable
(start, mandatory rooms, boss floor and exit connected; locked doors always
paired with keys obtainable before them); 800 loot rolls structurally valid;
grid placement/rotation/swap invariants; armor/resistance formula bounds;
price/identify/repair formulas; save item round-trip.
