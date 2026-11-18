# Experiment log — first-person dungeon ARPG

Each subfolder is one attempt to implement `../first_person_dungeon_arpg_design.md`
under a fixed set of variables (prompt, constraints, generation mode, model), so
that approaches can be compared fairly.

| Folder | Approach | Prompt mode | Status |
|---|---|---|---|
| `2026-11-18_one-shot-no-engine/` | No engine: raw WebGL2 + DOM UI + WebAudio, single continuous generation, agent self-tested via `node game.js` | "No engine, one shot, take design document, make a game" | Delivered · self-tests 27/27 |

Each folder contains an `EXPERIMENT.md` that pins the date, specification
version, model, branch, the verbatim prompt, the constraints, the feature
coverage, and honest deviations. Keep the specification at the repo root
untouched between experiments so it stays a controlled variable.
