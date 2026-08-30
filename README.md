# triangle-free process

Talk preparation for **Hefty, Horn, King, Pfender — *Improving R(3,k) in just two bites*** (arXiv:2510.19718).

* [`TALK.md`](TALK.md) — full 2-hour transcript (14:00–16:00, break at 15:08), written for an
  audience with no prior background, with whiteboard cues, timing map, cheat sheet and expected questions.
* [`listen.html`](listen.html) — teleprompter: reads the spoken lines aloud in the browser (Web Speech API),
  scrolls itself, and shows a pacing table of speaking time against each part's slot.
* [`sim/triangle_free_process.c`](sim/triangle_free_process.c) — exact simulation of the triangle-free
  process, run to maximality; used to check the density constant quoted in the talk.
* [`sim/RESULTS.md`](sim/RESULTS.md) — the measured numbers.

Build scripts live in `sim/`: `build.py` renders `TALK.md` to `talk.html`; `extract.py` pulls the spoken
lines out of `TALK.md` and normalises the maths for speech; `mkpage.py` writes `listen.html`.
