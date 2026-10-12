#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): Specification.md v0.1 demo lineage, superseded by GW.Endpoint.Kernel.SigmaSpec and GW.Bridge; kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Render a scientific figure from the saved, inspectable numerical experiment."""

import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / "artifacts/numerical-demo.json").read_text())
rows = [r for r in data["experiment"] if r["raw"] is not None]
x = [r["actual_offset"] for r in rows]
plt.rcParams.update({"font.size": 11, "axes.spines.top": False, "axes.spines.right": False})
fig, axes = plt.subplots(1, 2, figsize=(11, 4.4), layout="constrained")
colors = ["#bf3b36", "#167469"]
for name, color, label in [("raw", colors[0], "Split SX + CH"), ("merged", colors[1], "Merged expression")]:
    axes[0].semilogx(x, [r[name] for r in rows], "o-", color=color, label=label, markersize=5)
    axes[1].loglog(x, [r[name + "_abs_error"] for r in rows], "o-", color=color, markersize=5)
axes[0].set_ylabel("Computed contribution (eV)")
axes[0].set_title("Cancellation loses the finite result", loc="left", fontsize=13)
axes[0].legend(frameon=False, loc="lower left")
axes[0].set_ylim(-0.08, 1.14)
axes[1].set_ylabel("Absolute error against exact rational oracle (eV)")
axes[1].set_title("Error for the same binary64 input", loc="left", fontsize=13)
for ax in axes:
    ax.invert_xaxis()
    ax.set_xlabel("Actual x - w (eV), approaching zero")
    ax.grid(alpha=0.2)
fig.suptitle("Occupied GPP pole: A = 4 eV$^3$, w = 1 eV", fontsize=16)
fig.savefig(ROOT / "artifacts/pole-cancellation.png", dpi=180)
fig.savefig(ROOT / "artifacts/pole-cancellation.pdf")
plt.close(fig)
print("Saved artifacts/pole-cancellation.png and .pdf")

