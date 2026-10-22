#!/usr/bin/env python3
# Produced for the AxiomProver formalization using AxiomCode.
"""mark.py <label> --decl Name[,Name2] [--ok]

Record the Lean declaration(s) of a blueprint node (\\lean{...}) and, with --ok, mark it
\\leanok. Use --ok only after Axile has verified the declaration (compiles, no sorry,
standard axioms only). Rewrites blueprint.tex in place, then regenerates blueprint.json.
"""
import argparse, re, subprocess, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
TEX = HERE / "blueprint.tex"
ap = argparse.ArgumentParser()
ap.add_argument("label"); ap.add_argument("--decl", required=True); ap.add_argument("--ok", action="store_true")
a = ap.parse_args()
s = TEX.read_text()
key = "\\label{%s}" % a.label
if key not in s:
    sys.exit(f"unknown label {a.label}")
i = s.index(key) + len(key)
# drop existing markup lines directly after the label
rest = s[i:]
rest = re.sub(r"\A(\n\\(lean\{[^}]*\}|leanok))+", "", rest)
ins = "\n\\lean{%s}" % a.decl + ("\n\\leanok" if a.ok else "")
TEX.write_text(s[:i] + ins + rest)
subprocess.run([sys.executable, str(HERE / "bptools.py"), "json"], check=True)
