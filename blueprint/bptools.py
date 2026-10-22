#!/usr/bin/env python3
# Produced for the AxiomProver formalization using AxiomCode.
"""Blueprint helpers for ThetaSignPatterns.

  python3 bptools.py verify            strip leanblueprint markup, run verify_graph.py
  python3 bptools.py json              write blueprint.json (nodes, deps, Lean decls, status)
  python3 bptools.py check-leanok      fail unless every node is leanok

blueprint.tex carries leanblueprint markup (\\lean{..}, \\leanok) inserted by mark.py.
AxiomCode's verify_graph.py rejects that markup, so `verify` checks a stripped copy.
"""
import json, re, subprocess, sys, tempfile
from pathlib import Path
HERE = Path(__file__).resolve().parent
TEX = HERE / "blueprint.tex"
ROOTS = "thm_12,thm_13,thm_14,thm_16"
MARKUP = re.compile(r"^\s*\\(lean\{[^}]*\}|leanok)\s*$")

def stripped_text():
    return "\n".join(l for l in TEX.read_text().split("\n")
                     if not MARKUP.match(l) and not l.startswith("\\newcommand{\\lean"))

def verify():
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / "blueprint.tex"
        p.write_text(stripped_text())
        r = subprocess.run([sys.executable, str(HERE / "verify_graph.py"), str(p), "--root", ROOTS])
        return r.returncode

def nodes():
    sys.path.insert(0, str(HERE))
    import verify_graph as vg
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / "blueprint.tex"
        p.write_text(stripped_text())
        ns, order, *_ = vg.parse([p], None)
    raw = TEX.read_text()
    out = []
    for lab in order:
        n = ns[lab]
        i = raw.index("\\label{%s}" % lab)
        j = raw.find("\\begin{", i + 1)
        seg = raw[i: j if j > 0 else len(raw)]
        decls = re.findall(r"\\lean\{([^}]*)\}", seg)
        decls = [x.strip() for d in decls for x in d.split(",") if x.strip()]
        out.append(dict(label=lab, kind=n["env"],
                        statement_uses=sorted(n["stmt_edges"]),
                        proof_uses=sorted(n["out"] - n["stmt_edges"]),
                        lean=decls, leanok=("\\leanok" in seg),
                        external=lab.startswith("prop_E")))
    return out

def write_json():
    ns = nodes()
    data = dict(title="On sign patterns of Fourier coefficients of theta quotients",
                roots=ROOTS.split(","), verified_with="verify_graph.py (AxiomCode), markup stripped",
                lean_root="blessed/ThetaSignPatterns", nodes=ns,
                summary=dict(total=len(ns), leanok=sum(n["leanok"] for n in ns)))
    (HERE / "blueprint.json").write_text(json.dumps(data, indent=1) + "\n")
    print(f"blueprint.json: {len(ns)} nodes, {data['summary']['leanok']} leanok")

if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "verify"
    if cmd == "verify":
        sys.exit(verify())
    if cmd == "json":
        write_json()
    if cmd == "check-leanok":
        bad = [n["label"] for n in nodes() if not n["leanok"]]
        print("not leanok:", bad if bad else "none")
        sys.exit(1 if bad else 0)
