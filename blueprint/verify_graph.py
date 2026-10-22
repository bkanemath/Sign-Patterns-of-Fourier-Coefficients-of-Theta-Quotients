#!/usr/bin/env python3
# Produced for the AxiomProver formalization using AxiomCode.
"""
verify_graph.py -- dependency-graph verifier for formalization blueprints
(the /blueprint skill).

A blueprint is a LaTeX file (or a directory of section files) whose declarations
(definition / notation / lemma / proposition / theorem, and optionally corollary
/ sublemma) each carry a \\label, and whose dependency edges are recorded in the
ENVIRONMENT form

    \\begin{uses-statement} \\ref{a}, \\ref{b} \\end{uses-statement}
    \\begin{uses-proof}     \\ref{c}          \\end{uses-proof}

placed immediately after the statement (uses-statement / uses-notation) and
after the proof (uses-proof). The COMMAND form is also accepted -- `\\uses{a, b}`
in the body is a statement dep, `\\uses{c}` inside the proof is a proof dep --
which is what axiom-dashboard's `extract` parses. This tool reads those, NOT
prose \\ref, and checks the invariants the /blueprint skill requires:

  * forward refs   : every edge target is defined earlier in the file
  * undefined refs : every edge target is some declaration's \\label
  * orphans        : every declaration except the declared sink(s) has
                     in-degree >= 1
  * cycles         : the edge graph is acyclic (a DAG)
  * def -> lemma   : a definition/notation never cites a provable statement
  * thoroughness   : every \\ref in a statement/proof span (excluding uses-*
                     blocks) is listed in that entity's uses-* blocks
  * stmt :=        : no ':=' inside a lemma/sublemma/theorem/proposition/
                     corollary statement body (objects belong in definitions)
  * stmt-cites-
    lemma-as-source: no prose in a statement that treats a lemma as an
                     object source, e.g. 'as in Lemma X', 'defined by
                     Lemma X', 'from Lemma X' where X is a provable label
  * leanblueprint  : no \\lean / \\leanok / \\notready / \\proves markup. We do
                     not use Massot's leanblueprint, and a blueprint never
                     names a Lean declaration -- that name is chosen when the
                     node is formalized, not guessed here

It also flags disallowed environments (remark / corollary) as a hygiene note.

NOT EVERY PROJECT USES THE SAME TAG SCHEME OR HAS A SINGLE SINK, so nothing
about either is hardcoded:

  * `--tag-regex` filters which \\label counts as a canonical entity tag
    (e.g. `^T\\d{3,4}[a-z]?$` for tamagawa's TXXX labels). Default: read
    `[tag] regex` from dashboard.toml; failing that, accept every label.
  * `--root` takes a comma-separated list, so a multi-sink blueprint (a paper
    with several independent headline results) can declare all its sinks.
    `--multi-sink` downgrades the orphan check to a note entirely.
  * Several .tex files may be passed (or a directory / glob), for flat
    blueprints whose sections are separate files; they are concatenated in the
    given order, which must be document order.

**A parse of ZERO declarations is a hard FAILURE, never a pass.** If the tag
scheme or the environment names don't match what this tool looks for, it finds
nothing, every invariant is vacuously satisfied, and a green result would be
worse than no check at all. In that case the tool says so and exits non-zero.

Usage:
    python3 verify_graph.py <blueprint.tex> [more.tex ...] [--root thm_main]
    python3 verify_graph.py blueprint/src/Sections --tag-regex '^T\\d{3,4}[a-z]?$' \\
        --multi-sink

Exit code 0 iff all invariants pass AND at least one declaration was parsed.
"""

import argparse
import collections
import re
import sys
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # Python < 3.11
    try:
        import tomli as tomllib  # type: ignore[no-redef]
    except ModuleNotFoundError:
        tomllib = None  # type: ignore[assignment]

#: The environments `preamble.tex` permits, and nothing else: "ONLY these
#: environments carry mathematical content: definition, notation, lemma,
#: proposition, theorem (+ their proofs). No remark, no corollary."
DECL_ENVS = ["definition", "notation", "lemma", "proposition", "theorem"]
PROVABLE = {"lemma", "proposition", "theorem"}
DEFLIKE = {"definition", "notation"}
#: Environments a blueprint may not use. `corollary` used to sit in BOTH this
#: list and DECL_ENVS, so the same file counted it as a declaration and
#: flagged it as forbidden.
DISALLOWED = ["remark", "corollary"]

#: A LABELLED equation is a declaration in disguise -- an entity the extractor
#: picks up that the blueprint never meant to declare. The preamble's
#: `[equation]` is a shared COUNTER, and reading it as an environment is how
#: tagged equations came to be treated as entities at all.
DISALLOWED_LABELLED = ["equation"]

BEGIN_DECL = re.compile(r"\\begin\{(" + "|".join(DECL_ENVS) + r")\}")
LABEL = re.compile(r"\\label\{([^}]+)\}")
REF = re.compile(r"\\(?:ref|eqref|autoref|cref|Cref)\{([^}]+)\}")

# A6 checks: forbid `:=` and lemma-as-object-source prose inside a
# provable-statement body.  The prose regex is deliberately narrow --
# it targets the clearest object-introduction shapes:
#   "defined by/via/in/through Lemma X"
#   "as in Lemma X"
#   "witnesses of Lemma X"
# Bare "from Lemma X" and "of Lemma X" are excluded because they show up
# in benign non-introduction contexts (e.g. "conclusion of Lemma X" is
# a citation, not an object-source claim).  Genuine object-source uses
# of those bare prepositions can be caught by a second pass with a wider
# regex if needed.
STMT_ASSIGN = re.compile(r":=")
STMT_LEMMA_SOURCE = re.compile(
    r"(?:defined\s+(?:by|via|in|through)|(?<!same\s)(?<!combine\s)as\s+in|witnesses?\s+of)"
    r"\s+(?:Lemma|Sublemma|Theorem|Proposition|Corollary)~?"
    r"\\(?:ref|autoref|cref|Cref)\{([^}]+)\}"
)
# Only meaningful for prefix-based tag schemes (`lem_x`, `thm_main`). Projects
# whose tags are opaque tokens (stacks' `01AB`, tamagawa's `T030`) get this
# check skipped with a note rather than a silent pass -- see `--tag-regex`.
PROVABLE_PREFIXES = ("lem_", "slem_", "prop_", "thm_", "cor_")


def env_block_refs(text, env):
    """All \\ref targets inside every \\begin{env}...\\end{env} block in text."""
    out = set()
    for m in re.finditer(r"\\begin\{" + env + r"\}(.*?)\\end\{" + env + r"\}", text, re.DOTALL):
        out.update(r.strip() for r in REF.findall(m.group(1)))
    return out


def env_block_text(text, env):
    """Concatenate the bodies of every \\begin{env}...\\end{env} block in text."""
    parts = []
    for m in re.finditer(r"\\begin\{" + env + r"\}(.*?)\\end\{" + env + r"\}", text, re.DOTALL):
        parts.append(m.group(1))
    return "\n".join(parts)


def strip_uses(text):
    text = re.sub(
        r"\\begin\{uses-(statement|proof|notation)\}.*?"
        r"\\end\{uses-\1\}",
        "",
        text,
        flags=re.DOTALL,
    )
    return re.sub(r"\\uses\{[^}]*\}", "", text)


# Both blueprint dialects are accepted. The env form
# (`\begin{uses-statement} … \end{uses-statement}`) is this skill's; the command
# form (`\uses{a, b}` in the body, `\uses{c}` inside the proof) is what
# axiom-dashboard's `extract` parses. A blueprint may use either, and shipping
# two components that disagree just forces the author to write an adapter.
CMD_USES = re.compile(r"\\uses\{([^}]*)\}")

# Massot leanblueprint markup. We do not use leanblueprint; in particular a
# blueprint never names a Lean declaration.
LEANBLUEPRINT = re.compile(r"\\(lean|leanok|notready|proves|discussion|home)\b")


def cmd_uses(text):
    out = set()
    for m in CMD_USES.finditer(text):
        out.update(t.strip() for t in m.group(1).split(",") if t.strip())
    return out


def env_span(text, env):
    """The concatenated bodies of every `\\begin{env} … \\end{env}` in text."""
    return "\n".join(
        m.group(1)
        for m in re.finditer(r"\\begin\{" + env + r"\}(.*?)\\end\{" + env + r"\}", text, re.DOTALL)
    )


def find_repo_root(start):
    """Nearest ancestor holding a dashboard.toml, else None."""
    start = Path(start).resolve()
    for candidate in (start, *start.parents):
        if (candidate / "dashboard.toml").is_file():
            return candidate
    return None


def config_tag_regex(anchor):
    """`[tag] regex` from the repo's dashboard.toml, if there is one."""
    root = find_repo_root(anchor)
    if root is None or tomllib is None:
        return None
    try:
        with open(root / "dashboard.toml", "rb") as f:
            return tomllib.load(f).get("tag", {}).get("regex")
    except Exception:  # noqa: BLE001
        return None


def collect_tex(inputs):
    """Expand file / directory / glob arguments into an ordered .tex list."""
    out = []
    for item in inputs:
        p = Path(item)
        if p.is_dir():
            out.extend(sorted(p.glob("*.tex")))
        elif p.is_file():
            out.append(p)
        else:  # treat as a glob relative to cwd
            matched = sorted(Path().glob(item))
            if not matched:
                print(f"error: {item} is not a file, directory or matching glob", file=sys.stderr)
                return None
            out.extend(matched)
    return out


def parse(paths, tag_re):
    """Parse declarations across `paths`, concatenated in the order given."""
    lines, origin = [], []
    for path in paths:
        text = Path(path).read_text(encoding="utf-8").split("\n")
        for i, line in enumerate(text):
            lines.append(line)
            origin.append((path, i + 1))
    # segment at each declaration \begin
    starts = [(i, m.group(1)) for i, l in enumerate(lines) for m in [BEGIN_DECL.search(l)] if m]
    nodes = {}  # label -> dict(env, line, out, stmt_edges, span_refs)
    order = []  # labels in file order
    skipped_labels = 0  # labels seen but rejected by --tag-regex
    for idx, (start, env) in enumerate(starts):
        end = starts[idx + 1][0] if idx + 1 < len(starts) else len(lines)
        chunk = "\n".join(lines[start:end])
        candidates = [c.strip() for c in LABEL.findall(chunk)]
        if not candidates:
            continue
        if tag_re is not None:
            matching = [c for c in candidates if tag_re.match(c)]
            if not matching:
                skipped_labels += len(candidates)
                continue
            lab = matching[0]
        else:
            lab = candidates[0]
        us = env_block_refs(chunk, "uses-statement")
        up = env_block_refs(chunk, "uses-proof")
        # command form: \uses{} in the proof is a proof dep, anywhere else a
        # statement dep.
        proof_text = env_span(chunk, "proof")
        up |= cmd_uses(proof_text)
        us |= cmd_uses(chunk) - cmd_uses(proof_text)
        # refs appearing in the declaration env or its proof, excluding uses-*
        bare = strip_uses(chunk)
        span = set()
        for e in [env, "proof"]:
            for m in re.finditer(r"\\begin\{" + e + r"\}(.*?)\\end\{" + e + r"\}", bare, re.DOTALL):
                span.update(r.strip() for r in REF.findall(m.group(1)))
        stmt_text = env_block_text(chunk, env)
        nodes[lab] = dict(
            env=env,
            line=start + 1,
            out=us | up,
            stmt_edges=us,
            span=span,
            stmt_text=stmt_text,
            where=origin[start],
        )
        order.append(lab)
    return nodes, order, lines, len(starts), skipped_labels


def main():
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument(
        "tex",
        nargs="+",
        type=str,
        help="blueprint .tex file(s), a directory of sections, or a "
        "glob — concatenated in the order given (= document order)",
    )
    ap.add_argument(
        "--root",
        default="thm_main",
        help="comma-separated label(s) of the target theorem(s) — the "
        "DAG sink(s); default thm_main. A multi-sink blueprint "
        "lists all of them.",
    )
    ap.add_argument(
        "--multi-sink",
        action="store_true",
        help="the blueprint legitimately has many sinks (several "
        "independent headline results): report in-degree-0 nodes "
        "as a note instead of failing",
    )
    ap.add_argument(
        "--tag-regex",
        default=None,
        help=r"which \label counts as a canonical entity tag, e.g. "
        r"'^T\d{3,4}[a-z]?$'. Default: [tag] regex from the "
        "repo's dashboard.toml, else every label",
    )
    args = ap.parse_args()

    paths = collect_tex(args.tex)
    if not paths:
        return 2

    pattern = args.tag_regex or config_tag_regex(paths[0].parent)
    tag_re = re.compile(pattern) if pattern else None

    nodes, order, lines, decl_blocks, skipped = parse(paths, tag_re)
    labels = set(nodes)
    roots = {r.strip() for r in args.root.split(",") if r.strip()}

    # ---- Vacuous-green guard. A verifier that understood nothing must never
    # ---- report a pass: every invariant below is trivially satisfied by an
    # ---- empty graph, so a green here would be actively misleading.
    if not labels:
        print(f"verify_graph: {', '.join(str(p) for p in paths)}")
        print("  declarations: 0")
        print("\nNO DECLARATIONS PARSED — THIS IS A FAILURE, NOT A PASS.")
        print("  This tool understood nothing about your blueprint, so every")
        print("  invariant below would be vacuously satisfied. Likely causes:")
        if decl_blocks and skipped:
            print(
                f"  * {decl_blocks} declaration environments were found but all "
                f"{skipped} of their labels were rejected by the tag regex "
                f"({pattern!r}) — fix --tag-regex / [tag] regex."
            )
        elif decl_blocks:
            print(
                f"  * {decl_blocks} declaration environments were found but none carried a \\label."
            )
        else:
            print(
                "  * no declaration environments found: this blueprint may use "
                f"environment names outside {DECL_ENVS}, or you pointed the tool "
                "at a thin \\documentclass root instead of the section files "
                "that hold the content."
            )
        print("  Fix the invocation (or use a project-specific verifier) and re-run.")
        return 2

    forward, undefined, deflemma, thorough = [], [], [], []
    stmt_assign, stmt_lem_source = [], []
    indeg = {l: 0 for l in labels}
    adj = {l: set() for l in labels}

    for lab, d in nodes.items():
        for t in d["out"]:
            if t not in labels:
                undefined.append((lab, t))
                continue
            if nodes[t]["line"] > d["line"]:
                forward.append((lab, t))
            indeg[t] += 1
            adj[lab].add(t)
            if d["env"] in DEFLIKE and nodes[t]["env"] in PROVABLE:
                deflemma.append((lab, t))
        for r in d["span"]:
            if r in labels and r != lab and r not in d["out"]:
                thorough.append((lab, r))
        # A6: forbid `:=` and lemma-as-object-source prose inside a
        # provable-statement body.
        if d["env"] in PROVABLE:
            body = d.get("stmt_text", "")
            for _ in STMT_ASSIGN.finditer(body):
                stmt_assign.append((lab,))
            for m in STMT_LEMMA_SOURCE.finditer(body):
                target = m.group(1).strip()
                # For a prefix-based scheme, only provable targets count. For an
                # opaque scheme the prefix says nothing, so use the parsed env.
                is_provable = target.startswith(PROVABLE_PREFIXES) or (
                    target in nodes and nodes[target]["env"] in PROVABLE
                )
                if is_provable:
                    stmt_lem_source.append((lab, target))

    sinks = sorted(l for l in labels if indeg[l] == 0)
    orphans = [] if args.multi_sink else [l for l in sinks if l not in roots]
    missing_roots = sorted(r for r in roots if r not in labels)
    if missing_roots and not args.multi_sink:
        print(
            f"warning: root label(s) {', '.join(missing_roots)} not found; "
            "pass --root (comma-separated) or --multi-sink",
            file=sys.stderr,
        )

    # cycle detection (Kahn over the edge graph)
    ind = {l: 0 for l in labels}
    for s in labels:
        for t in adj[s]:
            ind[t] += 1
    q = collections.deque(l for l in labels if ind[l] == 0)
    seen = 0
    while q:
        x = q.popleft()
        seen += 1
        for t in adj[x]:
            ind[t] -= 1
            if ind[t] == 0:
                q.append(t)
    cyclic = seen != len(labels)

    # Disallowed environments. NOT hygiene: the preamble says these carry no
    # mathematical content, so a blueprint using one is malformed. Saying so in a
    # note that still exits 0 is how HCL I came to hold a labelled remark and two
    # labelled equations with a clean verifier.
    disallowed = []
    for i, l in enumerate(lines):
        for env in DISALLOWED:
            if re.search(r"\\begin\{" + env + r"\}", l):
                disallowed.append((env, i + 1))
    for env in DISALLOWED_LABELLED:
        for start in [k for k, l in enumerate(lines) if re.search(r"\\begin\{" + env + r"\}", l)]:
            body = "\n".join(lines[start : start + 12]).split("\\end{" + env + "}")[0]
            if "\\label{" in body:
                disallowed.append((env + " (labelled)", start + 1))

    # We do not use Massot's leanblueprint, and a blueprint never names Lean
    # declarations: the formal name is chosen at formalization time, against the
    # library as it then stands. A guessed name is either wrong or silently
    # becomes a constraint nobody agreed to. Blocking, not advisory.
    leanblueprint = []
    for i, l in enumerate(lines):
        for m in LEANBLUEPRINT.finditer(l):
            leanblueprint.append((m.group(1), i + 1))

    def show(name, items, fmt):
        bad = len(items)
        mark = "ok " if bad == 0 else "FAIL"
        print(f"  [{mark}] {name:<26} {bad}")
        for it in items[:20]:
            print(f"           {fmt(it)}")

    print(f"verify_graph: {', '.join(str(p) for p in paths)}")
    sink_desc = "multi-sink" if args.multi_sink else ", ".join(sorted(roots))
    print(
        f"  declarations: {len(labels)}   sink(s): {sink_desc}"
        + (f"   tag regex: {pattern}" if pattern else "")
    )
    if skipped:
        print(
            f"  [note] {skipped} label(s) skipped by the tag regex "
            "(cross-ref anchors, not entities)"
        )
    show("forward references", forward, lambda t: f"{t[0]} -> {t[1]} (later)")
    show("undefined references", undefined, lambda t: f"{t[0]} -> {t[1]} (no label)")
    if args.multi_sink:
        print(f"  [note] sinks (in-degree 0)      {len(sinks)}")
        for s in sinks[:20]:
            print(f"           {s}")
    else:
        show("orphans (in-degree 0)", [(o,) for o in orphans], lambda t: t[0])
    print(f"  [{'ok ' if not cyclic else 'FAIL'}] {'cycles':<26} {'present' if cyclic else 0}")
    show("def/not -> provable", deflemma, lambda t: f"{t[0]} -> {t[1]}")
    show("thoroughness", thorough, lambda t: f"{t[0]} refs {t[1]} but not in uses-*")
    show("stmt := (A6)", stmt_assign, lambda t: f"{t[0]}: `:=` inside a provable statement body")
    show(
        "stmt cites lemma as source (A6)",
        stmt_lem_source,
        lambda t: f"{t[0]}: statement treats {t[1]} as an object source",
    )
    show(
        "leanblueprint markup",
        leanblueprint,
        lambda t: (
            rf"line {t[1]}: \{t[0]} — we do not use leanblueprint, and a "
            "blueprint does not name Lean declarations"
        ),
    )
    if disallowed:
        print(f"  [FAIL] disallowed environments  {len(disallowed)}")
        for env, ln in disallowed[:20]:
            print(f"           line {ln}: {env}")

    ok = not (
        forward
        or undefined
        or orphans
        or cyclic
        or deflemma
        or thorough
        or stmt_assign
        or stmt_lem_source
        or leanblueprint
        or disallowed
    )
    print("\n" + ("ALL GRAPH INVARIANTS PASS" if ok else "INVARIANT VIOLATIONS PRESENT"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
