#!/usr/bin/env python3
"""Draw the dependency graph of the DiscreteStability Lean files.

Scans DiscreteStability/*.lean for theorem/def/structure declarations and, inside each
declaration's source, for references to the other declarations of this project.
Mathlib names are ignored. An edge A -> B means the source of A mentions B.

Usage (from the repository root, needs Graphviz `dot`):
    python3 scripts/dependency_graph.py
Writes docs/dependency-graph.dot, docs/dependency-graph.svg and
docs/dependency-graph-dark.svg (proof structure; definitions and hypotheses omitted).
"""
import glob
import html
import os
import re
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "DiscreteStability")
OUT = os.path.join(ROOT, "docs")

# Results that appear in the paper, with their numbering there.
PAPER = {
    "ascent": "Lemma 4.1",
    "step_mono": "(C1)",
    "step_strict": "(C2)",
    "segment_ge": "(C3)",
    "stable": "Thm 5.1(i)",
    "asympStable": "Thm 5.1(ii)",
    "asympStable_weighted": "Cor 5.2",
    "basin": "Thm 6.1",
}
FILES = ["Basin", "Stability", "Ascent", "Basic"]  # top-to-bottom cluster order

THEMES = {
    "light": dict(bg="#ffffff", fg="#1d2126", muted="#5d646d", line="#d6d8d2", edge="#7d848c",
                  node="#eef0ec", paper="#8a5a12", paper_fill="#f6ead2"),
    "dark": dict(bg="#0d1117", fg="#e6e8ea", muted="#9aa2ab", line="#353b42", edge="#8a929b",
                 node="#262b31", paper="#e4b464", paper_fill="#3a2d17"),
}

DECL = re.compile(r"^(?:private |protected |noncomputable )*(theorem|lemma|def|structure|abbrev)\s+([^\s({\[:]+)", re.M)
NS = re.compile(r"^(namespace|end)\s+(\S+)", re.M)


def strip_comments(s):
    s = re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), s, flags=re.S)
    return re.sub(r"--[^\n]*", "", s)


def scan():
    decls = []
    for path in sorted(glob.glob(os.path.join(SRC, "*.lean"))):
        fname = os.path.basename(path)[:-5]
        s = strip_comments(open(path, encoding="utf-8").read())
        ms = list(DECL.finditer(s))
        for i, m in enumerate(ms):
            stack = []
            for n in NS.finditer(s[: m.start()]):
                if n.group(1) == "namespace":
                    stack.append(n.group(2))
                elif stack and stack[-1] == n.group(2):
                    stack.pop()
            prefix = [x for x in stack if x != "DiscreteStability"]
            end = ms[i + 1].start() if i + 1 < len(ms) else len(s)
            decls.append(dict(name=".".join(prefix + [m.group(2)]), file=fname, kind=m.group(1),
                              line=s[: m.start()].count("\n") + 1, body=s[m.end():end]))
    names = {d["name"] for d in decls}
    short = {}
    for n in names:
        short.setdefault(n.split(".")[-1], set()).add(n)
    for d in decls:
        deps = set()
        for t in re.findall(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*", d["body"]):
            if t in names:
                deps.add(t)
            parts = t.split(".")
            if len(parts) > 1 and parts[0] in names:
                deps.add(parts[0])
            for j, p in enumerate(parts):
                for n in short.get(p, ()):
                    if j > 0 or "." not in n:
                        deps.add(n)
        for p in re.findall(r"\.([A-Za-z_][A-Za-z0-9_']*)", d["body"]):
            deps.update(short.get(p, ()))
        deps.discard(d["name"])
        d["deps"] = sorted(deps)
    return decls


def to_dot(decls, th):
    is_def = {d["name"]: d["kind"] in ("structure", "def") for d in decls}
    out = [
        "digraph DiscreteStability {",
        f'  rankdir=TB; newrank=true; nodesep=0.25; ranksep=0.45; bgcolor="{th["bg"]}"; pad=0.2;',
        f'  node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=11, margin="0.12,0.05",'
        f' color="{th["edge"]}", fillcolor="{th["node"]}", fontcolor="{th["fg"]}"];',
        f'  edge [color="{th["edge"]}", arrowsize=0.6];',
    ]
    for f in FILES:
        out.append(f'  subgraph cluster_{f} {{ label="{f}.lean"; labeljust=l; style=rounded; '
                   f'color="{th["line"]}"; fontname="Courier"; fontsize=11; fontcolor="{th["muted"]}";')
        for d in decls:
            if d["file"] != f or is_def[d["name"]]:
                continue
            n = d["name"]
            lab = f'<<FONT FACE="Courier">{html.escape(n)}</FONT>'
            extra = ""
            if n in PAPER:
                lab += f'<BR/><FONT POINT-SIZE="9">{PAPER[n]}</FONT>'
                extra = f', color="{th["paper"]}", fillcolor="{th["paper_fill"]}", penwidth=1.6'
            out.append(f'    "{n}" [label={lab}>{extra}];')
        out.append("  }")
    for d in decls:
        if is_def[d["name"]]:
            continue
        for t in d["deps"]:
            if not is_def[t]:
                out.append(f'  "{d["name"]}" -> "{t}";')
    out.append("}")
    return "\n".join(out) + "\n"


def main():
    decls = scan()
    os.makedirs(OUT, exist_ok=True)
    for theme, suffix in (("light", ""), ("dark", "-dark")):
        dot = to_dot(decls, THEMES[theme])
        if theme == "light":
            open(os.path.join(OUT, "dependency-graph.dot"), "w", encoding="utf-8").write(dot)
        svg = subprocess.run(["dot", "-Tsvg"], input=dot, capture_output=True, text=True, check=True).stdout
        open(os.path.join(OUT, f"dependency-graph{suffix}.svg"), "w", encoding="utf-8").write(svg)
    print(f"{len(decls)} declarations; wrote docs/dependency-graph.dot, .svg, -dark.svg")


if __name__ == "__main__":
    main()
