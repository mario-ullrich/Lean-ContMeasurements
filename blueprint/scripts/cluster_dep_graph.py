"""Set the nodes of the blueprint's appendix apart in the dependency graph.

The appendix proves the Borsuk--Ulam theorem, which the two papers only cite.  In the
dependency graph its nodes form one cluster: a thin grey rounded frame labelled as the
appendix, in the style of the blocks of the sibling projects.  The nodes are read from
the blueprint source, as the labels of the theorem-like environments after `\\appendix`,
so a statement added to or removed from the appendix needs no change here.

The cluster is appended to the DOT text that the page passes to `renderDot`, before the
closing brace of the graph, which is followed by the unique anchor "`)".  Every name
listed must be a node of the graph, since Graphviz would draw a missing one as an empty
node; the script checks this and fails otherwise, as it does when the anchor or
`\\appendix` is missing.  A second run changes nothing.

Usage: python blueprint/scripts/cluster_dep_graph.py [PAGE]
with PAGE defaulting to blueprint/web/dep_graph_document.html.
"""

import io
import re
import sys

SOURCE = "blueprint/src/content.tex"
NAME = "cluster_borsuk_ulam"
LABEL = "Appendix: the Borsuk\u2013Ulam theorem"
ANCHOR = "}`)"
ENVIRONMENTS = ("theorem", "lemma", "proposition", "corollary", "definition")
BLOCK = re.compile(
    r"\\begin\{(" + "|".join(ENVIRONMENTS) + r")\}(.*?)\\end\{\1\}", re.S)
NODE_LABEL = re.compile(r"\\label\{([^}]*)\}")


def appendix_labels(source):
    """The labels of the theorem-like environments after `\\appendix`, in order."""
    text = io.open(source, encoding="utf-8").read()
    start = text.find("\n\\appendix")
    if start < 0:
        raise SystemExit(f"error: {source} has no \\appendix")
    labels = []
    for block in BLOCK.finditer(text, start):
        label = NODE_LABEL.search(block.group(2))
        if label:
            labels.append(label.group(1))
    if not labels:
        raise SystemExit(f"error: no labelled statement after \\appendix in {source}")
    return labels


def cluster(labels):
    """The DOT text of the cluster, with the attributes of the sibling projects' blocks."""
    nodes = " ".join(f'"{name}";' for name in labels)
    return (f' subgraph {NAME} {{ label="{LABEL}"; labeljust=l; fontcolor="#808080";'
            f' color="#b0b0b0"; style=rounded; penwidth=1; margin=12; {nodes} }}')


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "blueprint/web/dep_graph_document.html"
    page = io.open(path, encoding="utf-8", newline="").read()
    if NAME in page:
        print(f"{path}: already done")
        return
    j = page.find(ANCHOR)
    if j < 0 or page.find(ANCHOR, j + 1) >= 0:
        raise SystemExit(f"error: {path} has no unique {ANCHOR!r} -- has the template changed?")
    labels = appendix_labels(SOURCE)
    missing = [name for name in labels
               if not re.search(re.escape(f'"{name}"') + r"\s*\[", page[:j])]
    if missing:
        raise SystemExit(f"error: not nodes of the graph: {', '.join(missing)}")
    page = page[:j] + cluster(labels) + page[j:]
    io.open(path, "w", encoding="utf-8", newline="").write(page)
    print(f"{path}: {len(labels)} appendix nodes set apart")


if __name__ == "__main__":
    main()
