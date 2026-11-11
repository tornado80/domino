#!/usr/bin/env python3
"""A throwaway prototype of the blind walk of docs/proving-algorithm.md section 7.4, over
`easycrypt cli -json` (story 101). It wrote the oracle proofs of this directory. Story 103
implements the real walk in Rust; this script is not used by any test.

usage: blind_walk.py <dir> <file.ec>
<dir> holds an exported tree with the prototype files copied in. The one lemma of <file.ec>
must start its proof with `proc; inline *.` followed by `admit.`. The walked script (to replace
`admit.`) goes to stdout, every refused trial and every admit to stderr.

Simplifications against section 7.4: no timeouts, no budget but a step cap, `sp k l` counts
are the leading assignments of each side, the leaf is `skip => />; smt().` after the quick
close, and a side goal is `auto => /#.` then `smt().`. Run it under a memory cap.
"""
import json, re, subprocess, sys

inc, path = sys.argv[1], sys.argv[2]
src = open(path).read()
head = src[: src.index("proc; inline *.\n") + len("proc; inline *.\n")]

ec = subprocess.Popen(["easycrypt", "cli", "-json", "-I", inc], stdin=subprocess.PIPE,
                      stdout=subprocess.PIPE, text=True, bufsize=1, cwd=inc)
LOG = []


def send(sentence):
    ec.stdin.write(json.dumps({"sentence": sentence, "want": "full"}) + "\n")
    ec.stdin.flush()
    return json.loads(ec.stdout.readline())


def sentences(text):
    # split on a full stop at the end of a line, outside comments
    out, cur = [], []
    for line in text.split("\n"):
        if line.startswith("(*") or not line.strip():
            continue
        cur.append(line)
        if line.rstrip().endswith("."):
            out.append("\n".join(cur)); cur = []
    return out


state = None
for s in sentences(head):
    r = send(s)
    if r["status"] != "ok":
        sys.exit(f"prefix failed at {s!r}: {r.get('error')}")
    state = r


def ngoals(r):
    p = r.get("proof")
    return 0 if not p else len(p["kinds"])


def front(r):
    p = r.get("proof")
    return p and p.get("front")


def tryit(sentence, cur):
    r = send(sentence)
    if r["status"] == "ok":
        return r
    LOG.append(f"  refused: {sentence}  -- {(r.get('error') or {}).get('msg','')[:100]}")
    # a refused sentence leaves the state as it was
    return None


def lead_asgn(stmt):
    n = 0
    for i in stmt:
        if i["kind"] != "asgn":
            break
        n += 1
    return n


def walk(cur, budget=200):
    """Close the front goal of `cur`. Returns (lines, resp)."""
    lines = []
    base = ngoals(cur)
    while ngoals(cur) >= base and budget > 0:
        budget -= 1
        g = front(cur)
        c = g["concl"]
        if c["kind"] != "equivS":
            for s in ("auto => /#.", "smt()."):
                r = tryit(s, cur)
                if r is not None:
                    lines.append(s); return lines, r
            LOG.append("ADMIT side goal: " + g["text"][-300:])
            lines.append("admit."); return lines, send("admit.")
        r = tryit("auto => /#.", cur)  # quick close
        if r is not None and ngoals(r) < base:
            lines.append("auto => /#.")
            return lines, r
        if r is not None:  # did not close: undo
            r = send(f"undo {cur['state']}.")
            if r["status"] != "ok":
                sys.exit(f"undo failed: {r.get('error')}")
        L, R = c["left"]["stmt"], c["right"]["stmt"]
        k, l = lead_asgn(L), lead_asgn(R)
        if k or l:
            r = tryit(f"sp {k} {l}.", cur)
            if r is None:
                LOG.append("ADMIT sp refused"); lines.append("admit."); return lines, send("admit.")
            lines.append(f"sp {k} {l}."); cur = r
            continue
        if not L and not R:
            r = tryit("skip => />; smt().", cur)
            if r is None:
                LOG.append("ADMIT leaf: " + g["text"][-400:])
                lines.append("admit."); return lines, send("admit.")
            lines.append("skip => />; smt()."); return lines, r
        done = False
        for i, S in ((1, L), (2, R)):
            if S and S[0]["kind"] == "if":
                for t in ("rcondt", "rcondf"):
                    s = f"{t}{{{i}}} ^if; 1: auto => /#."
                    r = tryit(s, cur)
                    if r is not None:
                        lines.append(s); cur = r; done = True; break
            if done:
                break
        if done:
            continue
        if L and R and L[0]["kind"] == "if" and R[0]["kind"] == "if":
            r = tryit("if.", cur)
            if r is not None:
                lines.append("if.")
                n = ngoals(r) - ngoals(cur) + 1
                cur = r
                for _ in range(n):
                    sub, cur = walk(cur)
                    lines.append("+ " + sub[0]); lines += ["  " + x for x in sub[1:]]
                return lines, cur
        for i, S in ((1, L), (2, R)):
            if S and S[0]["kind"] == "if":
                r = tryit(f"if{{{i}}}.", cur)
                if r is not None:
                    lines.append(f"if{{{i}}}.")
                    n = ngoals(r) - ngoals(cur) + 1
                    cur = r
                    for _ in range(n):
                        sub, cur = walk(cur)
                        lines.append("+ " + sub[0]); lines += ["  " + x for x in sub[1:]]
                    return lines, cur
        if L and R and L[0]["kind"] == "rnd" and R[0]["kind"] == "rnd":
            x, y = L[0]["lvalue"]["pp"], R[0]["lvalue"]["pp"]
            s = f"seq 1 1 : (#pre /\\ {x}{{1}} = {y}{{2}}); 1: auto => /#."
            r = tryit(s, cur)
            if r is not None:
                lines.append(s); cur = r; continue
        LOG.append("ADMIT program-mismatch: heads " + str([i["kind"] for i in L[:1]]) + str([i["kind"] for i in R[:1]]))
        lines.append("admit."); return lines, send("admit.")
    return lines, cur


lines, cur = walk(state)
print("\n".join(lines))
print("--- remaining goals:", ngoals(cur), file=sys.stderr)
print("\n".join(LOG), file=sys.stderr)
ec.stdin.close()
