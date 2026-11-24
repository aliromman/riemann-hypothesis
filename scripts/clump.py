#!/usr/bin/env python3
"""Combine small modules into larger files ("clumps") along the import graph, and undo it.

A clump is a coarsening of the import graph: a module R (the clump root) together with
modules whose only project importer lies inside the clump.  Contracting such a set can never
create an import cycle, and every module outside the clump that imported a member imported R,
so the clump file keeps R's module name and path.  No importer anywhere needs rewriting; the
other members' files are deleted.

The file lists the members in dependency order. Short comments mark their Lean
scopes. Members with the same initial namespace opens can share those opens.
The table at the end of the file contains the original import headers.

The command also reads the earlier layout with a marker before and after each member.
Edits to a shared open apply to each member in that group.

`clump.py unclump` splits clump files back into the original files, byte for byte, provided
the member bodies were not edited.  If they were, it still restores the edited bodies; the
original import headers are restored as recorded.

Usage:
    clump.py plan   ROOT [--max-lines N] [--out plan.json]
    clump.py apply  ROOT plan.json
    clump.py unclump ROOT
    clump.py blame  ROOT build.log...   # members containing build errors, for clump-exclude.txt

Members that fail to compile once clumped (e.g. because a sibling member's declarations or
imports change how a name resolves) are listed in scripts/clump-exclude.txt and stay standalone.
"""

import argparse
import collections
import json
import os
import re
import subprocess
import sys

SEAM_BEGIN = "-- ===== clump member: "
SEAM_END = "-- ===== end clump member: "
HEADER_TAG = "-- clump-header: "
AUTO = " -- clump:auto"
MEMBER_TAG = "-- clump member: "
SHARED_OPENS = "-- clump: shared namespace opens"
END_SHARED = "end " + SHARED_OPENS
PUBLIC_SECTIONS = ("@[expose] public section", "@[expose] public noncomputable section")
MEMBER_PREFIXES = ("", "section ", *(s + " " for s in PUBLIC_SECTIONS))
END_WORD = re.compile(r"\bend\b")
NAMED_END = re.compile(r"end [A-Z][\w'.]*(?:\s*--.*)?\Z")
NAME = r"[^\W\d][\w'.]*"
OPEN_NAMES = re.compile(rf"open (?:scoped )?{NAME}(?: +{NAME})*\Z")
CLUMP_MARK = "-- This file was produced by scripts/clump.py from the modules listed below."

# Modules in these libraries are never clumped (protected statement / solution files).
PROTECTED_LIBS = {"Main", "Challenge"}

IMPORT_RE = re.compile(r"^((?:(?:public|private|meta)\s+)*)import\s+((?:all\s+)?)(\S+)\s*$")


def lib_of(mod):
    """Return the lake library a module belongs to (mirrors lakefile.toml)."""
    if mod in ("Statements", "Main"):
        return "Main"
    if mod == "Challenge":
        return "Challenge"
    parts = mod.split(".")
    if parts[0] == "GroundTheory" and len(parts) > 1 and parts[1] in ("LocalFields", "GlobalFields"):
        return "GroundTheoryFields"
    return parts[0]


class Module:
    __slots__ = ("name", "path", "header", "body", "imports", "lines", "exotic", "decls", "scopes")

    def __init__(self, name, path, text):
        self.name = name
        self.path = path
        lines = text.split("\n")
        h = 0
        imports = []  # (module, public: bool)
        exotic = False
        for i, l in enumerate(lines):
            s = l.strip()
            if s == "" or s == "module":
                continue
            m = IMPORT_RE.match(s)
            if m:
                mods = m.group(1).split()
                if m.group(2) or "meta" in mods:
                    exotic = True
                imports.append((m.group(3), "public" in mods))
                continue
            h = i
            break
        else:
            h = len(lines)
        self.header = "\n".join(lines[:h]) + ("\n" if h < len(lines) else "")
        self.body = "\n".join(lines[h:])
        self.imports = imports
        # Size counts the body plus seam overhead; imports are deduplicated in the clump header.
        self.scopes, self.decls = scan(self.body)
        self.lines = self.body.count("\n") + 6 + len(self.scopes)
        self.exotic = exotic

    @property
    def already_clumped(self):
        return is_clump_file(self)


PlanModule = collections.namedtuple("PlanModule", "imports lines exotic decls already_clumped")


def iter_modules(root, names=None):
    """Read each selected tracked Lean source once."""
    out = subprocess.run(["git", "-C", root, "ls-files", "-z", "src/*.lean"],
                         capture_output=True, check=True).stdout.decode()
    for p in out.split("\0"):
        if not p:
            continue
        name = p[len("src/"):-len(".lean")].replace("/", ".")
        if names is not None and name not in names:
            continue
        with open(os.path.join(root, p), encoding="utf-8") as f:
            mod = Module(name, p, f.read())
        yield mod


def load(root, names=None):
    """Read the complete tracked modules selected by name."""
    return {m.name: m for m in iter_modules(root, names)}


def load_for_plan(root):
    """Keep the import graph, declaration names and sizes needed by the planner."""
    return {m.name: PlanModule(m.imports, m.lines, m.exotic, m.decls, m.already_clumped)
            for m in iter_modules(root)}


# ---------------------------------------------------------------------------
# Planning

def plan(mods, max_lines, exclude=frozenset()):
    deps = {m: list(dict.fromkeys(x for x, _ in mods[m].imports if x in mods)) for m in mods}
    rev = collections.defaultdict(list)
    for m, ds in deps.items():
        for x in ds:
            rev[x].append(m)

    def clumpable(m):
        return (lib_of(m) not in PROTECTED_LIBS and not mods[m].exotic and m not in exclude
                and not mods[m].already_clumped)

    # Reverse topological order: dependencies before importers.
    indeg = {m: len(deps[m]) for m in mods}
    ready = sorted(m for m in mods if indeg[m] == 0)
    order = []
    while ready:
        m = ready.pop()
        order.append(m)
        for u in rev[m]:
            indeg[u] -= 1
            if indeg[u] == 0:
                ready.append(u)
    if len(order) != len(mods):
        sys.exit("import graph has a cycle")

    members = {m: [m] for m in mods}
    body = {m: mods[m].lines for m in mods}  # summed body lines of the clump rooted here
    imps = {m: {x for x, _ in mods[m].imports} for m in mods}  # union of members' imports
    names = {m: mods[m].decls for m in mods}  # top-level declaration names in the clump

    def total(b, i, mem):  # output lines: header (deduplicated imports) + bodies
        return b + len(i) - len(mem) + 6

    absorbed = set()
    clashes = [0]
    for v in order:
        if not clumpable(v):
            continue
        kids = [c for c in deps[v]
                if rev[c] == [v] and clumpable(c) and lib_of(c) == lib_of(v)]
        kids.sort(key=lambda c: (body[c], c))
        for c in kids:
            b = body[v] + body[c]
            i = imps[v] | imps[c]
            mem = members[v] + members[c]
            if total(b, i, mem) > max_lines:
                continue
            if not names[v].isdisjoint(names[c]):
                # Declarations that coexisted in separate modules (private ones, or
                # duplicates that no single module ever imported together) clash in one file.
                clashes[0] += 1
                continue
            body[v], imps[v], members[v] = b, i, mem
            names[v] = names[v] | names[c]
            absorbed.add(c)
    print(f"refused {clashes[0]} folds because of clashing declaration names", file=sys.stderr)
    clumps = {}
    for r in mods:
        if r in absorbed or len(members[r]) == 1:
            continue
        clumps[r] = linearise(r, set(members[r]), deps)
    return clumps


def linearise(root, mem, deps):
    """DFS post-order from the root over imports inside the clump: dependencies first."""
    seen, out = set(), []
    stack = [(root, iter(deps[root]))]
    seen.add(root)
    while stack:
        m, it = stack[-1]
        for x in it:
            if x in mem and x not in seen:
                seen.add(x)
                stack.append((x, iter(deps[x])))
                break
        else:
            stack.pop()
            out.append(m)
    assert set(out) == mem and out[-1] == root
    return out


# ---------------------------------------------------------------------------
# Scope tracking: which sections / namespaces does a body leave open?

NAME_PART = re.compile(r"(?:«[^»]*»|[^\s.«»-])+")
SCOPE_NAME = rf"({NAME_PART.pattern}(?:\.{NAME_PART.pattern})*)"
SECTION_RE = re.compile(
    rf"^(?:@\[[^\]]*\]\s*)?(?:(?:public|private|noncomputable|meta)\s+)*section(?:\s+{SCOPE_NAME})?\s*(?:--.*)?$")
NAMESPACE_RE = re.compile(rf"^namespace\s+{SCOPE_NAME}\s*(?:--.*)?$")
END_RE = re.compile(rf"^end(?:\s+{SCOPE_NAME})?\s*(?:--.*)?$")
MUTUAL_RE = re.compile(r"^mutual\s*(?:--.*)?$")


DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|public|nonrec|scoped|local)\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|structure|class|inductive|opaque|axiom|irreducible_def)"
    r"\s+([^\s:({\[]+)")


def scan(body):
    """Return (scopes left open at the end of `body`, set of full names declared at top level).

    Line-based and approximate: commands are recognised only at column 0, outside block comments.
    """
    stack = []
    decls = set()
    depth = 0  # block comment nesting
    for l in body.split("\n"):
        if depth == 0 and not l.startswith(("/-", " ", "\t")) and l:
            m = SECTION_RE.match(l)
            if m:
                parts = NAME_PART.findall(m.group(1)) if m.group(1) else [None]
                stack.extend(("section", part) for part in parts)
            else:
                m = NAMESPACE_RE.match(l)
                if m:
                    stack.extend(("namespace", part) for part in NAME_PART.findall(m.group(1)))
                elif MUTUAL_RE.match(l):
                    stack.append(("mutual", None))
                else:
                    m = END_RE.match(l)
                    if m and stack:
                        count = len(NAME_PART.findall(m.group(1))) if m.group(1) else 1
                        del stack[-count:]
                    else:
                        m = DECL_RE.match(l)
                        if m and not m.group(1).startswith(("where", ":=")):
                            name = m.group(1)
                            if name.startswith("_root_."):
                                decls.add(name[len("_root_."):])
                            else:
                                ns = ".".join(n for k, n in stack if k == "namespace")
                                decls.add(ns + "." + name if ns else name)
        # crude block-comment tracking (ignores comment markers inside strings)
        depth += l.count("/-") - l.count("-/")
        depth = max(depth, 0)
    return stack, decls


def open_scopes(body):
    return scan(body)[0]


def closers(stack):
    out = []
    names = []
    for kind, name in reversed(stack):
        if kind == "mutual":
            raise ValueError("unterminated mutual block")
        if name is not None:
            names.append(name)
            continue
        if names:
            out.append("end " + ".".join(reversed(names)) + AUTO)
            names.clear()
        out.append("end" + AUTO)
    if names:
        out.append("end " + ".".join(reversed(names)) + AUTO)
    return out


# ---------------------------------------------------------------------------
# Applying

def is_clump_file(mod):
    return CLUMP_MARK in mod.header or CLUMP_MARK in mod.body or SEAM_BEGIN in mod.body


def member_start(line):
    if MEMBER_TAG not in line:
        return None
    code, _, name = line.partition(MEMBER_TAG)
    if code in MEMBER_PREFIXES:
        return code.rstrip(), name
    return None


def has_own_scope(body, closings):
    """The first anonymous section can isolate the member until its end."""
    if not body or body[0] not in PUBLIC_SECTIONS or "end" + AUTO not in closings:
        return False
    # Lean closes an anonymous scope with a bare end. A named end can only
    # close named scopes. Keep the wrapper for all other spellings.
    return all(NAMED_END.fullmatch(line) for line in body if "end" in line and END_WORD.search(line))


def simple_open(line):
    return OPEN_NAMES.fullmatch(line) and not {"in", "hiding", "renaming"}.intersection(line.split())


def leading_opens(body):
    if not body or body[0] not in PUBLIC_SECTIONS:
        return ()
    last = previous = 0
    for i, line in enumerate(body[1:], 1):
        if not line.strip():
            continue
        if simple_open(line):
            previous, last = last, i
            continue
        # A namespace list can continue on an indented line. A comment can
        # also separate an open from its continuation or from a trailing in.
        if (line[0].isspace() or line.startswith(("--", "/-", "(")) or
                line.split()[0] in ("in", "hiding", "renaming")):
            last = previous
        break
    return tuple(body[1:last + 1])


def common_prefix(left, right):
    length = 0
    for a, b in zip(left, right):
        if a != b:
            break
        length += 1
    while length and not left[length - 1].strip():
        length -= 1
    return left[:length]


def shared_open_groups(bodies):
    """Choose disjoint runs of members with the same leading namespace opens."""
    prefixes = [leading_opens(body) for body in bodies]
    count = len(prefixes)
    savings = [0] * (count + 1)
    choices = [None] * count
    for start in reversed(range(count)):
        savings[start] = savings[start + 1]
        prefix = prefixes[start]
        for stop in range(start + 1, count):
            prefix = common_prefix(prefix, prefixes[stop])
            if not prefix:
                break
            # A group that ends before the file does needs its own section.
            overhead = 0 if stop + 1 == count else 2
            gain = (stop - start) * sum(bool(line.strip()) for line in prefix) - overhead
            if gain > 0 and gain + savings[stop + 1] > savings[start]:
                savings[start] = gain + savings[stop + 1]
                choices[start] = stop, prefix
    groups = {}
    i = 0
    while i < count:
        choice = choices[i]
        if choice is None:
            i += 1
        else:
            groups[i] = choice
            i = choice[0] + 1
    return groups


def render_members(out, order, mods):
    headers = []
    bodies = []
    for name in order:
        mod = mods[name]
        info = {"m": name, "h": mod.header}
        if not mod.body.endswith("\n"):
            info["nonl"] = True
        bodies.append(mod.body.removesuffix("\n").split("\n"))
        headers.append(HEADER_TAG + json.dumps(info, ensure_ascii=False))

    groups = shared_open_groups(bodies)
    opens = ()
    group_end = None
    for i, (name, original) in enumerate(zip(order, bodies)):
        if i in groups:
            group_end, opens = groups[i]
            marker = SHARED_OPENS if group_end + 1 == len(order) else "section " + SHARED_OPENS
            out.extend([marker, *opens, ""])
        body = original if not opens else original[:1] + original[1 + len(opens):]
        closing = closers(mods[name].scopes)
        final = i + 1 == len(order)
        borrow = final or has_own_scope(body, closing)
        if borrow and body and body[0] in PUBLIC_SECTIONS:
            out.extend([body[0] + " " + MEMBER_TAG + name, *body[1:]])
        elif final:
            out.extend([MEMBER_TAG + name, *body])
        else:
            out.extend(["section " + MEMBER_TAG + name, *body])
        if not final:
            out.extend(closing)
            if not borrow:
                out.append("end" + AUTO)
        out.append("")
        if i == group_end and not final:
            out.extend([END_SHARED, ""])
            opens = ()
    out.extend([*headers, ""])


def render(root, order, mods):
    mem = set(order)
    by = {m: mods[m] for m in order}
    # A clump-external import is public iff some member imported it publicly: public
    # statements in an `@[expose] public section` may only mention publicly imported names.
    ext = {}
    for m in order:
        for x, pub in by[m].imports:
            if x in mem:
                continue
            ext[x] = ext.get(x, False) or pub
    pubs = [x for x in ext if ext[x]]
    privs = [x for x in ext if not ext[x]]
    out = ["module", ""]
    out += ["public import " + x for x in pubs]
    out += ["import " + x for x in privs]
    out += ["", CLUMP_MARK]
    out += ["-- Members: " + ", ".join(order), ""]
    # Preserve literal markers in member source with the paired layout.
    if not any(tag in mod.body for mod in by.values()
               for tag in (MEMBER_TAG, HEADER_TAG, SHARED_OPENS)):
        render_members(out, order, by)
        return "\n".join(out)
    for m in order:
        mod = by[m]
        body = mod.body
        trailing_nl = body.endswith("\n")
        if trailing_nl:
            body = body[:-1]
        info = {"m": m, "h": mod.header}
        if not trailing_nl:
            info["nonl"] = True
        out.append(SEAM_BEGIN + m + " =====")
        out.append(HEADER_TAG + json.dumps(info, ensure_ascii=False))
        out.append("section" + AUTO)
        out.append(body)
        out += closers(mod.scopes)
        out.append("end" + AUTO)
        out.append(SEAM_END + m + " =====")
        out.append("")
    return "\n".join(out)


def apply(root, clumps):
    members = set(clumps).union(*clumps.values())
    mods = load(root, members)
    for r, order in clumps.items():
        text = render(r, order, mods)
        for m in order:
            if m != r:
                os.remove(os.path.join(root, mods[m].path))
        with open(os.path.join(root, mods[r].path), "w", encoding="utf-8") as f:
            f.write(text)


# ---------------------------------------------------------------------------
# Unclumping

def read_scope_members(lines):
    """Restore each compact member and insert the namespace opens for its group."""
    marks = []
    table = len(lines)
    for i, line in enumerate(lines):
        if "-- clump" not in line:
            continue
        if line.startswith(HEADER_TAG):
            table = i
            break
        start = member_start(line)
        if start:
            marks.append((i, "member", start))
        elif line in (SHARED_OPENS, "section " + SHARED_OPENS):
            marks.append((i, "open", None))
        elif line == END_SHARED:
            marks.append((i, "close", None))
    footer = [line for line in lines[table:] if line.strip()]
    if any(not line.startswith(HEADER_TAG) for line in footer):
        raise ValueError("unexpected text after the clump header table")
    headers = [json.loads(line[len(HEADER_TAG):]) for line in footer]
    names = [value[1] for _, kind, value in marks if kind == "member"]
    if len(set(names)) != len(names):
        raise ValueError("duplicate clump member in the header table")
    if not names or names != [info["m"] for info in headers]:
        raise ValueError("clump member names differ from the header table")
    preamble = [line for line in lines[:marks[0][0]] if line.strip()]
    if preamble != ["-- Members: " + ", ".join(names)]:
        raise ValueError("unexpected text before the first clump member")
    result = {}
    infos = iter(headers)
    opens = None
    needs_end = False
    for j, (begin, kind, value) in enumerate(marks):
        stop = marks[j + 1][0] if j + 1 < len(marks) else table
        body = lines[begin + 1:stop]
        if body and not body[-1]:
            body.pop()
        if kind == "open":
            if opens is not None:
                raise ValueError("nested shared clump opens")
            if any(line.strip() and not line.lstrip().startswith("--") and not simple_open(line)
                   for line in body):
                raise ValueError("unexpected command in shared clump opens")
            opens = body
            needs_end = lines[begin].startswith("section ")
        elif kind == "close":
            if any(line.strip() for line in body) or not needs_end:
                raise ValueError("unexpected end of shared clump opens")
            opens = None
            needs_end = False
        else:
            first, name = value
            while body and body[-1].endswith(AUTO):
                body.pop()
            if first in PUBLIC_SECTIONS:
                body.insert(0, first)
            if opens:
                if not body or body[0] not in PUBLIC_SECTIONS:
                    raise ValueError("missing public section in " + name)
                body[1:1] = opens
            info = next(infos)
            newline = "" if info.get("nonl") else "\n"
            result[name] = info["h"] + "\n".join(body) + newline
    if needs_end:
        raise ValueError("missing end of shared clump opens")
    return result


def clump_layout(lines):
    """Find the archive banner and identify the layout below it."""
    try:
        start = lines.index(CLUMP_MARK) + 1
    except ValueError:
        return None, False
    for i in range(start, len(lines)):
        line = lines[i]
        if line.startswith(SEAM_BEGIN):
            break
        if member_start(line) or line in (SHARED_OPENS, "section " + SHARED_OPENS) or line.startswith(HEADER_TAG):
            return start, True
    return start, False


def unclump_text(text):
    lines = text.split("\n")
    start, compact = clump_layout(lines)
    if compact:
        return read_scope_members(lines[start:])
    i, out = start or 0, {}
    while i < len(lines):
        if not lines[i].startswith(SEAM_BEGIN):
            i += 1
            continue
        info = json.loads(lines[i + 1][len(HEADER_TAG):])
        name = info["m"]
        j = i + 2
        assert lines[j] == "section" + AUTO, (name, lines[j])
        k = j + 1
        while lines[k] != SEAM_END + name + " =====":
            k += 1
        body = [l for l in lines[j + 1:k] if not l.endswith(AUTO)]
        body = "\n".join(body) + ("" if info.get("nonl") else "\n")
        out[name] = info["h"] + body
        i = k + 1
    return out


def unclump(root):
    out = subprocess.run(["git", "-C", root, "ls-files", "-z", "--cached", "--others",
                          "--exclude-standard", "src/*.lean"],
                         capture_output=True, check=True).stdout.decode()
    n = 0
    for p in out.split("\0"):
        if not p or not os.path.exists(os.path.join(root, p)):
            continue
        with open(os.path.join(root, p), encoding="utf-8") as f:
            text = f.read()
        if CLUMP_MARK not in text:
            continue
        for name, content in unclump_text(text).items():
            q = os.path.join(root, "src", *name.split(".")) + ".lean"
            with open(q, "w", encoding="utf-8") as f:
                f.write(content)
        n += 1
    print(f"unclumped {n} files")


# ---------------------------------------------------------------------------

def blame(root, logs):
    """Map `error: <file>:<line>:...` lines in build logs to the clump member containing them."""
    err = re.compile(r"^error: (src/\S+?\.lean):(\d+):")
    found = set()
    for log in logs:
        with open(log, encoding="utf-8", errors="replace") as f:
            for l in f:
                m = err.match(l)
                if not m:
                    continue
                path, line = m.group(1), int(m.group(2))
                try:
                    with open(os.path.join(root, path), encoding="utf-8") as g:
                        lines = g.read().split("\n")
                except FileNotFoundError:
                    continue
                start, compact = clump_layout(lines)
                if start is None:
                    continue
                member = None
                for x in reversed(lines[start:line]):
                    if not compact:
                        if x.startswith(SEAM_BEGIN):
                            member = x[len(SEAM_BEGIN):].rstrip(" =")
                            break
                        continue
                    start = member_start(x)
                    if start:
                        member = start[1]
                        break
                    if x in (SHARED_OPENS, "section " + SHARED_OPENS):
                        for row in lines[line:]:
                            start = member_start(row)
                            if start:
                                member = start[1]
                                break
                        break
                if member:
                    found.add(member)
    return sorted(found)


def read_exclude(path):
    if not path or not os.path.exists(path):
        return frozenset()
    with open(path) as f:
        return frozenset(l.split("#")[0].strip() for l in f if l.split("#")[0].strip())


def stats(mods, clumps, max_lines):
    gone = sum(len(o) - 1 for o in clumps.values())
    print(f"modules {len(mods)}  clumps {len(clumps)}  absorbed {gone}  "
          f"files after {len(mods) - gone}  (max-lines {max_lines})")
    sizes = []
    in_clump = set()
    for r, o in clumps.items():
        in_clump.update(o)
        sizes.append(sum(mods[m].lines for m in o))
    sizes += [mods[m].lines for m in mods if m not in in_clump]
    bins = [0, 50, 100, 200, 500, 1000, 2000, 5000, 10000, 10**9]
    for a, b in zip(bins, bins[1:]):
        c = sum(a <= s < b for s in sizes)
        print(f"  {a:>6}-{b:<6} {c:7d}")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("plan"); p.add_argument("root"); p.add_argument("--max-lines", type=int, default=10000)
    p.add_argument("--out")
    p.add_argument("--exclude", default=os.path.join(os.path.dirname(__file__), "clump-exclude.txt"),
                   help="modules never to fold (one per line; default scripts/clump-exclude.txt)")
    b = sub.add_parser("blame", help="list clump members containing errors in build logs")
    b.add_argument("root"); b.add_argument("logs", nargs="+")
    a = sub.add_parser("apply"); a.add_argument("root"); a.add_argument("plan")
    u = sub.add_parser("unclump"); u.add_argument("root")
    args = ap.parse_args()
    if args.cmd == "plan":
        mods = load_for_plan(args.root)
        clumps = plan(mods, args.max_lines, read_exclude(args.exclude))
        stats(mods, clumps, args.max_lines)
        if args.out:
            with open(args.out, "w") as f:
                json.dump(clumps, f, indent=0)
    elif args.cmd == "apply":
        with open(args.plan) as f:
            apply(args.root, json.load(f))
    elif args.cmd == "blame":
        print("\n".join(blame(args.root, args.logs)))
    else:
        unclump(args.root)


if __name__ == "__main__":
    main()
