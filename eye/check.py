#!/usr/bin/env python3
"""oocert/check.py -- N3/EYE re-implementation of OOCert.checkCert.

Usage:  python3 check.py ASSERTED.tsv DERIVATIONS.tsv

Exit codes, matching `lake exe oo-cert` (lean/Main.lean):
  0  every step checks
  1  a step was rejected; JSON names the first one
  2  a file could not be read or parsed

With the optional trust anchor set (OO_HORN_ROCQ + OO_RULES), one more code:
  3  EYE accepted but the proven oo-horn checker refused (anchor_disagrees).
     A caught false pass is NOT a clean accept: a pipeline that only checks for
     0 cannot silently treat "EYE said ok, the theorem said no" as success.
     Without an anchor configured, 3 is never returned.

The trusted part is checker.n3, run by the EYE/WASM reasoner.  This driver is
the untrusted wrapper: it parses the TSV, emits canonical N3, runs EYE, and
reads back the `:ok` facts.  It never decides a step itself.
"""

import json
import os
import re
import shutil
import subprocess
import sys

# --- the rule table, in the order Rules.lean documents (names are a contract)
RULES = [
    "rdfs2", "rdfs3", "rdfs5", "rdfs7", "rdfs9", "rdfs11",
    "prp-trp", "prp-symp", "prp-inv1", "prp-inv2", "eq-sym",
    "scm-eqc1", "scm-eqp1",
    "cls-svf1", "cls-avf", "cls-hv1", "cls-hv2",
    "cls-int1", "cls-int2", "cls-uni", "cls-oo",
    "scm-svf1", "scm-svf2", "scm-avf1", "scm-avf2",
    "scm-dom1", "scm-dom2", "scm-rng1", "scm-rng2",
]

# OOCert.Builtin.asHorn -- the 27 Horn rule patterns, by certificate index.
# scm-eqc1/scm-eqp1 each contribute two entries (two licensed conclusions).
HORN = [
    "rdfs2", "rdfs3", "rdfs5", "rdfs7", "rdfs9", "rdfs11",
    "prp-trp", "prp-symp", "prp-inv1", "prp-inv2", "eq-sym",
    "scm-eqc1", "scm-eqc1", "scm-eqp1", "scm-eqp1",
    "cls-svf1", "cls-avf", "cls-hv1", "cls-hv2",
    "scm-svf1", "scm-svf2", "scm-avf1", "scm-avf2",
    "scm-dom1", "scm-dom2", "scm-rng1", "scm-rng2",
]

# Terms that name vocabulary the rules mention: their N-Triples spelling is
# kept verbatim as a URI, which is the table checker.n3 matches against.  Every
# other term is opaque and gets its own <urn:t:N> node.  A term is the same
# term iff its spelling is the same string -- exactly Rules.lean.
VOCAB_IRIS = {
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#type",
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#first",
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest",
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil",
    "http://www.w3.org/2000/01/rdf-schema#subClassOf",
    "http://www.w3.org/2000/01/rdf-schema#subPropertyOf",
    "http://www.w3.org/2000/01/rdf-schema#domain",
    "http://www.w3.org/2000/01/rdf-schema#range",
    "http://www.w3.org/2002/07/owl#TransitiveProperty",
    "http://www.w3.org/2002/07/owl#SymmetricProperty",
    "http://www.w3.org/2002/07/owl#inverseOf",
    "http://www.w3.org/2002/07/owl#sameAs",
    "http://www.w3.org/2002/07/owl#equivalentClass",
    "http://www.w3.org/2002/07/owl#equivalentProperty",
    "http://www.w3.org/2002/07/owl#onProperty",
    "http://www.w3.org/2002/07/owl#someValuesFrom",
    "http://www.w3.org/2002/07/owl#allValuesFrom",
    "http://www.w3.org/2002/07/owl#hasValue",
    "http://www.w3.org/2002/07/owl#intersectionOf",
    "http://www.w3.org/2002/07/owl#unionOf",
    "http://www.w3.org/2002/07/owl#oneOf",
}

HERE = os.path.dirname(os.path.abspath(__file__))
EYE_DIR = HERE  # lib/ (native image) or node_modules/ (npm) lives beside this file
CHECKER = os.path.join(HERE, "checker.n3")
WORK = os.path.join(HERE, "combined.n3")
# The native EYE image built by build_eye.sh. Preferred over the npm package:
# same reasoner, no Node toolchain. Override with $EYE_PVM.
EYE_PVM = os.environ.get("EYE_PVM", os.path.join(HERE, "lib", "eye.pvm"))


class ParseError(Exception):
    pass


Term = str
Triple = tuple  # (s, p, o), each Term in N-Triples spelling


# ---------------------------------------------------------------- parsing
def parse_asserted(text):
    out = []
    for n, line in enumerate(text.split("\n"), 1):
        line = line.rstrip("\r")
        if line == "":
            continue
        parts = line.split("\t")
        if len(parts) != 3:
            raise ParseError("asserted.tsv line %d: expected three tab-separated terms" % n)
        out.append((parts[0], parts[1], parts[2]))
    return out


def parse_steps(text):
    """oo-cert derivations.tsv: rule TAB s TAB p TAB o [TAB ps TAB pp TAB po]*"""
    out = []
    for n, line in enumerate(text.split("\n"), 1):
        line = line.rstrip("\r")
        if line == "":
            continue
        parts = line.split("\t")
        if len(parts) < 4:
            raise ParseError("derivations.tsv line %d: expected rule, conclusion, premises" % n)
        rule, s, p, o, prem = parts[0], parts[1], parts[2], parts[3], parts[4:]
        if rule not in RULES:
            raise ParseError("derivations.tsv line %d: unknown rule %r" % (n, rule))
        if len(prem) % 3 != 0:
            raise ParseError("derivations.tsv line %d: premises are not whole triples" % n)
        premises = [(prem[i], prem[i + 1], prem[i + 2]) for i in range(0, len(prem), 3)]
        out.append((rule, (s, p, o), premises))
    return out


def parse_horn_steps(text):
    """oo-horn horn.tsv: idx TAB nb TAB (var TAB term)* TAB cs TAB cp TAB co
    TAB (ps TAB pp TAB po)*

    The premises and the conclusion travel as concrete triples, so the rule
    index is only a name; we map it through asHorn and reuse the same checker.
    """
    out = []
    for n, line in enumerate(text.split("\n"), 1):
        line = line.rstrip("\r")
        if line == "":
            continue
        parts = line.split("\t")
        if len(parts) < 5:
            raise ParseError("horn.tsv line %d: expected index, bind count, bindings, conclusion" % n)
        try:
            idx = int(parts[0])
            nb = int(parts[1])
        except ValueError:
            raise ParseError("horn.tsv line %d: rule index or bind count is not a number" % n)
        if idx < 0 or idx >= len(HORN):
            raise ParseError("horn.tsv line %d: rule index %d out of range" % (n, idx))
        rest = parts[2:]
        if len(rest) < 2 * nb + 3:
            raise ParseError("horn.tsv line %d: malformed bindings or conclusion" % n)
        after_binds = rest[2 * nb:]
        cs, cp, co = after_binds[0], after_binds[1], after_binds[2]
        prem = after_binds[3:]
        if len(prem) % 3 != 0:
            raise ParseError("horn.tsv line %d: premises are not whole triples" % n)
        premises = [(prem[i], prem[i + 1], prem[i + 2]) for i in range(0, len(prem), 3)]
        out.append((HORN[idx], (cs, cp, co), premises))
    return out


def load_derivations(path):
    """Read derivations.tsv, auto-detecting oo-cert / oo-horn / oo-refute."""
    with open(path, "r", encoding="utf-8") as fh:
        raw = fh.read()
    lines = [l.rstrip("\r") for l in raw.split("\n")]
    # oo-refute/1 refutation certificate: first non-empty line is the tag.
    first = next((l for l in lines if l != ""), "")
    if first == "oo-refute/1":
        # The derivation PREFIX (steps before the `refute ...` line) is a plain
        # oo-cert certificate; check it, then flag that the file is a
        # refutation, which earns a different verdict from oo-cert's.
        body = lines[1:]
        steps_lines = []
        refute_line = None
        for l in body:
            if l == "":
                continue
            if l.split("\t", 1)[0] == "refute":
                refute_line = l
                break
            steps_lines.append(l)
        prefix = parse_steps("\n".join(steps_lines))
        return ("oo-refute", prefix, refute_line)
    # Decide oo-cert vs oo-horn from the first data line's shape.
    if first == "":
        return ("oo-cert", [], None)
    head = first.split("\t")
    if head[0] in RULES:
        return ("oo-cert", parse_steps(raw), None)
    if head[0].lstrip("-").isdigit() and len(head) > 1 and head[1].lstrip("-").isdigit():
        return ("oo-horn", parse_horn_steps(raw), None)
    raise ParseError("derivations.tsv: unknown certificate format (first field %r)" % head[0])


# ---------------------------------------------------------------- N3 gen
class Gen:
    def __init__(self):
        self.terms = {}
        self.triples = {}
        self.lines = []

    def term(self, t):
        if t in self.terms:
            return self.terms[t]
        if t.startswith("<") and t.endswith(">") and t[1:-1] in VOCAB_IRIS:
            node = "<%s>" % t[1:-1]
        else:
            node = "<urn:t:%d>" % len(self.terms)
        self.terms[t] = node
        return node

    def triple(self, tr):
        if tr in self.triples:
            return self.triples[tr]
        k = len(self.triples)
        node = "<urn:tr:%d>" % k
        self.triples[tr] = node
        s, p, o = (self.term(x) for x in tr)
        self.lines.append("%s <urn:s> %s ; <urn:p> %s ; <urn:o> %s ." % (node, s, p, o))
        return node

    def build(self, asserted, steps):
        asserted_nodes = set()
        for tr in asserted:
            node = self.triple(tr)
            asserted_nodes.add(node)
        for node in asserted_nodes:
            self.lines.append("%s a <urn:Asserted> ." % node)
        # chain triples read off the ASSERTED graph (rdf:first / rdf:rest only),
        # for the four list rules; emitted as bare triples.
        for tr in asserted:
            if tr[1] in ("<http://www.w3.org/1999/02/22-rdf-syntax-ns#first>",
                         "<http://www.w3.org/1999/02/22-rdf-syntax-ns#rest>"):
                s, p, o = (self.term(x) for x in tr)
                self.lines.append("%s %s %s ." % (s, p, o))
        for i, (rule, conclusion, premises) in enumerate(steps):
            cnode = self.triple(conclusion)
            pnodes = [self.triple(p) for p in premises]
            self.lines.append('<urn:st:%d> a <urn:Step> ; <urn:rule> <urn:rule:%s> ; '
                              '<urn:idx> %d ; <urn:conclusion> %s .'
                              % (i, rule, i, cnode))
            for pn in pnodes:
                self.lines.append("<urn:st:%d> <urn:premise> %s ." % (i, pn))
            if pnodes:
                self.lines.append("<urn:st:%d> <urn:premiseList> ( %s ) ."
                                  % (i, " ".join(pnodes)))
            else:
                self.lines.append("<urn:st:%d> <urn:premiseList> ( ) ." % i)
        return "\n".join(self.lines) + "\n"


def reasoner_cmd():
    """Resolve the EYE reasoner, most explicit first.

      1. `$EYE_PVM` or `lib/eye.pvm` -- the NATIVE image built by build_eye.sh,
         run by SWI-Prolog. This is the same reasoner the npm package carries,
         without the Node toolchain, and it is preferred: a notebook that needs
         npm to check a certificate is a notebook most users cannot run.
      2. `$EYE_BIN`          -- an explicit reasoner executable, for odd installs.
      3. a local `node_modules/.bin/eyereasoner` -- a checkout that ran
         `npm install`; kept as a fallback, not a requirement.
      4. `eyereasoner`/`eye` on PATH.
      5. `npx eyereasoner`   -- LAST: it may fetch from the network on first use,
         so it is never reached on a machine that has the native image."""
    if os.path.exists(EYE_PVM):
        swipl = shutil.which("swipl")
        if swipl:
            return [swipl, "-x", EYE_PVM, "--"]
    explicit = os.environ.get("EYE_BIN")
    if explicit:
        return [explicit]
    here = HERE
    while True:
        cand = os.path.join(here, "node_modules", ".bin", "eyereasoner")
        if os.path.exists(cand):
            return [cand]
        parent = os.path.dirname(here)
        if parent == here:
            break
        here = parent
    for name in ("eyereasoner", "eye"):
        found = shutil.which(name)
        if found:
            return [found]
    return ["npx", "--yes", "eyereasoner"]


def run_eye(work_abs):
    """Run the resolved reasoner over one combined .n3 file. The native image
    takes an absolute path (SWI-Prolog opens it relative to the process cwd, and
    that is EYE_DIR); the npm CLI takes a path relative to EYE_DIR, which is its
    own Emscripten working directory."""
    cmd = reasoner_cmd()
    native = "-x" in cmd
    target = work_abs if native else os.path.relpath(work_abs, EYE_DIR)
    cmd = cmd + ["--nope", "--quiet", "--pass",
                 "--ignore-inference-fuse", target]
    proc = subprocess.run(cmd, cwd=EYE_DIR, capture_output=True, text=True)
    return proc.stdout + "\n" + proc.stderr


OK_RE = re.compile(r"<urn:st:(\d+)>\s+<urn:ok>\s+<urn:True>")


# ------------------------------------------------------------ trust anchor
# The OPTIONAL trust anchor is the Rocq-extracted, machine-checked checker
# (../open-ontologies/rocq/build/oo-horn-rocq).  When it speaks, an `accept`
# means "entailed", not "a rule ran".  Set OO_HORN_ROCQ to its path and
# OO_RULES to the Horn rules table (e.g. tests/fixtures/horn/builtin_rules.tsv).
#
# The SAME binary now speaks for BOTH certificate kinds:
#   oo-horn  -> `check RULES.tsv ASSERTED.tsv HORN.tsv`,  theorem
#               OOCertRocq.entails_of_builtin_horn
#   oo-cert  -> `cert ASSERTED.tsv CERT.tsv`,             theorem
#               OOCertRocq.check_ccert_sound  (the full OWL-RL rule set,
#               including the four RDF-list rules)
# So the anchor no longer DECLINES for oo-cert; it checks it, and a refusal of
# a certificate EYE accepted is a caught false pass (exit 3), exactly as for
# oo-horn.
ANCHOR = os.environ.get("OO_HORN_ROCQ")
RULES_TSV = os.environ.get("OO_RULES")


def run_anchor(cert_path, asserted_path, fmt="oo-horn", binary=None, rules=None):
    """Run the proven Rocq checker over the same inputs.  Returns a dict, or
    None when no anchor is configured.  Raises RuntimeError when it is
    configured but cannot run, so a caller never reads 'could not check' as
    'checked and agreed'.

    `binary`/`rules` default to the module's ANCHOR/RULES_TSV (what the CLI
    sets from OO_HORN_ROCQ/OO_RULES) so an importing caller can pass them
    directly instead of mutating module state.  `rules` is needed only for the
    Horn path; the oo-cert path carries its table in the binary."""
    binary = binary if binary is not None else ANCHOR
    rules = rules if rules is not None else RULES_TSV
    if not binary:
        return None
    if not os.path.exists(binary):
        raise RuntimeError("anchor binary not found: %s" % binary)
    if fmt == "oo-horn":
        if not rules:
            raise RuntimeError("the oo-horn anchor needs a rules table")
        cmd = [binary, "check", rules, asserted_path, cert_path]
    elif fmt == "oo-cert":
        cmd = [binary, "cert", asserted_path, cert_path]
    else:
        raise RuntimeError("the anchor does not speak for %s certificates" % fmt)
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True)
    except OSError as e:
        # A binary that exists but cannot execute (wrong architecture, no exec
        # bit, a host build in a shared tree) must read as 'could not check',
        # never as 'checked and agreed'. The caller turns this into exit 2.
        raise RuntimeError("anchor binary could not be run (%s): %s" % (e, binary))
    try:
        verdict = json.loads(proc.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        verdict = {"raw": proc.stdout.strip()}
    return {"binary": os.path.basename(binary),
            "exit": proc.returncode,
            "verdict": verdict}


def anchor_declined(fmt):
    """The note shown when an anchor is configured but cannot speak for this
    certificate kind."""
    return {"applied": False,
            "reason": ("oo-horn (Horn) checker only; %s uses the OWL-RL rule set "
                       "(incl. the RDF-list rules it does not cover)" % fmt)}


def check_certificate(asserted, steps, fmt="oo-cert", refute_line=None,
                      cert_path=None, asserted_path=None,
                      anchor_binary=None, anchor_rules=None):
    """The whole verdict, as a pure function of already-parsed inputs.

    Returns (exit_code, result_dict) with the SAME code contract the CLI uses
    (0 accept, 1 rejected, 2 parse/other, 3 an anchor disagreement). `main()`
    is a thin adapter over this: it reads files, calls here, prints the dict.
    A notebook imports and calls HERE, so no argv and no process boundary is
    involved in deciding a verdict.

    `anchor_binary`/`anchor_rules` default to this module's ANCHOR/RULES_TSV
    (what the CLI sets from OO_HORN_ROCQ/OO_RULES); an importing caller can
    pass them instead of touching module state. `cert_path`/`asserted_path` are
    only needed when an anchor runs, because the anchor is a separate binary
    that takes file paths.
    """
    if fmt == "oo-refute":
        # Check the derivation prefix with the same machinery, then flag.
        prefix_ok, prefix_idx = check_steps(asserted, steps)
        out = {"ok": False, "format": "oo-refute/1",
               "error": "this is an oo-refute/1 refutation certificate; "
                        "oo-cert does not check it (different verdict)",
               "prefix_ok": prefix_ok}
        if not prefix_ok:
            out["rejected_step"] = prefix_idx
        return (2, out)

    # The optional trust anchor.  The proven Rocq checker speaks for BOTH
    # oo-horn (theorem entails_of_builtin_horn) and oo-cert (theorem
    # check_ccert_sound, the full OWL-RL rule set).  A configured-but-broken
    # anchor is a hard error (exit 2): 'could not check' must never read as
    # 'checked and agreed'.
    binary = anchor_binary if anchor_binary is not None else ANCHOR
    anchor = None
    if binary:
        if fmt in ("oo-horn", "oo-cert"):
            if not cert_path or not asserted_path:
                raise RuntimeError("an anchor needs cert_path and asserted_path")
            try:
                anchor = run_anchor(cert_path, asserted_path, fmt=fmt, binary=binary,
                                    rules=anchor_rules if anchor_rules is not None else RULES_TSV)
            except RuntimeError as e:
                return (2, {"ok": False, "error": "anchor: %s" % e})
        else:
            anchor = anchor_declined(fmt)

    ok, idx = check_steps(asserted, steps)
    if ok:
        out = {"ok": True, "asserted": len(asserted), "derivations": len(steps)}
        disagree = False
        if anchor is not None:
            out["anchor"] = anchor
            # EYE accepted.  If the proven anchor refused the same certificate,
            # that is a caught FALSE PASS, not a clean accept: surface it and
            # leave with a distinct code, so a pipeline checking only for 0 can
            # not treat ``EYE said ok, the theorem said no'' as success.
            if fmt in ("oo-horn", "oo-cert") and anchor.get("exit") not in (0, None):
                disagree = True
                out["anchor_disagrees"] = True
                out["ok"] = False
                out["error"] = ("the proven Rocq anchor refused an %s certificate "
                                "EYE accepted (possible false pass)" % fmt)
        return (3 if disagree else 0, out)
    rule, conclusion, premises = steps[idx]
    out = {
        "ok": False,
        "rejected_step": idx,
        "rule": rule,
        "conclusion": "%s %s %s" % conclusion,
        "premises": ["%s %s %s" % p for p in premises],
    }
    if anchor is not None:
        out["anchor"] = anchor
    return (1, out)


def main(argv):
    """CLI adapter: read two files, call check_certificate, print one JSON
    line, return the exit code. The verdict itself is decided in
    check_certificate, so an importing caller never needs this path."""
    if len(argv) != 3:
        sys.stderr.write("usage: check.py ASSERTED.tsv DERIVATIONS.tsv\n")
        return 2
    gpath, dpath = argv[1], argv[2]
    try:
        with open(gpath, "r", encoding="utf-8") as fh:
            asserted = parse_asserted(fh.read())
    except OSError as e:
        sys.stderr.write("cannot read %s: %s\n" % (gpath, e))
        return 2
    except ParseError as e:
        sys.stderr.write(str(e) + "\n")
        return 2
    try:
        with open(dpath, "r", encoding="utf-8") as fh:
            fh.read()
        fmt, steps, refute_line = load_derivations(dpath)
    except OSError as e:
        sys.stderr.write("cannot read %s: %s\n" % (dpath, e))
        return 2
    except ParseError as e:
        sys.stderr.write(str(e) + "\n")
        return 2

    code, out = check_certificate(asserted, steps, fmt=fmt, refute_line=refute_line,
                                  cert_path=dpath, asserted_path=gpath)
    print(json.dumps(out))
    return code


def check_steps(asserted, steps):
    gen = Gen()
    data = gen.build(asserted, steps)
    with open(CHECKER, "r", encoding="utf-8") as fh:
        checker = fh.read()
    with open(WORK, "w", encoding="utf-8") as fh:
        fh.write(checker + "\n" + data)
    out = run_eye(WORK)
    ok_idx = {int(m.group(1)) for m in OK_RE.finditer(out)}
    for i in range(len(steps)):
        if i not in ok_idx:
            return (False, i)
    return (True, None)


def cli():
    """Console-script entry point (see pyproject.toml):
    `oocert-eye ASSERTED.tsv DERIVATIONS.tsv`. Console scripts are called with
    no arguments and their return value is passed to sys.exit, so this is the
    same call the `__main__` guard makes."""
    return main(sys.argv)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
