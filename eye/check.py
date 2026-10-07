#!/usr/bin/env python3
"""oocert/check.py -- N3/EYE re-implementation of OOCert.checkCert.

Usage:  python3 check.py ASSERTED.tsv DERIVATIONS.tsv

Exit codes, matching `lake exe oo-cert` (lean/Main.lean):
  0  every step checks
  1  a step was rejected; JSON names the first one
  2  a file could not be read or parsed

The trusted part is checker.n3, run by the EYE/WASM reasoner.  This driver is
the untrusted wrapper: it parses the TSV, emits canonical N3, runs EYE, and
reads back the `:ok` facts.  It never decides a step itself.
"""

import json
import os
import re
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
EYE_DIR = HERE  # node_modules/ lives beside this file
CHECKER = os.path.join(HERE, "checker.n3")
WORK = os.path.join(HERE, "combined.n3")


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


def run_eye(work_abs):
    rel = os.path.relpath(work_abs, EYE_DIR)
    cmd = ["npx", "eyereasoner", "--nope", "--quiet", "--pass",
           "--ignore-inference-fuse", rel]
    proc = subprocess.run(cmd, cwd=EYE_DIR, capture_output=True, text=True)
    return proc.stdout + "\n" + proc.stderr


OK_RE = re.compile(r"<urn:st:(\d+)>\s+<urn:ok>\s+<urn:True>")


# ------------------------------------------------------------ trust anchor
# The OPTIONAL trust anchor is the Rocq-extracted, machine-checked oo-horn
# checker (../open-ontologies/rocq/build/oo-horn-rocq), which carries the
# theorem OOCertRocq.entails_of_builtin_horn.  When it speaks, an `accept`
# means "entailed", not "a rule ran".  Set OO_HORN_ROCQ to its path and
# OO_RULES to a rules table (e.g. tests/fixtures/horn/builtin_rules.tsv).
#
# It checks the HORN rule set only.  It does NOT cover the oo-cert OWL-RL rule
# set -- the four RDF-list rules in particular -- so the anchor is applied to
# oo-horn certificates and DECLINES for oo-cert rather than overclaiming.
ANCHOR = os.environ.get("OO_HORN_ROCQ")
RULES_TSV = os.environ.get("OO_RULES")


def run_anchor(cert_path, asserted_path):
    """Run the proven oo-horn checker over the same inputs.  Returns a dict,
    or None when no anchor is configured.  Raises RuntimeError when it is
    configured but cannot run, so a caller never reads 'could not check' as
    'checked and agreed'."""
    if not ANCHOR:
        return None
    if not RULES_TSV:
        raise RuntimeError("OO_HORN_ROCQ is set but OO_RULES (rules table) is not")
    if not os.path.exists(ANCHOR):
        raise RuntimeError("anchor binary not found: %s" % ANCHOR)
    cmd = [ANCHOR, "check", RULES_TSV, asserted_path, cert_path]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    try:
        verdict = json.loads(proc.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        verdict = {"raw": proc.stdout.strip()}
    return {"binary": os.path.basename(ANCHOR),
            "exit": proc.returncode,
            "verdict": verdict}


def anchor_declined(fmt):
    """The note shown when an anchor is configured but cannot speak for this
    certificate kind."""
    return {"applied": False,
            "reason": ("oo-horn (Horn) checker only; %s uses the OWL-RL rule set "
                       "(incl. the RDF-list rules it does not cover)" % fmt)}


def main(argv):
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
            dtext = fh.read()
        fmt, steps, refute_line = load_derivations(dpath)
    except OSError as e:
        sys.stderr.write("cannot read %s: %s\n" % (dpath, e))
        return 2
    except ParseError as e:
        sys.stderr.write(str(e) + "\n")
        return 2

    if fmt == "oo-refute":
        # Check the derivation prefix with the same machinery, then flag.
        prefix_result = check_steps(asserted, steps)
        out = {"ok": False, "format": "oo-refute/1",
               "error": "this is an oo-refute/1 refutation certificate; "
                        "oo-cert does not check it (different verdict)",
               "prefix_ok": prefix_result[0]}
        if not prefix_result[0]:
            out["rejected_step"] = prefix_result[1]
        print(json.dumps(out))
        return 2

    # The optional trust anchor.  It speaks for oo-horn certificates; for
    # oo-cert it declines, because the proven checker does not cover the
    # OWL-RL rule set.  A configured-but-broken anchor is a hard error (exit 2):
    # 'could not check' must never read as 'checked and agreed'.
    anchor = None
    if ANCHOR:
        if fmt == "oo-horn":
            try:
                anchor = run_anchor(dpath, gpath)
            except RuntimeError as e:
                sys.stderr.write("anchor: %s\n" % e)
                return 2
        else:
            anchor = anchor_declined(fmt)

    ok, idx = check_steps(asserted, steps)
    if ok:
        out = {"ok": True, "asserted": len(asserted), "derivations": len(steps)}
        if anchor is not None:
            out["anchor"] = anchor
            # The anchor's verdict is advisory evidence here: EYE ran the check,
            # the anchor is the proven second opinion.  Disagreement is surfaced,
            # never hidden.
            if fmt == "oo-horn" and anchor.get("exit") not in (0, None):
                out["anchor_disagrees"] = True
        print(json.dumps(out))
        return 0
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
    print(json.dumps(out))
    return 1


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


if __name__ == "__main__":
    sys.exit(main(sys.argv))
