# oocert -- an N3/EYE re-implementation of the open-ontologies `oo-cert` checker

`oo-cert` (`lake exe oo-cert ASSERTED.tsv DERIVATIONS.tsv`) checks a derivation
certificate against `lean/OOCert/Rules.lean`. This directory re-implements the
same check in N3, run by EYE (WASM, `eyereasoner` v11.24.8). The point is to
show that the certificate-checking pattern does not need Lean: the rule table
is data, the semantics fit in N3 forward rules, and the trusted core is one
readable `checker.n3`.

## Run it

```bash
cd /a0/usr/projects/pup/eye-ontologies/oocert
python3 check.py ASSERTED.tsv DERIVATIONS.tsv

# full test suite (expects the open-ontologies checkout at its default path,
# or set OPEN_ONTOLOGIES=/path/to/open-ontologies):
bash run_tests.sh
```

Exit codes, matching `lean/Main.lean`:

| code | meaning |
| --- | --- |
| `0` | every step checks -- `{"ok":true,"asserted":A,"derivations":D}` |
| `1` | a step was rejected -- JSON names the FIRST one (rule, conclusion, premises) |
| `2` | a file could not be read or parsed (or it is an `oo-refute/1` certificate) |

## Design

Two files:

* **`checker.n3`** -- the trusted core: the meta-rules and one N3 rule per
  `Rules.lean` arm. It matches premise lists, requires each premise to be
  *known*, and re-derives the conclusion. It never searches.
* **`check.py`** -- the untrusted driver, the analogue of `oo-cert`'s CLI
  wrapper: it parses the TSVs, emits canonical N3, runs EYE, and reads back the
  `:ok` facts. It decides nothing itself.

### Canonical encoding (the generator and `checker.n3` agree on this table)

* Each unique term string gets one node. The vocabulary the rules mention
  (`rdf:type`, `rdfs:subClassOf`, `owl:someValuesFrom`, ...) is emitted verbatim
  as its N-Triples IRI, which is the spelling `checker.n3` matches against;
  every other term is opaque and becomes `<urn:t:N>` (N dense). Term equality is
  therefore string equality, exactly as `Rules.lean` treats it.
* Each unique triple `(s,p,o)` gets a node `<urn:tr:K>` with
  `<urn:s>/<urn:p>/<urn:o>`; asserted triples also get `a <urn:Asserted>`.
* Step `i` is `<urn:st:i>` with `<urn:rule> <urn:rule:NAME>`, `<urn:idx> i`,
  `<urn:premise>` per premise, `<urn:premiseList> ( ... )` in documented order,
  and `<urn:conclusion>`.

### Why order is enforced

`Rules.lean` says premise order is part of the contract, and a wrong-order
certificate must be rejected (a false alarm is acceptable, a false pass is not).
Every fixed-arity arm matches `?S <urn:premiseList> (?P1 ?P2 ...)`, so an N3
list pattern binds the premises in position. Get the order wrong and no arm
fires -> the step has no `:ok` -> rejected. Test `neg(b)` proves this.

### Why only earlier-ok conclusions count

`checkAll` inserts each passing step's conclusion and each later step sees it.
The N3 meta-rule that makes an earlier conclusion a known premise is guarded by
`?ji math:lessThan ?si` over integer `<urn:idx>` literals, so a premise counts
only when an EARLIER step that is itself `:ok` concluded it. A circular or
self-supporting certificate cannot pass.

`scm-avf2` concludes `?c2 rdfs:subClassOf ?c1`, the reverse of the other three
restriction-ordering rules. The arm is written that way round and test `neg(c)`
shows the natural direction is rejected.

## Which rules are faithfully ported

All 29 rule ids, with the documented premise order:

`rdfs2 rdfs3 rdfs5 rdfs7 rdfs9 rdfs11 prp-trp prp-symp prp-inv1 prp-inv2 eq-sym`
`scm-eqc1 scm-eqp1 cls-svf1 cls-avf cls-hv1 cls-hv2 cls-int1 cls-int2 cls-uni`
`cls-oo scm-svf1 scm-svf2 scm-avf1 scm-avf2 scm-dom1 scm-dom2 scm-rng1 scm-rng2`

Notable faithful points:

* `scm-eqc1` and `scm-eqp1` each license TWO conclusions; two N3 rules each,
  one per allowed direction.
* `scm-avf2` conclusion reversed, as above.
* `cls-hv1`/`cls-hv2` share the `owl:hasValue` premise but conclude differently.

## Divergence from `Rules.lean` (named, not hidden)

Exactly one relaxation, and only for the four rules that read an RDF list:
`cls-int1`, `cls-int2`, `cls-uni`, `cls-oo`.

In `Rules.lean`, `takeChain` consumes the list chain as an exact, interleaved
run of premises inside the step's premise list. In N3, the chain is emitted as
real asserted triples (`l rdf:first m . l rdf:rest l2 . ...`) but ONLY for
chain triples that appear in `asserted.tsv`, and membership is derived from
that asserted chain. So:

* the constructor triple (`c owl:intersectionOf l`, etc.) must be a premise of
  the step AND asserted -> enforced (`a <urn:Asserted>` in the arm);
* the chain must be asserted (not derived) -> enforced, because only asserted
  `rdf:first`/`rdf:rest` triples are emitted as bare triples;
* the typed-member premises must be premises of the step and known -> enforced;
* **not** enforced: the exact positional interleaving of the chain triples
  within `<urn:premiseList>`, i.e. that the chain appears as the exact contiguous
  block `Rules.lean` expects. Membership is read from the asserted chain by
  structure instead of by position.

For `cls-int1` the arm additionally requires EVERY member of the chain to be
`x rdf:type m` for the conclusion's subject (`?S <urn:allTyped> ?l`); for
`cls-int2`/`cls-uni` it requires the single member named in the conclusion to be
in the chain and typed; for `cls-oo` it requires the conclusion's subject to be
in the chain and needs no instance premise. Test `neg(d)` shows `cls-int1`
rejects when one member's type is missing.

Nothing else diverges: the other 25 rules match `Rules.lean` arm for arm,
including premise order and the `scm-avf2` reversal.

## `oo-refute/1` handling (test 4)

`tests/fixtures/refute/derivations.tsv` is a PLAIN `oo-cert` certificate (one
`rdfs9` step); it is checked normally and passes. The `oo-refute/1` format lives
in `tests/fixtures/refute/good.tsv`: its first line is the tag `oo-refute/1`,
then derivation steps, then a `refute TAB rule ...` line. That is a DIFFERENT
sentence (a refutation, not a derivation), so `check.py` does not silently check
it as an `oo-cert` certificate: it checks the derivation prefix with the same
machinery and returns exit 2 with `"format":"oo-refute/1"` and a `prefix_ok`
flag. Mapping it to an `oo-cert` verdict would be a category error, the same one
`docs/lean-certificates.md` warns about between `oo-cert` and `oo-refute`.

## `oo-horn` files

`tests/fixtures/horn/supplier/derivations.tsv` is `oo-horn` `horn.tsv` format
(`idx TAB bindCount TAB (var TAB term)* TAB conclusion TAB premises`), not
`oo-cert`. `check.py` auto-detects it from the first field's shape, maps the
rule index through `OOCert.Builtin.asHorn`, and reuses the same `checker.n3`
(the premises and conclusion travel as concrete triples). Positive test 2 is
this file; `forged.tsv` is rejected at step 2.

## Tests

`run_tests.sh` builds its negative fixtures on the fly and checks 8 cases:

| case | expected |
| --- | --- |
| positive `refute/derivations.tsv` (single `rdfs9`) | 0 |
| positive `horn/supplier` (`oo-horn`, three `rdfs9`) | 0 |
| neg(a) premise asserted nowhere, concluded nowhere | 1 |
| neg(b) `rdfs9` premises in the wrong order | 1 |
| neg(c) `scm-avf2` conclusion in the natural (wrong) direction | 1 |
| neg(d) `cls-int1` missing one member's type | 1 |
| neg `horn/supplier/forged.tsv` | 1 |
| parse `refute/good.tsv` flagged as `oo-refute/1` | 2 |

## Performance

Each run starts the EYE WASM engine, so the wall time is dominated by `npx`
startup, not reasoning. Measured here: ~0.65 s for a 3-step certificate, of
which ~0.55 s is `npx`/WASM startup and the reasoning itself is a few ms. The
cost that will actually bite is O(steps x candidates) in the two meta-rules that
copy an earlier conclusion onto every later step's premise (`<urn:knownAt>`), so
runtime should scale worse than linearly in the number of steps. For large real
certificates this encoding is a feasibility demo, not a fast checker; the Lean
checker is the production one. No inference-fuse aborts were observed on the
fixtures here (`--ignore-inference-fuse` is passed to be safe).

## What this does NOT claim

The soundness theorem `OOCert.certificate_sound` is about the Lean function and
is not reproved here. N3 rules are data interpreted by EYE; an extension or a
bug in the reasoner is outside this checker's trust argument. What it shows is
that the *shape* of the check -- opaque-term equality, ordered premises,
earlier-ok conclusions, per-rule arms -- is expressible in N3 without search.
