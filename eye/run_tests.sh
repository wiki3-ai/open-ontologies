#!/usr/bin/env bash
# oocert/run_tests.sh -- exercise the EYE/N3 re-implementation of oo-cert.
#
# Positive cases come from the open-ontologies fixtures; negative cases are
# built here so the rejection behaviour is reproducible.  Exits non-zero if
# any expectation is not met.
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
O="${OPEN_ONTOLOGIES:-$(cd "$HERE/.." && pwd)}"
FIX="$O/tests/fixtures"
NEG="$HERE/neg"
mkdir -p "$NEG"

fails=0
ran=0

# expect <wanted-exit> <label> -- <check.py args...>
expect() {
  local want="$1"; shift
  local label="$1"; shift
  [ "$1" = "--" ] && shift
  ran=$((ran + 1))
  local out
  out="$(python3 "$HERE/check.py" "$@" 2>&1)"
  local got=$?
  if [ "$got" = "$want" ]; then
    echo "PASS [$label] exit=$got"
    echo "       $out"
  else
    echo "FAIL [$label] want exit=$want got=$got"
    echo "       $out"
    fails=$((fails + 1))
  fi
}

RDF='http://www.w3.org/1999/02/22-rdf-syntax-ns'
OWL='http://www.w3.org/2002/07/owl'
RDFS='http://www.w3.org/2000/01/rdf-schema'
T="<$RDF#type>"; SC="<$RDFS#subClassOf>"; SP="<$RDFS#subPropertyOf>"
AVF="<$OWL#allValuesFrom>"; OP="<$OWL#onProperty>"; ISEC="<$OWL#intersectionOf>"
FIRST="<$RDF#first>"; REST="<$RDF#rest>"; NIL="<$RDF#nil>"

# --- negative fixtures ------------------------------------------------------
# (a) premise asserted nowhere and concluded nowhere
printf '<http://ex.org/B>\t%s\t<http://ex.org/C>\n' "$SC" > "$NEG/a_asserted.tsv"
printf '%s\t<http://ex.org/a>\t%s\t<http://ex.org/C>\t<http://ex.org/a>\t%s\t<http://ex.org/B>\t<http://ex.org/B>\t%s\t<http://ex.org/C>\n' \
  rdfs9 "$T" "$T" "$SC" > "$NEG/a_deriv.tsv"

# (b) rdfs9 with the premises in the wrong order (both asserted)
printf '<http://ex.org/a>\t%s\t<http://ex.org/A>\n<http://ex.org/A>\t%s\t<http://ex.org/B>\n' \
  "$T" "$SC" > "$NEG/b_asserted.tsv"
printf '%s\t<http://ex.org/a>\t%s\t<http://ex.org/B>\t<http://ex.org/A>\t%s\t<http://ex.org/B>\t<http://ex.org/a>\t%s\t<http://ex.org/A>\n' \
  rdfs9 "$T" "$SC" "$T" > "$NEG/b_deriv.tsv"

# (c) scm-avf2 with the conclusion in the natural (wrong) direction c1 sc c2
printf '<http://ex.org/C1>\t%s\t<http://ex.org/Y>\n<http://ex.org/C1>\t%s\t<http://ex.org/p1>\n<http://ex.org/C2>\t%s\t<http://ex.org/Y>\n<http://ex.org/C2>\t%s\t<http://ex.org/p2>\n<http://ex.org/p1>\t%s\t<http://ex.org/p2>\n' \
  "$AVF" "$OP" "$AVF" "$OP" "$SP" > "$NEG/c_asserted.tsv"
printf '%s\t<http://ex.org/C1>\t%s\t<http://ex.org/C2>\t<http://ex.org/C1>\t%s\t<http://ex.org/Y>\t<http://ex.org/C1>\t%s\t<http://ex.org/p1>\t<http://ex.org/C2>\t%s\t<http://ex.org/Y>\t<http://ex.org/C2>\t%s\t<http://ex.org/p2>\t<http://ex.org/p1>\t%s\t<http://ex.org/p2>\n' \
  scm-avf2 "$SC" "$AVF" "$OP" "$AVF" "$OP" "$SP" > "$NEG/c_deriv.tsv"

# (d) cls-int1 with one member's type missing
printf '<http://ex.org/c>\t%s\t<http://ex.org/l>\n' "$ISEC" > "$NEG/d_asserted.tsv"
printf '<http://ex.org/l>\t%s\t<http://ex.org/A>\n' "$FIRST" >> "$NEG/d_asserted.tsv"
printf '<http://ex.org/l>\t%s\t<http://ex.org/l2>\n' "$REST" >> "$NEG/d_asserted.tsv"
printf '<http://ex.org/l2>\t%s\t<http://ex.org/B>\n' "$FIRST" >> "$NEG/d_asserted.tsv"
printf '<http://ex.org/l2>\t%s\t%s\n' "$REST" "$NIL" >> "$NEG/d_asserted.tsv"
printf '<http://ex.org/x>\t%s\t<http://ex.org/A>\n' "$T" >> "$NEG/d_asserted.tsv"
printf '%s\t<http://ex.org/x>\t%s\t<http://ex.org/c>\t<http://ex.org/c>\t%s\t<http://ex.org/l>\t<http://ex.org/l>\t%s\t<http://ex.org/A>\t<http://ex.org/l>\t%s\t<http://ex.org/l2>\t<http://ex.org/l2>\t%s\t<http://ex.org/B>\t<http://ex.org/l2>\t%s\t%s\t<http://ex.org/x>\t%s\t<http://ex.org/A>\n' \
  cls-int1 "$T" "$ISEC" "$FIRST" "$REST" "$FIRST" "$REST" "$NIL" "$T" > "$NEG/d_deriv.tsv"

# --- positive ---------------------------------------------------------------
expect 0 "pos: refute/derivations.tsv (single rdfs9)" -- \
  "$FIX/refute/asserted.tsv" "$FIX/refute/derivations.tsv"
expect 0 "pos: horn/supplier (oo-horn, 3 rdfs9)" -- \
  "$FIX/horn/supplier/asserted.tsv" "$FIX/horn/supplier/derivations.tsv"

# --- negative ---------------------------------------------------------------
expect 1 "neg(a): unasserted / underived premise" -- \
  "$NEG/a_asserted.tsv" "$NEG/a_deriv.tsv"
expect 1 "neg(b): premise in wrong order" -- \
  "$NEG/b_asserted.tsv" "$NEG/b_deriv.tsv"
expect 1 "neg(c): scm-avf2 conclusion wrong direction" -- \
  "$NEG/c_asserted.tsv" "$NEG/c_deriv.tsv"
expect 1 "neg(d): cls-int1 missing a member type" -- \
  "$NEG/d_asserted.tsv" "$NEG/d_deriv.tsv"
expect 1 "neg: horn/supplier/forged.tsv" -- \
  "$FIX/horn/supplier/asserted.tsv" "$FIX/horn/supplier/forged.tsv"
expect 2 "parse: refute/good.tsv is oo-refute/1" -- \
  "$FIX/refute/asserted.tsv" "$FIX/refute/good.tsv"

# --- summary ----------------------------------------------------------------
echo
echo "ran $ran, failed $fails"
[ "$fails" = 0 ]
