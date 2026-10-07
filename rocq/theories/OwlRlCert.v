(** * The oo-cert checker for the OWL-RL rule set, and its soundness.

    [OwlRl.v] proves the four RDF-list rules sound and gives a combined checker
    for a certificate that mixes Horn steps and list steps. This file adds the
    oo-cert INPUT FORMAT (the `derivations.tsv` the notebook and `eye/check.py`
    already write): `rule TAB s TAB p TAB o TAB premise*`.

    In that format the rule is a NAME and the premises are concrete triples, so
    the fixed-arity rows are checked by MATCHING the written premises against the
    rule's patterns rather than by reading a binding out of the certificate. The
    matcher computes a consistent substitution; [match_body_sound] proves the
    computed binding instantiates the rule's body to exactly the written premises,
    which is the same fact [ainsts_agrees] gives the Horn path, so the row is
    discharged by [builtin_sound] for free.

    Nothing above changes. This is the file that turns the Rocq checker into one
    that can speak for `oo-cert`, not just `oo-horn`.
*)

From Stdlib Require Import String List Bool Arith NArith.
From OOCertRocq Require Import Syntax Semantics Checker Sound Interp Builtin OwlRl Parse Run.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** ** Consistency of an accumulated binding *)

Definition extends (b b' : list (string * term)) : Prop :=
  forall v t, blookup b v = Some t -> blookup b' v = Some t.

Lemma extends_refl : forall b, extends b b.
Proof. intros b v t H. exact H. Qed.

Lemma extends_trans : forall a b c, extends a b -> extends b c -> extends a c.
Proof. intros a b c Hab Hbc v t H. apply Hbc, Hab, H. Qed.

Lemma pinst_extends : forall b b' p t,
  extends b b' -> pinst b p = Some t -> pinst b' p = Some t.
Proof.
  intros b b' [v|u] t He H; simpl in *.
  - apply He. exact H.
  - exact H.
Qed.

Lemma ainst_extends : forall b b' a t,
  extends b b' -> ainst b a = Some t -> ainst b' a = Some t.
Proof.
  intros b b' a t He H. unfold ainst in H.
  destruct (pinst b (psubj a)) as [ts|] eqn:Es; try discriminate.
  destruct (pinst b (ppred a)) as [tp|] eqn:Ep; try discriminate.
  destruct (pinst b (pobj a)) as [to|] eqn:Eo; try discriminate.
  injection H as <-.
  unfold ainst.
  rewrite (pinst_extends b b' (psubj a) ts He Es),
          (pinst_extends b b' (ppred a) tp He Ep),
          (pinst_extends b b' (pobj a) to He Eo).
  reflexivity.
Qed.

Lemma ainsts_extends : forall b b' l ts,
  extends b b' -> ainsts b l = Some ts -> ainsts b' l = Some ts.
Proof.
  intros b b' l. induction l as [|a ar IH]; intros ts He H; simpl in *.
  - injection H as <-. reflexivity.
  - destruct (ainst b a) as [ta|] eqn:Ea; try discriminate.
    destruct (ainsts b ar) as [tr|] eqn:Er; try discriminate.
    injection H as <-.
    rewrite (ainst_extends b b' a ta He Ea).
    now rewrite (IH tr He eq_refl).
Qed.

(** ** The matcher

    [bind_add] extends a binding only if the variable is free or agrees.
    [match_pat] / [match_tpat] / [match_body] walk the pattern and the concrete
    triples together, left to right, which is the premise order the format fixes. *)

Definition bind_add (b : list (string * term)) (v : string) (t : term)
  : option (list (string * term)) :=
  match blookup b v with
  | Some t' => if String.eqb t' t then Some b else None
  | None => Some ((v, t) :: b)
  end.

Definition match_pat (b : list (string * term)) (p : pat) (t : term)
  : option (list (string * term)) :=
  match p with
  | PTerm u => if String.eqb u t then Some b else None
  | PVar v => bind_add b v t
  end.

Definition match_tpat (b : list (string * term)) (a : tpat) (tr : triple)
  : option (list (string * term)) :=
  match match_pat b (psubj a) (tsubj tr) with
  | Some b1 =>
      match match_pat b1 (ppred a) (tpred tr) with
      | Some b2 => match_pat b2 (pobj a) (tobj tr)
      | None => None
      end
  | None => None
  end.

Fixpoint match_body (b : list (string * term)) (body : list tpat)
                    (prems : list triple) : option (list (string * term)) :=
  match body, prems with
  | [], [] => Some b
  | a :: ar, tr :: trr =>
      match match_tpat b a tr with
      | Some b1 => match_body b1 ar trr
      | None => None
      end
  | _, _ => None
  end.

(** ** The matcher is faithful *)

Lemma bind_add_extends : forall b v t b',
  bind_add b v t = Some b' -> extends b b'.
Proof.
  intros b v t b' H. unfold bind_add in H.
  destruct (blookup b v) as [t'|] eqn:E.
  - destruct (String.eqb t' t) eqn:E2; [|discriminate].
    injection H as <-. apply extends_refl.
  - injection H as <-. intros w u Hw. simpl. fold blookup.
    destruct (String.eqb v w) eqn:E3.
    + apply String.eqb_eq in E3. subst w. rewrite E in Hw. discriminate.
    + exact Hw.
Qed.

Lemma match_pat_sound : forall b p t b',
  match_pat b p t = Some b' -> pinst b' p = Some t /\ extends b b'.
Proof.
  intros b [v|u] t b' H; simpl in H.
  - unfold bind_add in H.
    destruct (blookup b v) as [t'|] eqn:E.
    + destruct (String.eqb t' t) eqn:E2; [|discriminate].
      injection H as <-. split.
      * simpl. apply String.eqb_eq in E2. rewrite E, E2. reflexivity.
      * apply extends_refl.
    + injection H as <-. split.
      * simpl. fold blookup. rewrite (String.eqb_refl v). reflexivity.
      * unfold extends. intros w u0 Hw. simpl. fold blookup.
        destruct (String.eqb v w) eqn:E3.
        -- apply String.eqb_eq in E3. subst w. rewrite E in Hw. discriminate.
        -- exact Hw.
  - destruct (String.eqb u t) eqn:E; [|discriminate].
    injection H as <-. apply String.eqb_eq in E. subst t. split.
    * simpl. reflexivity.
    * apply extends_refl.
Qed.

Lemma match_tpat_sound : forall b a tr b',
  match_tpat b a tr = Some b' -> ainst b' a = Some tr /\ extends b b'.
Proof.
  intros b a tr b' H. unfold match_tpat in H.
  destruct a as [ps pp po]. destruct tr as [ts tp to]. cbn in H.
  destruct (match_pat b ps ts) as [b1|] eqn:E1.
  - cbn in H.
    destruct (match_pat b1 pp tp) as [b2|] eqn:E2.
    + cbn in H.
      destruct (match_pat b2 po to) as [b3|] eqn:E3.
      * cbn in H. injection H as <-.
        apply match_pat_sound in E1 as [H1 He1].
        apply match_pat_sound in E2 as [H2 He2].
        apply match_pat_sound in E3 as [H3 He3].
        split.
        -- unfold ainst. cbn.
           assert (Eb1 : extends b1 b3) by (apply (extends_trans b1 b2 b3 He2 He3)).
           rewrite (pinst_extends b1 b3 ps ts Eb1 H1),
                   (pinst_extends b2 b3 pp tp He3 H2), H3.
           reflexivity.
        -- apply (extends_trans b b1 b3 He1). apply (extends_trans b1 b2 b3 He2 He3).
      * cbn in H. discriminate.
    + cbn in H. discriminate.
  - cbn in H. discriminate.
Qed.

Lemma match_body_sound : forall body prems b b',
  match_body b body prems = Some b' ->
  ainsts b' body = Some prems /\ extends b b'.
Proof.
  induction body as [|a ar IH]; intros prems b b' H.
  - destruct prems; simpl in H; try discriminate.
    injection H as <-. split; [reflexivity | apply extends_refl].
  - destruct prems as [|tr trr]; simpl in H; [discriminate|].
    destruct (match_tpat b a tr) as [b1|] eqn:E1; [|discriminate].
    destruct (match_body b1 ar trr) as [b2|] eqn:E2; [|discriminate].
    injection H as <-.
    apply match_tpat_sound in E1 as [Ha He1].
    apply IH in E2 as [Har He2].
    split.
    + unfold ainsts. fold ainsts.
      rewrite (ainst_extends _ _ _ _ He2 Ha), Har. reflexivity.
    + apply (extends_trans b b1 b2 He1 He2).
Qed.

(** ** Checking a named fixed-arity rule against concrete premises *)

Fixpoint check_named (nm : string) (prems : list triple) (concl : triple)
                    (R : list rule) : bool :=
  match R with
  | [] => false
  | r :: rest =>
      (String.eqb (rname r) nm &&
       match match_body [] (rbody r) prems with
       | Some b => match ainst b (rhead r) with
                   | Some t => triple_eqb t concl
                   | None => false
                   end
       | None => false
       end)
      || check_named nm prems concl rest
  end.

Lemma check_named_spec : forall nm prems concl R,
  check_named nm prems concl R = true ->
  exists r, In r R /\ rname r = nm /\
    exists b, match_body [] (rbody r) prems = Some b /\ ainst b (rhead r) = Some concl.
Proof.
  induction R as [|r rest IH]; intros H; simpl in H; [discriminate|].
  apply orb_prop in H as [H|H].
  - apply andb_prop in H as [Hnm Hm].
    apply String.eqb_eq in Hnm.
    destruct (match_body [] (rbody r) prems) as [b|] eqn:Eb; [|discriminate].
    destruct (ainst b (rhead r)) as [t|] eqn:Et; [|discriminate].
    apply triple_eqb_true in Hm. subst t.
    exists r. split; [now left|]. split; [exact Hnm|].
    exists b. split; assumption.
  - apply IH in H as [r' [Hin [Hnm Hx]]].
    exists r'. split; [now right|]. split; assumption.
Qed.

(** ** A concrete oo-cert step and the checker *)

Record cstep : Set := CStep {
  crule  : string ;
  cprem  : list triple ;
  cconcl : triple
}.

Definition is_list_rule (nm : string) : option lrule :=
  if String.eqb nm "cls-int1" then Some LInt1
  else if String.eqb nm "cls-int2" then Some LInt2
  else if String.eqb nm "cls-uni" then Some LUni
  else if String.eqb nm "cls-oo" then Some LOo
  else None.

Definition check_cstep (G known : list triple) (s : cstep) : bool :=
  match is_list_rule (crule s) with
  | Some lr => check_lstep G known (LStep lr (cprem s) (cconcl s))
  | None =>
      check_named (crule s) (cprem s) (cconcl s) builtin
      && forallb (fun p => lknown G known p) (cprem s)
  end.

Lemma check_cstep_sound : forall G known s,
  (forall t, In t known -> entails_owlrl G t) ->
  check_cstep G known s = true ->
  entails_owlrl G (cconcl s).
Proof.
  intros G known s Hk Hchk I HRL HLC HG.
  unfold check_cstep in Hchk.
  destruct (is_list_rule (crule s)) as [lr|] eqn:Elr.
  - exact (check_lstep_sound G known (LStep lr (cprem s) (cconcl s)) Hk Hchk I HRL HLC HG).
  - apply andb_prop in Hchk as [Hmatch Hprems].
    apply check_named_spec in Hmatch as [r [Hin [Hnm [b [Hb Hhd]]]]].
    apply match_body_sound in Hb as [Hinst _].
    apply ainsts_agrees in Hinst.
    apply ainst_agrees in Hhd.
    change (itrue I (cconcl s)).
    rewrite <- Hhd.
    apply (builtin_sound I HRL r Hin).
    intros a Ha.
    assert (Hinp : In (inst (subst_of b) a) (cprem s))
      by (rewrite <- Hinst; now apply in_map).
    rewrite forallb_forall in Hprems.
    specialize (Hprems _ Hinp).
    exact (lknown_true G known I Hk HRL HLC HG (inst (subst_of b) a) Hprems).
Qed.

Fixpoint check_cfrom (G known : list triple) (ss : list cstep) : bool :=
  match ss with
  | [] => true
  | s :: rest => check_cstep G known s && check_cfrom G (known ++ [cconcl s]) rest
  end.

Definition check_ccert (G : list triple) (ss : list cstep) : bool :=
  check_cfrom G G ss.

Lemma check_cfrom_sound : forall G ss known,
  (forall t, In t known -> entails_owlrl G t) ->
  check_cfrom G known ss = true ->
  forall t, In t (map cconcl ss) -> entails_owlrl G t.
Proof.
  intros G ss. induction ss as [|s rest IH]; intros known Hk Hchk t Hin.
  - simpl in Hin. contradiction.
  - simpl in Hchk. apply andb_prop in Hchk as [Hstep Hrest].
    apply check_cstep_sound in Hstep; [|exact Hk].
    simpl in Hin. destruct Hin as [<-|Hin].
    + exact Hstep.
    + apply (IH (known ++ [cconcl s])); [|exact Hrest|exact Hin].
      intros u Hu. apply in_app_or in Hu as [Hu|Hu].
      * now apply Hk.
      * destruct Hu as [<-|[]]. exact Hstep.
Qed.

(** ** THE ABSOLUTE THEOREM for an oo-cert certificate

    Every conclusion of a class-"oo-cert" certificate accepted by this checker
    is true in every OWL-RL model of the asserted graph. The Horn rows are
    discharged by [builtin_sound] through the matcher, the four list rules by
    [ListConds]. No rule is assumed. *)

Theorem check_ccert_sound : forall G ss,
  check_ccert G ss = true ->
  forall t, In t (map cconcl ss) -> entails_owlrl G t.
Proof.
  intros G ss Hchk t Hin.
  apply (check_cfrom_sound G ss G); [|exact Hchk|exact Hin].
  intros u Hu I HRL HLC HG. exact (HG u Hu).
Qed.

(** ** Parsing the oo-cert derivations format *)

Definition parse_cstep_line (fs : list string) : option cstep :=
  match fs with
  | nm :: s :: p :: o :: prems =>
      match triples_of prems with
      | Some ps => Some (CStep nm ps (Tri s p o))
      | None => None
      end
  | _ => None
  end.

Definition parse_ccert (txt : string) : option (list cstep) :=
  map_opt (fun l => parse_cstep_line (fields l)) (lines txt).

Definition run_owlrl (gtxt dtxt : string) : outcome :=
  match parse_triples gtxt with
  | None => ParseError 1
  | Some G =>
      match parse_ccert dtxt with
      | None => ParseError 2
      | Some ss =>
          if check_ccert G ss
          then Accepted true 0 (length G) (length ss)
          else Rejected 0 (length G) (length ss)
      end
  end.

Theorem run_owlrl_is_sound : forall gtxt dtxt G ss b nr ng ns,
  parse_triples gtxt = Some G ->
  parse_ccert dtxt = Some ss ->
  run_owlrl gtxt dtxt = Accepted b nr ng ns ->
  forall t, In t (map cconcl ss) -> entails_owlrl G t.
Proof.
  intros gtxt dtxt G ss b nr ng ns HG Hss Hrun t Hin.
  unfold run_owlrl in Hrun. rewrite HG, Hss in Hrun.
  destruct (check_ccert G ss) eqn:Hchk; [|discriminate].
  exact (check_ccert_sound G ss Hchk t Hin).
Qed.
