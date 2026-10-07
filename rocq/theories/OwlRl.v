(** * The four OWL-RL list rules, and the soundness theorem for the whole
      OWL-RL rule set.

    ADDITIVE. Nothing in [Checker.v], [Sound.v] or [Builtin.v] changes. The 27
    built-in Horn rows are already proved over [entails_abs], and they lift to
    the weaker OWL-RL claim for free ([entails_abs_owlrl]). This file adds the
    FOUR rules whose premise count is data rather than fixed by the rule:
    [cls-int1], [cls-int2], [cls-uni] and [cls-oo]. Together the two give
    [owl_rl_certificate_sound] over the full OWL-RL rule set.

    The reading mirrors `lean/OOCert/Rules.lean` and `eye/checker.n3`: the
    constructor triple and the whole rdf:first / rdf:rest chain must be
    ASSERTED (read off G), while the member-typing premises may be asserted or
    concluded by an earlier step ([lknown]). The model side is [ListConds] in
    [Interp.v]. See [rocq-owl-rl-scope.md] sections 2a-2c.
*)

From Stdlib Require Import String List Bool Arith NArith Lia Wellfounded.
From OOCertRocq Require Import Syntax Semantics Checker Sound Interp Builtin.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** ** Strings *)

Lemma mem_str_In : forall x l, mem_str x l = true -> In x l.
Proof.
  intros x l. induction l as [|k rest IH]; simpl; intro H.
  - discriminate.
  - apply orb_prop in H as [H|H].
    + apply String.eqb_eq in H. left. now symmetry.
    + right. now apply IH.
Qed.

(** ** The four rule names *)

Inductive lrule : Set := LInt1 | LInt2 | LUni | LOo.

Definition lrule_name (r : lrule) : string :=
  match r with
  | LInt1 => "cls-int1" | LInt2 => "cls-int2"
  | LUni  => "cls-uni"  | LOo   => "cls-oo"
  end.

(** ** A list step

    [lprem] is the written premise list: the constructor triple first, then
    the chain, then the rule-specific member premises. Written rather than
    computed, as everywhere else in this development (R-CHK-3). *)

Record lstep : Set := LStep {
  lrule_ : lrule ;
  lprem  : list triple ;
  lconcl : triple
}.

(** ** Reading the chain off the premise list, ASSERTING each link

    This is `takeChain` from `Rules.lean` with [inG] fixed to membership in G:
    every chain triple must be in the asserted graph. *)

Fixpoint take_chain (G : list triple) (l : term) (ps : list triple)
  : option (list term * list triple) :=
  if String.eqb l rdf_nil then Some ([], ps)
  else
    match ps with
    | Tri l1 f m :: Tri l2 r l' :: ps' =>
        if String.eqb l1 l && String.eqb f rdf_first &&
           String.eqb l2 l && String.eqb r rdf_rest &&
           mem_triple (Tri l1 f m) G && mem_triple (Tri l2 r l') G
        then match take_chain G l' ps' with
             | Some (ms, q) => Some (m :: ms, q)
             | None => None
             end
        else None
    | _ => None
    end.

(** `all_typed x k ms ps`: `ps` is exactly `x rdf:type m` for each `m` in `ms`,
    in order. *)

Fixpoint all_typed (x : term) (k : triple -> bool) (ms : list term)
                 (ps : list triple) : bool :=
  match ms, ps with
  | [], [] => true
  | m :: ms', Tri x' t m' :: ps' =>
      String.eqb x' x && String.eqb t rdf_type && String.eqb m' m &&
      k (Tri x' t m') && all_typed x k ms' ps'
  | _, _ => false
  end.

(** A premise may be ASSERTED or concluded by an earlier step, EXCEPT the
    constructor and the chain, which are tested against G directly. *)

Definition lknown (G known : list triple) (t : triple) : bool :=
  mem_triple t G || mem_triple t known.

(** ** The checker

    The four arms, each a transcription of the rule in `Rules.lean`. *)

Definition check_lstep (G known : list triple) (s : lstep) : bool :=
  match s.(lrule_), s.(lprem), s.(lconcl) with
  | LInt1, Tri c io l :: ps, Tri xs xp xo =>
      String.eqb io owl_intersectionOf && mem_triple (Tri c io l) G &&
      match take_chain G l ps with
      | Some (ms, q) =>
          all_typed xs (lknown G known) ms q &&
          String.eqb xp rdf_type && String.eqb xo c
      | None => false
      end
  | LInt2, Tri c io l :: ps, Tri xs xp xo =>
      String.eqb io owl_intersectionOf && mem_triple (Tri c io l) G &&
      match take_chain G l ps with
      | Some (ms, [Tri x t c']) =>
          String.eqb t rdf_type && String.eqb c' c &&
          lknown G known (Tri x t c') &&
          String.eqb xs x && String.eqb xp rdf_type && mem_str xo ms
      | _ => false
      end
  | LUni, Tri c uo l :: ps, Tri xs xp xo =>
      String.eqb uo owl_unionOf && mem_triple (Tri c uo l) G &&
      match take_chain G l ps with
      | Some (ms, [Tri x t m]) =>
          String.eqb t rdf_type && mem_str m ms &&
          lknown G known (Tri x t m) &&
          String.eqb xs x && String.eqb xp rdf_type && String.eqb xo c
      | _ => false
      end
  | LOo, Tri c oo l :: ps, Tri xs xp xo =>
      String.eqb oo owl_oneOf && mem_triple (Tri c oo l) G &&
      match take_chain G l ps with
      | Some (ms, []) =>
          mem_str xs ms && String.eqb xp rdf_type && String.eqb xo c
      | _ => false
      end
  | _, _, _ => false
  end.

Fixpoint check_lfrom (G : list triple) (known : list triple)
                     (ss : list lstep) : bool :=
  match ss with
  | [] => true
  | s :: rest => check_lstep G known s && check_lfrom G (known ++ [lconcl s]) rest
  end.

Definition check_lcert (G : list triple) (ss : list lstep) : bool :=
  check_lfrom G [] ss.

(** ** Bridge lemmas *)

(** If the checker read a chain then it IS a chain in G. This is the lemma
    section 2c of the scope report is about: the checker's structural reading of
    the chain agrees with the model's reading of it. Proved by well-founded
    induction on the premise list, because [take_chain] consumes TWO premises at
    a time. *)

Lemma take_chain_chain : forall ps G l ms q,
  take_chain G l ps = Some (ms, q) -> chain G l ms.
Proof.
  apply (@well_founded_ind (list triple) (ltof (list triple) (@length triple))
           (well_founded_ltof (list triple) (@length triple))
           (fun psm => forall G l ms q, take_chain G l psm = Some (ms, q) -> chain G l ms)).
  intros ps IH G l ms q Htc.
  destruct ps as [|[l1 f m] ps0].
  - cbn [take_chain] in Htc.
    destruct (String.eqb l rdf_nil) eqn:E.
    + simpl in Htc. injection Htc as Hms Hq. subst ms q.
      apply String.eqb_eq in E. subst. constructor.
    + simpl in Htc. discriminate.
  - destruct ps0 as [|[l2 r l'] ps1].
    + cbn [take_chain] in Htc.
      destruct (String.eqb l rdf_nil) eqn:E.
      * simpl in Htc. injection Htc as Hms Hq. subst ms q.
        apply String.eqb_eq in E. subst. constructor.
      * simpl in Htc. discriminate.
    + cbn [take_chain] in Htc.
      destruct (String.eqb l rdf_nil) eqn:E.
      * simpl in Htc. injection Htc as Hms Hq. subst ms q.
        apply String.eqb_eq in E. subst. constructor.
      * simpl in Htc.
        destruct (String.eqb l1 l && String.eqb f rdf_first && String.eqb l2 l &&
                  String.eqb r rdf_rest && mem_triple (Tri l1 f m) G &&
                  mem_triple (Tri l2 r l') G) eqn:Eif.
        -- simpl in Htc.
           destruct (take_chain G l' ps1) as [[ms' q']|] eqn:Erec.
           ++ simpl in Htc. injection Htc as Hms Hq. subst ms q.
              apply andb_prop in Eif as [Eif HF].
              apply andb_prop in Eif as [Eif HE].
              apply andb_prop in Eif as [Eif HD].
              apply andb_prop in Eif as [Eif HC].
              apply andb_prop in Eif as [El1 Ef].
              apply String.eqb_eq in El1, Ef, HC, HD. subst l1 f l2 r.
              apply mem_triple_In in HE, HF.
              assert (Hlt : length ps1 < length (Tri l rdf_first m :: Tri l rdf_rest l' :: ps1))
                by (simpl; lia).
              assert (Hrec : chain G l' ms')
                by (apply (IH ps1 Hlt G l' ms' q'); exact Erec).
              exact (@chain_cons G l m l' ms' HE HF Hrec).
           ++ simpl in Htc. discriminate.
        -- simpl in Htc. discriminate.
Qed.

(** `all_typed` at a member gives the member premise. *)

Lemma all_typed_mem : forall x k ms ps,
  all_typed x k ms ps = true ->
  forall m, In m ms -> k (Tri x rdf_type m) = true.
Proof.
  intros x k ms. induction ms as [|m ms' IH]; intros ps H m' Hm.
  - contradiction.
  - destruct ps as [|t ps']; [discriminate|].
    destruct t as [x' t' m0]. simpl in H.
    apply andb_prop in H as [H4 Hall].
    apply andb_prop in H4 as [H3 Hk].
    apply andb_prop in H3 as [H2 Hm0].
    apply andb_prop in H2 as [Hx' Ht].
    apply String.eqb_eq in Hx', Ht, Hm0.
    destruct Hm as [<-|Hm].
    + rewrite Hx', Ht, Hm0 in Hk. exact Hk.
    + exact (IH ps' Hall m' Hm).
Qed.

(** A premise that [lknown] accepts is true in every OWL-RL model of G. *)

Lemma lknown_true : forall G known I,
  (forall t, In t known -> entails_owlrl G t) ->
  RL I -> ListConds G I -> (forall u, In u G -> itrue I u) ->
  forall t, lknown G known t = true -> itrue I t.
Proof.
  intros G known I Hk HRL HLC HG t H.
  unfold lknown in H. apply orb_prop in H as [H|H].
  - apply mem_triple_In in H. exact (HG t H).
  - apply mem_triple_In in H. exact (Hk t H I HRL HLC HG).
Qed.

(** ** One step *)

Lemma check_lstep_sound : forall G known s,
  (forall t, In t known -> entails_owlrl G t) ->
  check_lstep G known s = true ->
  entails_owlrl G (lconcl s).
Proof.
  intros G known s Hk Hchk I HRL HLC HG.
  destruct s as [r prem concl]. destruct concl as [xs xp xo].
  change (itrue I (Tri xs xp xo)).
  destruct r; simpl in Hchk.
  - (* LInt1 *)
    destruct prem as [| [c io l] ps]; [simpl in Hchk; discriminate|].
    apply andb_prop in Hchk as [Hhead Hmatch].
    apply andb_prop in Hhead as [Hio Hmem].
    apply String.eqb_eq in Hio. subst io.
    apply mem_triple_In in Hmem.
    destruct (take_chain G l ps) as [[ms q]|] eqn:Etc.
    + simpl in Hmatch.
      apply andb_prop in Hmatch as [Hatxp Hxo].
      apply andb_prop in Hatxp as [Hat Hxp].
      apply String.eqb_eq in Hxp, Hxo. subst xp xo.
      apply take_chain_chain in Etc.
      apply (lc_int HLC c l ms Hmem Etc (iden I xs)).
      intros m Hm.
      apply (lknown_true G known I Hk HRL HLC HG (Tri xs rdf_type m)).
      now apply (all_typed_mem xs (lknown G known) ms q Hat m Hm).
    + simpl in Hmatch. discriminate.
  - (* LInt2 *)
    destruct prem as [| [c io l] ps]; [simpl in Hchk; discriminate|].
    apply andb_prop in Hchk as [Hhead Hmatch].
    apply andb_prop in Hhead as [Hio Hmem].
    apply String.eqb_eq in Hio. subst io.
    apply mem_triple_In in Hmem.
    destruct (take_chain G l ps) as [[ms q]|] eqn:Etc.
    + simpl in Hmatch.
      destruct q as [|[x t c'] q'].
      * simpl in Hmatch. discriminate.
      * destruct q' as [|w q''].
        -- simpl in Hmatch.
           apply andb_prop in Hmatch as [H5 Hmm].
           apply andb_prop in H5 as [H4 Hxp].
           apply andb_prop in H4 as [H3 Hxs].
           apply andb_prop in H3 as [H2 Hlk].
           apply andb_prop in H2 as [Ht Hc'].
           apply String.eqb_eq in Ht, Hc', Hxs, Hxp. subst t c' xp xs.
           apply mem_str_In in Hmm.
           apply take_chain_chain in Etc.
           assert (Hcx : icext I (iden I c) (iden I x))
             by (apply (lknown_true G known I Hk HRL HLC HG (Tri x rdf_type c) Hlk)).
           exact (lc_int2 HLC c l ms Hmem Etc (iden I x) Hcx xo Hmm).
        -- simpl in Hmatch. discriminate.
    + simpl in Hmatch. discriminate.
  - (* LUni *)
    destruct prem as [| [c uo l] ps]; [simpl in Hchk; discriminate|].
    apply andb_prop in Hchk as [Hhead Hmatch].
    apply andb_prop in Hhead as [Huo Hmem].
    apply String.eqb_eq in Huo. subst uo.
    apply mem_triple_In in Hmem.
    destruct (take_chain G l ps) as [[ms q]|] eqn:Etc.
    + simpl in Hmatch.
      destruct q as [|[x t m] q'].
      * simpl in Hmatch. discriminate.
      * destruct q' as [|w q''].
        -- simpl in Hmatch.
           apply andb_prop in Hmatch as [H5 Hxo].
           apply andb_prop in H5 as [H4 Hxp].
           apply andb_prop in H4 as [H3 Hxs].
           apply andb_prop in H3 as [H2 Hlk].
           apply andb_prop in H2 as [Ht Hmm].
           apply String.eqb_eq in Ht, Hxs, Hxp, Hxo. subst t xp xo xs.
           apply mem_str_In in Hmm.
           apply take_chain_chain in Etc.
           exact (lc_uni HLC c l ms Hmem Etc (iden I x) m Hmm
                        (lknown_true G known I Hk HRL HLC HG (Tri x rdf_type m) Hlk)).
        -- simpl in Hmatch. discriminate.
    + simpl in Hmatch. discriminate.
  - (* LOo *)
    destruct prem as [| [c oo l] ps]; [simpl in Hchk; discriminate|].
    apply andb_prop in Hchk as [Hhead Hmatch].
    apply andb_prop in Hhead as [Hoo Hmem].
    apply String.eqb_eq in Hoo. subst oo.
    apply mem_triple_In in Hmem.
    destruct (take_chain G l ps) as [[ms q]|] eqn:Etc.
    + simpl in Hmatch.
      destruct q as [|u q'].
      * simpl in Hmatch.
        apply andb_prop in Hmatch as [Hxstype Hxo].
        apply andb_prop in Hxstype as [Hxs Hxp].
        apply String.eqb_eq in Hxp, Hxo. subst xp xo.
        apply mem_str_In in Hxs.
        apply take_chain_chain in Etc.
        exact (lc_oo HLC c l ms Hmem Etc xs Hxs).
      * simpl in Hmatch. discriminate.
    + simpl in Hmatch. discriminate.
Qed.

Lemma check_lfrom_sound : forall G ss known,
  (forall t, In t known -> entails_owlrl G t) ->
  check_lfrom G known ss = true ->
  forall t, In t (map lconcl ss) -> entails_owlrl G t.
Proof.
  intros G ss. induction ss as [|s rest IH]; intros known Hk Hchk t Hin.
  - simpl in Hin. contradiction.
  - simpl in Hchk. apply andb_prop in Hchk as [Hstep Hrest].
    apply check_lstep_sound in Hstep; [|exact Hk].
    simpl in Hin. destruct Hin as [<-|Hin].
    + exact Hstep.
    + apply (IH (known ++ [lconcl s])); [|exact Hrest|exact Hin].
      intros u Hu. apply in_app_or in Hu as [Hu|Hu].
      * now apply Hk.
      * destruct Hu as [<-|[]]. exact Hstep.
Qed.

(** ** The four list rules are sound *)

Theorem owl_rl_list_sound : forall G ss,
  check_lcert G ss = true ->
  forall t, In t (map lconcl ss) -> entails_owlrl G t.
Proof.
  intros G ss Hchk t Hin.
  apply (check_lfrom_sound G ss []); [|exact Hchk|exact Hin].
  intros u Hu. contradiction.
Qed.

(** ** The 27 Horn rows lift to the OWL-RL claim *)

Lemma entails_abs_owlrl : forall G t, entails_abs G t -> entails_owlrl G t.
Proof. intros G t H I HRL HLC HG. exact (H I HRL HG). Qed.

(** ** Horn steps, discharged against the built-in table *)

Lemma check_hstep_owlrl : forall G known s,
  (forall t, In t known -> entails_owlrl G t) ->
  check_step_weak known builtin s = true ->
  entails_owlrl G (sconcl s).
Proof.
  intros G known s Hk Hchk I HRL HLC HG.
  unfold check_step_weak in Hchk.
  destruct (nth_error_N builtin (sidx s)) as [r|] eqn:Hr; [|discriminate].
  destruct (ainsts (sbind s) (rbody r)) as [prems|] eqn:Hprems; [|discriminate].
  destruct (ainst (sbind s) (rhead r)) as [hd|] eqn:Hhd; [|discriminate].
  apply andb_prop in Hchk as [Hconcl Hmem].
  apply triple_eqb_true in Hconcl. subst hd.
  apply ainsts_agrees in Hprems.
  apply ainst_agrees in Hhd.
  rewrite <- Hhd.
  apply (builtin_sound I HRL r (nth_error_N_In _ _ _ Hr)).
  intros a Ha.
  assert (Hin : In (inst (subst_of (sbind s)) a) prems).
  { rewrite <- Hprems. now apply in_map. }
  rewrite forallb_forall in Hmem.
  specialize (Hmem _ Hin).
  apply mem_triple_In in Hmem.
  exact (Hk _ Hmem I HRL HLC HG).
Qed.

(** ** The combined certificate: Horn rows and list rules in one run *)

Inductive ostep : Set :=
| OHorn : step -> ostep
| OList : lstep -> ostep.

Definition oconcl (s : ostep) : triple :=
  match s with OHorn h => sconcl h | OList l => lconcl l end.

Definition check_ostep (G known : list triple) (s : ostep) : bool :=
  match s with
  | OHorn h => check_step_weak known builtin h
  | OList l => check_lstep G known l
  end.

Fixpoint check_ofrom (G known : list triple) (ss : list ostep) : bool :=
  match ss with
  | [] => true
  | s :: rest => check_ostep G known s && check_ofrom G (known ++ [oconcl s]) rest
  end.

Definition check_ocert (G : list triple) (ss : list ostep) : bool :=
  check_ofrom G G ss.

Lemma check_ostep_sound : forall G known s,
  (forall t, In t known -> entails_owlrl G t) ->
  check_ostep G known s = true ->
  entails_owlrl G (oconcl s).
Proof.
  intros G known [h|l] Hk Hchk.
  - apply (check_hstep_owlrl G known h Hk). exact Hchk.
  - apply (check_lstep_sound G known l Hk). exact Hchk.
Qed.

Lemma check_ofrom_sound : forall G ss known,
  (forall t, In t known -> entails_owlrl G t) ->
  check_ofrom G known ss = true ->
  forall t, In t (map oconcl ss) -> entails_owlrl G t.
Proof.
  intros G ss. induction ss as [|s rest IH]; intros known Hk Hchk t Hin.
  - simpl in Hin. contradiction.
  - simpl in Hchk. apply andb_prop in Hchk as [Hstep Hrest].
    apply check_ostep_sound in Hstep; [|exact Hk].
    simpl in Hin. destruct Hin as [<-|Hin].
    + exact Hstep.
    + apply (IH (known ++ [oconcl s])); [|exact Hrest|exact Hin].
      intros u Hu. apply in_app_or in Hu as [Hu|Hu].
      * now apply Hk.
      * destruct Hu as [<-|[]]. exact Hstep.
Qed.

(** ** THE ABSOLUTE THEOREM for the whole OWL-RL rule set *)

Theorem owl_rl_certificate_sound : forall G ss,
  check_ocert G ss = true ->
  forall t, In t (map oconcl ss) -> entails_owlrl G t.
Proof.
  intros G ss Hchk t Hin.
  apply (check_ofrom_sound G ss G); [|exact Hchk|exact Hin].
  intros u Hu I HRL HLC HG. exact (HG u Hu).
Qed.

(** ** Non-vacuity: the checker rejects a cls-int1 certificate missing a member
      type, and accepts the same certificate with it. This is the (d) fixture
      from `eye/run_tests.sh`, at the kernel level. *)

Definition c_int := owl_intersectionOf.

Definition dG : list triple :=
  [ Tri "c" c_int "l" ;
    Tri "l" rdf_first "A" ;
    Tri "l" rdf_rest "l2" ;
    Tri "l2" rdf_first "B" ;
    Tri "l2" rdf_rest rdf_nil ;
    Tri "x" rdf_type "A" ;
    Tri "x" rdf_type "B" ].

Definition dchain : list triple :=
  [ Tri "l" rdf_first "A" ; Tri "l" rdf_rest "l2" ;
    Tri "l2" rdf_first "B" ; Tri "l2" rdf_rest rdf_nil ].

Definition dgood : lstep :=
  LStep LInt1 (Tri "c" c_int "l" :: dchain ++ [ Tri "x" rdf_type "A" ; Tri "x" rdf_type "B" ])
        (Tri "x" rdf_type "c").

Definition dbad : lstep :=
  LStep LInt1 (Tri "c" c_int "l" :: dchain ++ [ Tri "x" rdf_type "A" ])
        (Tri "x" rdf_type "c").

Theorem cls_int1_with_every_member_typed_is_accepted :
  check_lcert dG [dgood] = true.
Proof. vm_compute. reflexivity. Qed.

Theorem cls_int1_missing_a_member_type_is_rejected :
  check_lcert dG [dbad] = false.
Proof. vm_compute. reflexivity. Qed.
