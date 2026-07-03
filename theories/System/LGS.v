Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Strings.String.
Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Monad.
Require Import PnV.Data.FiniteMap.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.Graph.
Require Import PnV.System.Regex.
Require Import PnV.Prelude.X.

Import DoNotations.

#[local] Hint Rewrite andb_true_iff : simplication_hints.
#[local] Hint Rewrite @eqb_spec@{Set} : simplication_hints.
#[local] Hint Rewrite @L.nodup_In : simplication_hints.
#[local] Hint Rewrite @L.in_map_iff : simplication_hints.
#[local] Hint Rewrite @L.in_app_iff : simplication_hints.

#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "=~=" := (is_similar_to (Similarity := Re.in_regex eq)) : type_scope.
#[local] Infix "∈" := L.In.
#[local] Infix "⊑" := is_similar_to.

#[local] Existing Instance Similarity_bool_Prop.

#[global]
Instance ascii_hasEqDec
  : hasEqDec@{Set} ascii.
Proof.
  exact Ascii.ascii_dec.
Defined.

#[global]
Instance regex_hasEqDec {A : Set}
  (A_hasEqDec : hasEqDec@{Set} A)
  : hasEqDec@{Set} (regex A).
Proof.
  red in A_hasEqDec |- *. decide equality.
Defined.

Abbreviation all_bools := Bool_FinEnum.all.

Abbreviation in_all_bools_intro := Bool_FinEnum.in_all_intro.

Module Ascii_FinEnum <: FINITE_ENUM.

Definition t : Set :=
  ascii.

Definition t_hasEqDec : hasEqDec@{Set} Ascii_FinEnum.t :=
  ascii_hasEqDec.

Definition all : list ascii := do
  'b0 <- all_bools;
  'b1 <- all_bools;
  'b2 <- all_bools;
  'b3 <- all_bools;
  'b4 <- all_bools;
  'b5 <- all_bools;
  'b6 <- all_bools;
  'b7 <- all_bools;
  ret (Ascii b0 b1 b2 b3 b4 b5 b6 b7).

Lemma in_all_intro
  : forall x : Ascii_FinEnum.t, L.In x Ascii_FinEnum.all.
Proof.
  unfold all; intros [b0 b1 b2 b3 b4 b5 b6 b7].
  eapply in_list_bind_intro with (x := b0); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b1); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b2); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b3); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b4); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b5); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b6); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b7); [eapply in_all_bools_intro | ].
  eapply in_list_pure_intro.
Qed.

Lemma all_no_dup
  : NoDup Ascii_FinEnum.all.
Proof.
  assert (EQ : L.nodup (@eq_dec@{Set} ascii ascii_hasEqDec) all = all) by reflexivity.
  rewrite <- EQ. eapply L.NoDup_nodup.
Qed.

End Ascii_FinEnum.

Abbreviation all_asciis := Ascii_FinEnum.all.

Abbreviation in_all_asciis_intro := Ascii_FinEnum.in_all_intro.

Module Type TOKEN_SPEC.

Parameter t : Set.

Parameter t_hasEqDec : hasEqDec@{Set} TOKEN_SPEC.t.

Parameter rules : list (TOKEN_SPEC.t * regex ascii).

End TOKEN_SPEC.

Module BuildError.

Inductive t : Set :=
  | NullableTokenRule (idx : nat).

End BuildError.

#[universes(polymorphic=yes)]
Definition BuildErrorM@{u | } (A : Type@{u}) : Type@{u} :=
  BuildError.t + A.

#[universes(polymorphic=yes)]
Instance BuildErrorM_isMonad@{u} : isMonad@{u u} BuildErrorM@{u} :=
  { pure {A : Type@{u}} (x : A) := inr x
  ; bind {A : Type@{u}} {B : Type@{u}} (m : BuildErrorM A) (k : A -> BuildErrorM B) := B.either (@inl BuildError.t B) k m
  }.

#[local] Hint Rewrite eqb_spec@{Set} : simplication_hints.
#[local] Hint Rewrite mem_spec : simplication_hints.
#[local] Hint Rewrite existsb_iff : simplication_hints.
#[local] Hint Rewrite forallb_iff : simplication_hints.
#[global] Hint Rewrite in_union_iff: simplication_hints.
#[global] Hint Rewrite in_normalize_iff : simplication_hints.
#[global] Hint Rewrite in_unions_iff : simplication_hints.
#[global] Hint Rewrite product_iff : simplication_hints.

#[local] Hint Rewrite L.filter_In : simplication_hints.

#[local] Existing Instance list_corresponds_to_finite_ensemble.
#[local] Existing Instance alist_corresponds_to_finite_partial_map.

Module MkLGS (Token : TOKEN_SPEC).

#[global] Existing Instance Token.t_hasEqDec.

Module Input.

Definition t : Set :=
  list ascii.

Fixpoint of_string (s : string) : Input.t :=
  match s with
  | EmptyString => []
  | String c s' => c :: of_string s'
  end.

Fixpoint to_string (s : Input.t) : string :=
  match s with
  | [] => EmptyString
  | c :: s' => String c (to_string s')
  end.

Theorem to_of_string (s : string)
  : to_string (of_string s) = s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Theorem of_to_string (s : Input.t)
  : of_string (to_string s) = s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Theorem length_of_string (s : string)
  : length (of_string s) = String.length s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Theorem to_string_app (s1 : Input.t) (s2 : Input.t)
  : to_string (s1 ++ s2) = String.append (to_string s1) (to_string s2).
Proof.
  induction s1 as [ | c s1 IH]; simpl; congruence.
Qed.

Theorem prefix_suffix_decompose (s : Input.t) (n : nat)
  (LE : n <= length s)
  : exists prefix, exists suffix, s = prefix ++ suffix /\ length prefix = n.
Proof.
  exists (firstn n s), (skipn n s). rewrite firstn_skipn. rewrite length_firstn. done.
Qed.

Theorem app_cancel_prefix (prefix : Input.t) (s1 : Input.t) (s2 : Input.t)
  (EQ : prefix ++ s1 = prefix ++ s2)
  : s1 = s2.
Proof.
  eapply L.app_cancel_l. exact EQ.
Qed.

Theorem app_cancel_suffix (s1 : Input.t) (s2 : Input.t) (suffix : Input.t)
  (EQ : s1 ++ suffix = s2 ++ suffix)
  : s1 = s2.
Proof.
  eapply L.app_cancel_r. exact EQ.
Qed.

Theorem empty_or_nonempty (s : Input.t)
  : { s = [] } + { exists c, exists s', s = c :: s' }.
Proof.
  destruct s as [ | c s']; [left; reflexivity | right; exists c, s'; reflexivity].
Defined.

Theorem nonempty_prefix_rest_shorter (consumed : Input.t) (rest : Input.t)
  (NONEMPTY : consumed ≠ [])
  : length rest < length (consumed ++ rest).
Proof.
  destruct consumed as [ | c consumed]; done.
Qed.

End Input.

Fixpoint nullable (e : regex ascii) {struct e} : bool :=
  match e with
  | Re.Null => false
  | Re.Empty => true
  | Re.Char c => false
  | Re.Union e1 e2 => nullable e1 || nullable e2
  | Re.Append e1 e2 => nullable e1 && nullable e2
  | Re.Star e1 => true
  end.

Lemma nullable_similar_spec (e : regex ascii)
  : nullable e = true <-> [] =~= e.
Proof.
  split.
  - induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; simpl; i; try congruence.
    + econs.
    + rewrite orb_true_iff in H. destruct H as [H | H]; eauto with *.
    + rewrite andb_true_iff in H. destruct H as [H1 H2].
      change (@nil ascii) with (@nil ascii ++ @nil ascii); eauto with *.
    + econs.
  - revert e.
    enough (CLAIM : forall s, forall e, s =~= e -> s = [] -> nullable e = true).
    { i. eapply CLAIM; eauto. }
    intros s e H_IN; induction H_IN; simpl; i; subst; try congruence.
    + rewrite orb_true_iff. left. eauto.
    + rewrite orb_true_iff. right. eauto.
    + pose proof (app_eq_nil _ _ H) as [EQ1 EQ2]. done.
Qed.

Theorem nullable_true_iff (e : regex ascii)
  : nullable e = true <-> [] \in eval_regex e.
Proof.
  rewrite eval_regex_good. eapply nullable_similar_spec.
Qed.

Theorem nullable_false_iff (e : regex ascii)
  : nullable e = false <-> (~ [] \in eval_regex e).
Proof.
  destruct (nullable _) eqn: EQ; split; intros H.
  - congruence.
  - contradiction H. rewrite <- nullable_true_iff. exact EQ.
  - intros IN. rewrite <- nullable_true_iff in IN. congruence.
  - reflexivity.
Qed.

Corollary nullable_refines (e : regex ascii)
  : nullable e ⊑ ([] \in eval_regex e).
Proof.
  destruct (nullable _) as [ | ] eqn: H_OBS.
  - now rewrite nullable_true_iff in H_OBS.
  - now rewrite nullable_false_iff in H_OBS.
Qed.

Lemma union_inv (s : Input.t) (e1 : regex ascii) (e2 : regex ascii)
  (IN : s \in eval_regex (Re.Union e1 e2))
  : s \in eval_regex e1 \/ s \in eval_regex e2.
Proof.
  ss!.
Qed.

Theorem append_inv (s : Input.t) (e1 : regex ascii) (e2 : regex ascii)
  (IN : s \in eval_regex (Re.Append e1 e2))
  : exists s1, exists s2, s = s1 ++ s2 /\ s1 \in eval_regex e1 /\ s2 \in eval_regex e2.
Proof.
  ss!.
Qed.

Lemma star_nil (e : regex ascii)
  : [] \in eval_regex (Re.Star e).
Proof.
  ss!.
Qed.

Lemma star_inv (s : Input.t) (e : regex ascii)
  (IN : s \in eval_regex (Re.Star e))
  : s = [] \/ (exists s1, exists s2, s = s1 ++ s2 /\ s1 \in eval_regex e /\ s2 \in eval_regex (Re.Star e)).
Proof.
  simpl in IN; inv IN; ss!.
Qed.

Module Rule.

#[projections(primitive)]
Record t : Set :=
  mk
  { index : nat
  ; token : Token.t
  ; regex : Re.t ascii
  } as rule.

#[global]
Instance Rule_hasEqDec
  : hasEqDec@{Set} Rule.t.
Proof.
  red; decide equality; eapply eq_dec.
Defined.

Definition compileRule (rule : Rule.t) : BuildErrorM@{Set} Rule.t :=
  if nullable rule.(Rule.regex) then
    inl (BuildError.NullableTokenRule rule.(Rule.index))
  else
    pure rule.

Lemma compileRule_preserves (rule : Rule.t) (rule' : Rule.t)
  (COMPILE : compileRule rule = inr rule')
  : rule = rule'.
Proof.
  unfold compileRule in COMPILE. now destruct (nullable _); inv COMPILE.
Qed.

Theorem compileRule_spec (rule : Rule.t) (rule' : Rule.t)
  (COMPILE : compileRule rule = inr rule')
  : forall s, s \in eval_regex rule.(Rule.regex) <-> s \in eval_regex rule'.(Rule.regex).
Proof.
  now i; rewrite compileRule_preserves with (rule := rule) (rule' := rule').
Qed.

Lemma compileRule_guarantees_consumption (rule : Rule.t) (rule' : Rule.t)
  (COMPILE : compileRule rule = inr rule')
  : ~ ([] \in eval_regex rule'.(Rule.regex)).
Proof.
  rewrite <- nullable_false_iff. now unfold compileRule in COMPILE; destruct (nullable _) eqn: NULLABLE; inv COMPILE.
Qed.

Fixpoint compileRules (rules : list Rule.t) {struct rules} : BuildErrorM (list Rule.t) :=
  match rules with
  | [] => pure (@nil Rule.t)
  | rule :: rules => liftM2 (@cons Rule.t) (compileRule rule) (compileRules rules)
  end.

Theorem compileRules_preserves (rules : list Rule.t) (rules' : list Rule.t)
  (COMPILE : compileRules rules = inr rules')
  : rules = rules'.
Proof.
  revert rules' COMPILE; induction rules as [ | rule rules IH]; ii; simpl in *; try congruence.
  destruct (compileRule _) as [err | rule1] eqn: H_OBS1; simpl in *; try congruence.
  destruct (compileRules _) as [err | rules2] eqn: H_OBS2; simpl in *; try congruence.
  rewrite compileRule_preserves with (rule := rule) (rule' := rule1) by eauto.
  inv COMPILE. f_equal. now eapply IH.
Qed.

Definition accepts (rule : Rule.t) (s : Input.t) : Prop :=
  s \in eval_regex rule.(Rule.regex).

Theorem compileRules_success_intro (rules : list Rule.t)
  (NOT_NULLABLE : forall rule, rule ∈ rules -> nullable rule.(Rule.regex) = false)
  : compileRules rules = inr rules.
Proof.
  induction rules as [ | rule rules IH]; simpl; eauto.
  unfold compileRule at 1. rewrite NOT_NULLABLE by now left.
  cbn. now rewrite IH by ss!.
Qed.

Theorem compileRules_success_elim (rules : list Rule.t) (rules' : list Rule.t) (rule : Rule.t)
  (COMPILE : compileRules rules = inr rules')
  (IN : rule ∈ rules')
  : rule ∈ rules /\ (~ accepts rule []).
Proof.
  revert rules' COMPILE rule IN; induction rules as [ | rule rules IH]; intros rules' COMPILE rule0 IN; simpl in COMPILE.
  - now inv COMPILE. 
  - destruct (compileRule _) as [err | rule'] eqn: COMPILE_RULE; cbn in COMPILE; try congruence.
    destruct (compileRules _) as [err | rules0] eqn: COMPILE_RULES; cbn in COMPILE; try congruence.
    inv COMPILE. simpl in IN. destruct IN as [EQ | IN]; subst.
    + pose proof (compileRule_preserves rule rule0 COMPILE_RULE) as EQ; subst rule0.
      split; eauto with *. eapply compileRule_guarantees_consumption. exact COMPILE_RULE.
    + pose proof (IH rules0 eq_refl rule0 IN) as [IN_RULES NONEMPTY]; ss!.
Qed.

Theorem compile_rules_failure_intro (rules : list Rule.t)
  (NULLABLE : exists rule, rule ∈ rules /\ nullable rule.(Rule.regex) = true)
  : exists idx, compileRules rules = inl (BuildError.NullableTokenRule idx).
Proof.
  induction rules as [ | rule rules IH].
  - now destruct NULLABLE as (rule & IN & _).
  - destruct NULLABLE as (bad_rule & [EQ | IN_RULES] & NULLABLE); subst; simpl.
    + unfold compileRule at 1. rewrite NULLABLE. ss!.
    + destruct (compileRule _) as [[idx] | rule'] eqn: COMPILE_RULE; cbn; eauto.
      pose proof (IH (@ex_intro _ _ bad_rule (conj IN_RULES NULLABLE))) as (idx & FAILURE).
      rewrite FAILURE. ss!.
Qed.

Theorem compileRules_failure_elim (rules : list Rule.t) (err : BuildError.t)
  (COMPILE : compileRules rules = inl err)
  : exists rule, rule ∈ rules /\ nullable rule.(Rule.regex) = true /\ err = BuildError.NullableTokenRule rule.(Rule.index).
Proof.
  revert err COMPILE; induction rules as [ | rule rules IH]; ii; simpl in COMPILE; try congruence.
  destruct (compileRule _) as [err' | rule'] eqn: COMPILE_RULE; cbn in COMPILE.
  - inv COMPILE. unfold compileRule in COMPILE_RULE.
    destruct (nullable _) eqn: NULLABLE; inv COMPILE_RULE; ss!.
  - destruct (compileRules _) as [err' | rules'] eqn: COMPILE_RULES; cbn in COMPILE; try congruence.
    inv COMPILE. pose proof (IH err eq_refl) as (? & IN_RULES & NULLABLE & ERR); ss!.
Qed.

Definition raws : list Rule.t :=
  L.mapi_from 1 (fun index => fun '(token, regex) => {| index := index; token := token; regex := regex |}) Token.rules.

Definition compileds : BuildErrorM@{Set} (list Rule.t) :=
  compileRules raws.

End Rule.

Module TaggedENFA.

#[projections(primitive)]
Record t : Type :=
  mk
  { state : Set
  ; state_hasEqDec : hasEqDec@{Set} state
  ; states : fin_ensemble state
  ; start_state : state
  ; accept_states : alist state Token.t
  ; eps_step (q : state) : fin_ensemble state
  ; char_step (q : state) (c : ascii) : fin_ensemble state
  } as M.

#[global] Existing Instance state_hasEqDec.

Variant okay (M : TaggedENFA.t) : Prop :=
  | okay_intro
    (start_okay : M.(TaggedENFA.start_state) ∈ M.(TaggedENFA.states))
    (accept_states_okay : forall q, forall tag, (q, tag) ∈ M.(TaggedENFA.accept_states).(kvlist) -> q ∈ M.(TaggedENFA.states))
    (eps_step_okay : forall q, forall q', q ∈ M.(TaggedENFA.states) -> q' ∈ M.(TaggedENFA.eps_step) q -> q' ∈ M.(TaggedENFA.states))
    (char_step_okay : forall q, forall q', forall c, q ∈ M.(TaggedENFA.states) -> q' ∈ M.(TaggedENFA.char_step) q c -> q' ∈ M.(TaggedENFA.states)).

Section TRANSITION.

Context {Q : Type}.

Variable eps_step : Q -> list Q.

Inductive eclosure (q : Q) : ensemble Q :=
  | eclosure_refl
    : q \in eclosure q
  | eclosure_step q1 q2
    (STEP : q1 ∈ eps_step q)
    (REST : q2 \in eclosure q1)
    : q2 \in eclosure q.

#[local] Hint Constructors eclosure : core.

Lemma eclosure_trans (q1 : Q) (q2 : Q) (q3 : Q)
  (H1_eclosure : q2 \in eclosure q1)
  (H2_eclosure : q3 \in eclosure q2)
  : q3 \in eclosure q1.
Proof.
  induction H1_eclosure as [q | q q1' q2' STEP REST IH]; simpl; eauto with *.
Qed.

Variable char_step : Q -> ascii -> list Q.

Inductive delta_star (q : Q) : Input.t -> ensemble Q :=
  | delta_star_nil
    : q \in delta_star q []
  | delta_star_eps q1 q2 s
    (STEP : q1 ∈ eps_step q)
    (REST : q2 \in delta_star q1 s)
    : q2 \in delta_star q s
  | delta_star_char q1 q2 c s
    (STEP : q1 ∈ char_step q c)
    (REST : q2 \in delta_star q1 s)
    : q2 \in delta_star q (c :: s).

#[local] Hint Constructors delta_star : core.

Lemma delta_star_app (q1 : Q) (q2 : Q) (q3 : Q) (s1 : Input.t) (s2 : Input.t)
  (H1_delta_star : q2 \in delta_star q1 s1)
  (H2_delta_star : q3 \in delta_star q2 s2)
  : q3 \in delta_star q1 (s1 ++ s2).
Proof.
  induction H1_delta_star as [q | q q1' q2' s STEP REST IH | q q1' q2' c s STEP REST IH]; simpl; eauto with *.
Qed.

Lemma delta_star_nil_iff_eclosure (q : Q) (q' : Q)
  : q' \in delta_star q [] <-> q' \in eclosure q.
Proof.
  split; [intros H_delta_star | intros H_eclosure].
  - remember (@nil ascii) as s eqn: EQ; induction H_delta_star; inv EQ; simpl; eauto with *.
  - induction H_eclosure as [q | q q1' q2' STEP REST IH]; simpl; eauto with *.
Qed.

Lemma delta_star_elim (q1 : Q) (q3 : Q) (s : Input.t)
  (H_delta_star : q3 \in delta_star q1 s)
  : ⟪ DELTA_STAR_NIL : s = [] /\ q3 = q1 ⟫ \/ ⟪ DELTA_STAR_EPS : exists q2, q2 ∈ eps_step q1 /\ q3 \in delta_star q2 s ⟫ \/ ⟪ DELTA_STAR_CHAR : exists c, exists s', exists q2, s = c :: s' /\ q2 ∈ char_step q1 c /\ q3 \in delta_star q2 s' ⟫.
Proof.
  unnw; destruct H_delta_star as [ | q1' q2' s' STEP REST | q1' q2' c s' STEP REST]; [left | right; left | right; right]; done!.
Qed.

Lemma delta_star_stuck (q1 : Q) (q2 : Q) (s : Input.t)
  (NO_EPS : forall q, ~ (q ∈ eps_step q1))
  (NO_CHAR : forall c, forall q, ~ (q ∈ char_step q1 c))
  (H_delta_star : q2 \in delta_star q1 s)
  : s = [] /\ q2 = q1.
Proof.
  inv H_delta_star; ss!.
Qed.

End TRANSITION.

#[local] Hint Constructors eclosure : core.
#[local] Hint Constructors delta_star : core.

Section BASICS.

Variable M : TaggedENFA.t.

#[local] Abbreviation Q := M.(TaggedENFA.state).
#[local] Abbreviation eclosure := (eclosure M.(TaggedENFA.eps_step)).
#[local] Abbreviation delta_star := (delta_star M.(TaggedENFA.eps_step) M.(TaggedENFA.char_step)).

Lemma eclosure_okay (q1 : Q) (q2 : Q)
  (OKAY : TaggedENFA.okay M)
  (IN : q1 ∈ M.(TaggedENFA.states))
  (H_eclosure : q2 \in eclosure q1)
  : q2 ∈ M.(TaggedENFA.states).
Proof.
  destruct OKAY as [_ _ ? _]; induction H_eclosure as [q | q q1' q2' STEP REST IH]; simpl; eauto with *.
Qed.

Lemma delta_star_okay (q1 : Q) (q2 : Q) (s : Input.t)
  (OKAY : TaggedENFA.okay M)
  (IN : q1 ∈ M.(TaggedENFA.states))
  (H_delta_star : q2 \in delta_star q1 s)
  : q2 ∈ M.(TaggedENFA.states).
Proof.
  destruct OKAY as [_ _ ? ?]; induction H_delta_star as [q | q q1' q2' s STEP REST IH | q q1' q2' c s STEP REST IH]; simpl; eauto with *.
Qed.

Definition accepts (s : Input.t) (tag : Token.t) : Prop :=
  exists qf, qf \in delta_star M.(TaggedENFA.start_state) s /\ (qf, tag) ∈ M.(TaggedENFA.accept_states).(kvlist).

Definition accepted_tags (s : Input.t) : ensemble Token.t :=
  fun tag => accepts s tag.

End BASICS.

Section Thompson's_construction.

#[projections(primitive)]
Record char_edge : Set :=
  mkCharEdge
  { char_edge_src : nat
  ; char_edge_label : ascii
  ; char_edge_dst : nat
  } as edge.

Lemma char_edge_eq_intro (edge : char_edge) (edge' : char_edge)
  (src_eq : edge.(char_edge_src) = edge'.(char_edge_src))
  (label_eq : edge.(char_edge_label) = edge'.(char_edge_label))
  (dst_eq : edge.(char_edge_dst) = edge'.(char_edge_dst))
  : edge = edge'.
Proof.
  now assert ({| char_edge_src := edge.(char_edge_src); char_edge_label := edge.(char_edge_label); char_edge_dst := edge.(char_edge_dst) |} = {| char_edge_src := edge'.(char_edge_src); char_edge_label := edge'.(char_edge_label); char_edge_dst := edge'.(char_edge_dst) |}) by congruence.
Qed.

#[local] Hint Extern 0 (@eq char_edge _ _) => eapply char_edge_eq_intro : core.

#[projections(primitive)]
Record fragment : Set :=
  mkFragment
  { frag_start : nat
  ; frag_accept : nat
  ; frag_eps_edges : list (nat * nat)
  ; frag_char_edges : list char_edge
  } as frag.

Fixpoint regex2fragment (e : regex ascii) (qi : nat) {struct e} : nat * fragment :=
  match e with
  | Re.Null =>
    let qf := qi + 1 in
    (qf, mkFragment qi qf [] [])
  | Re.Empty =>
    let qf := qi + 1 in
    (qf, mkFragment qi qf [(qi, qf)] [])
  | Re.Char c =>
    let qf := qi + 1 in
    (qf, mkFragment qi qf [] [mkCharEdge qi c qf])
  | Re.Union e1 e2 =>
    let qi1 := qi + 1 in
    let '(qf1, frag1) := regex2fragment e1 qi1 in
    let qi2 := qf1 + 1 in
    let '(qf2, frag2) := regex2fragment e2 qi2 in
    let qf := qf2 + 1 in
    (qf, mkFragment qi qf ((qi, qi1) :: (qi, qi2) :: (qf1, qf) :: (qf2, qf) :: frag1.(frag_eps_edges) ++ frag2.(frag_eps_edges)) (frag1.(frag_char_edges) ++ frag2.(frag_char_edges)))
  | Re.Append e1 e2 =>
    let qi1 := qi + 1 in
    let '(qf1, frag1) := regex2fragment e1 qi1 in
    let qi2 := qf1 + 1 in
    let '(qf2, frag2) := regex2fragment e2 qi2 in
    let qf := qf2 + 1 in
    (qf, mkFragment qi qf ((qi, qi1) :: (qf1, qi2) :: (qf2, qf) :: frag1.(frag_eps_edges) ++ frag2.(frag_eps_edges)) (frag1.(frag_char_edges) ++ frag2.(frag_char_edges)))
  | Re.Star e1 =>
    let qi1 := qi + 1 in
    let '(qf1, frag1) := regex2fragment e1 qi1 in
    let qf := qf1 + 1 in
    (qf, mkFragment qi qf ((qi, qi1) :: (qf1, qi1) :: (qi1, qf) :: frag1.(frag_eps_edges)) frag1.(frag_char_edges))
  end.

Fixpoint rules2fragments (qi : nat) (rules : list Rule.t) {struct rules} : nat * list (Rule.t * fragment) :=
  match rules with
  | [] => (qi, [])
  | rule :: rules' =>
    let '(qf, frag) := regex2fragment rule.(Rule.regex) qi in
    let '(qmax, frags) := rules2fragments (qf + 1) rules' in
    (qmax, (rule, frag) :: frags)
  end.

Fixpoint eps_step_from_edges (edges : list (nat * nat)) (q : nat) {struct edges} : list nat :=
  match edges with
  | [] => []
  | (src, dst) :: edges' =>
    if eq_dec@{Set} q src then
      dst :: eps_step_from_edges edges' q
    else
      eps_step_from_edges edges' q
  end.

Fixpoint char_step_from_edges (edges : list char_edge) (q : nat) (c : ascii) {struct edges} : list nat :=
  match edges with
  | [] => []
  | edge :: edges' =>
    if eq_dec@{Set} q edge.(char_edge_src) then
      if eq_dec@{Set} c edge.(char_edge_label) then
        edge.(char_edge_dst) :: char_step_from_edges edges' q c
      else
        char_step_from_edges edges' q c
    else
      char_step_from_edges edges' q c
  end.

Fixpoint fragment_eps_edges (frags : list (Rule.t * fragment)) {struct frags} : list (nat * nat) :=
  match frags with
  | [] => []
  | (_, frag) :: frags' => (0, frag.(frag_start)) :: frag.(frag_eps_edges) ++ fragment_eps_edges frags'
  end.

Fixpoint fragment_char_edges (frags : list (Rule.t * fragment)) {struct frags} : list char_edge :=
  match frags with
  | [] => []
  | (_, frag) :: frags' => frag.(frag_char_edges) ++ fragment_char_edges frags'
  end.

Definition fragments2TaggedENFA (qmax : nat) (frags : list (Rule.t * fragment)) : TaggedENFA.t :=
  {|
    state := nat;
    state_hasEqDec := nat_hasEqDec;
    states := seq 0 qmax;
    start_state := 0;
    accept_states := {| kvlist := map (fun '(rule, frag) => (frag.(frag_accept), rule.(Rule.token))) frags |};
    eps_step := eps_step_from_edges (fragment_eps_edges frags);
    char_step := char_step_from_edges (fragment_char_edges frags);
  |}.

Definition mkUnitedTaggedENFA (rules : list Rule.t) : TaggedENFA.t :=
  let '(qmax, frags) := rules2fragments 1 rules in
  fragments2TaggedENFA qmax frags.

Lemma eps_step_from_edges_iff (q : nat) (q' : nat) (edges : list (nat * nat))
  : q' ∈ eps_step_from_edges edges q <-> (q, q') ∈ edges.
Proof.
  induction edges as [ | [src dst] edges IH]; simpl; eauto.
  des_ifs; simpl; rewrite IH; clear IH; done.
Qed.

#[local] Hint Rewrite eps_step_from_edges_iff : simplication_hints.

Lemma char_step_from_edges_iff (edge : char_edge) (edges : list char_edge)
  : edge.(char_edge_dst) ∈ char_step_from_edges edges edge.(char_edge_src) edge.(char_edge_label) <-> edge ∈ edges.
Proof.
  induction edges as [ | edge' edges IH]; simpl; eauto.
  des_ifs; simpl; rewrite IH; clear IH; done.
Qed.

#[local] Hint Rewrite char_step_from_edges_iff : simplication_hints.

Lemma q0_eps_qi_intro (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment)
  (IN : (rule, frag) ∈ frags)
  : (0, frag.(frag_start)) ∈ fragment_eps_edges frags.
Proof.
  revert rule IN; induction frags as [ | [rule' frag'] frags IH]; simpl; ii; eauto. des; ss!.
Qed.

Lemma qi_eps_qf_intro (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment) (q : nat) (q' : nat)
  (in_frags : (rule, frag) ∈ frags)
  (IN : (q, q') ∈ frag.(frag_eps_edges))
  : (q, q') ∈ fragment_eps_edges frags.
Proof.
  revert rule in_frags q q' IN; induction frags as [ | [rule' frag'] frags IH]; simpl; ii; eauto. des; ss!.
Qed.

Lemma qi_char_qf_intro (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment) (edge : char_edge)
  (in_frags : (rule, frag) ∈ frags)
  (IN : edge ∈ frag.(frag_char_edges))
  : edge ∈ fragment_char_edges frags.
Proof.
  revert rule in_frags edge IN; induction frags as [ | [rule' frag'] frags IH]; simpl; ii; eauto. des; ss!.
Qed.

Lemma qf_accept_intro (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment)
  (in_frags : (rule, frag) ∈ frags)
  : (frag.(frag_accept), rule.(Rule.token)) ∈ map (fun '(rule, frag) => (frag.(frag_accept), rule.(Rule.token))) frags.
Proof.
  revert rule frag in_frags; induction frags as [ | [rule' frag'] frags IH]; simpl; ii; eauto. ss!.
Qed.

Lemma in_eps_step_from_edges_iff (q : nat) (q' : nat) (edges : list (nat * nat))
  : q' ∈ eps_step_from_edges edges q <-> (q, q') ∈ edges.
Proof.
  revert q q'; induction edges as [ | [? ?] edges IH]; simpl; ii; eauto. des_ifs; done!.
Qed.

Lemma in_char_step_from_edges_iff (edge : char_edge) (edges : list char_edge)
  : edge.(char_edge_dst) ∈ char_step_from_edges edges edge.(char_edge_src) edge.(char_edge_label) <-> edge ∈ edges.
Proof.
  revert edge; induction edges as [ | ? edges IH]; simpl; ii; eauto. des_ifs; done!.
Qed.
Lemma eps_step_from_edges_complete (q : nat) (q' : nat) (edges : list (nat * nat))
  (IN : (q, q') ∈ edges)
  : q' ∈ eps_step_from_edges edges q.
Proof.
  ss!.
Qed.

Lemma eps_step_from_edges_sound (q : nat) (q' : nat) (edges : list (nat * nat))
  (IN : q' ∈ eps_step_from_edges edges q)
  : (q, q') ∈ edges.
Proof.
  ss!.
Qed.

Lemma char_step_from_edges_complete (edge : char_edge) (edges : list char_edge)
  (IN : edge ∈ edges)
  : edge.(char_edge_dst) ∈ char_step_from_edges edges edge.(char_edge_src) edge.(char_edge_label).
Proof.
  ss!.
Qed.

Lemma char_step_from_edges_sound (q : nat) (q' : nat) (c : ascii) (edges : list char_edge)
  (IN : q' ∈ char_step_from_edges edges q c)
  : exists edge, edge ∈ edges /\ edge.(char_edge_src) = q /\ edge.(char_edge_label) = c /\ edge.(char_edge_dst) = q'.
Proof.
  set {| char_edge_src := q; char_edge_label := c; char_edge_dst := q' |} as edge.
  change (edge.(char_edge_dst) ∈ char_step_from_edges edges edge.(char_edge_src) edge.(char_edge_label)) in IN.
  rewrite in_char_step_from_edges_iff in IN. done.
Qed.

Lemma fragment_eps_edges_start_complete (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment)
  (IN : (rule, frag) ∈ frags)
  : (0, frag.(frag_start)) ∈ fragment_eps_edges frags.
Proof.
  induction frags as [ | [rule' frag'] frags IH]; ss!.
Qed.

Lemma fragment_eps_edges_complete (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment) (q : nat) (q' : nat)
  (IN_FRAG : (rule, frag) ∈ frags)
  (IN_EDGE : (q, q') ∈ frag.(frag_eps_edges))
  : (q, q') ∈ fragment_eps_edges frags.
Proof.
  induction frags as [ | [rule' frag'] frags IH]; ss!.
Qed.

Lemma fragment_char_edges_complete (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment) (edge : char_edge)
  (IN_FRAG : (rule, frag) ∈ frags)
  (IN_EDGE : edge ∈ frag.(frag_char_edges))
  : edge ∈ fragment_char_edges frags.
Proof.
  induction frags as [ | [rule' frag'] frags IH]; ss!.
Qed.

Lemma fragment_accept_states_complete (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment)
  (IN_FRAG : (rule, frag) ∈ frags)
  : (frag.(frag_accept), rule.(Rule.token)) ∈ map (fun '(rule, frag) => (frag.(frag_accept), rule.(Rule.token))) frags.
Proof.
  ss!.
Qed.

Lemma fragment_accept_states_sound (frags : list (Rule.t * fragment)) q tag
  (IN : (q, tag) ∈ map (fun '(rule, frag) => (frag.(frag_accept), rule.(Rule.token))) frags)
  : exists rule, exists frag, (rule, frag) ∈ frags /\ q = frag.(frag_accept) /\ tag = rule.(Rule.token).
Proof.
  rewrite L.in_map_iff in IN. destruct IN as ([rule frag] & EQ & IN_FRAG); ss!.
Qed.

Variant TaggedENFA_COMPILED (M : TaggedENFA.t) rules qmax frags : Prop :=
  | TaggedENFA_COMPILED_INTRO
    (COMPILED_RULES : Rule.compileds = inr rules)
    (COMPILED_ENFA : M = mkUnitedTaggedENFA rules)
    (COMPILED_FRAGS : rules2fragments 1 rules = (qmax, frags)).

Variant TaggedENFA_FRAGMENTS (frags : list (Rule.t * fragment)) rule frag : Prop :=
  | TaggedENFA_FRAGMENTS_INTRO
    (IN1 : frag.(frag_start) ∈ eps_step_from_edges (fragment_eps_edges frags) 0)
    (IN2 : (frag.(frag_accept), rule.(Rule.token)) ∈ map (fun '(rule, frag) => (frag.(frag_accept), rule.(Rule.token))) frags)
    (EPS : forall q, forall q', (q, q') ∈ frag.(frag_eps_edges) -> q' ∈ eps_step_from_edges (fragment_eps_edges frags) q)
    (CHAR : forall edge, edge ∈ frag.(frag_char_edges) -> edge.(char_edge_dst) ∈ char_step_from_edges (fragment_char_edges frags) edge.(char_edge_src) edge.(char_edge_label)).

Theorem mkUnitedTaggedENFA_spec (M : TaggedENFA.t)
  (COMPILE : fmap mkUnitedTaggedENFA Rule.compileds = inr M)
  : exists rules, exists qmax, exists frags, TaggedENFA_COMPILED M rules qmax frags /\ ⟪ FRAGMENTS : forall rule, forall frag, (rule, frag) ∈ frags -> TaggedENFA_FRAGMENTS frags rule frag ⟫.
Proof.
  unnw. unfold fmap, mkFunctorFromMonad in COMPILE. simpl in COMPILE.
  destruct (Rule.compileds) as [err | rules] eqn: COMPILED; inv COMPILE.
  destruct (rules2fragments 1 rules) as [qmax frags] eqn: FRAGS.
  exists rules, qmax, frags. split.
  - econs; eauto.
  - ii; econs; ii.
    + rewrite eps_step_from_edges_iff. eapply q0_eps_qi_intro; eauto.
    + eapply qf_accept_intro; eauto.
    + rewrite eps_step_from_edges_iff. eapply qi_eps_qf_intro; eauto.
    + rewrite char_step_from_edges_iff. eapply qi_char_qf_intro; eauto.
Qed.

Definition fragments_delta_star (frags : list (Rule.t * fragment)) : nat -> Input.t -> ensemble nat :=
  delta_star (eps_step_from_edges (fragment_eps_edges frags)) (char_step_from_edges (fragment_char_edges frags)).

Definition fragment_delta_star (frag : fragment) : nat -> Input.t -> ensemble nat :=
  delta_star (eps_step_from_edges frag.(frag_eps_edges)) (char_step_from_edges frag.(frag_char_edges)).

Lemma TaggedENFA_FRAGMENTS_delta_star_step frags rule frag
  (FRAGMENTS : TaggedENFA_FRAGMENTS frags rule frag)
  : ⟪ EPS : forall q, forall q', (q, q') ∈ frag.(frag_eps_edges) -> q' \in fragments_delta_star frags q [] ⟫ /\ ⟪ CHAR : forall edge, edge ∈ frag.(frag_char_edges) -> edge.(char_edge_dst) \in fragments_delta_star frags edge.(char_edge_src) [edge.(char_edge_label)] ⟫.
Proof.
  destruct FRAGMENTS as [_ _ EPS CHAR]; unnw; split.
  - intros q q' IN. eapply delta_star_eps with (q1 := q'); eauto.
  - intros edge IN. eapply delta_star_char with (q1 := edge.(char_edge_dst)); eauto.
Qed.

Lemma regex2fragment_start_accept e qi qf frag
  (REGEX2FRAGMENT : regex2fragment e qi = (qf, frag))
  : frag.(frag_start) = qi /\ frag.(frag_accept) = qf.
Proof.
  revert qi qf frag REGEX2FRAGMENT; induction e; simpl in *; ii; des_ifs.
Qed.

Lemma regex2fragment_same_fragment e qi1 qf1 qi2 qf2 frag
  (REGEX1 : regex2fragment e qi1 = (qf1, frag))
  (REGEX2 : regex2fragment e qi2 = (qf2, frag))
  : qi1 = qi2 /\ qf1 = qf2.
Proof.
  pose proof (regex2fragment_start_accept _ _ _ _ REGEX1) as [START1 ACCEPT1].
  pose proof (regex2fragment_start_accept _ _ _ _ REGEX2) as [START2 ACCEPT2].
  split; congruence.
Qed.

Variant FRAGMENT_BOUNDS (lo : nat) (hi : nat) (frag : fragment) : Prop :=
  | FRAGMENT_BOUNDS_INTRO
    (BOUNDS_START : frag.(frag_start) = lo)
    (BOUNDS_ACCEPT : frag.(frag_accept) = hi)
    (BOUNDS_LT : lo < hi)
    (BOUNDS_EPS : forall q, forall q', (q, q') ∈ frag.(frag_eps_edges) -> (lo <= q <= hi /\ lo <= q' <= hi)%nat)
    (BOUNDS_CHAR : forall edge, edge ∈ frag.(frag_char_edges) -> (lo <= edge.(char_edge_src) <= hi /\ lo <= edge.(char_edge_dst) <= hi)%nat).

Theorem regex2fragment_bounds e qi qf frag
  (REGEX2FRAGMENT : regex2fragment e qi = (qf, frag))
  : FRAGMENT_BOUNDS qi qf frag.
Proof.
  revert qi qf frag REGEX2FRAGMENT; induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; simpl in *; ii.
  - inv REGEX2FRAGMENT. econs; simpl; try lia.
  - inv REGEX2FRAGMENT. econs; simpl; try lia; intros q q' [EQ | []]; done.
  - inv REGEX2FRAGMENT. econs; simpl; try lia; intros edge [EQ | IN]; done.
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    pose proof (IH1 _ _ _ REGEX1) as [START1 ACCEPT1 LT1 EPS1 CHAR1].
    pose proof (IH2 _ _ _ REGEX2) as [START2 ACCEPT2 LT2 EPS2 CHAR2].
    inv REGEX2FRAGMENT. econs; simpl; try lia; ii; s!; des; subst; done.
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    pose proof (IH1 _ _ _ REGEX1) as [START1 ACCEPT1 LT1 EPS1 CHAR1].
    pose proof (IH2 _ _ _ REGEX2) as [START2 ACCEPT2 LT2 EPS2 CHAR2].
    inv REGEX2FRAGMENT. econs; simpl; try lia; ii; s!; des; subst; done.
  - destruct (regex2fragment e (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    pose proof (IH _ _ _ REGEX1) as [START1 ACCEPT1 LT1 EPS1 CHAR1].
    inv REGEX2FRAGMENT. econs; simpl; try lia; ii; s!; des; subst; done.
Qed.

Lemma regex2fragment_edge_src_lt e qi qf frag
  (REGEX2FRAGMENT : regex2fragment e qi = (qf, frag))
  : (forall q, forall q', (q, q') ∈ frag.(frag_eps_edges) -> q < qf) /\ (forall edge, edge ∈ frag.(frag_char_edges) -> edge.(char_edge_src) < qf).
Proof.
  revert qi qf frag REGEX2FRAGMENT; induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; simpl in *; ii.
  - inv REGEX2FRAGMENT; simpl in *; split; ii; done.
  - inv REGEX2FRAGMENT; simpl in *; split; ii; done.
  - inv REGEX2FRAGMENT; simpl in *; split; ii; done.
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    pose proof (IH1 _ _ _ REGEX1) as [EPS1 CHAR1].
    pose proof (IH2 _ _ _ REGEX2) as [EPS2 CHAR2].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 _ _].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 _ _].
    inv REGEX2FRAGMENT; simpl in *; split; ii.
    + des; try (inv H; lia). rewrite in_app_iff in H. des; eauto; [pose proof (EPS1 _ _ H) | pose proof (EPS2 _ _ H)]; lia.
    + rewrite in_app_iff in H. des; eauto; [pose proof (CHAR1 _ H) | pose proof (CHAR2 _ H)]; lia.
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    pose proof (IH1 _ _ _ REGEX1) as [EPS1 CHAR1].
    pose proof (IH2 _ _ _ REGEX2) as [EPS2 CHAR2].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 _ _].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 _ _].
    inv REGEX2FRAGMENT; simpl in *; split; ii.
    + des; try (inv H; lia). rewrite in_app_iff in H. des; eauto; [pose proof (EPS1 _ _ H) | pose proof (EPS2 _ _ H)]; lia.
    + rewrite in_app_iff in H. des; eauto; [pose proof (CHAR1 _ H) | pose proof (CHAR2 _ H)]; lia.
  - destruct (regex2fragment e (qi + 1)) as [qf1 frag1] eqn: REGEX.
    pose proof (IH _ _ _ REGEX) as [EPS1 CHAR1].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT1 _ _].
    inv REGEX2FRAGMENT; simpl in *; split; ii.
    + des; try (inv H; lia). pose proof (EPS1 _ _ H). lia.
    + pose proof (CHAR1 _ H). lia.
Qed.

Lemma regex2fragment_edge_dst_gt e qi qf frag
  (REGEX2FRAGMENT : regex2fragment e qi = (qf, frag))
  : (forall q, forall q', (q, q') ∈ frag.(frag_eps_edges) -> qi < q') /\ (forall edge, edge ∈ frag.(frag_char_edges) -> qi < edge.(char_edge_dst)).
Proof.
  revert qi qf frag REGEX2FRAGMENT; induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; simpl in *; ii.
  - inv REGEX2FRAGMENT; simpl in *; split; ii; done.
  - inv REGEX2FRAGMENT; simpl in *; split; ii; done.
  - inv REGEX2FRAGMENT; simpl in *; split; ii; done.
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    pose proof (IH1 _ _ _ REGEX1) as [EPS1 CHAR1].
    pose proof (IH2 _ _ _ REGEX2) as [EPS2 CHAR2].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 _ _].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 _ _].
    inv REGEX2FRAGMENT; simpl in *; split; ii.
    + des; try (inv H; lia). rewrite in_app_iff in H. des; [pose proof (EPS1 _ _ H) | pose proof (EPS2 _ _ H)]; lia.
    + rewrite in_app_iff in H. des; [pose proof (CHAR1 _ H) | pose proof (CHAR2 _ H)]; lia.
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    pose proof (IH1 _ _ _ REGEX1) as [EPS1 CHAR1].
    pose proof (IH2 _ _ _ REGEX2) as [EPS2 CHAR2].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 _ _].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 _ _].
    inv REGEX2FRAGMENT; simpl in *; split; ii.
    + des; try (inv H; lia). rewrite in_app_iff in H. des; [pose proof (EPS1 _ _ H) | pose proof (EPS2 _ _ H)]; lia.
    + rewrite in_app_iff in H. des; [pose proof (CHAR1 _ H) | pose proof (CHAR2 _ H)]; lia.
  - destruct (regex2fragment e (qi + 1)) as [qf1 frag1] eqn: REGEX.
    pose proof (IH _ _ _ REGEX) as [EPS1 CHAR1].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT1 _ _].
    inv REGEX2FRAGMENT; simpl in *; split; ii.
    + des; try (inv H; lia). pose proof (EPS1 _ _ H). lia.
    + pose proof (CHAR1 _ H). lia.
Qed.

Lemma regex2fragment_complete' (e : regex ascii) (s : Input.t) (frags : list (Rule.t * fragment)) (rule : Rule.t) (qi : nat) (qf : nat) (frag : fragment) (topfrag : fragment)
  (IN_REGEX : s \in eval_regex e)
  (REGEX2FRAGMENT : regex2fragment e qi = (qf, frag))
  (FRAGMENTS : TaggedENFA_FRAGMENTS frags rule topfrag)
  (EPS_INCL : forall q, forall q', (q, q') ∈ frag.(frag_eps_edges) -> (q, q') ∈ topfrag.(frag_eps_edges))
  (CHAR_INCL : forall edge, edge ∈ frag.(frag_char_edges) -> edge ∈ topfrag.(frag_char_edges))
  : frag.(frag_accept) \in fragments_delta_star frags frag.(frag_start) s.
Proof.
  revert s IN_REGEX frags rule qi qf frag topfrag REGEX2FRAGMENT FRAGMENTS EPS_INCL CHAR_INCL.
  induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; simpl; ii.
  - s!; tauto.
  - s!. des; subst.
    pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule topfrag FRAGMENTS) as [EPS _].
    eapply EPS. eapply EPS_INCL. s!; tauto.
  - s!. des; subst.
    pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule topfrag FRAGMENTS) as [_ CHAR].
    eapply CHAR with (edge := mkCharEdge qi c (qi + 1)). eapply CHAR_INCL. s!; tauto.
  - s!. cbn [eval_regex] in IN_REGEX.
    destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    inv REGEX2FRAGMENT. destruct IN_REGEX as [IN1 | IN2].
    + pose proof (TaggedENFA_FRAGMENTS_delta_star_step _ _ _ FRAGMENTS) as [EPS _].
      pose proof (regex2fragment_start_accept _ _ _ _ REGEX1) as [START1 ACCEPT1].
      rewrite <- app_nil_r with (l := s). eapply delta_star_app with (q2 := qf1).
      { change s with ([] ++ s). eapply delta_star_app with (q2 := qi + 1).
        - eapply EPS. eapply EPS_INCL. s!; tauto.
        - rewrite <- START1. rewrite <- ACCEPT1.
          eapply IH1 with (s := s) (frags := frags) (qi := qi + 1) (qf := qf1)  (topfrag := topfrag); eauto.
          + ii. eapply EPS_INCL. s!; tauto.
          + ii. eapply CHAR_INCL. s!; tauto.
      }
      { eapply EPS. eapply EPS_INCL. s!; tauto. }
    + pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule topfrag FRAGMENTS) as [EPS _].
      pose proof (regex2fragment_start_accept _ _ _ _ REGEX2) as [START2 ACCEPT2].
      rewrite <- app_nil_r with (l := s). eapply delta_star_app with (q2 := qf2).
      { change s with ([] ++ s). eapply delta_star_app with (q2 := qf1 + 1).
        - eapply EPS. eapply EPS_INCL. s!; tauto.
        - rewrite <- START2. rewrite <- ACCEPT2.
          eapply IH2 with (s := s) (qi := qf1 + 1) (qf := qf2) (frag := frag2) (topfrag := topfrag); eauto.
          + ii. eapply EPS_INCL. s!; tauto.
          + ii. eapply CHAR_INCL. s!; tauto.
      }
      { eapply EPS. eapply EPS_INCL. s!; tauto. }
  - s!. cbn [eval_regex] in IN_REGEX.
    destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    inv REGEX2FRAGMENT. destruct IN_REGEX as (s1 & IN1 & s2 & IN2 & EQ). subst s.
    pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule topfrag FRAGMENTS) as [EPS _].
    pose proof (regex2fragment_start_accept _ _ _ _ REGEX1) as [START1 ACCEPT1].
    pose proof (regex2fragment_start_accept _ _ _ _ REGEX2) as [START2 ACCEPT2].
    eapply delta_star_app with (q2 := qf1) (s1 := s1) (s2 := s2).
    { change s1 with ([] ++ s1). eapply delta_star_app with (q2 := qi + 1).
      - eapply EPS. eapply EPS_INCL. s!; tauto.
      - rewrite <- START1. rewrite <- ACCEPT1.
        eapply IH1 with (s := s1) (qi := qi + 1) (qf := qf1) (frag := frag1) (topfrag := topfrag); eauto.
        + ii. eapply EPS_INCL. s!; tauto.
        + ii. eapply CHAR_INCL. s!; tauto.
    }
    rewrite <- app_nil_r with (l := s2). eapply delta_star_app with (q2 := qf2).
    { change s2 with ([] ++ s2). eapply delta_star_app with (q2 := qf1 + 1).
      - eapply EPS. eapply EPS_INCL. s!; tauto.
      - rewrite <- START2. rewrite <- ACCEPT2.
        eapply IH2 with (s := s2) (qi := qf1 + 1) (qf := qf2) (frag := frag2) (topfrag := topfrag); eauto.
        + ii. eapply EPS_INCL. s!; tauto.
        + ii. eapply CHAR_INCL. s!; tauto.
    }
    { eapply EPS. eapply EPS_INCL. s!; tauto. }
  - destruct (regex2fragment e (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    inv REGEX2FRAGMENT.
    pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule topfrag FRAGMENTS) as [EPS _].
    pose proof (regex2fragment_start_accept _ _ _ _ REGEX1) as [START1 ACCEPT1].
    assert (claim1 : forall t, t \in star (eval_regex e) -> qf1 + 1 \in delta_star (eps_step_from_edges (fragment_eps_edges frags)) (char_step_from_edges (fragment_char_edges frags)) (qi + 1) t).
    { intros t STAR_IN. induction STAR_IN as [ | s1 s2 IN1 IN2 IHSTAR].
      - eapply EPS. eapply EPS_INCL. s!; tauto.
      - replace (s1 ++ s2) with ((s1 ++ []) ++ s2) by now rewrite app_nil_r.
        eapply delta_star_app with (q2 := qi + 1).
        + eapply delta_star_app with (q2 := qf1).
          * rewrite <- START1. rewrite <- ACCEPT1.
            eapply IH with (s := s1) (frags := frags) (qi := qi + 1) (qf := qf1) (frag := frag1) (topfrag := topfrag); done.
          * eapply EPS. eapply EPS_INCL. s!; tauto.
        + exact IHSTAR.
    }
    change s with ([] ++ s). eapply delta_star_app with (q2 := qi + 1); done.
Qed.

Theorem regex2fragment_complete frags rule qi qf frag s
  (REGEX2FRAGMENT : regex2fragment rule.(Rule.regex) qi = (qf, frag))
  (FRAGMENTS : TaggedENFA_FRAGMENTS frags rule frag)
  (IN_REGEX : s \in eval_regex rule.(Rule.regex))
  : frag.(frag_accept) \in fragments_delta_star frags frag.(frag_start) s.
Proof.
  eapply regex2fragment_complete'; eauto.
Qed.

Theorem TaggedENFA_FRAGMENTS_complete qmax frags rule qi qf frag s
  (REGEX2FRAGMENT : regex2fragment rule.(Rule.regex) qi = (qf, frag))
  (FRAGMENTS : TaggedENFA_FRAGMENTS frags rule frag)
  (IN_REGEX : s \in eval_regex rule.(Rule.regex))
  : accepts (fragments2TaggedENFA qmax frags) s rule.(Rule.token).
Proof.
  destruct FRAGMENTS as [START ACCEPT EPS CHAR]. exists frag.(frag_accept). split.
  - change s with ([] ++ s). eapply delta_star_app with (q2 := frag.(frag_start)).
    + eapply delta_star_eps with (q1 := frag.(frag_start)); done.
    + eapply regex2fragment_complete; done.
  - exact ACCEPT.
Qed.

Theorem rules2fragments_complete qi rules qmax frags rule
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_RULE : rule ∈ rules)
  : exists qi_rule, exists qf, exists frag, regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ (rule, frag) ∈ frags.
Proof.
  revert qi qmax frags FRAGS IN_RULE; induction rules as [ | rule' rules IH]; simpl in *; ii; try tauto.
  destruct (regex2fragment rule'.(Rule.regex) qi) as [qf frag] eqn: REGEX2FRAGMENT.
  destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
  s!; des; subst.
  - exists qi, qf, frag. done.
  - pose proof (IH (qf + 1) qmax frags' FRAGS' IN_RULE) as (qi_rule & qf_rule & frag_rule & REGEX & IN_FRAGS).
    exists qi_rule, qf_rule, frag_rule. done.
Qed.

Lemma rules2fragments_sound qi rules qmax frags rule frag
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  : rule ∈ rules.
Proof.
  revert qi qmax frags FRAGS IN_FRAG; induction rules as [ | rule' rules IH]; ii; simpl in FRAGS.
  - now inv FRAGS.
  - destruct (regex2fragment rule'.(Rule.regex) qi) as [qf frag'] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    s!; des; subst. simpl in IN_FRAG. des; done.
Qed.

Lemma rules2fragments_bounds qi rules qmax frags
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  : qi <= qmax /\ ⟪ BOUND : forall rule, forall frag, (rule, frag) ∈ frags -> (exists qi_rule, exists qf, regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ FRAGMENT_BOUNDS qi_rule qf frag /\ qi <= qi_rule /\ qf < qmax) ⟫.
Proof.
  revert qi qmax frags FRAGS.
  induction rules as [ | rule' rules IH]; intros qi qmax frags FRAGS; simpl in FRAGS.
  - inv FRAGS. done.
  - destruct (regex2fragment rule'.(Rule.regex) qi) as [qf frag] eqn: REGEX2FRAGMENT.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    injection FRAGS as Hqmax Hfrags. subst qmax frags.
    pose proof (regex2fragment_bounds _ _ _ _ REGEX2FRAGMENT) as BOUNDS.
    assert (LT : qi < qf) by now destruct BOUNDS as [_ _ LT _ _].
    pose proof (IH (qf + 1) qmax' frags' FRAGS') as [QMAX HH].
    split; [lia | intros rule frag' IN]. destruct IN as [EQ | IN].
    + inv EQ. exists qi, qf. done.
    + pose proof (HH rule frag' IN) as (qi_rule & qf_rule & REGEX & BOUNDS' & LE_START & LT_END). exists qi_rule, qf_rule. done.
Qed.

Lemma rules2fragments_ranges_disjoint qi rules qmax frags rule1 frag1 qi1 qf1 rule2 frag2 qi2 qf2 q
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN1 : (rule1, frag1) ∈ frags)
  (IN2 : (rule2, frag2) ∈ frags)
  (REGEX1 : regex2fragment rule1.(Rule.regex) qi1 = (qf1, frag1))
  (REGEX2 : regex2fragment rule2.(Rule.regex) qi2 = (qf2, frag2))
  (RANGE1 : qi1 <= q <= qf1)
  (RANGE2 : qi2 <= q <= qf2)
  : (rule1, frag1) = (rule2, frag2).
Proof.
  s!. revert qi qmax frags FRAGS rule1 frag1 qi1 qf1 rule2 frag2 qi2 qf2 q IN1 IN2 REGEX1 REGEX2 RANGE1 RANGE2.
  induction rules as [ | rule rules IH]; ii; simpl in FRAGS.
  - now inv FRAGS.
  - destruct (regex2fragment rule.(Rule.regex) qi) as [qf frag] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    s!; des; subst.
    pose proof (rules2fragments_bounds _ _ _ _ FRAGS') as [_ BOUNDS].
    simpl in *; des; s!; des; subst; eauto.
    + pose proof (regex2fragment_same_fragment _ _ _ _ _ _ REGEX1 REGEX) as [EQ_QI EQ_QF]. subst qi1 qf1.
      pose proof (BOUNDS _ _ IN2) as (qi2' & qf2' & REGEX2' & _ & LE2 & _).
      pose proof (regex2fragment_same_fragment _ _ _ _ _ _ REGEX2 REGEX2') as [EQ_QI EQ_QF]. subst qi2 qf2.
      lia.
    + pose proof (regex2fragment_same_fragment _ _ _ _ _ _ REGEX2 REGEX) as [EQ_QI EQ_QF]. subst qi2 qf2.
      pose proof (BOUNDS _ _ IN1) as (qi1' & qf1' & REGEX1' & _ & LE1 & _).
      pose proof (regex2fragment_same_fragment _ _ _ _ _ _ REGEX1 REGEX1') as [EQ_QI EQ_QF]. subst qi1 qf1.
      lia.
Qed.

Lemma fragment_eps_edges_owner qi rules qmax frags q q'
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_EDGE : (q, q') ∈ fragment_eps_edges frags)
  (SRC_NONZERO : q ≠ 0)
  : exists rule, exists frag, exists qi_rule, exists qf, (rule, frag) ∈ frags /\ regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ FRAGMENT_BOUNDS qi_rule qf frag /\ qi <= qi_rule /\ qf < qmax /\ qi_rule <= q <= qf /\ (q, q') ∈ frag.(frag_eps_edges).
Proof.
  revert qi qmax frags FRAGS IN_EDGE; induction rules as [ | rule rules IH]; ii; simpl in FRAGS.
  - now inv FRAGS.
  - destruct (regex2fragment rule.(Rule.regex) qi) as [qf frag] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    pose proof (rules2fragments_bounds _ _ _ _ FRAGS') as [QMAX _].
    s!; des; subst; simpl in *; des; subst; s!; des; subst.
    + contradiction.
    + pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT EPS _].
      exists rule, frag, qi, qf. pose proof (EPS _ _ IN_EDGE). simpl in *; splits; lia || eauto.
      eapply regex2fragment_bounds; eauto.
    + pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT _ _].
      pose proof (IH (qf + 1) qmax frags' FRAGS' IN_EDGE) as (rule' & frag' & qi_rule & qf' & IN_FRAG & REGEX' & BOUNDS & LE & LT' & RANGE & IN_EDGE').
      exists rule', frag', qi_rule, qf'. simpl in *; splits; lia || eauto.
Qed.

Lemma fragment_eps_edges_start_sound qi rules qmax frags q'
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (qi_POS : 0 < qi)
  (IN_EDGE : (0, q') ∈ fragment_eps_edges frags)
  : exists rule, exists frag, exists qi_rule, exists qf, (rule, frag) ∈ frags /\ regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ q' = frag.(frag_start).
Proof.
  revert qi qmax frags q' FRAGS qi_POS IN_EDGE; induction rules as [ | rule rules IH]; ii; simpl in FRAGS.
  - now inv FRAGS.
  - destruct (regex2fragment rule.(Rule.regex) qi) as [qf frag] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    s!; des; subst. simpl in IN_EDGE. s!; des.
    + exists rule, frag, qi, qf. splits; done.
    + pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ _ EPS _].
      pose proof (EPS _ _ IN_EDGE). done.
    + pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT _ _].
      assert (qi_POS' : 0 < qf + 1) by lia.
      pose proof (IH (qf + 1) qmax frags' q' FRAGS' qi_POS' IN_EDGE) as (rule' & frag' & qi_rule & qf' & IN_FRAG & REGEX' & START).
      exists rule', frag', qi_rule, qf'. done.
Qed.

Lemma fragment_char_edges_owner qi rules qmax frags edge
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_EDGE : edge ∈ fragment_char_edges frags)
  : exists rule, exists frag, exists qi_rule, exists qf, (rule, frag) ∈ frags /\ regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ FRAGMENT_BOUNDS qi_rule qf frag /\ qi <= qi_rule /\ qf < qmax /\ qi_rule <= edge.(char_edge_src) <= qf /\ edge ∈ frag.(frag_char_edges).
Proof.
  revert qi qmax frags FRAGS IN_EDGE.
  induction rules as [ | rule rules IH]; ii; simpl in FRAGS.
  - inv FRAGS. contradiction.
  - destruct (regex2fragment rule.(Rule.regex) qi) as [qf frag] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    injection FRAGS as Hqmax Hfrags. subst qmax frags.
    pose proof (rules2fragments_bounds _ _ _ _ FRAGS') as [QMAX _].
    simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (regex2fragment_bounds _ _ _ _ REGEX) as BOUNDS.
      destruct BOUNDS as [_ _ LT _ CHAR].
      pose proof (CHAR _ IN_EDGE). exists rule, frag, qi, qf. splits; simpl; lia || eauto.
      eapply regex2fragment_bounds; eauto.
    + pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT _ _].
      pose proof (IH (qf + 1) qmax' frags' FRAGS' IN_EDGE) as (rule' & frag' & qi_rule & qf' & IN_FRAG & REGEX' & BOUNDS & LE & LT' & RANGE & IN_EDGE').
      exists rule', frag', qi_rule, qf'. splits; simpl; lia || eauto.
Qed.

Lemma fragments2TaggedENFA_okay rules qmax frags
  (FRAGS : rules2fragments 1 rules = (qmax, frags))
  : TaggedENFA.okay (fragments2TaggedENFA qmax frags).
Proof.
  assert (QI_POS : 0 < 1) by lia.
  split; simpl.
  - pose proof (rules2fragments_bounds _ _ _ _ FRAGS) as [LE _].
    rewrite in_seq. lia.
  - intros q tag ACCEPT.
    pose proof (fragment_accept_states_sound _ _ _ ACCEPT) as (rule & frag & IN_FRAG & ACCEPT_EQ & TOKEN_EQ). subst q tag.
    pose proof (rules2fragments_bounds _ _ _ _ FRAGS) as [_ BOUND].
    pose proof (BOUND _ _ IN_FRAG) as (qi_rule & qf & REGEX & [_ ACCEPT_EQ _ _ _] & LE_START & LT_END). subst qf.
    rewrite in_seq. lia.
  - intros q q' IN_STATES STEP.
    pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    pose proof (Nat.eq_dec q 0) as [EQ | NE].
    + subst q.
      pose proof (fragment_eps_edges_start_sound _ _ _ _ _ FRAGS QI_POS IN_EDGE) as (rule & frag & qi_rule & qf & IN_FRAG & REGEX & START_EQ). subst q'.
      pose proof (rules2fragments_bounds _ _ _ _ FRAGS) as [_ BOUND].
      pose proof (BOUND _ _ IN_FRAG) as (qi_rule' & qf' & REGEX' & [START_EQ _ LT _ _] & LE_START & LT_END).
      pose proof (regex2fragment_same_fragment _ _ _ _ _ _ REGEX REGEX') as [EQ_QI EQ_QF]. subst.
      rewrite in_seq. lia.
    + pose proof (fragment_eps_edges_owner _ _ _ _ _ _ FRAGS IN_EDGE NE) as (rule & frag & qi_rule & qf & IN_FRAG & REGEX & [_ _ _ EPS _] & LE_START & LT_END & RANGE & IN_EDGE').
      pose proof (EPS _ _ IN_EDGE') as RANGE'.
      rewrite in_seq. lia.
  - intros q q' c IN_STATES STEP.
    pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST). subst q q' c.
    pose proof (fragment_char_edges_owner _ _ _ _ _ FRAGS IN_EDGE) as (rule & frag & qi_rule & qf & IN_FRAG & REGEX & [_ _ _ _ CHAR] & LE_START & LT_END & RANGE & IN_EDGE').
    pose proof (CHAR _ IN_EDGE') as RANGE'.
    rewrite in_seq. lia.
Qed.

Theorem mkUnitedTaggedENFA_okay rules
  : TaggedENFA.okay (mkUnitedTaggedENFA rules).
Proof.
  unfold mkUnitedTaggedENFA. destruct (rules2fragments 1 rules) as [qmax frags] eqn: FRAGS.
  eapply fragments2TaggedENFA_okay. exact FRAGS.
Qed.

Lemma fragment_eps_edges_isolate qi rules qmax frags rule frag qi_rule qf q q'
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  (SRC_NONZERO : q ≠ 0)
  (RANGE : qi_rule <= q <= qf)
  (IN_EDGE : (q, q') ∈ fragment_eps_edges frags)
  : (q, q') ∈ frag.(frag_eps_edges).
Proof.
  pose proof (fragment_eps_edges_owner _ _ _ _ _ _ FRAGS IN_EDGE SRC_NONZERO) as (rule' & frag' & qi_rule' & qf' & IN_FRAG' & REGEX' & _ & _ & _ & RANGE' & IN_EDGE').
  pose proof (rules2fragments_ranges_disjoint _ _ _ _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG IN_FRAG' REGEX REGEX' RANGE RANGE') as EQ.
  now inv EQ.
Qed.

Lemma fragment_char_edges_isolate qi rules qmax frags rule frag qi_rule qf edge
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  (RANGE : qi_rule <= edge.(char_edge_src) <= qf)
  (IN_EDGE : edge ∈ fragment_char_edges frags)
  : edge ∈ frag.(frag_char_edges).
Proof.
  pose proof (fragment_char_edges_owner _ _ _ _ _ FRAGS IN_EDGE) as (rule' & frag' & qi_rule' & qf' & IN_FRAG' & REGEX' & _ & _ & _ & RANGE' & IN_EDGE').
  pose proof (rules2fragments_ranges_disjoint _ _ _ _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG IN_FRAG' REGEX REGEX' RANGE RANGE') as EQ.
  now inv EQ.
Qed.

Lemma rules2fragments_start_ge qi rules qmax frags rule frag qi_rule qf
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  : qi <= qi_rule.
Proof.
  pose proof (rules2fragments_bounds _ _ _ _ FRAGS) as [_ BOUND].
  pose proof (BOUND _ _ IN_FRAG) as (qi_rule' & qf' & REGEX' & _ & LE & _).
  pose proof (regex2fragment_same_fragment _ _ _ _ _ _ REGEX REGEX') as [EQ _].
  now subst qi_rule'.
Qed.

Lemma delta_star_fragment_range qi rules qmax frags rule frag qi_rule qf q q' s
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  (qi_POS : 0 < qi)
  (RANGE : qi_rule <= q <= qf)
  (DELTA : q' \in fragments_delta_star frags q s)
  : qi_rule <= q' <= qf.
Proof.
  revert qi rules rule frag qi_rule qf FRAGS IN_FRAG REGEX qi_POS RANGE; induction DELTA; ii.
  - exact RANGE.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    assert (claim1 : q ≠ 0) by now pose proof (rules2fragments_start_ge _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX); lia.
    pose proof (fragment_eps_edges_isolate _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX claim1 RANGE IN_EDGE) as IN_FRAG_EDGE.
    pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ _ EPS _].
    pose proof (EPS _ _ IN_FRAG_EDGE).
    simpl in *. eapply IHDELTA; eauto. lia.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    assert (claim2 : qi_rule <= edge.(char_edge_src) <= qf) by lia.
    pose proof (fragment_char_edges_isolate _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX claim2 IN_EDGE) as IN_FRAG_EDGE.
    pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ _ _ CHAR].
    pose proof (CHAR _ IN_FRAG_EDGE).
    eapply IHDELTA; eauto. lia.
Qed.

Lemma delta_star_global_to_fragment qi rules qmax frags rule frag qi_rule qf q q' s
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  (qi_POS : 0 < qi)
  (RANGE : qi_rule <= q <= qf)
  (DELTA : q' \in fragments_delta_star frags q s)
  : q' \in fragment_delta_star frag q s.
Proof.
  revert qi rules rule frag qi_rule qf FRAGS IN_FRAG REGEX qi_POS RANGE; induction DELTA; ii.
  - econs.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    assert (SRC_NONZERO : ~ q = 0) by now pose proof (rules2fragments_start_ge _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX); lia.
    pose proof (fragment_eps_edges_isolate _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX SRC_NONZERO RANGE IN_EDGE) as IN_FRAG_EDGE.
    pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ _ EPS _].
    pose proof (EPS _ _ IN_FRAG_EDGE). 
    simpl in *. eapply delta_star_eps.
    + eapply eps_step_from_edges_complete. exact IN_FRAG_EDGE.
    + eapply IHDELTA; eauto. lia.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    assert (RANGE_SRC : qi_rule <= edge.(char_edge_src) <= qf) by lia.
    pose proof (fragment_char_edges_isolate _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX RANGE_SRC IN_EDGE) as IN_FRAG_EDGE.
    pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ _ _ CHAR].
    pose proof (CHAR _ IN_FRAG_EDGE).
    eapply delta_star_char with (q1 := edge.(char_edge_dst)).
    + rewrite <- SRC. rewrite <- LABEL. eapply char_step_from_edges_complete. exact IN_FRAG_EDGE.
    + rewrite DST. eapply IHDELTA; eauto. lia.
Qed.

Lemma regex2fragment_global_to_local qi rules qmax frags rule qf frag s
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) frag.(frag_start) = (qf, frag))
  (qi_POS : 0 < qi)
  (DELTA : frag.(frag_accept) \in fragments_delta_star frags frag.(frag_start) s)
  : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s.
Proof.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [START ACCEPT LT _ _].
  eapply delta_star_global_to_fragment; eauto. lia.
Qed.

Lemma delta_star_fragment_elim qi rules qmax frags rule frag qi_rule qf q q' s
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  (qi_POS : 0 < qi)
  (RANGE : qi_rule <= q <= qf)
  (DELTA : q' \in fragments_delta_star frags q s)
  : ⟪ DELTA_STAR_NIL : s = [] /\ q' = q ⟫ \/ ⟪ DELTA_STAR_EPS : exists q1, (q, q1) ∈ frag.(frag_eps_edges) /\ q' \in fragments_delta_star frags q1 s ⟫ \/ ⟪ DELTA_STAR_CHAR : exists edge, exists s', s = edge.(char_edge_label) :: s' /\ edge ∈ frag.(frag_char_edges) /\ q' \in fragments_delta_star frags edge.(char_edge_dst) s' ⟫.
Proof.
  pose proof (delta_star_elim _ _ q q' s DELTA) as [NIL | [EPS | CHAR]]; [left | right; left | right; right].
  - exact NIL.
  - destruct EPS as (q1 & STEP & REST).
    pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    assert (SRC_NONZERO : q ≠ 0) by now pose proof (rules2fragments_start_ge _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX); lia.
    pose proof (fragment_eps_edges_isolate _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX SRC_NONZERO RANGE IN_EDGE) as IN_FRAG_EDGE.
    exists q1; eauto.
  - destruct CHAR as (c & s' & q1 & EQ & STEP & REST).
    pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    assert (RANGE_SRC : qi_rule <= edge.(char_edge_src) <= qf) by lia.
    pose proof (fragment_char_edges_isolate _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX RANGE_SRC IN_EDGE) as IN_FRAG_EDGE.
    exists edge, s'. done.
Qed.

Lemma fragment_delta_star_elim frag q q' s
  (DELTA : q' \in fragment_delta_star frag q s)
  : ⟪ DELTA_STAR_NIL : s = [] /\ q' = q ⟫ \/ ⟪ DELTA_STAR_EPS : exists q1, (q, q1) ∈ frag.(frag_eps_edges) /\ q' \in fragment_delta_star frag q1 s ⟫ \/ ⟪ DELTA_STAR_CHAR : exists edge, exists s', s = edge.(char_edge_label) :: s' /\ edge ∈ frag.(frag_char_edges) /\ q' \in fragment_delta_star frag edge.(char_edge_dst) s' ⟫.
Proof.
  pose proof (delta_star_elim _ _ q q' s DELTA) as [NIL | [EPS | CHAR]]; [left | right; left | right; right].
  - exact NIL.
  - destruct EPS as (q1 & STEP & REST).
    pose proof (eps_step_from_edges_sound _ _ _ STEP).
    exists q1; eauto.
  - destruct CHAR as (c & s' & q1 & EQ & STEP & REST).
    pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    exists edge, s'. done.
Qed.

Lemma fragment_delta_star_elim_with_src frag q q' s
  (DELTA : q' \in fragment_delta_star frag q s)
  : ⟪ DELTA_STAR_NIL : s = [] /\ q' = q ⟫ \/ ⟪ DELTA_STAR_EPS : exists q1, (q, q1) ∈ frag.(frag_eps_edges) /\ q' \in fragment_delta_star frag q1 s ⟫ \/ ⟪ DELTA_STAR_CHAR : exists edge, exists s', s = edge.(char_edge_label) :: s' /\ edge.(char_edge_src) = q /\ edge ∈ frag.(frag_char_edges) /\ q' \in fragment_delta_star frag edge.(char_edge_dst) s' ⟫.
Proof.
  pose proof (delta_star_elim _ _ q q' s DELTA) as [NIL | [EPS | CHAR]]; [left | right; left | right; right].
  - exact NIL.
  - destruct EPS as (q1 & STEP & REST).
    pose proof (eps_step_from_edges_sound _ _ _ STEP).
    exists q1; eauto.
  - destruct CHAR as (c & s' & q1 & EQ & STEP & REST).
    pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    exists edge, s'. done.
Qed.

Lemma regex2fragment_Union_delta_star_start qi qf frag e1 e2 s
  (REGEX : regex2fragment (Re.Union e1 e2) qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : exists qf1, exists frag1, exists qf2, exists frag2, regex2fragment e1 (qi + 1) = (qf1, frag1) /\ regex2fragment e2 (qf1 + 1) = (qf2, frag2) /\ (frag.(frag_accept) \in fragment_delta_star frag (qi + 1) s \/ frag.(frag_accept) \in fragment_delta_star frag (qf1 + 1) s).
Proof.
  simpl in REGEX.
  destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
  destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
  inv REGEX. exists qf1, frag1, qf2, frag2. splits; eauto.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  pose proof (fragment_delta_star_elim_with_src _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; lia.
  - destruct EPS as (q1 & IN_EDGE & REST); simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | [EQ | IN_EDGE]]]].
    + inv EQ. left. exact REST.
    + inv EQ. right. exact REST.
    + inv EQ. lia.
    + inv EQ. lia.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (EPS1 _ _ IN_EDGE). simpl in *. lia.
      * pose proof (EPS2 _ _ IN_EDGE). simpl in *. lia.
  - destruct CHAR as (edge & s' & EQ & SRC & IN_EDGE & REST); simpl in IN_EDGE.
    rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]; simpl in SRC; done.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] _]; simpl in SRC; done.
Qed.

#[local] Hint Unfold fragment_delta_star : simplication_hints.
#[local] Hint Constructors delta_star : core.

Lemma regex2fragment_Union_left_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 q q' s
  (REGEX : regex2fragment (Re.Union e1 e2) qi = (qf, frag))
  (REGEX1 : regex2fragment e1 (qi + 1) = (qf1, frag1))
  (REGEX2 : regex2fragment e2 (qf1 + 1) = (qf2, frag2))
  (RANGE : qi + 1 <= q <= qf1)
  (DELTA : q' \in fragment_delta_star frag q s)
  (ACCEPT : q' = frag.(frag_accept))
  : exists s1, exists s2, s = s1 ++ s2 /\ qf1 \in fragment_delta_star frag1 q s1 /\ frag.(frag_accept) \in fragment_delta_star frag frag.(frag_accept) s2.
Proof.
  revert q q' s RANGE DELTA ACCEPT; simpl in REGEX.
  rewrite REGEX1, REGEX2 in REGEX. inv REGEX; ii.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  revert RANGE ACCEPT. induction DELTA; ii.
  - simpl in *. lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | [EQ | IN_EDGE]]]].
    + inv EQ. lia.
    + inv EQ. lia.
    + inv EQ. exists [], s. done.
    + inv EQ. lia.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (EPS1 _ _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]]; simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
        assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
        pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
        exists s1, s2. splits; eauto. eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete; eauto.
      * pose proof (EPS2 _ _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in *. lia.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists (edge.(char_edge_label) :: s1), s2. split.
      * rewrite EQ. simpl. now rewrite LABEL.
      * split; eauto. eapply delta_star_char with (q1 := q1); eauto.
        rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete; eauto.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in SRC. lia.
Qed.

Lemma regex2fragment_Union_right_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 q q' s
  (REGEX : regex2fragment (Re.Union e1 e2) qi = (qf, frag))
  (REGEX1 : regex2fragment e1 (qi + 1) = (qf1, frag1))
  (REGEX2 : regex2fragment e2 (qf1 + 1) = (qf2, frag2))
  (RANGE : qf1 + 1 <= q <= qf2)
  (DELTA : q' \in fragment_delta_star frag q s)
  (ACCEPT : q' = frag.(frag_accept))
  : exists s1, exists s2, s = s1 ++ s2 /\ qf2 \in fragment_delta_star frag2 q s1 /\ frag.(frag_accept) \in fragment_delta_star frag frag.(frag_accept) s2.
Proof.
  revert q q' s RANGE DELTA ACCEPT; simpl in REGEX.
  rewrite REGEX1, REGEX2 in REGEX. inv REGEX; ii.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  revert RANGE ACCEPT. induction DELTA; ii.
  - simpl in *. lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | [EQ | IN_EDGE]]]].
    + inv EQ. lia.
    + inv EQ. lia.
    + inv EQ. lia.
    + inv EQ. exists [], s. done.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (EPS1 _ _ IN_EDGE) as [[SRC_LO SRC_HI] _]; simpl in *; lia.
      * pose proof (EPS2 _ _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]]; simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
        assert (RANGE_STEP : qf1 + 1 <= q1 <= qf2) by lia.
        pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
        exists s1, s2. splits; eauto. eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete; eauto.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in SRC. lia.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      assert (RANGE_STEP : qf1 + 1 <= q1 <= qf2) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists (edge.(char_edge_label) :: s1), s2. split.
      * rewrite EQ. simpl. now rewrite LABEL.
      * split; eauto. eapply delta_star_char with (q1 := q1); eauto.
        rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete; eauto.
Qed.

Lemma regex2fragment_Append_delta_star_start qi qf frag e1 e2 s
  (REGEX : regex2fragment (Re.Append e1 e2) qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : exists qf1, exists frag1, exists qf2, exists frag2, regex2fragment e1 (qi + 1) = (qf1, frag1) /\ regex2fragment e2 (qf1 + 1) = (qf2, frag2) /\ frag.(frag_accept) \in fragment_delta_star frag (qi + 1) s.
Proof.
  simpl in REGEX. destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
  destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2. inv REGEX.
  exists qf1, frag1, qf2, frag2. splits; eauto.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  pose proof (fragment_delta_star_elim_with_src _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; lia.
  - destruct EPS as (q1 & IN_EDGE & REST). simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]].
    + inv EQ. exact REST.
    + inv EQ. lia.
    + inv EQ. lia.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (EPS1 _ _ IN_EDGE). simpl in *. lia.
      * pose proof (EPS2 _ _ IN_EDGE). simpl in *. lia.
  - destruct CHAR as (edge & s' & EQ & SRC & IN_EDGE & REST). simpl in IN_EDGE.
    rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]; simpl in SRC. done.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] _]; simpl in SRC. done.
Qed.

Lemma regex2fragment_Append_left_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 q q' s
  (REGEX : regex2fragment (Re.Append e1 e2) qi = (qf, frag))
  (REGEX1 : regex2fragment e1 (qi + 1) = (qf1, frag1))
  (REGEX2 : regex2fragment e2 (qf1 + 1) = (qf2, frag2))
  (RANGE : qi + 1 <= q <= qf1)
  (DELTA : q' \in fragment_delta_star frag q s)
  (ACCEPT : q' = frag.(frag_accept))
  : exists s1, exists s2, s = s1 ++ s2 /\ qf1 \in fragment_delta_star frag1 q s1 /\ frag.(frag_accept) \in fragment_delta_star frag (qf1 + 1) s2.
Proof.
  revert q q' s RANGE DELTA ACCEPT; simpl in REGEX.
  rewrite REGEX1, REGEX2 in REGEX. inv REGEX; ii.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  revert RANGE ACCEPT. induction DELTA; ii.
  - simpl in *. lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]].
    + inv EQ. lia.
    + inv EQ. exists [], s. done.
    + inv EQ. lia.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (EPS1 _ _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]]; simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
        assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
        pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
        exists s1, s2. splits; eauto. eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete; eauto.
      * pose proof (EPS2 _ _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in *. lia.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists (edge.(char_edge_label) :: s1), s2. split.
      * rewrite EQ. simpl. now rewrite LABEL.
      * split; eauto. eapply delta_star_char with (q1 := q1); eauto.
        rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete; eauto.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] _]; simpl in SRC. done.
Qed.

Lemma regex2fragment_Append_right_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 q q' s
  (REGEX : regex2fragment (Re.Append e1 e2) qi = (qf, frag))
  (REGEX1 : regex2fragment e1 (qi + 1) = (qf1, frag1))
  (REGEX2 : regex2fragment e2 (qf1 + 1) = (qf2, frag2))
  (RANGE : qf1 + 1 <= q <= qf2)
  (DELTA : q' \in fragment_delta_star frag q s)
  (ACCEPT : q' = frag.(frag_accept))
  : exists s1, exists s2, s = s1 ++ s2 /\ qf2 \in fragment_delta_star frag2 q s1 /\ frag.(frag_accept) \in fragment_delta_star frag frag.(frag_accept) s2.
Proof.
  revert q q' s RANGE DELTA ACCEPT; simpl in REGEX.
  rewrite REGEX1, REGEX2 in REGEX. inv REGEX; ii.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  revert RANGE ACCEPT. induction DELTA; ii.
  - simpl in *. lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]].
    + inv EQ. lia.
    + inv EQ. lia.
    + inv EQ. exists [], s. done.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (EPS1 _ _ IN_EDGE) as [[SRC_LO SRC_HI] _]; simpl in *. lia.
      * pose proof (EPS2 _ _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]]; simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
        assert (RANGE_STEP : qf1 + 1 <= q1 <= qf2) by lia.
        pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
        exists s1, s2. splits; eauto. eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete; eauto.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in SRC. lia.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      assert (RANGE_STEP : qf1 + 1 <= q1 <= qf2) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists (edge.(char_edge_label) :: s1), s2. split.
      * rewrite EQ. simpl. now rewrite LABEL.
      * split; eauto. eapply delta_star_char with (q1 := q1); eauto.
        rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete; eauto.
Qed.

Lemma regex2fragment_Star_delta_star_start qi qf frag e s
  (REGEX : regex2fragment (Re.Star e) qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : exists qf1, exists frag1, regex2fragment e (qi + 1) = (qf1, frag1) /\ frag.(frag_accept) \in fragment_delta_star frag (qi + 1) s.
Proof.
  simpl in REGEX. destruct (regex2fragment e (qi + 1)) as [qf1 frag1] eqn: REGEX1.
  inv REGEX. exists qf1, frag1. split; eauto.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (fragment_delta_star_elim_with_src _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; lia.
  - destruct EPS as (q1 & IN_EDGE & REST); simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]].
    + inv EQ. exact REST.
    + inv EQ. lia.
    + inv EQ. lia.
    + pose proof (EPS1 _ _ IN_EDGE). simpl in *. lia.
  - destruct CHAR as (edge & s' & EQ & SRC & IN_EDGE & REST).
    pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _].
    simpl in SRC. lia.
Qed.

Lemma regex2fragment_accept_delta_star_stuck e qi qf frag q' s
  (REGEX : regex2fragment e qi = (qf, frag))
  (DELTA : q' \in fragment_delta_star frag qf s)
  : s = [] /\ q' = qf.
Proof.
  eapply delta_star_stuck; eauto.
  - intros q IN. pose proof (eps_step_from_edges_sound _ _ _ IN) as IN_EDGE.
    pose proof (regex2fragment_edge_src_lt _ _ _ _ REGEX) as [EPS _].
    pose proof (EPS _ _ IN_EDGE).
    lia.
  - intros c q IN. pose proof (char_step_from_edges_sound _ _ _ _ IN) as (edge & IN_EDGE & SRC & LABEL & DST).
    pose proof (regex2fragment_edge_src_lt _ _ _ _ REGEX) as [_ CHAR].
    pose proof (CHAR _ IN_EDGE).
    lia.
Qed.

Lemma regex2fragment_Star_delta_star_sound' e
  (SOUND : forall qi, forall qf, forall frag, forall s, regex2fragment e qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e)
  : forall qi, forall qf, forall frag, forall qf1, forall frag1, forall q, forall q', forall s, regex2fragment (Re.Star e) qi = (qf, frag) -> regex2fragment e (qi + 1) = (qf1, frag1) -> qi + 1 <= q <= qf1 -> q' \in fragment_delta_star frag q s -> q' = frag.(frag_accept) ->  ((s = [] /\ q = qi + 1) \/ (exists s1, exists s2, s = s1 ++ s2 /\ qf1 \in fragment_delta_star frag1 q s1 /\ s2 \in eval_regex (Re.Star e))).
Proof.
  ii. revert q q' s H1 H2 H3. simpl in H. rewrite H0 in H. inv H. intros q q' s RANGE DELTA ACCEPT.
  pose proof (regex2fragment_bounds _ _ _ _ H0) as [START1 ACCEPT1 LT1 EPS1 CHAR1].
  pose proof (regex2fragment_edge_dst_gt _ _ _ _ H0) as [EPS_DST CHAR_DST].
  revert RANGE ACCEPT. induction DELTA; ii.
  - simpl in *. lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]].
    + inv EQ. lia.
    + inv EQ.
      assert (STAR_IN : s \in eval_regex (Re.Star e)).
      { hexploit (IHDELTA); try reflexivity; try lia.
        intros [[EQ _] | (s1 & s2 & EQ & DELTA1 & STAR)].
        - subst s. simpl. econs.
        - subst s. simpl. eapply star_app.
          + eapply SOUND; eauto. rewrite START1. exact DELTA1.
          + exact STAR.
      }
      right. exists [], s. done.
    + inv EQ. set (qf1 := frag_accept frag1). set (q2 := qf1 + 1).
      assert (REGEX_STAR : regex2fragment (Re.Star e) qi = (qf1 + 1, mkFragment qi (qf1 + 1) ((qi, qi + 1) :: (qf1, qi + 1) :: (qi + 1, qf1 + 1) :: frag1.(frag_eps_edges)) frag1.(frag_char_edges))) by (simpl; rewrite H0; reflexivity).
      pose proof (regex2fragment_accept_delta_star_stuck (Re.Star e) qi (qf1 + 1) (mkFragment qi (qf1 + 1) ((qi, qi + 1) :: (qf1, qi + 1) :: (qi + 1, qf1 + 1) :: frag1.(frag_eps_edges)) frag1.(frag_char_edges)) q2 s REGEX_STAR REST) as [EQ _].
      subst s. left; eauto.
    + pose proof (EPS1 _ _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
      assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as [[EQ EQ'] | (s1 & s2 & EQ & DELTA1 & STAR)].
      * subst s q1. pose proof (EPS_DST _ _ IN_EDGE). lia.
      * right. exists s1, s2. repeat split; eauto.
        eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete. exact IN_EDGE.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
    assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
    pose proof (IHDELTA RANGE_STEP ACCEPT) as [[EQ EQ'] | (s1 & s2 & EQ & DELTA1 & STAR)].
    + subst s q1. pose proof (CHAR_DST _ IN_EDGE). lia.
    + right. exists (edge.(char_edge_label) :: s1), s2. split.
      * rewrite EQ. simpl. now rewrite LABEL.
      * split; eauto. eapply delta_star_char with (q1 := q1); eauto.
        rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete; eauto.
Qed.

Lemma regex2fragment_sound_Null qi qf frag s
  (REGEX : regex2fragment Re.Null qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : s \in eval_regex Re.Null.
Proof.
  simpl in REGEX. inv REGEX. pose proof (fragment_delta_star_elim _ _ _ _ DELTA) as [NIL | [EPS | CHAR]]; done.
Qed.

Lemma regex2fragment_sound_Empty qi qf frag s
  (REGEX : regex2fragment Re.Empty qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : s \in eval_regex Re.Empty.
Proof.
  simpl in REGEX. inv REGEX. pose proof (fragment_delta_star_elim _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; lia.
  - destruct EPS as (q1 & IN_EDGE & REST). simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | []]. inv EQ.
    pose proof (regex2fragment_accept_delta_star_stuck Re.Empty qi (qi + 1) (mkFragment qi (qi + 1) [(qi, qi + 1)] []) (qi + 1) s eq_refl REST) as [EQ ?].
    subst s. simpl. autorewrite with simplication_hints. reflexivity.
  - des; contradiction.
Qed.

Lemma regex2fragment_sound_Char c qi qf frag s
  (REGEX : regex2fragment (Re.Char c) qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : s \in eval_regex (Re.Char c).
Proof.
  simpl in REGEX. inv REGEX. pose proof (fragment_delta_star_elim _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; lia.
  - des; contradiction.
  - destruct CHAR as (edge & s' & EQ & IN_EDGE & REST). simpl in IN_EDGE.
    destruct IN_EDGE as [EDGE_EQ | []]. subst edge. simpl in EQ. subst s.
    pose proof (regex2fragment_accept_delta_star_stuck (Re.Char c) qi (qi + 1) (mkFragment qi (qi + 1) [] [mkCharEdge qi c (qi + 1)]) (qi + 1) s' eq_refl REST) as [EQ ?].
    subst s'. simpl. done.
Qed.

Lemma regex2fragment_sound_Union e1 e2
  (SOUND1 : forall qi, forall qf, forall frag, forall s, regex2fragment e1 qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e1)
  (SOUND2 : forall qi, forall qf, forall frag, forall s, regex2fragment e2 qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e2)
  : forall qi, forall qf, forall frag, forall s, regex2fragment (Re.Union e1 e2) qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex (Re.Union e1 e2).
Proof.
  ii. pose proof (regex2fragment_start_accept _ _ _ _ H) as [_ ACCEPT].
  pose proof (regex2fragment_Union_delta_star_start qi qf frag e1 e2 s H H0) as (qf1 & frag1 & qf2 & frag2 & REGEX1 & REGEX2 & [DELTA1 | DELTA2]).
  - pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [START1 ACCEPT1 LT1 _ _].
    assert (RANGE1 : qi + 1 <= qi + 1 <= qf1) by lia.
    pose proof (regex2fragment_Union_left_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 (qi + 1) frag.(frag_accept) s H REGEX1 REGEX2 RANGE1 DELTA1 eq_refl) as (s1 & s2 & EQ & DELTA1' & DELTA2').
    rewrite ACCEPT in DELTA2'.
    pose proof (regex2fragment_accept_delta_star_stuck (Re.Union e1 e2) qi qf frag qf s2 H DELTA2') as [EQ2 _]. subst s2.
    rewrite app_nil_r in EQ. subst s. simpl. rewrite E.in_union_iff. left. eapply SOUND1; eauto.
    rewrite START1. rewrite ACCEPT1. exact DELTA1'.
  - pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [START2 ACCEPT2 LT2 _ _].
    assert (RANGE2 : qf1 + 1 <= qf1 + 1 <= qf2) by lia.
    pose proof (regex2fragment_Union_right_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 (qf1 + 1) frag.(frag_accept) s H REGEX1 REGEX2 RANGE2 DELTA2 eq_refl) as (s1 & s2 & EQ & DELTA1' & DELTA2').
    rewrite ACCEPT in DELTA2'.
    pose proof (regex2fragment_accept_delta_star_stuck (Re.Union e1 e2) qi qf frag qf s2 H DELTA2') as [EQ2 _].
    subst s2. rewrite app_nil_r in EQ. subst s.
    simpl. rewrite E.in_union_iff. right. eapply SOUND2; eauto.
    rewrite START2. rewrite ACCEPT2. exact DELTA1'.
Qed.

Lemma regex2fragment_sound_Append e1 e2
  (SOUND1 : forall qi, forall qf, forall frag, forall s, regex2fragment e1 qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e1)
  (SOUND2 : forall qi, forall qf, forall frag, forall s, regex2fragment e2 qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e2)
  : forall qi, forall qf, forall frag, forall s, regex2fragment (Re.Append e1 e2) qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex (Re.Append e1 e2).
Proof.
  ii. pose proof (regex2fragment_start_accept _ _ _ _ H) as [_ ACCEPT].
  pose proof (regex2fragment_Append_delta_star_start qi qf frag e1 e2 s H H0) as (qf1 & frag1 & qf2 & frag2 & REGEX1 & REGEX2 & DELTA).
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [START1 ACCEPT1 LT1 _ _].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [START2 ACCEPT2 LT2 _ _].
  assert (RANGE1 : qi + 1 <= qi + 1 <= qf1) by lia.
  assert (RANGE2 : qf1 + 1 <= qf1 + 1 <= qf2) by lia.
  pose proof (regex2fragment_Append_left_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 (qi + 1) frag.(frag_accept) s H REGEX1 REGEX2 RANGE1 DELTA eq_refl) as (s1 & s2 & EQ & DELTA1 & DELTA2).
  pose proof (regex2fragment_Append_right_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 (qf1 + 1) frag.(frag_accept) s2 H REGEX1 REGEX2 RANGE2 DELTA2 eq_refl) as (s2' & s3 & EQ' & DELTA2' & DELTA3).
  rewrite ACCEPT in DELTA3.
  pose proof (regex2fragment_accept_delta_star_stuck (Re.Append e1 e2) qi qf frag qf s3 H DELTA3) as [EQ3 _]. subst s3.
  rewrite app_nil_r in EQ'. subst s2. subst s. simpl. exists s1. split.
  - eapply SOUND1; eauto. rewrite START1. rewrite ACCEPT1. exact DELTA1.
  - exists s2'. split.
    + eapply SOUND2; eauto. rewrite START2. rewrite ACCEPT2. exact DELTA2'.
    + reflexivity.
Qed.

Lemma regex2fragment_sound_Star e1
  (SOUND : forall qi, forall qf, forall frag, forall s, regex2fragment e1 qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e1)
  : forall qi, forall qf, forall frag, forall s, regex2fragment (Re.Star e1) qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex (Re.Star e1).
Proof.
  ii. pose proof (regex2fragment_Star_delta_star_start qi qf frag e1 s H H0) as (qf1 & frag1 & REGEX & DELTA).
  pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [START ACCEPT LT _ _].
  assert (RANGE : qi + 1 <= qi + 1 <= qf1) by lia.
  pose proof (regex2fragment_Star_delta_star_sound' e1 SOUND qi qf frag qf1 frag1 (qi + 1) frag.(frag_accept) s H REGEX RANGE DELTA eq_refl) as [[EQ _] | (s1 & s2 & EQ & DELTA1 & STAR)].
  - subst s. simpl. econs.
  - subst s. simpl. eapply star_app.
    + eapply SOUND; eauto. rewrite START. rewrite ACCEPT. exact DELTA1.
    + exact STAR.
Qed.

Theorem regex2fragment_sound (e : regex ascii)
  : forall qi, forall qf, forall frag, forall s, regex2fragment e qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e.
Proof.
  induction e.
  - now eapply regex2fragment_sound_Null.
  - now eapply regex2fragment_sound_Empty.
  - now eapply regex2fragment_sound_Char.
  - now eapply regex2fragment_sound_Union.
  - now eapply regex2fragment_sound_Append.
  - now eapply regex2fragment_sound_Star.
Qed.

Lemma fragments_delta_star_start_to_fragment qi rules qmax frags rule frag qi_rule qf s
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  (qi_POS : 0 < qi)
  (DELTA : frag.(frag_accept) \in fragments_delta_star frags 0 s)
  : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s.
Proof.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [START ACCEPT LT _ _].
  pose proof (delta_star_elim _ _ 0 frag.(frag_accept) s DELTA) as [NIL | [EPS | CHAR]].
  - des; subst.
    pose proof (rules2fragments_start_ge _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX).
    lia.
  - destruct EPS as (q1 & STEP & REST).
    pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    pose proof (fragment_eps_edges_start_sound _ _ _ _ _ FRAGS qi_POS IN_EDGE) as (rule' & frag' & qi_rule' & qf' & IN_FRAG' & REGEX' & START_EDGE). subst q1.
    pose proof (regex2fragment_bounds _ _ _ _ REGEX') as [START' ACCEPT' LT' _ _].
    assert (RANGE : qi_rule <= frag.(frag_accept) <= qf) by lia.
    assert (RANGE' : qi_rule' <= frag.(frag_accept) <= qf').
    { eapply delta_star_fragment_range with (qi := qi) (rules := rules) (qmax := qmax) (frags := frags) (rule := rule') (frag := frag') (q := frag'.(frag_start)) (s := s); eauto. lia. }
    pose proof (rules2fragments_ranges_disjoint _ _ _ _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG IN_FRAG' REGEX REGEX' RANGE RANGE') as EQ.
    inv EQ. eapply delta_star_global_to_fragment; eauto. lia.
  - destruct CHAR as (c & s' & q1 & EQ & STEP & REST).
    pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    pose proof (fragment_char_edges_owner _ _ _ _ _ FRAGS IN_EDGE) as (rule' & frag' & qi_rule' & qf' & IN_FRAG' & REGEX' & BOUNDS' & LE_START & LT_END & RANGE' & IN_EDGE').
    lia.
Qed.

Lemma TaggedENFA_FRAGMENTS_sound qi rules qmax frags s tag
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (qi_POS : 0 < qi)
  (ACCEPTS : accepts (fragments2TaggedENFA qmax frags) s tag)
  : exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex).
Proof.
  destruct ACCEPTS as (q & DELTA & ACCEPT). simpl in DELTA, ACCEPT.
  pose proof (fragment_accept_states_sound _ _ _ ACCEPT) as (rule & frag & IN_FRAG & ACCEPT_EQ & TOKEN_EQ); subst q tag.
  pose proof (rules2fragments_bounds _ _ _ _ FRAGS) as [_ BOUND].
  pose proof (BOUND _ _ IN_FRAG) as (qi_rule & qf & REGEX & _ & _ & _).
  exists rule. split.
  - eapply rules2fragments_sound; eauto.
  - split; eauto. eapply regex2fragment_sound; eauto. eapply fragments_delta_star_start_to_fragment; eauto.
Qed.

Theorem mkUnitedTaggedENFA_sound (M : TaggedENFA.t)
  (COMPILE : fmap mkUnitedTaggedENFA Rule.compileds = inr M)
  : exists rules, Rule.compileds = inr rules /\ ⟪ ACCEPT : forall s, forall tag, accepts M s tag -> (exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex)) ⟫.
Proof.
  pose proof (mkUnitedTaggedENFA_spec M COMPILE) as (rules & qmax & frags & [COMPILED_RULES COMPILED_ENFA COMPILED_FRAGS] & FRAGMENTS_OF).
  exists rules. split; [exact COMPILED_RULES | unnw]. intros s tag ACCEPTS.
  assert (ENFA_EQ : M = fragments2TaggedENFA qmax frags).
  { unfold mkUnitedTaggedENFA in COMPILED_ENFA. now rewrite COMPILED_FRAGS in COMPILED_ENFA. }
  rewrite ENFA_EQ in ACCEPTS. eapply TaggedENFA_FRAGMENTS_sound; eauto.
Qed.

Theorem mkUnitedTaggedENFA_complete (M : TaggedENFA.t)
  (COMPILE : fmap mkUnitedTaggedENFA Rule.compileds = inr M)
  : exists rules, Rule.compileds = inr rules /\ ⟪ ACCEPT : forall s, forall tag, (exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex)) -> accepts M s tag ⟫.
Proof.
  pose proof (mkUnitedTaggedENFA_spec M COMPILE) as (rules & qmax & frags & [COMPILED_RULES COMPILED_ENFA COMPILED_FRAGS] & FRAGMENTS_OF).
  exists rules. split; [exact COMPILED_RULES | unnw]. intros s tag (rule & IN_RULE & TOKEN & IN_REGEX); subst tag.
  pose proof (rules2fragments_complete 1 rules qmax frags rule COMPILED_FRAGS IN_RULE) as (qi & qf & frag & REGEX2FRAGMENT & IN_FRAGS).
  pose proof (FRAGMENTS_OF rule frag IN_FRAGS) as FRAGMENTS.
  pose proof (TaggedENFA_FRAGMENTS_complete qmax frags rule qi qf frag s REGEX2FRAGMENT FRAGMENTS IN_REGEX) as ACCEPTS.
  unfold mkUnitedTaggedENFA in COMPILED_ENFA. rewrite COMPILED_FRAGS in COMPILED_ENFA. now subst M.
Qed.

End Thompson's_construction.

End TaggedENFA.

Module TaggedDFA.

#[projections(primitive)]
Record t : Type :=
  mk
  { state : Set
  ; state_hasEqDec : hasEqDec@{Set} state
  ; states : fin_ensemble state
  ; start_state : state
  ; accept_states : alist state Token.t
  ; transition (q : state) (c : ascii) : state
  } as M.

#[global] Existing Instance state_hasEqDec.

Fixpoint delta (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) (s : Input.t) {struct s} : M.(TaggedDFA.state) :=
  match s with
  | [] => q
  | c :: s' => delta M (M.(TaggedDFA.transition) q c) s'
  end.

Definition accepts (M : TaggedDFA.t) (s : Input.t) (tag : Token.t) : Prop :=
  (delta M M.(TaggedDFA.start_state) s, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).

Definition accepted_tags (M : TaggedDFA.t) (s : Input.t) : ensemble Token.t :=
  fun tag => accepts M s tag.

Definition state_reachable (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) : Prop :=
  exists s, q = delta M M.(TaggedDFA.start_state) s.

Definition all_states_reachable (M : TaggedDFA.t) : Prop :=
  forall q, q ∈ M.(TaggedDFA.states) -> state_reachable M q.

Definition language_equiv (M1 : TaggedDFA.t) (M2 : TaggedDFA.t) : Prop :=
  forall s, forall tag, accepts M1 s tag <-> accepts M2 s tag.

Variant okay (M : TaggedDFA.t) : Prop :=
  | okay_intro
    (start_okay : M.(TaggedDFA.start_state) ∈ M.(TaggedDFA.states))
    (accept_states_okay : forall q, forall tag, (q, tag) ∈ M.(TaggedDFA.accept_states).(kvlist) -> q ∈ M.(TaggedDFA.states))
    (transition_okay : forall q, forall c, q ∈ M.(TaggedDFA.states) -> M.(TaggedDFA.transition) q c ∈ M.(TaggedDFA.states)).

Lemma delta_app (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) (s1 : Input.t) (s2 : Input.t)
  : delta M q (s1 ++ s2) = delta M (delta M q s1) s2.
Proof.
  revert q. induction s1 as [ | c s1 IH]; intros q; simpl; eauto.
Qed.

Lemma delta_okay (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) (s : Input.t)
  (OKAY : okay M)
  (IN : q ∈ M.(TaggedDFA.states))
  : delta M q s ∈ M.(TaggedDFA.states).
Proof.
  revert q IN. induction s as [ | c s IH]; intros q IN; simpl; [exact IN | ].
  eapply IH. destruct OKAY as [_ _ TRANS_OKAY]. eapply TRANS_OKAY. exact IN.
Qed.

Section NUMBER_STATES.

Variable M : TaggedDFA.t.

#[local] Abbreviation Q := M.(TaggedDFA.state).

Definition state_number (q : Q) : nat :=
  index_of (EQ_DEC := M.(state_hasEqDec)) q M.(TaggedDFA.states).

Definition numbered_state_denote (n : nat) : Q :=
  lookup M.(TaggedDFA.start_state) n M.(TaggedDFA.states).

Definition numbered_states : list nat :=
  seq 0 (length M.(TaggedDFA.states)).

Lemma numbered_states_NoDup
  : NoDup numbered_states.
Proof.
  eapply seq_NoDup.
Qed.

Definition numbered_start_state : nat :=
  state_number M.(TaggedDFA.start_state).

Definition numbered_transition (n : nat) (c : ascii) : nat :=
  state_number (M.(TaggedDFA.transition) (numbered_state_denote n) c).

Definition numbered_accept_states : list (nat * Token.t) :=
  M.(TaggedDFA.accept_states).(kvlist) >>= fun '(q, tag) => pure (state_number q, tag).

Definition number_states : TaggedDFA.t :=
  {|
    state := nat;
    state_hasEqDec := nat_hasEqDec;
    states := numbered_states;
    start_state := numbered_start_state;
    accept_states := {| kvlist := numbered_accept_states |};
    transition := numbered_transition;
  |}.

Theorem number_states_states_NoDup
  : NoDup number_states.(TaggedDFA.states).
Proof.
  eapply numbered_states_NoDup.
Qed.

Lemma numbered_state_denote_state_number (q : Q)
  (IN : q ∈ M.(TaggedDFA.states))
  : numbered_state_denote (state_number q) = q.
Proof.
  now eapply lookup_index_of.
Qed.

Lemma numbered_state_denote_in (n : nat)
  (IN : n ∈ numbered_states)
  : numbered_state_denote n ∈ M.(TaggedDFA.states).
Proof.
  unfold numbered_states, numbered_state_denote in *.
  rewrite in_seq in IN. eapply lookup_in. lia.
Qed.

Lemma numbered_accept_states_complete (q : Q) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  : (state_number q, tag) ∈ numbered_accept_states.
Proof.
  eapply in_list_bind_intro with (x := (q, tag)); done.
Qed.

Lemma numbered_accept_states_sound (n : nat) (tag : Token.t)
  (ACCEPT : (n, tag) ∈ numbered_accept_states)
  : exists q, (q, tag) ∈ M.(TaggedDFA.accept_states).(kvlist) /\ n = state_number q.
Proof.
  unfold numbered_accept_states in ACCEPT.
  pose proof (in_list_bind_elim _ _ _ ACCEPT) as ([q tag'] & ACCEPT' & IN).
  done.
Qed.

Lemma numbered_delta (q : Q) (s : Input.t)
  (OKAY : okay M)
  (IN : q ∈ M.(TaggedDFA.states))
  : delta number_states (state_number q) s = state_number (delta M q s).
Proof.
  revert q IN. induction s as [ | c s IH]; intros q IN; simpl; auto.
  unfold numbered_transition. rewrite numbered_state_denote_state_number; auto.
  eapply IH. destruct OKAY as [_ _ TRANS_OKAY]. eapply TRANS_OKAY; auto.
Qed.

Theorem number_states_sound (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : accepts number_states s tag)
  : accepts M s tag.
Proof.
  cbv [accepts] in *. simpl in ACCEPT. destruct OKAY as [START_OKAY ACCEPT_OKAY TRANS_OKAY]. unfold numbered_start_state in *.
  assert (NUMBERED_DELTA : delta number_states (state_number M.(TaggedDFA.start_state)) s = state_number (delta M M.(TaggedDFA.start_state) s)).
  { eapply numbered_delta; [econs; eauto | exact START_OKAY]. }
  rewrite NUMBERED_DELTA in ACCEPT.
  pose proof (numbered_accept_states_sound _ _ ACCEPT) as (q & ACCEPT_Q & EQ).
  assert (DELTA_IN : delta M M.(TaggedDFA.start_state) s ∈ M.(TaggedDFA.states)).
  { eapply delta_okay; [econs; eauto | exact START_OKAY]. }
  assert (Q_IN : q ∈ M.(TaggedDFA.states)) by (eapply ACCEPT_OKAY; exact ACCEPT_Q).
  pose proof (index_of_inj _ _ M.(TaggedDFA.states) M.(TaggedDFA.start_state) DELTA_IN Q_IN EQ) as DELTA_EQ.
  now subst q.
Qed.

Theorem number_states_complete (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : accepts M s tag)
  : accepts number_states s tag.
Proof.
  unfold accepts in ACCEPT |- *. simpl. destruct OKAY as [START_OKAY ACCEPT_OKAY TRANS_OKAY]. unfold numbered_start_state.
  assert (NUMBERED_DELTA : delta number_states (state_number M.(TaggedDFA.start_state)) s = state_number (delta M M.(TaggedDFA.start_state) s)).
  { eapply numbered_delta; [econs; eauto | exact START_OKAY]. }
  rewrite NUMBERED_DELTA. now eapply numbered_accept_states_complete.
Qed.

Theorem number_states_okay
  (OKAY : okay M)
  : okay number_states.
Proof.
  destruct OKAY as [START_OKAY ACCEPT_OKAY TRANS_OKAY]. split; simpl.
  - now eapply index_of_in_seq.
  - intros n tag ACCEPT.
    pose proof (numbered_accept_states_sound n tag ACCEPT) as (q & ACCEPT_Q & EQ).
    subst n. eapply index_of_in_seq. done.
  - intros n c IN. unfold numbered_transition. eapply index_of_in_seq.
    eapply TRANS_OKAY. now eapply numbered_state_denote_in.
Qed.

End NUMBER_STATES.

Section SUBSET_CONSTRUCTION.

Variable M : TaggedENFA.t.

#[local] Abbreviation Q := M.(TaggedENFA.state).
#[local] Abbreviation eclosure := (TaggedENFA.eclosure M.(TaggedENFA.eps_step)).
#[local] Abbreviation delta_star := (TaggedENFA.delta_star M.(TaggedENFA.eps_step) M.(TaggedENFA.char_step)).

Definition subset_state : Set :=
  fin_ensemble Q.

Definition normalize (qs : subset_state) : subset_state :=
  filter (fun q => mem (EQ_DEC := M.(TaggedENFA.state_hasEqDec)) q qs) M.(TaggedENFA.states).

Definition move (qs : subset_state) (c : ascii) : subset_state :=
  bind (isMonad := B.list_isMonad) qs (fun q => M.(TaggedENFA.char_step) q c).

Definition eps_move (qs : subset_state) : subset_state :=
  bind (isMonad := B.list_isMonad) qs M.(TaggedENFA.eps_step).

Definition eclose_step (qs : subset_state) : subset_state :=
  normalize (union (EQ_DEC := M.(TaggedENFA.state_hasEqDec)) (eps_move qs) qs).

Definition eclose (qs : subset_state) : subset_state :=
  iter (length M.(TaggedENFA.states)) eclose_step (normalize qs).

Lemma in_normalize_iff (qs : subset_state)
  : forall q, q ∈ normalize qs <-> (q ∈ qs /\ q ∈ M.(TaggedENFA.states)).
Proof.
  i; unfold normalize. done.
Qed.

#[local] Hint Rewrite in_normalize_iff : simplication_hints.

Lemma in_move_iff (qs : subset_state) (c : ascii)
  : forall q', q' ∈ move qs c <-> (exists q, q ∈ qs /\ q' ∈ M.(TaggedENFA.char_step) q c).
Proof.
  i; unfold move. split; i; des.
  - eapply in_list_bind_elim; eauto.
  - eapply in_list_bind_intro; eauto.
Qed.

#[local] Hint Rewrite in_move_iff : simplication_hints.

Lemma in_eps_move_iff (qs : subset_state)
  : forall q', q' ∈ eps_move qs <-> (exists q, q ∈ qs /\ q' ∈ M.(TaggedENFA.eps_step) q).
Proof.
  i; unfold eps_move. split; i; des.
  - eapply in_list_bind_elim; eauto.
  - eapply in_list_bind_intro; eauto.
Qed.

#[local] Hint Rewrite in_eps_move_iff : simplication_hints.

#[local] Hint Constructors TaggedENFA.eclosure : core.
#[local] Hint Constructors TaggedENFA.delta_star : core.

Lemma eclose_step_sound (qs : subset_state) (q' : Q)
  (IN : q' ∈ eclose_step qs)
  : exists q, q ∈ qs /\ q' \in eclosure q.
Proof.
  unfold eclose_step in IN.
  rewrite in_normalize_iff in IN. destruct IN as [IN_UNION _].
  rewrite in_union_iff in IN_UNION. destruct IN_UNION as [IN_EPS | IN_QS].
  - rewrite in_eps_move_iff in IN_EPS. destruct IN_EPS as (q & IN_QS & STEP).
    done.
  - done.
Qed.

#[local] Hint Resolve TaggedENFA.eclosure_trans : core.

Lemma iter_eclose_step_sound (fuel : nat) (qs : subset_state) (q' : Q)
  (IN : q' ∈ iter fuel eclose_step qs)
  : exists q, q ∈ qs /\ q' \in eclosure q.
Proof.
  revert qs q' IN; induction fuel as [ | fuel IH]; ii; simpl in IN.
  - exists q'. done.
  - pose proof (IH _ _ IN) as (q1 & STEP & REST).
    pose proof (eclose_step_sound _ _ STEP) as (q0 & IN_QS & CLOS).
    exists q0. done.
Qed.

Lemma eclose_sound (qs : subset_state) (q' : Q)
  (IN : q' ∈ eclose qs)
  : exists q, q ∈ qs /\ q' \in eclosure q.
Proof.
  unfold eclose in IN.
  pose proof (iter_eclose_step_sound _ _ _ IN) as (q & IN_NORM & CLOS).
  rewrite in_normalize_iff in IN_NORM. destruct IN_NORM as [IN_QS _].
  exists q; eauto.
Qed.

Definition eps_graph : GRAPH.t :=
  {|
    GRAPH.vertices := Q;
    GRAPH.edges := fun '(q, q') => q' ∈ M.(TaggedENFA.eps_step) q;
  |}.

#[local] Notation " src ~~~[ w ]~~> tgt " := (@walk eps_graph tgt src w) : type_scope.

#[local] Hint Constructors walk : core.

Lemma eclosure_walk (q : Q) (q' : Q)
  (CLOS : q' \in eclosure q)
  : exists w, q ~~~[ w ]~~> q'.
Proof.
  induction CLOS as [q | q q1 q2 STEP REST [w WALK]]; eauto.
Qed.

Lemma eps_walk_states (q : Q) (q' : Q) (w : list Q)
  (OKAY : TaggedENFA.okay M)
  (STATE : q ∈ M.(TaggedENFA.states))
  (WALK : q ~~~[ w ]~~> q')
  : forall q0, q0 ∈ w -> q0 ∈ M.(TaggedENFA.states).
Proof.
  destruct OKAY as [_ _ EPS_OKAY _].
  induction WALK as [ | q q1 w STEP REST IH]; intros q0 IN; simpl in IN.
  - tauto.
  - destruct IN as [EQ | IN]; done.
Qed.

Lemma eclose_step_complete_keep (qs : subset_state) (q : Q)
  (STATE : q ∈ M.(TaggedENFA.states))
  (IN : q ∈ qs)
  : q ∈ eclose_step qs.
Proof.
  unfold eclose_step. done.
Qed.

Lemma eclose_step_complete_edge (qs : subset_state) (q : Q) (q' : Q)
  (STATE : q' ∈ M.(TaggedENFA.states))
  (IN : q ∈ qs)
  (STEP : q' ∈ M.(TaggedENFA.eps_step) q)
  : q' ∈ eclose_step qs.
Proof.
  unfold eclose_step. done.
Qed.

#[local] Hint Resolve eclose_step_complete_keep : core.

Lemma iter_eclose_step_keeps (fuel : nat) (qs : subset_state) (q : Q)
  (STATE : q ∈ M.(TaggedENFA.states))
  (IN : q ∈ qs)
  : q ∈ iter fuel eclose_step qs.
Proof.
  revert qs IN; induction fuel as [ | fuel IH]; ii; simpl; eauto.
Qed.

Lemma iter_eclose_step_walk_complete (fuel : nat) (qs : subset_state) (q : Q) (q' : Q) (w : list Q)
  (OKAY : TaggedENFA.okay M)
  (QS_STATES : forall q, q ∈ qs -> q ∈ M.(TaggedENFA.states))
  (IN : q ∈ qs)
  (WALK : q ~~~[ w ]~~> q')
  (LENGTH : length w <= fuel)
  : q' ∈ iter fuel eclose_step qs.
Proof.
  revert fuel qs IN QS_STATES LENGTH; induction WALK as [ | q q1 w STEP REST IH]; ii.
  - eapply iter_eclose_step_keeps; eauto.
  - destruct fuel as [ | fuel]; simpl in *; try lia. eapply IH.
    + eapply eclose_step_complete_edge; eauto. destruct OKAY as [_ _ EPS_OKAY _]; eauto.
    + clear. intros q IN. unfold eclose_step in IN. now rewrite in_normalize_iff in IN.
    + lia.
Qed.

Lemma eclose_complete (qs : subset_state) (q : Q) (q' : Q)
  (OKAY : TaggedENFA.okay M)
  (QS_STATES : forall q, q ∈ qs -> q ∈ M.(TaggedENFA.states))
  (IN : q ∈ qs)
  (CLOS : q' \in eclosure q)
  : q' ∈ eclose qs.
Proof.
  unfold eclose.
  pose proof (eclosure_walk _ _ CLOS) as [w WALK].
  exploit (@walk_finds_path eps_graph _ q q' w).
  { clear; intros q qs. now pose proof (L.in_dec (@eq_dec Q M.(TaggedENFA.state_hasEqDec)) q qs) as [YES | NO]; [left | right]. }
  { exact WALK. }
  intros [p PATH]. rewrite path_iff_no_dup_walk in PATH. destruct PATH as [WALK' NO_DUP].
  eapply iter_eclose_step_walk_complete with (q := q) (w := p); eauto.
  - ii; ss!.
  - ii; ss!.
  - eapply L.NoDup_incl_length; eauto. ii; eapply eps_walk_states; eauto.
Qed.

Definition subset_state_okay (qs : subset_state) : Prop :=
  (forall q : Q, forall IN : q ∈ qs, q ∈ M.(TaggedENFA.states)) /\ (forall q : Q, forall q' : Q, forall IN : q ∈ qs, forall CLOS : q' \in eclosure q, q' ∈ qs).

Lemma eclose_closed (qs : subset_state) (q : Q) (q' : Q)
  (OKAY : TaggedENFA.okay M)
  (QS_STATES : forall q, q ∈ qs -> q ∈ M.(TaggedENFA.states))
  (IN : q ∈ eclose qs)
  (CLOS : q' \in eclosure q)
  : q' ∈ eclose qs.
Proof.
  pose proof (eclose_sound _ _ IN) as (q0 & IN0 & CLOS0).
  eapply eclose_complete with (q := q0); eauto.
Qed.

Definition subset_states : fin_ensemble subset_state :=
  powerset M.(TaggedENFA.states).

Lemma normalize_in_subset_states (qs : subset_state)
  : normalize qs ∈ subset_states.
Proof.
  eapply filter_in_powerset.
Qed.

Lemma eclose_step_in_subset_states (qs : subset_state)
  : eclose_step qs ∈ subset_states.
Proof.
  eapply normalize_in_subset_states.
Qed.

Lemma iter_eclose_step_in_subset_states (fuel : nat) (qs : subset_state)
  (IN : qs ∈ subset_states)
  : iter fuel eclose_step qs ∈ subset_states.
Proof.
  revert qs IN; induction fuel as [ | fuel IH]; ii; simpl; eauto.
  eapply IH. eapply eclose_step_in_subset_states.
Qed.

Lemma eclose_in_subset_states (qs : subset_state)
  : eclose qs ∈ subset_states.
Proof.
  eapply iter_eclose_step_in_subset_states. eapply normalize_in_subset_states.
Qed.

Definition subset_start_state : subset_state :=
  eclose [M.(TaggedENFA.start_state)].

Definition subset_transition (qs : subset_state) (c : ascii) : subset_state :=
  eclose (move qs c).

Lemma subset_start_state_complete
  (OKAY : TaggedENFA.okay M)
  : M.(TaggedENFA.start_state) ∈ subset_start_state.
Proof.
  destruct OKAY. eapply eclose_complete with (q := M.(TaggedENFA.start_state)); eauto; done.
Qed.

Lemma subset_start_state_sound (q : Q)
  (IN : q ∈ subset_start_state)
  : q \in eclosure M.(TaggedENFA.start_state).
Proof.
  pose proof (eclose_sound _ _ IN) as (q0 & IN_START & CLOS). ss!.
Qed.

Lemma subset_start_state_okay
  (OKAY : TaggedENFA.okay M)
  : subset_state_okay subset_start_state.
Proof.
  split.
  - intros q IN. pose proof OKAY as [START_OKAY _ _ _].
    eapply TaggedENFA.eclosure_okay with (M := M) (q1 := M.(TaggedENFA.start_state)); eauto.
    now eapply subset_start_state_sound.
  - intros q q' IN CLOS.
    eapply eclose_closed with (q := q); eauto.
    destruct OKAY as [START_OKAY _ _ _]; done.
Qed.

Lemma subset_transition_sound (qs : subset_state) (c : ascii) (q' : Q)
  (IN : q' ∈ subset_transition qs c)
  : exists q, exists q1, q ∈ qs /\ q1 ∈ M.(TaggedENFA.char_step) q c /\ q' \in eclosure q1.
Proof.
  pose proof (eclose_sound _ _ IN) as (q1 & IN_MOVE & CLOS).
  rewrite in_move_iff in IN_MOVE. destruct IN_MOVE as (q & IN_QS & STEP).
  exists q, q1. eauto.
Qed.

Lemma subset_transition_complete (qs : subset_state) (c : ascii) (q : Q) (q1 : Q) (q' : Q)
  (OKAY : TaggedENFA.okay M)
  (QS_STATES : forall q, q ∈ qs -> q ∈ M.(TaggedENFA.states))
  (IN : q ∈ qs)
  (STEP : q1 ∈ M.(TaggedENFA.char_step) q c)
  (CLOS : q' \in eclosure q1)
  : q' ∈ subset_transition qs c.
Proof.
  eapply eclose_complete with (q := q1); eauto.
  - destruct OKAY as [_ _ _ CHAR_OKAY]. ii; done.
  - done.
Qed.

Lemma subset_transition_okay (qs : subset_state) (c : ascii)
  (OKAY : TaggedENFA.okay M)
  (QS_OKAY : subset_state_okay qs)
  : subset_state_okay (subset_transition qs c).
Proof.
  destruct QS_OKAY as [QS_STATES QS_CLOSED]. split.
  - intros q' IN.
    pose proof (subset_transition_sound _ _ _ IN) as (q & q1 & IN_QS & STEP & CLOS).
    eapply TaggedENFA.eclosure_okay with (M := M) (q1 := q1); eauto.
    pose proof OKAY as [_ _ _ CHAR_OKAY]. eapply CHAR_OKAY; eauto.
  - intros q q' IN CLOS. unfold subset_transition in *.
    eapply eclose_closed with (q := q); eauto.
    destruct OKAY as [_ _ _ CHAR_OKAY]. done.
Qed.

Lemma subset_transition_in_subset_states (qs : subset_state) (c : ascii)
  : subset_transition qs c ∈ subset_states.
Proof.
  eapply eclose_in_subset_states.
Qed.

Definition subset_accept_states_of (qs : subset_state) : list (subset_state * Token.t) :=
  bind (isMonad := B.list_isMonad) M.(TaggedENFA.accept_states).(kvlist) (fun '(q, tag) => if mem (EQ_DEC := M.(TaggedENFA.state_hasEqDec)) q qs then pure (isMonad := B.list_isMonad) (qs, tag) else []).

Definition subset_accept_states : list (subset_state * Token.t) :=
  bind (isMonad := B.list_isMonad) subset_states subset_accept_states_of.

Lemma subset_accept_states_of_complete (qs : subset_state) (q : Q) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ M.(TaggedENFA.accept_states).(kvlist))
  (IN : q ∈ qs)
  : (qs, tag) ∈ subset_accept_states_of qs.
Proof.
  eapply in_list_bind_intro with (x := (q, tag)); eauto. des_ifs; ss!.
Qed.

Lemma subset_accept_states_of_sound (qs : subset_state) (qs' : subset_state) (tag : Token.t)
  (ACCEPT : (qs', tag) ∈ subset_accept_states_of qs)
  : qs = qs' /\ (exists q : Q, (q, tag) ∈ M.(TaggedENFA.accept_states).(kvlist) /\ q ∈ qs).
Proof.
  unfold subset_accept_states_of in ACCEPT.
  pose proof (in_list_bind_elim _ _ _ ACCEPT) as ([q tag'] & ACCEPT' & IN).
  des_ifs; ss!.
Qed.

Lemma subset_accept_states_complete (qs : subset_state) (q : Q) (tag : Token.t)
  (QS : qs ∈ subset_states)
  (ACCEPT : (q, tag) ∈ M.(TaggedENFA.accept_states).(kvlist))
  (IN : q ∈ qs)
  : (qs, tag) ∈ subset_accept_states.
Proof.
  eapply in_list_bind_intro with (x := qs); eauto.
  eapply subset_accept_states_of_complete; eauto.
Qed.

Lemma subset_accept_states_sound (qs : subset_state) (tag : Token.t)
  (ACCEPT : (qs, tag) ∈ subset_accept_states)
  : qs ∈ subset_states /\ (exists q, (q, tag) ∈ M.(TaggedENFA.accept_states).(kvlist) /\ q ∈ qs).
Proof.
  unfold subset_accept_states in ACCEPT.
  pose proof (in_list_bind_elim _ _ _ ACCEPT) as (qs' & QS & ACCEPT').
  pose proof (subset_accept_states_of_sound qs' qs tag ACCEPT') as (EQ & q & ACCEPT_Q & IN).
  subst qs'; eauto.
Qed.

Definition subset_state_ensemble (qs : subset_state) : ensemble Q :=
  fun q => q ∈ qs.

Definition normalize_ensemble (qs : subset_state) : ensemble Q :=
  fun q => q ∈ M.(TaggedENFA.states) /\ q ∈ qs.

Definition move_ensemble (qs : subset_state) (c : ascii) : ensemble Q :=
  fun q' => exists q, q ∈ qs /\ q' ∈ M.(TaggedENFA.char_step) q c.

Definition eps_move_ensemble (qs : subset_state) : ensemble Q :=
  fun q' => exists q, q ∈ qs /\ q' ∈ M.(TaggedENFA.eps_step) q.

Definition eclose_ensemble (qs : subset_state) : ensemble Q :=
  fun q' => exists q, q ∈ qs /\ q' \in eclosure q.

Definition subset_transition_ensemble (qs : subset_state) (c : ascii) : ensemble Q :=
  fun q' => exists q, exists q1, q ∈ qs /\ q1 ∈ M.(TaggedENFA.char_step) q c /\ q' \in eclosure q1.

Definition subset_accept_state_ensemble : ensemble (subset_state * Token.t) :=
  fun '(qs, tag) => qs ∈ subset_states /\ (exists q, (q, tag) ∈ M.(TaggedENFA.accept_states).(kvlist) /\ q ∈ qs).

Corollary subset_membership_similarity (qs : subset_state) (q : Q)
  : is_similar_to (Similarity := Similarity_bool_Prop) (mem (EQ_DEC := M.(TaggedENFA.state_hasEqDec)) q qs) (q ∈ qs).
Proof.
  do 2 red. des_ifs; ss!.
Qed.

Corollary normalize_similarity (qs : subset_state)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (normalize qs) (normalize_ensemble qs).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q. split.
  - intros IN. done.
  - intros [STATES IN_QS]. done.
Qed.

Corollary normalize_membership_similarity (qs : subset_state) (q : Q)
  : is_similar_to (Similarity := Similarity_bool_Prop) (mem (EQ_DEC := M.(TaggedENFA.state_hasEqDec)) q (normalize qs)) (q ∈ M.(TaggedENFA.states) /\ q ∈ qs).
Proof.
  do 2 red. des_ifs; ss!.
Qed.

Corollary move_similarity (qs : subset_state) (c : ascii)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (move qs c) (move_ensemble qs c).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q'. split.
  - done.
  - intros (q & IN_QS & STEP). done.
Qed.

Lemma eps_move_similarity (qs : subset_state)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (eps_move qs) (eps_move_ensemble qs).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q'. split.
  - done.
  - intros (q & IN_QS & STEP). done.
Qed.

Lemma eclose_similarity (qs : subset_state)
  (OKAY : TaggedENFA.okay M)
  (QS_STATES : forall q, q ∈ qs -> q ∈ M.(TaggedENFA.states))
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (eclose qs) (eclose_ensemble qs).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q'. split.
  - eapply eclose_sound.
  - intros (q & IN_QS & CLOS). eapply eclose_complete; eauto.
Qed.

Lemma subset_transition_similarity (qs : subset_state) (c : ascii)
  (OKAY : TaggedENFA.okay M)
  (QS_STATES : forall q, q ∈ qs -> q ∈ M.(TaggedENFA.states))
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (subset_transition qs c) (subset_transition_ensemble qs c).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q'. split.
  - eapply subset_transition_sound.
  - intros (q & q1 & IN_QS & STEP & CLOS). eapply subset_transition_complete; eauto.
Qed.

Lemma subset_accept_states_similarity
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) subset_accept_states subset_accept_state_ensemble.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros [qs tag]. split.
  - intros ACCEPT. pose proof (subset_accept_states_sound qs tag ACCEPT) as [QS ACCEPT_Q]. split; eauto.
  - intros [QS (q & ACCEPT_Q & IN_QS)]. eapply subset_accept_states_complete; eauto.
Qed.

Definition subset_construct : TaggedDFA.t :=
  {|
    state := subset_state;
    state_hasEqDec := list_hasEqDec M.(TaggedENFA.state_hasEqDec);
    states := subset_states;
    start_state := subset_start_state;
    accept_states := {| kvlist := subset_accept_states |};
    transition := subset_transition;
  |}.

Lemma subset_delta_in_subset_states (qs : subset_state) (s : Input.t)
  (QS : qs ∈ subset_states)
  : TaggedDFA.delta subset_construct qs s ∈ subset_states.
Proof.
  revert qs QS; induction s as [ | c s IH]; ii; simpl; eauto.
  eapply IH. eapply subset_transition_in_subset_states.
Qed.

Lemma subset_delta_sound' (qs : subset_state) (s : Input.t) (q' : Q)
  (IN : q' ∈ TaggedDFA.delta subset_construct qs s)
  : exists q, q ∈ qs /\ q' \in delta_star q s.
Proof.
  revert qs q' IN; induction s as [ | c s IH]; ii; simpl in IN.
  - exists q'. done.
  - pose proof (IH _ _ IN) as (q1 & IN_TRANS & REST).
    pose proof (subset_transition_sound _ _ _ IN_TRANS) as (q0 & qchar & IN_QS & STEP & CLOS).
    exists q0. split; eauto.
    eapply TaggedENFA.delta_star_char; eauto.
    eapply TaggedENFA.delta_star_app with (eps_step := M.(TaggedENFA.eps_step)) (char_step := M.(TaggedENFA.char_step)) (q1 := qchar) (q2 := q1) (s1 := []) (s2 := s); eauto.
    now rewrite -> TaggedENFA.delta_star_nil_iff_eclosure with (q := qchar) (q' := q1).
Qed.

Theorem subset_construct_sound (s : Input.t) (tag : Token.t)
  (ACCEPT : TaggedDFA.accepts subset_construct s tag)
  : TaggedENFA.accepts M s tag.
Proof.
  unfold TaggedDFA.accepts in ACCEPT.
  assert ((delta subset_construct (start_state subset_construct) s, tag) \in subset_accept_state_ensemble) as (_ & qf & ACCEPT_Q & IN_QS).
  { pose proof (subset_accept_states_similarity) as HH.
    rewrite list_corresponds_to_finite_ensemble_iff in HH.
    done.
  }
  unfold TaggedENFA.accepts. exists qf. split; eauto.
  pose proof (subset_delta_sound' _ _ _ IN_QS) as (q0 & IN_START & REST).
  pose proof (subset_start_state_sound _ IN_START) as CLOS.
  eapply TaggedENFA.delta_star_app with (q1 := M.(TaggedENFA.start_state)) (q2 := q0) (q3 := qf) (s1 := []) (s2 := s); eauto.
  now rewrite -> TaggedENFA.delta_star_nil_iff_eclosure with (q := M.(TaggedENFA.start_state)) (q' := q0).
Qed.

Lemma subset_delta_complete' (s : Input.t) (q : Q) (q' : Q)
  (OKAY : TaggedENFA.okay M)
  (DELTA : q' \in delta_star q s)
  : forall qs, subset_state_okay qs -> q ∈ qs -> q' ∈ TaggedDFA.delta subset_construct qs s.
Proof.
  induction DELTA as [q | q q1 q2 s STEP REST IH | q q1 q2 c s STEP REST IH]; intros qs QS_OKAY IN; simpl.
  - exact IN.
  - eapply IH with (qs := qs); auto.
    destruct QS_OKAY as [_ QS_CLOSED]. eapply QS_CLOSED with (q := q); eauto.
  - eapply IH.
    + eapply subset_transition_okay; eauto.
    + eapply subset_transition_complete with (q := q) (q1 := q1); eauto.
      now destruct QS_OKAY as [QS_STATES _].
Qed.

Theorem subset_construct_complete (s : Input.t) (tag : Token.t)
  (OKAY : TaggedENFA.okay M)
  (ACCEPT : TaggedENFA.accepts M s tag)
  : TaggedDFA.accepts subset_construct s tag.
Proof.
  unfold TaggedENFA.accepts in ACCEPT. destruct ACCEPT as (qf & DELTA & ACCEPT_Q).
  enough (WTS : (delta subset_construct subset_start_state s, tag) \in subset_accept_state_ensemble).
  { unfold TaggedDFA.accepts. simpl.
    pose proof subset_accept_states_similarity as HH.
    rewrite list_corresponds_to_finite_ensemble_iff in HH.
    now rewrite -> HH.
  }
  simpl. split.
  - eapply subset_delta_in_subset_states. eapply eclose_in_subset_states.
  - exists qf. split; auto.
    eapply subset_delta_complete' with (q := M.(TaggedENFA.start_state)); eauto.
    + eapply subset_start_state_okay; eauto.
    + eapply subset_start_state_complete; eauto.
Qed.

Theorem subset_construct_okay
  (OKAY : TaggedENFA.okay M)
  : okay subset_construct.
Proof.
  split; simpl.
  - eapply eclose_in_subset_states.
  - intros qs tag ACCEPT.
    now pose proof (subset_accept_states_sound qs tag ACCEPT) as [? _].
  - ii. eapply subset_transition_in_subset_states.
Qed.

End SUBSET_CONSTRUCTION.

Section MINIMISATION.

Variable M : TaggedDFA.t.

#[local] Abbreviation Q := M.(TaggedDFA.state).

Definition accepts_from (q : Q) (s : Input.t) (tag : Token.t) : Prop :=
  (delta M q s, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).

Definition right_language_equiv (q1 : Q) (q2 : Q) : Prop :=
  forall s, forall tag, accepts_from q1 s tag <-> accepts_from q2 s tag.

Definition state_ensemble : ensemble Q :=
  fun q => q ∈ M.(TaggedDFA.states).

Definition accept_state_ensemble : ensemble (Q * Token.t) :=
  fun qtag => qtag ∈ M.(TaggedDFA.accept_states).(kvlist).

Definition accepting_tags_from (q : Q) : list Token.t :=
  bind (isMonad := B.list_isMonad) M.(TaggedDFA.accept_states).(kvlist) (fun '(q', tag) => if eq_dec (hasEqDec := M.(TaggedDFA.state_hasEqDec)) q q' then pure (isMonad := B.list_isMonad) tag else []).

Lemma accepting_tags_from_complete (q : Q) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  : tag ∈ accepting_tags_from q.
Proof.
  eapply in_list_bind_intro with (x := (q, tag)); eauto.
  des_ifs; ss!.
Qed.

Lemma accepting_tags_from_sound (q : Q) (tag : Token.t)
  (ACCEPT : tag ∈ accepting_tags_from q)
  : (q, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).
Proof.
  pose proof (in_list_bind_elim _ _ _ ACCEPT) as ([q' tag'] & ACCEPT' & IN).
  des_ifs; ss!.
Qed.

Definition accepting_tag_ensemble (q : Q) : ensemble Token.t :=
  fun tag => (q, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).

Lemma accepting_tags_from_similarity (q : Q)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (accepting_tags_from q) (accepting_tag_ensemble q).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff.
  intros tag; split; i.
  - now eapply accepting_tags_from_sound.
  - now eapply accepting_tags_from_complete.
Qed.

Definition same_accepting_tagsb (q1 : Q) (q2 : Q) : bool :=
  forallb (fun '(_, tag) => eqb (mem (q1, tag) M.(TaggedDFA.accept_states).(kvlist)) (mem (q2, tag) M.(TaggedDFA.accept_states).(kvlist))) M.(TaggedDFA.accept_states).(kvlist).

Definition same_accepting_tags (q1 : Q) (q2 : Q) : Prop :=
  forall tag, (q1, tag) ∈ M.(TaggedDFA.accept_states).(kvlist) <-> (q2, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).

Lemma right_language_equiv_step (q1 : Q) (q2 : Q) (c : ascii)
  (SAME : right_language_equiv q1 q2)
  : right_language_equiv (M.(TaggedDFA.transition) q1 c) (M.(TaggedDFA.transition) q2 c).
Proof.
  intros s tag. now pose proof (SAME (c :: s) tag).
Qed.

Lemma right_language_equiv_same_accepting_tags (q1 : Q) (q2 : Q)
  (SAME : right_language_equiv q1 q2)
  : same_accepting_tags q1 q2.
Proof.
  intros tag. now pose proof (SAME [] tag).
Qed.

Lemma same_accepting_tagsb_sound (q1 : Q) (q2 : Q) (tag : Token.t)
  (SAME : same_accepting_tagsb q1 q2 = true)
  (ACCEPT : (q1, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  : (q2, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).
Proof.
  unfold same_accepting_tagsb in SAME. rewrite forallb_forall in SAME.
  pose proof (SAME (q1, tag) ACCEPT) as EQB. simpl in EQB.
  assert (MEM1 : mem (q1, tag) M.(TaggedDFA.accept_states).(kvlist) = true) by done.
  rewrite -> MEM1, -> eqb_eq in EQB. symmetry in EQB. ss!.
Qed.

Lemma same_accepting_tagsb_complete (q1 : Q) (q2 : Q) (tag : Token.t)
  (SAME : same_accepting_tagsb q1 q2 = true)
  (ACCEPT : (q2, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  : (q1, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).
Proof.
  unfold same_accepting_tagsb in SAME. rewrite forallb_forall in SAME.
  pose proof (SAME (q2, tag) ACCEPT) as EQB. simpl in EQB.
  assert (MEM2 : mem (q2, tag) M.(TaggedDFA.accept_states).(kvlist) = true) by done.
  rewrite MEM2 in EQB. rewrite eqb_eq in EQB. ss!.
Qed.

Lemma same_accepting_tagsb_false_distinguish (q1 : Q) (q2 : Q)
  (SAME : same_accepting_tagsb q1 q2 = false)
  : exists tag, (accepts_from q1 [] tag /\ ~ accepts_from q2 [] tag) \/ (accepts_from q2 [] tag /\ ~ accepts_from q1 [] tag).
Proof.
  pose proof (forallb_false_exists _ _ SAME) as ([q tag] & _ & EQB). simpl in EQB.
  destruct (mem (q1, tag) M.(TaggedDFA.accept_states).(kvlist)) eqn: MEM1, (mem (q2, tag) M.(TaggedDFA.accept_states).(kvlist)) eqn: MEM2; simpl in EQB; inv EQB.
  - exists tag. left. split; unfold accepts_from; ss!.
  - exists tag. right. split; unfold accepts_from; ss!.
Qed.

Lemma same_accepting_tagsb_similarity (q1 : Q) (q2 : Q)
  : is_similar_to (Similarity := Similarity_bool_Prop) (same_accepting_tagsb q1 q2) (same_accepting_tags q1 q2).
Proof.
  do 2 red; des_ifs.
  - intros tag. split.
    + now eapply same_accepting_tagsb_sound.
    + now eapply same_accepting_tagsb_complete.
  - intros SAME_PROP.
    pose proof (same_accepting_tagsb_false_distinguish q1 q2 Heq) as (tag & [(ACCEPT & NOT_ACCEPT) | (ACCEPT & NOT_ACCEPT)]); unfold accepts_from in *; ss!.
Qed.

Definition transition_alist : alist (Q * ascii) Q :=
  {| kvlist := bind (isMonad := B.list_isMonad) M.(TaggedDFA.states) (fun q => bind (isMonad := B.list_isMonad) all_asciis (fun c => pure (isMonad := B.list_isMonad) ((q, c), M.(TaggedDFA.transition) q c))) |}.

Definition transition_partial_map (qc : Q * ascii) : option Q :=
  if mem (EQ_DEC := M.(state_hasEqDec)) (fst qc) M.(TaggedDFA.states) then
    Some (M.(TaggedDFA.transition) (fst qc) (snd qc))
  else
    None.

Lemma transition_alist_similarity
  : is_similar_to (Similarity := alist_corresponds_to_finite_partial_map) transition_alist transition_partial_map.
Proof.
  rewrite alist_corresponds_to_finite_partial_map_iff. intros [q c] q'. split.
  - intros IN. cbv [transition_alist] in IN. cbn [kvlist] in IN.
    pose proof (in_list_bind_elim _ _ _ IN) as (q0 & IN_Q0 & IN_C).
    pose proof (in_list_bind_elim _ _ _ IN_C) as (c0 & _ & IN_ENTRY).
    simpl in IN_ENTRY. destruct IN_ENTRY as [EQ | []]. inv EQ.
    assert (MEM : mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q M.(TaggedDFA.states) = true) by now rewrite mem_spec. 
    now unfold transition_partial_map; simpl; rewrite MEM.
  - intros FIND. unfold transition_partial_map in FIND. simpl in FIND.
    destruct (mem q M.(TaggedDFA.states)) eqn: MEM; inv FIND.
    cbv [transition_alist]. cbn [kvlist].
    eapply in_list_bind_intro with (x := q); [now rewrite mem_spec in MEM | ].
    eapply in_list_bind_intro with (x := c); [eapply in_all_asciis_intro | ].
    s!; tauto.
Qed.

Variant DFA_ACCEPTANCE_COMPUTATION_SPEC : Prop :=
  | dfa_acceptance_computation_spec_intro
    (states_sim : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) M.(TaggedDFA.states) state_ensemble)
    (accept_states_sim : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) M.(TaggedDFA.accept_states).(kvlist) accept_state_ensemble)
    (accepting_tags_sim : forall q, is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (accepting_tags_from q) (accepting_tag_ensemble q))
    (same_accepting_tags_sim : forall q1, forall q2, is_similar_to (Similarity := Similarity_bool_Prop) (same_accepting_tagsb q1 q2) (same_accepting_tags q1 q2))
    (transition_sim : is_similar_to (Similarity := alist_corresponds_to_finite_partial_map) transition_alist transition_partial_map).

Theorem dfa_acceptance_computation_okay
  : DFA_ACCEPTANCE_COMPUTATION_SPEC.
Proof.
  split.
  - rewrite list_corresponds_to_finite_ensemble_iff. intros q. split; intros IN; exact IN.
  - rewrite list_corresponds_to_finite_ensemble_iff. intros qtag. split; intros IN; exact IN.
  - eapply accepting_tags_from_similarity.
  - eapply same_accepting_tagsb_similarity.
  - eapply transition_alist_similarity.
Qed.

Definition hopcroft_block : Set :=
  list Q.

Definition hopcroft_partition : Set :=
  list hopcroft_block.

Definition hopcroft_splitter : Set :=
  hopcroft_block * ascii.

Definition hopcroft_worklist : Set :=
  list hopcroft_splitter.

Definition hopcroft_block_ensemble (block : hopcroft_block) : ensemble Q :=
  fun q => q ∈ block.

Definition hopcroft_predecessors (block : hopcroft_block) (c : ascii) : hopcroft_block :=
  filter (fun q => mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) (M.(TaggedDFA.transition) q c) block) M.(TaggedDFA.states).

Definition hopcroft_predecessor_ensemble (block : hopcroft_block) (c : ascii) : ensemble Q :=
  fun q => q ∈ M.(TaggedDFA.states) /\ M.(TaggedDFA.transition) q c ∈ block.

Lemma hopcroft_predecessors_similarity (block : hopcroft_block) (c : ascii)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (hopcroft_predecessors block c) (hopcroft_predecessor_ensemble block c).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q. split; [intros IN | intros [STATE IN]].
  - unfold hopcroft_predecessors in IN. s!. destruct IN as [STATE MEM].
    unfold hopcroft_predecessor_ensemble. done.
  - unfold hopcroft_predecessors. done.
Qed.

Lemma hopcroft_predecessors_iff (block : hopcroft_block) (c : ascii)
  : forall q, q ∈ hopcroft_predecessors block c <-> (q ∈ M.(TaggedDFA.states) /\ M.(TaggedDFA.transition) q c ∈ block).
Proof.
  unfold hopcroft_predecessors. done.
Qed.

Definition hopcroft_block_intersection (block : hopcroft_block) (splitter : hopcroft_block) : hopcroft_block :=
  filter (fun q => mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q splitter) block.

Definition hopcroft_block_difference (block : hopcroft_block) (splitter : hopcroft_block) : hopcroft_block :=
  filter (fun q => negb (mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q splitter)) block.

Definition hopcroft_block_intersection_ensemble (block : hopcroft_block) (splitter : hopcroft_block) : ensemble Q :=
  fun q => q ∈ block /\ q ∈ splitter.

Definition hopcroft_block_difference_ensemble (block : hopcroft_block) (splitter : hopcroft_block) : ensemble Q :=
  fun q => q ∈ block /\ ~ q ∈ splitter.

Lemma hopcroft_block_intersection_similarity (block : hopcroft_block) (splitter : hopcroft_block)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (hopcroft_block_intersection block splitter) (hopcroft_block_intersection_ensemble block splitter).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q. split; [intros IN | intros [IN_BLOCK IN_SPLITTER]].
  - unfold hopcroft_block_intersection in IN. s!. destruct IN as [IN_BLOCK MEM].
    unfold hopcroft_block_intersection_ensemble. done.
  - unfold hopcroft_block_intersection. done.
Qed.

Lemma hopcroft_block_difference_similarity (block : hopcroft_block) (splitter : hopcroft_block)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (hopcroft_block_difference block splitter) (hopcroft_block_difference_ensemble block splitter).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q. split; [intros IN | intros [IN_BLOCK NOT_IN]].
  - unfold hopcroft_block_difference in IN. s!. destruct IN as [IN_BLOCK MEM].
    unfold hopcroft_block_difference_ensemble. done.
  - unfold hopcroft_block_difference. done.
Qed.  

Definition hopcroft_all_splitters (partition : hopcroft_partition) : hopcroft_worklist :=
  partition >>= fun block => all_asciis >>= fun c => pure (block, c).

Definition hopcroft_worklist_valid (partition : hopcroft_partition) (worklist : hopcroft_worklist) : Prop :=
  forall block, forall c, (block, c) ∈ worklist -> block ∈ partition /\ c ∈ all_asciis.

Lemma hopcroft_all_splitters_valid (partition : hopcroft_partition)
  : hopcroft_worklist_valid partition (hopcroft_all_splitters partition).
Proof.
  intros block c IN. unfold hopcroft_all_splitters in IN.
  pose proof (in_list_bind_elim _ _ _ IN) as (block0 & BLOCK & IN_C).
  pose proof (in_list_bind_elim _ _ _ IN_C) as (c0 & C & IN_PAIR).
  simpl in IN_PAIR. destruct IN_PAIR as [EQ | []]. inv EQ. split; eauto.
Qed.

Lemma hopcroft_all_splitters_complete (partition : hopcroft_partition) (block : hopcroft_block) (c : ascii)
  (BLOCK : block ∈ partition)
  : (block, c) ∈ hopcroft_all_splitters partition.
Proof.
  unfold hopcroft_all_splitters.
  eapply in_list_bind_intro with (x := block); auto.
  eapply in_list_bind_intro with (x := c).
  - eapply in_all_asciis_intro.
  - s!; tauto.
Qed.

Definition hopcroft_smaller_block (block1 : hopcroft_block) (block2 : hopcroft_block) : hopcroft_block :=
  if Nat.leb (length block1) (length block2) then block1 else block2.

Lemma hopcroft_smaller_block_in_pieces (block1 : hopcroft_block) (block2 : hopcroft_block)
  : hopcroft_smaller_block block1 block2 = block1 \/ hopcroft_smaller_block block1 block2 = block2.
Proof.
  unfold hopcroft_smaller_block. destruct (Nat.leb (length block1) (length block2)); tauto.
Qed.

Definition hopcroft_worklist_mentions (block : hopcroft_block) (worklist : hopcroft_worklist) : bool :=
  existsb (fun '(block', _) => @eqb (list Q) (list_hasEqDec M.(TaggedDFA.state_hasEqDec)) block' block) worklist.

Definition hopcroft_update_splitter (old_block : hopcroft_block) (block1 : hopcroft_block) (block2 : hopcroft_block) (splitter : hopcroft_splitter) : hopcroft_worklist :=
  let '(block', c) := splitter in
  if @eq_dec (list Q) (list_hasEqDec M.(TaggedDFA.state_hasEqDec)) block' old_block then
    [(block1, c); (block2, c)]
  else
    [splitter].

Definition hopcroft_update_worklist (worklist : hopcroft_worklist) (old_block : hopcroft_block) (block1 : hopcroft_block) (block2 : hopcroft_block) : hopcroft_worklist :=
  let worklist' : hopcroft_worklist := worklist >>= hopcroft_update_splitter old_block block1 block2 in
  if hopcroft_worklist_mentions old_block worklist then
    worklist'
  else
    worklist' ++ hopcroft_all_splitters [hopcroft_smaller_block block1 block2].

Lemma hopcroft_update_worklist_valid_prefix (prefix : hopcroft_partition) (partition : hopcroft_partition) (worklist : hopcroft_worklist) (old_block : hopcroft_block) (block1 : hopcroft_block) (block2 : hopcroft_block)
  (VALID : hopcroft_worklist_valid (prefix ++ old_block :: partition) worklist)
  : hopcroft_worklist_valid (prefix ++ block1 :: block2 :: partition) (hopcroft_update_worklist worklist old_block block1 block2).
Proof.
  intros block c IN. unfold hopcroft_update_worklist in IN.
  destruct (hopcroft_worklist_mentions old_block worklist) eqn: MENTIONS.
  - pose proof (in_list_bind_elim _ _ _ IN) as ([block0 c0] & IN_WORKLIST & IN_UPDATE).
    unfold hopcroft_update_splitter in IN_UPDATE.
    destruct (eq_dec _ _) as [EQ | NE].
    + subst block0. simpl in IN_UPDATE.
      pose proof (VALID old_block c0 IN_WORKLIST) as [_ CHAR].
      destruct IN_UPDATE as [EQ | [EQ | []]]; inv EQ; split; ss!.
    + simpl in IN_UPDATE. destruct IN_UPDATE as [EQ | []]. inv EQ.
      pose proof (VALID block c IN_WORKLIST) as [BLOCK CHAR].
      split; auto. rewrite in_app_iff in BLOCK |- *.
      destruct BLOCK as [IN_PREFIX | [EQ | IN_PARTITION]]; done.
  - rewrite in_app_iff in IN. destruct IN as [IN | IN].
    + pose proof (in_list_bind_elim _ _ _ IN) as ([block0 c0] & IN_WORKLIST & IN_UPDATE).
      unfold hopcroft_update_splitter in IN_UPDATE.
      destruct (@eq_dec (list Q) (list_hasEqDec M.(TaggedDFA.state_hasEqDec)) block0 old_block) as [EQ | NE].
      * subst block0. simpl in IN_UPDATE.
        pose proof (VALID old_block c0 IN_WORKLIST) as [_ CHAR].
        destruct IN_UPDATE as [EQ | [EQ | []]]; inv EQ; split; ss!.
      * simpl in IN_UPDATE. destruct IN_UPDATE as [EQ | []]. inv EQ.
        pose proof (VALID block c IN_WORKLIST) as [BLOCK CHAR].
        split; auto. rewrite in_app_iff in BLOCK |- *.
        destruct BLOCK as [IN_PREFIX | [EQ | IN_PARTITION]]; done.
    + pose proof (hopcroft_all_splitters_valid [hopcroft_smaller_block block1 block2] block c IN) as [BLOCK CHAR].
      simpl in BLOCK. destruct BLOCK as [EQ | []]. subst block.
      pose proof (hopcroft_smaller_block_in_pieces block1 block2) as [EQ | EQ]; rewrite EQ; split.
      * rewrite in_app_iff. simpl. tauto.
      * exact CHAR.
      * rewrite in_app_iff. simpl. tauto.
      * exact CHAR.
Qed.

Definition hopcroft_split_block (splitter : hopcroft_block) (block : hopcroft_block) : list hopcroft_block :=
  let block1 : hopcroft_block := hopcroft_block_intersection block splitter in
  let block2 : hopcroft_block := hopcroft_block_difference block splitter in
  if nonempty block1 && nonempty block2 then
    [block1; block2]
  else
    [block].

Fixpoint hopcroft_refine_partition (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist) {struct partition} : hopcroft_partition * hopcroft_worklist :=
  match partition with
  | [] => ([], worklist)
  | block :: partition' =>
    let block1 := hopcroft_block_intersection block splitter in
    let block2 := hopcroft_block_difference block splitter in
    let '(partition'', worklist') := hopcroft_refine_partition splitter partition' worklist in
    if nonempty block1 && nonempty block2 then
      (block1 :: block2 :: partition'', hopcroft_update_worklist worklist' block block1 block2)
    else
      (block :: partition'', worklist')
  end.

Lemma hopcroft_refine_partition_worklist_valid_prefix (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist) (prefix : hopcroft_partition)
  (VALID : hopcroft_worklist_valid (prefix ++ partition) worklist)
  : hopcroft_worklist_valid (prefix ++ fst (hopcroft_refine_partition splitter partition worklist)) (snd (hopcroft_refine_partition splitter partition worklist)).
Proof.
  revert worklist prefix VALID. induction partition as [ | old_block partition IH]; intros worklist prefix VALID; simpl.
  - exact VALID.
  - set (block1 := hopcroft_block_intersection old_block splitter).
    set (block2 := hopcroft_block_difference old_block splitter).
    assert (VALID_TAIL : hopcroft_worklist_valid ((prefix ++ [old_block]) ++ partition) worklist).
    { intros block c IN.
      pose proof (VALID block c IN) as [BLOCK CHAR].
      split; auto. rewrite !in_app_iff in BLOCK |- *.
      destruct BLOCK as [IN_PREFIX | [EQ | IN_PARTITION]].
      - left. rewrite in_app_iff; simpl; tauto.
      - left. rewrite in_app_iff; simpl; tauto.
      - right. tauto.
    }
    pose proof (IH worklist (prefix ++ [old_block]) VALID_TAIL) as VALID_REFINED_TAIL.
    destruct (hopcroft_refine_partition splitter partition worklist) as [partition' worklist'] eqn: REFINE. simpl in VALID_REFINED_TAIL.
    replace ((prefix ++ [old_block]) ++ partition') with (prefix ++ old_block :: partition') in VALID_REFINED_TAIL by (rewrite <- app_assoc; reflexivity).
    destruct (nonempty block1 && nonempty block2) eqn: SPLIT; simpl.
    + eapply hopcroft_update_worklist_valid_prefix. exact VALID_REFINED_TAIL.
    + exact VALID_REFINED_TAIL.
Qed.

Lemma hopcroft_refine_partition_worklist_valid (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist)
  (VALID : hopcroft_worklist_valid partition worklist)
  : hopcroft_worklist_valid (fst (hopcroft_refine_partition splitter partition worklist)) (snd (hopcroft_refine_partition splitter partition worklist)).
Proof.
  now pose proof (hopcroft_refine_partition_worklist_valid_prefix splitter partition worklist [] VALID) as VALID'.
Qed.

Definition hopcroft_accepting_class (q : Q) : hopcroft_block :=
  filter (same_accepting_tagsb q) M.(TaggedDFA.states).

Definition hopcroft_initial_partition : hopcroft_partition :=
  L.nodup (@eq_dec (list Q) (list_hasEqDec M.(TaggedDFA.state_hasEqDec))) (map hopcroft_accepting_class M.(TaggedDFA.states)).

Definition hopcroft_initial_worklist : hopcroft_worklist :=
  hopcroft_all_splitters hopcroft_initial_partition.

Lemma hopcroft_initial_worklist_valid
  : hopcroft_worklist_valid hopcroft_initial_partition hopcroft_initial_worklist.
Proof.
  unfold hopcroft_initial_worklist. eapply hopcroft_all_splitters_valid.
Qed.

Definition hopcroft_config : Set :=
  hopcroft_partition * hopcroft_worklist.

Definition hopcroft_step_config (config : hopcroft_config) : hopcroft_config :=
  let '(partition, worklist) := config in
  match worklist with
  | [] => config
  | (active, c) :: worklist' => hopcroft_refine_partition (hopcroft_predecessors active c) partition worklist'
  end.

Definition hopcroft_fuel : nat :=
  length M.(TaggedDFA.states) * length M.(TaggedDFA.states) * length all_asciis + length M.(TaggedDFA.states) + 1.

Definition hopcroft_initial_config : hopcroft_config :=
  (hopcroft_initial_partition, hopcroft_initial_worklist).

Definition hopcroft_final_config : hopcroft_config :=
  iter hopcroft_fuel hopcroft_step_config hopcroft_initial_config.

Definition hopcroft_final_partition : hopcroft_partition :=
  fst hopcroft_final_config.

Variant HOPCROFT_COMPUTATION_SURFACE_SPEC : Prop :=
  | hopcroft_computation_surface_spec_intro
    (predecessors_sim : forall block, forall c, is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (hopcroft_predecessors block c) (hopcroft_predecessor_ensemble block c))
    (intersection_sim : forall block, forall splitter, is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (hopcroft_block_intersection block splitter) (hopcroft_block_intersection_ensemble block splitter))
    (difference_sim : forall block, forall splitter, is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (hopcroft_block_difference block splitter) (hopcroft_block_difference_ensemble block splitter)).

Lemma hopcroft_computation_surface_okay
  : HOPCROFT_COMPUTATION_SURFACE_SPEC.
Proof.
  constructor.
  - eapply hopcroft_predecessors_similarity.
  - eapply hopcroft_block_intersection_similarity.
  - eapply hopcroft_block_difference_similarity.
Qed.

Definition hopcroft_partition_blocks_in_states (partition : hopcroft_partition) : Prop :=
  forall block, block ∈ partition -> forall q, q ∈ block -> q ∈ M.(TaggedDFA.states).

Definition hopcroft_partition_blocks_nonempty (partition : hopcroft_partition) : Prop :=
  forall block, block ∈ partition -> nonempty block = true.

Definition hopcroft_partition_covers_states (partition : hopcroft_partition) : Prop :=
  forall q, q ∈ M.(TaggedDFA.states) -> (exists block, block ∈ partition /\ q ∈ block).

Definition hopcroft_partition_disjoint (partition : hopcroft_partition) : Prop :=
  forall block1, forall block2, forall q, block1 ∈ partition -> block2 ∈ partition -> q ∈ block1 -> q ∈ block2 -> block1 = block2.

Definition hopcroft_partition_respects_accepting_tags (partition : hopcroft_partition) : Prop :=
  forall block, forall q1, forall q2, block ∈ partition -> q1 ∈ block -> q2 ∈ block -> same_accepting_tags q1 q2.

Definition hopcroft_partition_relates (partition : hopcroft_partition) (q1 : Q) (q2 : Q) : Prop :=
  exists block, block ∈ partition /\ q1 ∈ block /\ q2 ∈ block.

Definition hopcroft_partition_stable (partition : hopcroft_partition) : Prop :=
  forall block, forall q1, forall q2, forall c, block ∈ partition -> q1 ∈ block -> q2 ∈ block -> hopcroft_partition_relates partition (M.(TaggedDFA.transition) q1 c) (M.(TaggedDFA.transition) q2 c).

Definition hopcroft_partition_stable_for_splitter (partition : hopcroft_partition) (active : hopcroft_block) (c : ascii) : Prop :=
  forall block, forall q1, forall q2, block ∈ partition -> q1 ∈ block -> q2 ∈ block -> (M.(TaggedDFA.transition) q1 c ∈ active <-> M.(TaggedDFA.transition) q2 c ∈ active).

Definition hopcroft_partition_preserves_right_language (partition : hopcroft_partition) : Prop :=
  forall block, forall q1, forall q2, block ∈ partition -> q1 ∈ block -> q2 ∈ M.(TaggedDFA.states) -> right_language_equiv q1 q2 -> q2 ∈ block.

Definition hopcroft_same_blockb (partition : hopcroft_partition) (q1 : Q) (q2 : Q) : bool :=
  existsb (fun block => mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q1 block && mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q2 block) partition.

Definition hopcroft_block_stableb (partition : hopcroft_partition) (block : hopcroft_block) (c : ascii) : bool :=
  forallb (fun q1 => forallb (fun q2 => hopcroft_same_blockb partition (M.(TaggedDFA.transition) q1 c) (M.(TaggedDFA.transition) q2 c)) block) block.

Definition hopcroft_partition_stableb (partition : hopcroft_partition) : bool :=
  forallb (fun block => forallb (fun c => hopcroft_block_stableb partition block c) all_asciis) partition.

Variant HOPCROFT_PARTITION_BASIC_SPEC (partition : hopcroft_partition) : Prop :=
  | hopcroft_partition_basic_spec_intro
    (partition_NoDup : NoDup partition)
    (blocks_nonempty : hopcroft_partition_blocks_nonempty partition)
    (blocks_in_states : hopcroft_partition_blocks_in_states partition)
    (covers_states : hopcroft_partition_covers_states partition)
    (disjoint : hopcroft_partition_disjoint partition)
    (respects_accepting_tags : hopcroft_partition_respects_accepting_tags partition).

Lemma same_accepting_tagsb_same_accepting_tags (q1 : Q) (q2 : Q)
  (SAME : same_accepting_tagsb q1 q2 = true)
  : same_accepting_tags q1 q2.
Proof.
  intros tag. split.
  - eapply same_accepting_tagsb_sound. exact SAME.
  - eapply same_accepting_tagsb_complete. exact SAME.
Qed.

Lemma same_accepting_tags_same_accepting_tagsb (q1 : Q) (q2 : Q)
  (SAME : same_accepting_tags q1 q2)
  : same_accepting_tagsb q1 q2 = true.
Proof.
  destruct (same_accepting_tagsb q1 q2) eqn: SAMEB; [reflexivity | ].
  pose proof (same_accepting_tagsb_similarity q1 q2) as SIM.
  change (if same_accepting_tagsb q1 q2 then same_accepting_tags q1 q2 else ~ same_accepting_tags q1 q2) in SIM.
  now rewrite SAMEB in SIM.
Qed.

Lemma hopcroft_same_blockb_sound (partition : hopcroft_partition) (q1 : Q) (q2 : Q)
  (SAME : hopcroft_same_blockb partition q1 q2 = true)
  : hopcroft_partition_relates partition q1 q2.
Proof.
  unfold hopcroft_same_blockb in SAME. red. done.
Qed.

Lemma hopcroft_partition_stableb_sound (partition : hopcroft_partition)
  (STABLE : hopcroft_partition_stableb partition = true)
  : hopcroft_partition_stable partition.
Proof.
  unfold hopcroft_partition_stableb in STABLE.
  rewrite forallb_forall in STABLE.
  intros block q1 q2 c BLOCK IN1 IN2.
  pose proof (STABLE block BLOCK) as BLOCK_STABLE.
  rewrite forallb_forall in BLOCK_STABLE.
  pose proof (BLOCK_STABLE c (in_all_asciis_intro c)) as CHAR_STABLE.
  unfold hopcroft_block_stableb in CHAR_STABLE.
  rewrite forallb_forall in CHAR_STABLE.
  pose proof (CHAR_STABLE q1 IN1) as Q1_STABLE.
  rewrite forallb_forall in Q1_STABLE.
  pose proof (Q1_STABLE q2 IN2) as SAME_BLOCK.
  eapply hopcroft_same_blockb_sound. exact SAME_BLOCK.
Qed.

Lemma hopcroft_accepting_class_contains (q : Q)
  (STATE : q ∈ M.(TaggedDFA.states))
  : q ∈ hopcroft_accepting_class q.
Proof.
  unfold hopcroft_accepting_class. rewrite filter_In. split; auto.
  unfold same_accepting_tagsb. ss!; des_ifs; ss!; des_ifs; ss!.
Qed.

Lemma hopcroft_accepting_class_states (q : Q) (q0 : Q)
  (IN : q0 ∈ hopcroft_accepting_class q)
  : q0 ∈ M.(TaggedDFA.states).
Proof.
  unfold hopcroft_accepting_class in IN. ss!.
Qed.

Lemma hopcroft_accepting_class_same (q : Q) (q0 : Q)
  (IN : q0 ∈ hopcroft_accepting_class q)
  : same_accepting_tags q q0.
Proof.
  unfold hopcroft_accepting_class in IN.
  eapply same_accepting_tagsb_same_accepting_tags. ss!.
Qed.

Lemma hopcroft_accepting_class_eq_of_same (q1 : Q) (q2 : Q)
  (SAME : same_accepting_tags q1 q2)
  : hopcroft_accepting_class q1 = hopcroft_accepting_class q2.
Proof.
  unfold hopcroft_accepting_class. eapply L.filter_ext_in. intros q STATE.
  destruct (same_accepting_tagsb q1 q) eqn: SAME1, (same_accepting_tagsb q2 q) eqn: SAME2; try reflexivity.
  - exfalso. pose proof (same_accepting_tagsb_same_accepting_tags q1 q SAME1) as SAME1_PROP.
    assert (SAME2_PROP : same_accepting_tags q2 q).
    { unfold same_accepting_tagsb in *. ss!. }
    pose proof (same_accepting_tags_same_accepting_tagsb q2 q SAME2_PROP) as SAME2_TRUE. rewrite SAME2 in SAME2_TRUE. inv SAME2_TRUE.
  - exfalso. pose proof (same_accepting_tagsb_same_accepting_tags q2 q SAME2) as SAME2_PROP.
    assert (SAME1_PROP : same_accepting_tags q1 q).
    { unfold same_accepting_tagsb in *. ss!. }
    pose proof (same_accepting_tags_same_accepting_tagsb q1 q SAME1_PROP) as SAME1_TRUE. rewrite SAME1 in SAME1_TRUE. inv SAME1_TRUE.
Qed.

Lemma hopcroft_accepting_class_eq_of_overlap (q1 : Q) (q2 : Q) (q : Q)
  (IN1 : q ∈ hopcroft_accepting_class q1)
  (IN2 : q ∈ hopcroft_accepting_class q2)
  : hopcroft_accepting_class q1 = hopcroft_accepting_class q2.
Proof.
  pose proof (hopcroft_accepting_class_same q1 q IN1) as SAME1.
  pose proof (hopcroft_accepting_class_same q2 q IN2) as SAME2.
  eapply hopcroft_accepting_class_eq_of_same.
  unfold same_accepting_tags in *; ss!. 
Qed.

Lemma hopcroft_accepting_class_in_initial_partition (q : Q)
  (STATE : q ∈ M.(TaggedDFA.states))
  : hopcroft_accepting_class q ∈ hopcroft_initial_partition.
Proof.
  unfold hopcroft_initial_partition. rewrite L.nodup_In, in_map_iff.
  exists q. split; [reflexivity | exact STATE].
Qed.

Lemma hopcroft_initial_partition_preserves_right_language
  : hopcroft_partition_preserves_right_language hopcroft_initial_partition.
Proof.
  intros block q1 q2 BLOCK IN1 STATE2 SAME.
  unfold hopcroft_initial_partition in BLOCK. rewrite L.nodup_In, in_map_iff in BLOCK.
  destruct BLOCK as (q & EQ & _). subst block.
  unfold hopcroft_accepting_class in IN1 |- *.
  rewrite filter_In in IN1. destruct IN1 as [_ SAME_Q_Q1B].
  rewrite filter_In. split; [exact STATE2 | ].
  eapply same_accepting_tags_same_accepting_tagsb.
  pose proof (same_accepting_tagsb_same_accepting_tags q q1 SAME_Q_Q1B) as SAME_Q_Q1.
  pose proof (right_language_equiv_same_accepting_tags q1 q2 SAME) as SAME_Q1_Q2.
  unfold same_accepting_tagsb in *; done.
Qed.

Lemma hopcroft_initial_partition_basic_okay
  : HOPCROFT_PARTITION_BASIC_SPEC hopcroft_initial_partition.
Proof.
  constructor.
  - unfold hopcroft_initial_partition. eapply L.NoDup_nodup.
  - intros block BLOCK.
    unfold hopcroft_initial_partition in BLOCK. rewrite L.nodup_In, in_map_iff in BLOCK.
    destruct BLOCK as (q & EQ & STATE). subst block.
    destruct (hopcroft_accepting_class q) as [ | q0 qs] eqn: CLASS; simpl; [ | reflexivity].
    pose proof (hopcroft_accepting_class_contains q STATE) as IN_CLASS. rewrite CLASS in IN_CLASS. contradiction.
  - intros block BLOCK q IN.
    unfold hopcroft_initial_partition in BLOCK. rewrite L.nodup_In, in_map_iff in BLOCK.
    destruct BLOCK as (q0 & EQ & STATE). subst block. eapply hopcroft_accepting_class_states. exact IN.
  - intros q STATE. exists (hopcroft_accepting_class q). split.
    + eapply hopcroft_accepting_class_in_initial_partition. exact STATE.
    + eapply hopcroft_accepting_class_contains. exact STATE.
  - intros block1 block2 q BLOCK1 BLOCK2 IN1 IN2.
    unfold hopcroft_initial_partition in BLOCK1, BLOCK2. rewrite L.nodup_In, in_map_iff in BLOCK1. rewrite L.nodup_In, in_map_iff in BLOCK2.
    destruct BLOCK1 as (q1 & EQ1 & STATE1). destruct BLOCK2 as (q2 & EQ2 & STATE2). subst block1 block2.
    eapply hopcroft_accepting_class_eq_of_overlap with (q := q); eauto.
  - intros block q1 q2 BLOCK IN1 IN2.
    unfold hopcroft_initial_partition in BLOCK. rewrite L.nodup_In, in_map_iff in BLOCK.
    destruct BLOCK as (q0 & EQ & STATE). subst block.
    pose proof (hopcroft_accepting_class_same q0 q1 IN1) as SAME1.
    pose proof (hopcroft_accepting_class_same q0 q2 IN2) as SAME2.
    unfold hopcroft_accepting_class in *; ss!.
Qed.

Variant HOPCROFT_PARTITION_SURFACE_SPEC (partition : hopcroft_partition) : Prop :=
  | hopcroft_partition_surface_spec_intro
    (surface_blocks_in_states : hopcroft_partition_blocks_in_states partition)
    (surface_covers_states : hopcroft_partition_covers_states partition)
    (surface_respects_accepting_tags : hopcroft_partition_respects_accepting_tags partition).

Lemma hopcroft_partition_stable_of_splitters (partition : hopcroft_partition)
  (OKAY : okay M)
  (SURFACE : HOPCROFT_PARTITION_SURFACE_SPEC partition)
  (SPLITTERS : forall active, forall c, active ∈ partition -> hopcroft_partition_stable_for_splitter partition active c)
  : hopcroft_partition_stable partition.
Proof.
  destruct OKAY as [_ _ TRANS_OKAY].
  destruct SURFACE as [BLOCKS COVER _].
  intros block q1 q2 c BLOCK IN1 IN2.
  assert (STATE1 : q1 ∈ M.(TaggedDFA.states)) by (eapply BLOCKS; eauto).
  assert (STATE2 : q2 ∈ M.(TaggedDFA.states)) by (eapply BLOCKS; eauto).
  pose proof (TRANS_OKAY q1 c STATE1) as NEXT1_STATE.
  pose proof (TRANS_OKAY q2 c STATE2) as NEXT2_STATE.
  pose proof (COVER (M.(TaggedDFA.transition) q1 c) NEXT1_STATE) as (active & ACTIVE & IN_ACTIVE1).
  pose proof (SPLITTERS active c ACTIVE block q1 q2 BLOCK IN1 IN2) as SAME_ACTIVE.
  exists active. unfold hopcroft_accepting_class in *; ss!.
Qed.

Lemma hopcroft_initial_partition_surface_okay
  : HOPCROFT_PARTITION_SURFACE_SPEC hopcroft_initial_partition.
Proof.
  pose proof hopcroft_initial_partition_basic_okay as BASIC.
  destruct BASIC as [_ _ BLOCKS COVER _ RESPECT]. split; eauto.
Qed.

Lemma hopcroft_block_intersection_subset (block : hopcroft_block) (splitter : hopcroft_block) (q : Q)
  (IN : q ∈ hopcroft_block_intersection block splitter)
  : q ∈ block.
Proof.
  unfold hopcroft_block_intersection in IN. ss!.
Qed.

Lemma hopcroft_block_difference_subset (block : hopcroft_block) (splitter : hopcroft_block) (q : Q)
  (IN : q ∈ hopcroft_block_difference block splitter)
  : q ∈ block.
Proof.
  unfold hopcroft_block_difference in IN. ss!.
Qed.

Lemma hopcroft_block_intersection_in_splitter (block : hopcroft_block) (splitter : hopcroft_block) (q : Q)
  (IN : q ∈ hopcroft_block_intersection block splitter)
  : q ∈ splitter.
Proof.
  unfold hopcroft_block_intersection in IN. ss!.
Qed.

Lemma hopcroft_block_difference_not_in_splitter (block : hopcroft_block) (splitter : hopcroft_block) (q : Q)
  (IN : q ∈ hopcroft_block_difference block splitter)
  : ~ q ∈ splitter.
Proof.
  unfold hopcroft_block_difference in IN. ss!.
Qed.

Lemma hopcroft_predecessors_preserves_right_language (active : hopcroft_block) (c : ascii) (q1 : Q) (q2 : Q)
  (OKAY : okay M)
  (ACTIVE : forall q, forall q', q ∈ active -> q' ∈ M.(TaggedDFA.states) -> right_language_equiv q q' -> q' ∈ active)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (SAME : right_language_equiv q1 q2)
  : q1 ∈ hopcroft_predecessors active c <-> q2 ∈ hopcroft_predecessors active c.
Proof.
  destruct OKAY as [_ _ TRANS_OKAY]. rewrite !hopcroft_predecessors_iff. split; intros [_ IN_ACTIVE]; split; eauto.
  - eapply ACTIVE; eauto. eapply right_language_equiv_step; eauto.
  - eapply ACTIVE; eauto. ii; symmetry; revert s tag. eapply right_language_equiv_step; eauto.
Qed.

Lemma hopcroft_block_intersection_difference_disjoint (block : hopcroft_block) (splitter : hopcroft_block) (q : Q)
  (IN1 : q ∈ hopcroft_block_intersection block splitter)
  (IN2 : q ∈ hopcroft_block_difference block splitter)
  : False.
Proof.
  pose proof (hopcroft_block_intersection_in_splitter block splitter q IN1) as IN_SPLITTER.
  pose proof (hopcroft_block_difference_not_in_splitter block splitter q IN2) as NOT_IN_SPLITTER.
  contradiction.
Qed.

Lemma hopcroft_refine_partition_preserves_right_language_for_predecessors (active : hopcroft_block) (c : ascii) (partition : hopcroft_partition) (worklist : hopcroft_worklist)
  (OKAY : okay M)
  (BLOCKS : hopcroft_partition_blocks_in_states partition)
  (PRESERVE : hopcroft_partition_preserves_right_language partition)
  (ACTIVE : forall q, forall q', q ∈ active -> q' ∈ M.(TaggedDFA.states) -> right_language_equiv q q' -> q' ∈ active)
  : hopcroft_partition_preserves_right_language (fst (hopcroft_refine_partition (hopcroft_predecessors active c) partition worklist)).
Proof.
  unfold hopcroft_partition_preserves_right_language in *. revert worklist BLOCKS PRESERVE.
  induction partition as [ | block partition IH]; intros worklist BLOCKS PRESERVE block' q1 q2 BLOCK' IN1 STATE2 SAME; simpl in BLOCK'; [contradiction | ].
  set (splitter := hopcroft_predecessors active c).
  set (block1 := hopcroft_block_intersection block splitter).
  set (block2 := hopcroft_block_difference block splitter).
  destruct (hopcroft_refine_partition splitter partition worklist) as [partition' worklist'] eqn: REFINE.
  fold splitter in BLOCK'. fold block1 in BLOCK'. fold block2 in BLOCK'.
  rewrite REFINE in BLOCK'. simpl in BLOCK'.
  assert (BLOCKS_TAIL : hopcroft_partition_blocks_in_states partition).
  { intros block0 BLOCK0 q IN_Q; eapply BLOCKS; [right; exact BLOCK0 | exact IN_Q]. }
  assert (PRESERVE_TAIL : hopcroft_partition_preserves_right_language partition).
  { intros block0 qa qb BLOCK0 IN_QA STATE_QB SAME_Q.
    eapply PRESERVE; [right; exact BLOCK0 | exact IN_QA | exact STATE_QB | exact SAME_Q].
  }
  destruct (nonempty block1 && nonempty block2) eqn: SPLIT; simpl in BLOCK'.
  - destruct BLOCK' as [EQ | [EQ | BLOCK']].
    + subst block'. subst block1. unfold hopcroft_block_intersection in IN1 |- *.
      rewrite filter_In in IN1 |- *. destruct IN1 as [IN_BLOCK IN_SPLITTER1].
      assert (STATE1 : q1 ∈ M.(TaggedDFA.states)) by (eapply BLOCKS; [left; reflexivity | exact IN_BLOCK]).
      assert (IN_BLOCK2 : q2 ∈ block).
      { eapply PRESERVE; [left; reflexivity | exact IN_BLOCK | exact STATE2 | exact SAME]. }
      split; [exact IN_BLOCK2 | ].
      rewrite mem_spec in IN_SPLITTER1 |- *.
      pose proof (hopcroft_predecessors_preserves_right_language active c q1 q2 OKAY ACTIVE STATE1 STATE2 SAME) as PRED.
      change (q2 ∈ hopcroft_predecessors active c). rewrite <- PRED. exact IN_SPLITTER1.
    + subst block'. subst block2. unfold hopcroft_block_difference in IN1 |- *.
      rewrite filter_In in IN1 |- *. destruct IN1 as [IN_BLOCK NOT_SPLITTER1].
      rewrite negb_true_iff in NOT_SPLITTER1. rewrite mem_spec in NOT_SPLITTER1.
      assert (STATE1 : q1 ∈ M.(TaggedDFA.states)) by (eapply BLOCKS; [left; reflexivity | exact IN_BLOCK]).
      assert (IN_BLOCK2 : q2 ∈ block).
      { eapply PRESERVE; [left; reflexivity | exact IN_BLOCK | exact STATE2 | exact SAME]. }
      split; [exact IN_BLOCK2 | ].
      rewrite negb_true_iff. rewrite mem_spec.
      pose proof (hopcroft_predecessors_preserves_right_language active c q1 q2 OKAY ACTIVE STATE1 STATE2 SAME) as PRED.
      intros IN_SPLITTER2. eapply NOT_SPLITTER1. change (q1 ∈ hopcroft_predecessors active c). rewrite -> PRED. exact IN_SPLITTER2.
    + assert (BLOCK_TAIL : block' ∈ fst (hopcroft_refine_partition (hopcroft_predecessors active c) partition worklist)).
      { change (block' ∈ fst (hopcroft_refine_partition splitter partition worklist)). rewrite REFINE. simpl. exact BLOCK'. }
      eapply IH with (worklist := worklist); eauto.
  - destruct BLOCK' as [EQ | BLOCK'].
    + subst block'. eapply PRESERVE; [left; reflexivity | exact IN1 | exact STATE2 | exact SAME].
    + assert (BLOCK_TAIL : block' ∈ fst (hopcroft_refine_partition (hopcroft_predecessors active c) partition worklist)).
      { change (block' ∈ fst (hopcroft_refine_partition splitter partition worklist)). rewrite REFINE. simpl. exact BLOCK'. }
      eapply IH with (worklist := worklist); eauto.
Qed.

Lemma hopcroft_refine_partition_block_source (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist) (block' : hopcroft_block)
  (IN : block' ∈ fst (hopcroft_refine_partition splitter partition worklist))
  : exists block, block ∈ partition /\ (forall q, q ∈ block' -> q ∈ block).
Proof.
  revert worklist block' IN. induction partition as [ | block partition IH]; intros worklist block' IN; simpl in IN.
  - contradiction.
  - set (block1 := hopcroft_block_intersection block splitter) in *.
    set (block2 := hopcroft_block_difference block splitter) in *.
    destruct (hopcroft_refine_partition splitter partition worklist) as [partition' worklist'] eqn: REFINE.
    destruct (nonempty block1 && nonempty block2) eqn: SPLIT; simpl in IN.
    + destruct IN as [EQ | [EQ | IN]].
      * subst block'. exists block. split; [left; reflexivity | intros q IN_Q; subst block1; eapply hopcroft_block_intersection_subset; exact IN_Q].
      * subst block'. exists block. split; [left; reflexivity | intros q IN_Q; subst block2; eapply hopcroft_block_difference_subset; exact IN_Q].
      * assert (IN_TAIL : block' ∈ fst (hopcroft_refine_partition splitter partition worklist)).
        { rewrite REFINE. simpl. exact IN. }
        pose proof (IH worklist block' IN_TAIL) as (source & SOURCE & SUBSET).
        exists source. split; [right; exact SOURCE | exact SUBSET].
    + destruct IN as [EQ | IN].
      * subst block'. exists block. split; [left; reflexivity | intros q IN_Q; exact IN_Q].
      * assert (IN_TAIL : block' ∈ fst (hopcroft_refine_partition splitter partition worklist)).
        { rewrite REFINE. simpl. exact IN. }
        pose proof (IH worklist block' IN_TAIL) as (source & SOURCE & SUBSET).
        exists source. split; [right; exact SOURCE | exact SUBSET].
Qed.

Lemma hopcroft_refine_partition_piece_not_in_tail (splitter : hopcroft_block) (block : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist) (piece : hopcroft_block)
  (NODUP : NoDup (block :: partition))
  (DISJOINT : hopcroft_partition_disjoint (block :: partition))
  (PIECE_SUBSET : forall q, q ∈ piece -> q ∈ block)
  (PIECE_NONEMPTY : nonempty piece = true)
  : ~ piece ∈ fst (hopcroft_refine_partition splitter partition worklist).
Proof.
  intros PIECE_IN_TAIL.
  pose proof (nonempty_exists piece PIECE_NONEMPTY) as (q & IN_PIECE).
  pose proof (hopcroft_refine_partition_block_source splitter partition worklist piece PIECE_IN_TAIL) as (source & SOURCE & SOURCE_SUBSET).
  assert (EQ : block = source).
  { eapply DISJOINT with (q := q); [left; reflexivity | right; exact SOURCE | eapply PIECE_SUBSET; exact IN_PIECE | eapply SOURCE_SUBSET; exact IN_PIECE]. }
  inversion NODUP as [ | block0 partition0 NOT_IN NODUP_TAIL]; subst block0 partition0.
  rewrite <- EQ in SOURCE. contradiction.
Qed.

Lemma hopcroft_block_intersection_difference_neq (block : hopcroft_block) (splitter : hopcroft_block)
  (NONEMPTY1 : nonempty (hopcroft_block_intersection block splitter) = true)
  (NONEMPTY2 : nonempty (hopcroft_block_difference block splitter) = true)
  : ~ hopcroft_block_intersection block splitter = hopcroft_block_difference block splitter.
Proof.
  intros EQ.
  pose proof (nonempty_exists (hopcroft_block_intersection block splitter) NONEMPTY1) as (q & IN1).
  assert (IN2 : q ∈ hopcroft_block_difference block splitter).
  { rewrite <- EQ. exact IN1. }
  eapply hopcroft_block_intersection_difference_disjoint; eauto.
Qed.

Lemma hopcroft_refine_partition_keeps_member (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist) (block : hopcroft_block) (q : Q)
  (BLOCK : block ∈ partition)
  (IN : q ∈ block)
  : exists block', block' ∈ fst (hopcroft_refine_partition splitter partition worklist) /\ q ∈ block'.
Proof.
  revert worklist block q BLOCK IN. induction partition as [ | block0 partition IH]; intros worklist block q BLOCK IN; simpl in BLOCK |- *; [contradiction | ].
  set (block1 := hopcroft_block_intersection block0 splitter).
  set (block2 := hopcroft_block_difference block0 splitter).
  destruct (hopcroft_refine_partition splitter partition worklist) as [partition' worklist'] eqn: REFINE.
  destruct BLOCK as [EQ | BLOCK].
  - subst block0.
    destruct (nonempty block1 && nonempty block2) eqn: SPLIT; simpl.
    + destruct (mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q splitter) eqn: MEM.
      * exists block1. split; [left; reflexivity | subst block1; unfold hopcroft_block_intersection; rewrite filter_In; split; [exact IN | exact MEM]].
      * exists block2. split; [right; left; reflexivity | subst block2; unfold hopcroft_block_difference; rewrite filter_In; split; [exact IN | now rewrite MEM]].
    + exists block. split; [left; reflexivity | exact IN].
  - pose proof (IH worklist block q BLOCK IN) as (block' & BLOCK' & IN').
    rewrite REFINE in BLOCK'. simpl in BLOCK'.
    destruct (nonempty block1 && nonempty block2) eqn: SPLIT; simpl.
    + exists block'. split; [right; right; exact BLOCK' | exact IN'].
    + exists block'. split; [right; exact BLOCK' | exact IN'].
Qed.

Lemma hopcroft_refine_partition_blocks_in_states (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist)
  (BLOCKS : hopcroft_partition_blocks_in_states partition)
  : hopcroft_partition_blocks_in_states (fst (hopcroft_refine_partition splitter partition worklist)).
Proof.
  intros block' BLOCK' q IN.
  pose proof (hopcroft_refine_partition_block_source splitter partition worklist block' BLOCK') as (block & BLOCK & SUBSET).
  eapply BLOCKS; [exact BLOCK | eapply SUBSET; exact IN].
Qed.

Lemma hopcroft_refine_partition_covers_states (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist)
  (COVER : hopcroft_partition_covers_states partition)
  : hopcroft_partition_covers_states (fst (hopcroft_refine_partition splitter partition worklist)).
Proof.
  intros q STATE.
  pose proof (COVER q STATE) as (block & BLOCK & IN).
  eapply hopcroft_refine_partition_keeps_member; eauto.
Qed.

Lemma hopcroft_refine_partition_respects_accepting_tags (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist)
  (RESPECT : hopcroft_partition_respects_accepting_tags partition)
  : hopcroft_partition_respects_accepting_tags (fst (hopcroft_refine_partition splitter partition worklist)).
Proof.
  intros block' q1 q2 BLOCK' IN1 IN2.
  pose proof (hopcroft_refine_partition_block_source splitter partition worklist block' BLOCK') as (block & BLOCK & SUBSET).
  eapply RESPECT; [exact BLOCK | eapply SUBSET; exact IN1 | eapply SUBSET; exact IN2].
Qed.

Lemma hopcroft_refine_partition_blocks_nonempty (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist)
  (NONEMPTY_BLOCKS : hopcroft_partition_blocks_nonempty partition)
  : hopcroft_partition_blocks_nonempty (fst (hopcroft_refine_partition splitter partition worklist)).
Proof.
  unfold hopcroft_partition_blocks_nonempty in *.
  revert worklist NONEMPTY_BLOCKS. induction partition as [ | block partition IH]; intros worklist NONEMPTY_BLOCKS block' BLOCK'; simpl in BLOCK'; [contradiction | ].
  set (block1 := hopcroft_block_intersection block splitter).
  set (block2 := hopcroft_block_difference block splitter).
  destruct (hopcroft_refine_partition splitter partition worklist) as [partition' worklist'] eqn: REFINE.
  fold block1 in BLOCK'. fold block2 in BLOCK'.
  assert (NONEMPTY_TAIL : hopcroft_partition_blocks_nonempty partition).
  { intros block0 BLOCK0. eapply NONEMPTY_BLOCKS. right. exact BLOCK0. }
  destruct (nonempty block1 && nonempty block2) eqn: SPLIT; simpl in BLOCK'.
  - rewrite andb_true_iff in SPLIT. destruct SPLIT as [NONEMPTY1 NONEMPTY2].
    destruct BLOCK' as [EQ | [EQ | BLOCK']].
    + subst block'. exact NONEMPTY1.
    + subst block'. exact NONEMPTY2.
    + eapply IH with (worklist := worklist); eauto. now rewrite REFINE.
  - destruct BLOCK' as [EQ | BLOCK'].
    + subst block'. eapply NONEMPTY_BLOCKS. left. reflexivity.
    + eapply IH with (worklist := worklist); eauto. now rewrite REFINE.
Qed.

Lemma hopcroft_refine_partition_NoDup_disjoint (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist)
  (NODUP : NoDup partition)
  (NONEMPTY_BLOCKS : hopcroft_partition_blocks_nonempty partition)
  (DISJOINT : hopcroft_partition_disjoint partition)
  : NoDup (fst (hopcroft_refine_partition splitter partition worklist)) /\ hopcroft_partition_disjoint (fst (hopcroft_refine_partition splitter partition worklist)).
Proof.
  revert worklist NODUP NONEMPTY_BLOCKS DISJOINT. induction partition as [ | block partition IH]; ii; simpl.
  - split.
    + constructor.
    + intros block1 block2 q BLOCK1 BLOCK2 IN1 IN2. contradiction.
  - inv NODUP.
    assert (NODUP_CONS : NoDup (block :: partition)) by (constructor; [exact H1 | exact H2]).
    assert (NONEMPTY_TAIL : hopcroft_partition_blocks_nonempty partition).
    { intros block0 BLOCK0. eapply NONEMPTY_BLOCKS. right. exact BLOCK0. }
    assert (DISJOINT_TAIL : hopcroft_partition_disjoint partition).
    { intros block1 block2 q BLOCK1 BLOCK2 IN1 IN2. eapply DISJOINT with (q := q); [right; exact BLOCK1 | right; exact BLOCK2 | exact IN1 | exact IN2]. }
    pose proof (IH worklist H2 NONEMPTY_TAIL DISJOINT_TAIL) as [TAIL_NODUP TAIL_DISJOINT].
    set (block1 := hopcroft_block_intersection block splitter).
    set (block2 := hopcroft_block_difference block splitter).
    destruct (hopcroft_refine_partition splitter partition worklist) as [partition' worklist'] eqn: REFINE. simpl in TAIL_NODUP, TAIL_DISJOINT.
    destruct (nonempty block1 && nonempty block2) eqn: SPLIT.
    + rewrite andb_true_iff in SPLIT. destruct SPLIT as [NONEMPTY1 NONEMPTY2]. split.
      * econs 2.
        { intros IN. destruct IN as [EQ | IN].
          - subst block2. subst block1. eapply hopcroft_block_intersection_difference_neq; eauto.
          - exfalso. eapply hopcroft_refine_partition_piece_not_in_tail with (splitter := splitter) (block := block) (partition := partition) (worklist := worklist) (piece := block1); eauto.
            + intros q IN_Q. subst block1. eapply hopcroft_block_intersection_subset. exact IN_Q.
            + rewrite REFINE; simpl; eauto.
        }
        econs 2.
        { intros IN. exfalso. eapply hopcroft_refine_partition_piece_not_in_tail with (splitter := splitter) (block := block) (partition := partition) (worklist := worklist) (piece := block2); eauto.
          - intros q IN_Q. subst block2. eapply hopcroft_block_difference_subset. exact IN_Q.
          - rewrite REFINE; simpl; eauto.
        }
        { exact TAIL_NODUP. }
      * intros blockA blockB q BLOCKA BLOCKB INA INB. simpl in BLOCKA, BLOCKB.
        destruct BLOCKA as [EQA | [EQA | BLOCKA]], BLOCKB as [EQB | [EQB | BLOCKB]].
        { subst blockA blockB. reflexivity. }
        { subst blockA blockB. exfalso. subst block1 block2. eapply hopcroft_block_intersection_difference_disjoint; eauto. }
        { subst blockA. exfalso.
          assert (BLOCKB_TAIL : blockB ∈ fst (hopcroft_refine_partition splitter partition worklist)).
          { rewrite REFINE. simpl. exact BLOCKB. }
          pose proof (hopcroft_refine_partition_block_source splitter partition worklist blockB BLOCKB_TAIL) as (source & SOURCE & SUBSET).
          assert (EQ : block = source).
          { eapply DISJOINT with (q := q); [left; reflexivity | right; exact SOURCE | subst block1; eapply hopcroft_block_intersection_subset; exact INA | eapply SUBSET; exact INB]. }
          rewrite <- EQ in SOURCE. contradiction.
        }
        { subst blockA blockB. exfalso. subst block1 block2. eapply hopcroft_block_intersection_difference_disjoint; eauto. }
        { subst blockA blockB. reflexivity. }
        { subst blockA. exfalso.
          assert (BLOCKB_TAIL : blockB ∈ fst (hopcroft_refine_partition splitter partition worklist)).
          { rewrite REFINE. simpl. exact BLOCKB. }
          pose proof (hopcroft_refine_partition_block_source splitter partition worklist blockB BLOCKB_TAIL) as (source & SOURCE & SUBSET).
          assert (EQ : block = source).
          { eapply DISJOINT with (q := q); [left; reflexivity | right; exact SOURCE | subst block2; eapply hopcroft_block_difference_subset; exact INA | eapply SUBSET; exact INB]. }
          rewrite <- EQ in SOURCE. contradiction.
        }
        { subst blockB. exfalso.
          assert (BLOCKA_TAIL : blockA ∈ fst (hopcroft_refine_partition splitter partition worklist)).
          { rewrite REFINE. simpl. exact BLOCKA. }
          pose proof (hopcroft_refine_partition_block_source splitter partition worklist blockA BLOCKA_TAIL) as (source & SOURCE & SUBSET).
          assert (EQ : block = source).
          { eapply DISJOINT with (q := q); [left; reflexivity | right; exact SOURCE | subst block1; eapply hopcroft_block_intersection_subset; exact INB | eapply SUBSET; exact INA]. }
          rewrite <- EQ in SOURCE. contradiction.
        }
        { subst blockB. exfalso.
          assert (BLOCKA_TAIL : blockA ∈ fst (hopcroft_refine_partition splitter partition worklist)).
          { rewrite REFINE. simpl. exact BLOCKA. }
          pose proof (hopcroft_refine_partition_block_source splitter partition worklist blockA BLOCKA_TAIL) as (source & SOURCE & SUBSET).
          assert (EQ : block = source).
          { eapply DISJOINT with (q := q); [left; reflexivity | right; exact SOURCE | subst block2; eapply hopcroft_block_difference_subset; exact INB | eapply SUBSET; exact INA]. }
          rewrite <- EQ in SOURCE. contradiction.
        }
        { eapply TAIL_DISJOINT with (q := q); eauto. }
    + split.
      * constructor.
        { intros IN_TAIL.
          assert (BLOCK_TAIL : block ∈ fst (hopcroft_refine_partition splitter partition worklist)).
          { rewrite REFINE. simpl. exact IN_TAIL. }
          pose proof (hopcroft_refine_partition_block_source splitter partition worklist block BLOCK_TAIL) as (source & SOURCE_IN & SOURCE_SUBSET).
          pose proof (nonempty_exists block (NONEMPTY_BLOCKS block (or_introl eq_refl))) as (q & IN_BLOCK).
          assert (EQ_SOURCE : q ∈ source) by (eapply SOURCE_SUBSET; exact IN_BLOCK).
          assert (EQ : block = source).
          { eapply DISJOINT with (q := q); [left; reflexivity | right; exact SOURCE_IN | exact IN_BLOCK | exact EQ_SOURCE]. }
          rewrite <- EQ in SOURCE_IN. contradiction.
        }
        exact TAIL_NODUP.
      * intros blockA blockB q BLOCKA BLOCKB INA INB.
        simpl in BLOCKA, BLOCKB.
        destruct BLOCKA as [EQA | BLOCKA], BLOCKB as [EQB | BLOCKB].
        { subst blockA blockB. reflexivity. }
        { subst blockA. exfalso.
          assert (BLOCKB_TAIL : blockB ∈ fst (hopcroft_refine_partition splitter partition worklist)).
          { rewrite REFINE. simpl. exact BLOCKB. }
          pose proof (hopcroft_refine_partition_block_source splitter partition worklist blockB BLOCKB_TAIL) as (source & SOURCE & SOURCE_SUBSET).
          assert (EQ : block = source).
          { eapply DISJOINT with (q := q); [left; reflexivity | right; exact SOURCE | exact INA | eapply SOURCE_SUBSET; exact INB]. }
          subst source. contradiction.
        }
        { subst blockB. exfalso.
          assert (BLOCKA_TAIL : blockA ∈ fst (hopcroft_refine_partition splitter partition worklist)).
          { rewrite REFINE. simpl. exact BLOCKA. }
          pose proof (hopcroft_refine_partition_block_source splitter partition worklist blockA BLOCKA_TAIL) as (source & SOURCE & SOURCE_SUBSET).
          assert (EQ : block = source).
          { eapply DISJOINT with (q := q); [left; reflexivity | right; exact SOURCE | exact INB | eapply SOURCE_SUBSET; exact INA]. }
          subst source. contradiction.
        }
        { eapply TAIL_DISJOINT with (q := q); eauto. }
Qed.

Lemma hopcroft_refine_partition_basic_okay (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC partition)
  : HOPCROFT_PARTITION_BASIC_SPEC (fst (hopcroft_refine_partition splitter partition worklist)).
Proof.
  destruct BASIC as [NODUP NONEMPTY BLOCKS COVER DISJOINT RESPECT].
  pose proof (hopcroft_refine_partition_NoDup_disjoint splitter partition worklist NODUP NONEMPTY DISJOINT) as [NODUP' DISJOINT'].
  constructor.
  - exact NODUP'.
  - eapply hopcroft_refine_partition_blocks_nonempty. exact NONEMPTY.
  - eapply hopcroft_refine_partition_blocks_in_states. exact BLOCKS.
  - eapply hopcroft_refine_partition_covers_states. exact COVER.
  - exact DISJOINT'.
  - eapply hopcroft_refine_partition_respects_accepting_tags. exact RESPECT.
Qed.

Lemma hopcroft_partition_length_le_states (partition : hopcroft_partition)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC partition)
  : length partition <= length M.(TaggedDFA.states).
Proof.
  destruct BASIC as [NODUP NONEMPTY BLOCKS _ DISJOINT _].
  eapply @NoDup_exists_injective_length with (R := fun block => fun q => q ∈ block).
  - exact M.(TaggedDFA.state_hasEqDec).
  - exact NODUP.
  - intros block BLOCK.
    pose proof (nonempty_exists block (NONEMPTY block BLOCK)) as (q & IN).
    exists q. split; [eapply BLOCKS; eauto | exact IN].
  - intros block1 block2 q BLOCK1 BLOCK2 IN1 IN2.
    eapply DISJOINT with (q := q); eauto.
Qed.

Lemma hopcroft_partition_stableb_false_finds_split (partition : hopcroft_partition)
  (OKAY : okay M)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC partition)
  (STABLEB : hopcroft_partition_stableb partition = false)
  : exists active, exists c, exists block, active ∈ partition /\ block ∈ partition /\ nonempty (hopcroft_block_intersection block (hopcroft_predecessors active c)) && nonempty (hopcroft_block_difference block (hopcroft_predecessors active c)) = true.
Proof.
  destruct OKAY as [_ _ TRANS_OKAY]. destruct BASIC as [_ _ BLOCKS COVER _ _].
  unfold hopcroft_partition_stableb in STABLEB.
  pose proof (forallb_false_exists _ _ STABLEB) as (block & BLOCK & BLOCK_STABLE_FALSE).
  pose proof (forallb_false_exists _ _ BLOCK_STABLE_FALSE) as (c & _ & CHAR_STABLE_FALSE).
  unfold hopcroft_block_stableb in CHAR_STABLE_FALSE.
  pose proof (forallb_false_exists _ _ CHAR_STABLE_FALSE) as (q1 & IN1 & Q1_STABLE_FALSE).
  pose proof (forallb_false_exists _ _ Q1_STABLE_FALSE) as (q2 & IN2 & SAME_BLOCK_FALSE).
  assert (STATE1 : q1 ∈ M.(TaggedDFA.states)) by (eapply BLOCKS; eauto).
  assert (STATE2 : q2 ∈ M.(TaggedDFA.states)) by (eapply BLOCKS; eauto).
  pose proof (TRANS_OKAY q1 c STATE1) as NEXT1_STATE.
  pose proof (TRANS_OKAY q2 c STATE2) as NEXT2_STATE.
  pose proof (COVER (M.(TaggedDFA.transition) q1 c) NEXT1_STATE) as (active & ACTIVE & IN_ACTIVE1).
  assert (NOT_IN_ACTIVE2 : ~ M.(TaggedDFA.transition) q2 c ∈ active).
  { intros IN_ACTIVE2.
    enough (SAME_BLOCK_TRUE : hopcroft_same_blockb partition (M.(TaggedDFA.transition) q1 c) (M.(TaggedDFA.transition) q2 c) = true).
    { rewrite SAME_BLOCK_FALSE in SAME_BLOCK_TRUE. inv SAME_BLOCK_TRUE. }
    unfold hopcroft_same_blockb. rewrite existsb_exists. exists active. split; [exact ACTIVE | ].
    rewrite andb_true_iff. split; rewrite mem_spec; assumption.
  }
  exists active. exists c. exists block. repeat split; [exact ACTIVE | exact BLOCK | ].
  rewrite andb_true_iff. split.
  - eapply nonempty_of_exists with (x := q1).
    unfold hopcroft_block_intersection. rewrite filter_In. split; [exact IN1 | ].
    rewrite mem_spec. rewrite hopcroft_predecessors_iff. split; [exact STATE1 | exact IN_ACTIVE1].
  - eapply nonempty_of_exists with (x := q2).
    unfold hopcroft_block_difference. rewrite filter_In. split; [exact IN2 | ].
    rewrite negb_true_iff. rewrite mem_spec.
    intros IN_PRE.
    rewrite hopcroft_predecessors_iff in IN_PRE. destruct IN_PRE as [_ IN_ACTIVE2].
    contradiction.
Qed.

Lemma hopcroft_refine_partition_length_ge (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist)
  : length partition <= length (fst (hopcroft_refine_partition splitter partition worklist)).
Proof.
  revert worklist. induction partition as [ | block partition IH]; intros worklist; simpl; [lia | ].
  destruct (hopcroft_refine_partition splitter partition worklist) as [partition' worklist'] eqn: REFINE.
  pose proof (IH worklist) as IH_LENGTH. rewrite REFINE in IH_LENGTH. simpl in IH_LENGTH.
  destruct (nonempty (hopcroft_block_intersection block splitter) && nonempty (hopcroft_block_difference block splitter)); simpl; lia.
Qed.

Lemma hopcroft_refine_partition_length_gt_of_split (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist) (block : hopcroft_block)
  (BLOCK : block ∈ partition)
  (SPLIT : nonempty (hopcroft_block_intersection block splitter) && nonempty (hopcroft_block_difference block splitter) = true)
  : length partition < length (fst (hopcroft_refine_partition splitter partition worklist)).
Proof.
  revert worklist block BLOCK SPLIT. induction partition as [ | block0 partition IH]; intros worklist block BLOCK SPLIT; simpl in BLOCK |- *; [contradiction | ].
  destruct (hopcroft_refine_partition splitter partition worklist) as [partition' worklist'] eqn: REFINE.
  destruct BLOCK as [EQ | BLOCK].
  - subst block0. rewrite SPLIT. simpl.
    pose proof (hopcroft_refine_partition_length_ge splitter partition worklist) as GE.
    rewrite REFINE in GE. simpl in GE. lia.
  - pose proof (IH worklist block BLOCK SPLIT) as LT_TAIL.
    rewrite REFINE in LT_TAIL. simpl in LT_TAIL.
    destruct (nonempty (hopcroft_block_intersection block0 splitter) && nonempty (hopcroft_block_difference block0 splitter)); simpl; lia.
Qed.

Lemma hopcroft_partition_stableb_false_has_length_increasing_refinement (partition : hopcroft_partition) (worklist : hopcroft_worklist)
  (OKAY : okay M)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC partition)
  (STABLEB : hopcroft_partition_stableb partition = false)
  : exists active, exists c, length partition < length (fst (hopcroft_refine_partition (hopcroft_predecessors active c) partition worklist)).
Proof.
  pose proof (hopcroft_partition_stableb_false_finds_split partition OKAY BASIC STABLEB) as (active & c & block & _ & BLOCK & SPLIT).
  exists active. exists c.
  eapply hopcroft_refine_partition_length_gt_of_split; eauto.
Qed.

Lemma hopcroft_refine_partition_stable_for_active (active : hopcroft_block) (c : ascii) (partition : hopcroft_partition) (worklist : hopcroft_worklist)
  (BLOCKS : hopcroft_partition_blocks_in_states partition)
  : hopcroft_partition_stable_for_splitter (fst (hopcroft_refine_partition (hopcroft_predecessors active c) partition worklist)) active c.
Proof.
  unfold hopcroft_partition_stable_for_splitter.
  revert worklist BLOCKS. induction partition as [ | block partition IH]; intros worklist BLOCKS block' q1 q2 BLOCK' IN1 IN2; simpl in BLOCK'; [contradiction | ].
  set (splitter := hopcroft_predecessors active c).
  set (block1 := hopcroft_block_intersection block splitter).
  set (block2 := hopcroft_block_difference block splitter).
  destruct (hopcroft_refine_partition splitter partition worklist) as [partition' worklist'] eqn: REFINE.
  fold splitter in BLOCK'. fold block1 in BLOCK'. fold block2 in BLOCK'.
  rewrite REFINE in BLOCK'. simpl in BLOCK'.
  assert (BLOCKS_TAIL : hopcroft_partition_blocks_in_states partition).
  { intros block0 BLOCK0 q IN_Q. eapply BLOCKS; [right; exact BLOCK0 | exact IN_Q]. }
  destruct (nonempty block1 && nonempty block2) eqn: SPLIT; simpl in BLOCK'.
  - destruct BLOCK' as [EQ | [EQ | BLOCK']].
    + subst block'. split; intros _.
      * pose proof (hopcroft_block_intersection_subset block splitter q2 IN2) as STATE_SOURCE.
        pose proof (BLOCKS block (or_introl eq_refl) q2 STATE_SOURCE) as STATE2.
        pose proof (hopcroft_block_intersection_in_splitter block splitter q2 IN2) as IN_SPLITTER2.
        subst splitter. rewrite hopcroft_predecessors_iff in IN_SPLITTER2. tauto.
      * pose proof (hopcroft_block_intersection_subset block splitter q1 IN1) as STATE_SOURCE.
        pose proof (BLOCKS block (or_introl eq_refl) q1 STATE_SOURCE) as STATE1.
        pose proof (hopcroft_block_intersection_in_splitter block splitter q1 IN1) as IN_SPLITTER1.
        subst splitter. rewrite hopcroft_predecessors_iff in IN_SPLITTER1. tauto.
    + subst block'. split; intros IN_ACTIVE.
      * pose proof (hopcroft_block_difference_subset block splitter q1 IN1) as STATE_SOURCE.
        pose proof (BLOCKS block (or_introl eq_refl) q1 STATE_SOURCE) as STATE1.
        pose proof (hopcroft_block_difference_not_in_splitter block splitter q1 IN1) as NOT_IN_SPLITTER1.
        subst splitter. rewrite hopcroft_predecessors_iff in NOT_IN_SPLITTER1. exfalso. eapply NOT_IN_SPLITTER1. split; eauto.
      * pose proof (hopcroft_block_difference_subset block splitter q2 IN2) as STATE_SOURCE.
        pose proof (BLOCKS block (or_introl eq_refl) q2 STATE_SOURCE) as STATE2.
        pose proof (hopcroft_block_difference_not_in_splitter block splitter q2 IN2) as NOT_IN_SPLITTER2.
        subst splitter. rewrite hopcroft_predecessors_iff in NOT_IN_SPLITTER2. exfalso. eapply NOT_IN_SPLITTER2. split; eauto.
    + assert (BLOCK_TAIL : block' ∈ fst (hopcroft_refine_partition (hopcroft_predecessors active c) partition worklist)).
      { change (block' ∈ fst (hopcroft_refine_partition splitter partition worklist)). rewrite REFINE. simpl. exact BLOCK'. }
      eapply IH with (worklist := worklist); [exact BLOCKS_TAIL | exact BLOCK_TAIL | exact IN1 | exact IN2].
  - destruct BLOCK' as [EQ | BLOCK'].
    + subst block'. split; intros IN_ACTIVE.
      * destruct (mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q2 splitter) eqn: MEM2.
        { rewrite mem_spec in MEM2. subst splitter. rewrite hopcroft_predecessors_iff in MEM2. tauto. }
        assert (IN_BLOCK1 : q1 ∈ block1).
        { subst block1. unfold hopcroft_block_intersection. rewrite filter_In. split; [exact IN1 | rewrite mem_spec; subst splitter; rewrite hopcroft_predecessors_iff; split; [eapply BLOCKS; [left; reflexivity | exact IN1] | exact IN_ACTIVE]]. }
        assert (IN_BLOCK2 : q2 ∈ block2).
        { subst block2. unfold hopcroft_block_difference. rewrite filter_In. split; [exact IN2 | rewrite MEM2; reflexivity]. }
        exfalso. rewrite andb_false_iff in SPLIT. destruct SPLIT as [EMPTY | EMPTY].
        { pose proof (nonempty_exists block1) as EXISTS. destruct block1 as [ | q0 qs] eqn: BLOCK1; simpl in IN_BLOCK1; [contradiction | inv EMPTY]. }
        { pose proof (nonempty_exists block2) as EXISTS. destruct block2 as [ | q0 qs] eqn: BLOCK2; simpl in IN_BLOCK2; [contradiction | inv EMPTY]. }
      * destruct (mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q1 splitter) eqn: MEM1.
        { rewrite mem_spec in MEM1. subst splitter. rewrite hopcroft_predecessors_iff in MEM1. tauto. }
        assert (IN_BLOCK1 : q2 ∈ block1).
        { subst block1. unfold hopcroft_block_intersection. rewrite filter_In. split; [exact IN2 | rewrite mem_spec; subst splitter; rewrite hopcroft_predecessors_iff; split; [eapply BLOCKS; [left; reflexivity | exact IN2] | exact IN_ACTIVE]]. }
        assert (IN_BLOCK2 : q1 ∈ block2).
        { subst block2. unfold hopcroft_block_difference. rewrite filter_In. split; [exact IN1 | rewrite MEM1; reflexivity]. }
        exfalso. rewrite andb_false_iff in SPLIT. destruct SPLIT as [EMPTY | EMPTY].
        { destruct block1 as [ | q0 qs] eqn: BLOCK1; simpl in IN_BLOCK1; [contradiction | inv EMPTY]. }
        { destruct block2 as [ | q0 qs] eqn: BLOCK2; simpl in IN_BLOCK2; [contradiction | inv EMPTY]. }
    + assert (BLOCK_TAIL : block' ∈ fst (hopcroft_refine_partition (hopcroft_predecessors active c) partition worklist)).
      { change (block' ∈ fst (hopcroft_refine_partition splitter partition worklist)). rewrite REFINE. simpl. exact BLOCK'. }
      eapply IH with (worklist := worklist); [exact BLOCKS_TAIL | exact BLOCK_TAIL | exact IN1 | exact IN2].
Qed.

Lemma hopcroft_refine_partition_preserves_stable_for_splitter (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist) (active : hopcroft_block) (c : ascii)
  (STABLE : hopcroft_partition_stable_for_splitter partition active c)
  : hopcroft_partition_stable_for_splitter (fst (hopcroft_refine_partition splitter partition worklist)) active c.
Proof.
  intros block q1 q2 BLOCK IN1 IN2.
  pose proof (hopcroft_refine_partition_block_source splitter partition worklist block BLOCK) as (source & SOURCE & SUBSET).
  eapply STABLE; [exact SOURCE | eapply SUBSET; exact IN1 | eapply SUBSET; exact IN2].
Qed.

Lemma hopcroft_step_config_basic_okay (config : hopcroft_config)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC (fst config))
  : HOPCROFT_PARTITION_BASIC_SPEC (fst (hopcroft_step_config config)).
Proof.
  destruct config as [partition worklist]. simpl in BASIC |- *.
  destruct worklist as [ | [active c] worklist]; simpl; [exact BASIC | ].
  eapply hopcroft_refine_partition_basic_okay. exact BASIC.
Qed.

Lemma hopcroft_step_config_worklist_valid (config : hopcroft_config)
  (VALID : hopcroft_worklist_valid (fst config) (snd config))
  : hopcroft_worklist_valid (fst (hopcroft_step_config config)) (snd (hopcroft_step_config config)).
Proof.
  destruct config as [partition worklist]. simpl in VALID |- *.
  destruct worklist as [ | [active c] worklist]; simpl; [exact VALID | ].
  eapply hopcroft_refine_partition_worklist_valid.
  intros block c0 IN.
  eapply VALID. right. exact IN.
Qed.

Lemma iter_hopcroft_step_config_basic_okay (fuel : nat) (config : hopcroft_config)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC (fst config))
  : HOPCROFT_PARTITION_BASIC_SPEC (fst (iter fuel hopcroft_step_config config)).
Proof.
  revert config BASIC. induction fuel as [ | fuel IH]; intros config BASIC; simpl.
  - exact BASIC.
  - eapply IH. eapply hopcroft_step_config_basic_okay. exact BASIC.
Qed.

Lemma iter_hopcroft_step_config_worklist_valid (fuel : nat) (config : hopcroft_config)
  (VALID : hopcroft_worklist_valid (fst config) (snd config))
  : hopcroft_worklist_valid (fst (iter fuel hopcroft_step_config config)) (snd (iter fuel hopcroft_step_config config)).
Proof.
  revert config VALID. induction fuel as [ | fuel IH]; intros config VALID; simpl.
  - exact VALID.
  - eapply IH. eapply hopcroft_step_config_worklist_valid. exact VALID.
Qed.

Lemma hopcroft_final_partition_basic_okay
  : HOPCROFT_PARTITION_BASIC_SPEC hopcroft_final_partition.
Proof.
  unfold hopcroft_final_partition, hopcroft_final_config.
  eapply iter_hopcroft_step_config_basic_okay.
  unfold hopcroft_initial_config. simpl. eapply hopcroft_initial_partition_basic_okay.
Qed.

Lemma hopcroft_final_partition_length_le_states
  : length hopcroft_final_partition <= length M.(TaggedDFA.states).
Proof.
  eapply hopcroft_partition_length_le_states.
  eapply hopcroft_final_partition_basic_okay.
Qed.

Lemma hopcroft_final_worklist_valid
  : hopcroft_worklist_valid (fst hopcroft_final_config) (snd hopcroft_final_config).
Proof.
  unfold hopcroft_final_config.
  eapply iter_hopcroft_step_config_worklist_valid.
  unfold hopcroft_initial_config. simpl. eapply hopcroft_initial_worklist_valid.
Qed.

Variant HOPCROFT_REFINEMENT_SPEC (config : hopcroft_config) : Prop :=
  | hopcroft_refinement_spec_intro
    (refinement_basic : HOPCROFT_PARTITION_BASIC_SPEC (fst config))
    (refinement_worklist_valid : hopcroft_worklist_valid (fst config) (snd config))
    (refinement_preserves_right_language : hopcroft_partition_preserves_right_language (fst config)).

Lemma hopcroft_initial_config_refinement_okay
  : HOPCROFT_REFINEMENT_SPEC hopcroft_initial_config.
Proof.
  constructor.
  - unfold hopcroft_initial_config. simpl. eapply hopcroft_initial_partition_basic_okay.
  - unfold hopcroft_initial_config. simpl. eapply hopcroft_initial_worklist_valid.
  - unfold hopcroft_initial_config. simpl. eapply hopcroft_initial_partition_preserves_right_language.
Qed.

Lemma hopcroft_step_config_refinement_okay (config : hopcroft_config)
  (OKAY : okay M)
  (SPEC : HOPCROFT_REFINEMENT_SPEC config)
  : HOPCROFT_REFINEMENT_SPEC (hopcroft_step_config config).
Proof.
  destruct config as [partition worklist]. simpl in SPEC |- *.
  destruct SPEC as [BASIC VALID PRESERVE].
  pose proof BASIC as BASIC_COPY.
  destruct BASIC_COPY as [_ _ BLOCKS _ _ _].
  destruct worklist as [ | [active c] worklist]; simpl; [constructor; eauto | ].
  pose proof (VALID active c (or_introl eq_refl)) as [ACTIVE_IN _].
  constructor.
  - eapply hopcroft_refine_partition_basic_okay. exact BASIC.
  - eapply hopcroft_refine_partition_worklist_valid.
    intros block c0 IN.
    eapply VALID. right. exact IN.
  - eapply hopcroft_refine_partition_preserves_right_language_for_predecessors.
    + exact OKAY.
    + exact BLOCKS.
    + exact PRESERVE.
    + intros q q' IN_ACTIVE STATE_Q' SAME_Q.
      eapply PRESERVE; [exact ACTIVE_IN | exact IN_ACTIVE | exact STATE_Q' | exact SAME_Q].
Qed.

Lemma iter_hopcroft_step_config_refinement_okay (fuel : nat) (config : hopcroft_config)
  (OKAY : okay M)
  (SPEC : HOPCROFT_REFINEMENT_SPEC config)
  : HOPCROFT_REFINEMENT_SPEC (iter fuel hopcroft_step_config config).
Proof.
  revert config SPEC. induction fuel as [ | fuel IH]; intros config SPEC; simpl.
  - exact SPEC.
  - eapply IH. eapply hopcroft_step_config_refinement_okay; eauto.
Qed.

Lemma hopcroft_final_config_refinement_okay
  (OKAY : okay M)
  : HOPCROFT_REFINEMENT_SPEC hopcroft_final_config.
Proof.
  unfold hopcroft_final_config.
  eapply iter_hopcroft_step_config_refinement_okay; [exact OKAY | ].
  eapply hopcroft_initial_config_refinement_okay.
Qed.

Lemma hopcroft_final_partition_preserves_right_language
  (OKAY : okay M)
  : hopcroft_partition_preserves_right_language hopcroft_final_partition.
Proof.
  pose proof (hopcroft_final_config_refinement_okay OKAY) as SPEC.
  destruct SPEC as [_ _ PRESERVE].
  unfold hopcroft_final_partition. exact PRESERVE.
Qed.

Lemma hopcroft_final_partition_relates_of_right_language (q1 : Q) (q2 : Q)
  (OKAY : okay M)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (SAME : right_language_equiv q1 q2)
  : hopcroft_partition_relates hopcroft_final_partition q1 q2.
Proof.
  pose proof hopcroft_final_partition_basic_okay as BASIC.
  destruct BASIC as [_ _ _ COVER _ _].
  pose proof (COVER q1 STATE1) as (block & BLOCK & IN1).
  exists block. split; [exact BLOCK | ].
  split; [exact IN1 | ].
  eapply hopcroft_final_partition_preserves_right_language; eauto.
Qed.

Lemma hopcroft_final_partition_surface_okay_aux
  : HOPCROFT_PARTITION_SURFACE_SPEC hopcroft_final_partition.
Proof.
  pose proof hopcroft_final_partition_basic_okay as BASIC.
  destruct BASIC as [_ _ BLOCKS COVER _ RESPECT].
  constructor; eauto.
Qed.

Fixpoint hopcroft_find_block (q : Q) (partition : hopcroft_partition) {struct partition} : hopcroft_block :=
  match partition with
  | [] => []
  | block :: partition' => if mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q block then block else hopcroft_find_block q partition'
  end.

Definition hopcroft_find_unstable_q2 (partition : hopcroft_partition) (block : hopcroft_block) (c : ascii) (q1 : Q) : option Q :=
  find (fun q2 => negb (hopcroft_same_blockb partition (M.(TaggedDFA.transition) q1 c) (M.(TaggedDFA.transition) q2 c))) block.

Definition hopcroft_find_unstable_q1 (partition : hopcroft_partition) (block : hopcroft_block) (c : ascii) : option Q :=
  find (fun q1 => match hopcroft_find_unstable_q2 partition block c q1 with Some _ => true | None => false end) block.

Definition hopcroft_find_unstable_char (partition : hopcroft_partition) (block : hopcroft_block) : option ascii :=
  find (fun c => match hopcroft_find_unstable_q1 partition block c with Some _ => true | None => false end) all_asciis.

Definition hopcroft_find_unstable_block (partition : hopcroft_partition) : option hopcroft_block :=
  find (fun block => match hopcroft_find_unstable_char partition block with Some _ => true | None => false end) partition.

Definition hopcroft_find_unstable_splitter (partition : hopcroft_partition) : option hopcroft_splitter :=
  match hopcroft_find_unstable_block partition with
  | None => None
  | Some block =>
    match hopcroft_find_unstable_char partition block with
    | None => None
    | Some c =>
      match hopcroft_find_unstable_q1 partition block c with
      | None => None
      | Some q1 => Some (hopcroft_find_block (M.(TaggedDFA.transition) q1 c) partition, c)
      end
    end
  end.

Lemma hopcroft_find_block_complete (q : Q) (partition : hopcroft_partition) (block : hopcroft_block)
  (BLOCK : block ∈ partition)
  (IN : q ∈ block)
  : hopcroft_find_block q partition ∈ partition /\ q ∈ hopcroft_find_block q partition.
Proof.
  revert block BLOCK IN. induction partition as [ | block0 partition IH]; intros block BLOCK IN; simpl in BLOCK |- *; [contradiction | ].
  destruct (mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q block0) eqn: MEM.
  - split; [left; reflexivity | now rewrite mem_spec in MEM].
  - destruct BLOCK as [EQ | BLOCK].
    + subst block0. rewrite mem_spec in MEM. contradiction.
    + pose proof (IH block BLOCK IN) as [FIND_BLOCK FIND_IN]. split; [right; exact FIND_BLOCK | exact FIND_IN].
Qed.

Lemma hopcroft_find_unstable_splitter_sound (partition : hopcroft_partition) (active : hopcroft_block) (c : ascii)
  (OKAY : okay M)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC partition)
  (FIND : hopcroft_find_unstable_splitter partition = Some (active, c))
  : length partition < length (fst (hopcroft_refine_partition (hopcroft_predecessors active c) partition [])).
Proof.
  destruct OKAY as [_ _ TRANS_OKAY].
  destruct BASIC as [_ _ BLOCKS COVER _ _].
  unfold hopcroft_find_unstable_splitter in FIND.
  destruct (hopcroft_find_unstable_block partition) as [block | ] eqn: FIND_BLOCK; [ | inv FIND].
  destruct (hopcroft_find_unstable_char partition block) as [c0 | ] eqn: FIND_CHAR; [ | inv FIND].
  destruct (hopcroft_find_unstable_q1 partition block c0) as [q1 | ] eqn: FIND_Q1; [ | inv FIND].
  inv FIND.
  unfold hopcroft_find_unstable_block in FIND_BLOCK.
  pose proof (find_some _ _ FIND_BLOCK) as [BLOCK BLOCK_HAS_CHAR].
  unfold hopcroft_find_unstable_char in FIND_CHAR.
  pose proof (find_some _ _ FIND_CHAR) as [_ CHAR_HAS_Q1].
  unfold hopcroft_find_unstable_q1 in FIND_Q1.
  pose proof (find_some _ _ FIND_Q1) as [IN1 Q1_HAS_Q2].
  destruct (hopcroft_find_unstable_q2 partition block c q1) as [q2 | ] eqn: FIND_Q2; [ | inv Q1_HAS_Q2].
  unfold hopcroft_find_unstable_q2 in FIND_Q2.
  pose proof (find_some _ _ FIND_Q2) as [IN2 SAME_FALSE].
  rewrite negb_true_iff in SAME_FALSE.
  assert (STATE1 : q1 ∈ M.(TaggedDFA.states)) by (eapply BLOCKS; eauto).
  assert (STATE2 : q2 ∈ M.(TaggedDFA.states)) by (eapply BLOCKS; eauto).
  pose proof (TRANS_OKAY q1 c STATE1) as NEXT1_STATE.
  pose proof (TRANS_OKAY q2 c STATE2) as NEXT2_STATE.
  pose proof (COVER (M.(TaggedDFA.transition) q1 c) NEXT1_STATE) as (target & TARGET & TARGET_IN).
  pose proof (hopcroft_find_block_complete (M.(TaggedDFA.transition) q1 c) partition target TARGET TARGET_IN) as [ACTIVE ACTIVE_IN].
  assert (NOT_ACTIVE2 : ~ M.(TaggedDFA.transition) q2 c ∈ hopcroft_find_block (M.(TaggedDFA.transition) q1 c) partition).
  { intros ACTIVE2.
    assert (SAME_TRUE : hopcroft_same_blockb partition (M.(TaggedDFA.transition) q1 c) (M.(TaggedDFA.transition) q2 c) = true).
    { unfold hopcroft_same_blockb. rewrite existsb_exists.
      exists (hopcroft_find_block (M.(TaggedDFA.transition) q1 c) partition). split; [exact ACTIVE | ].
      rewrite andb_true_iff. split; rewrite mem_spec; assumption.
    }
    rewrite SAME_FALSE in SAME_TRUE. inv SAME_TRUE.
  }
  eapply hopcroft_refine_partition_length_gt_of_split with (block := block).
  - exact BLOCK.
  - rewrite andb_true_iff. split.
    + eapply nonempty_of_exists with (x := q1).
      unfold hopcroft_block_intersection. rewrite filter_In. split; [exact IN1 | ].
      rewrite mem_spec. rewrite hopcroft_predecessors_iff. split; [exact STATE1 | exact ACTIVE_IN].
    + eapply nonempty_of_exists with (x := q2).
      unfold hopcroft_block_difference. rewrite filter_In. split; [exact IN2 | ].
      rewrite negb_true_iff. rewrite mem_spec.
      intros IN_PRE. rewrite hopcroft_predecessors_iff in IN_PRE.
      destruct IN_PRE as [_ ACTIVE2]. contradiction.
Qed.

Lemma hopcroft_find_unstable_splitter_active_valid (partition : hopcroft_partition) (active : hopcroft_block) (c : ascii)
  (OKAY : okay M)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC partition)
  (FIND : hopcroft_find_unstable_splitter partition = Some (active, c))
  : active ∈ partition.
Proof.
  destruct OKAY as [_ _ TRANS_OKAY].
  destruct BASIC as [_ _ BLOCKS COVER _ _].
  unfold hopcroft_find_unstable_splitter in FIND.
  destruct (hopcroft_find_unstable_block partition) as [block | ] eqn: FIND_BLOCK; [ | inv FIND].
  destruct (hopcroft_find_unstable_char partition block) as [c0 | ] eqn: FIND_CHAR; [ | inv FIND].
  destruct (hopcroft_find_unstable_q1 partition block c0) as [q1 | ] eqn: FIND_Q1; [ | inv FIND].
  inv FIND.
  unfold hopcroft_find_unstable_block in FIND_BLOCK.
  pose proof (find_some _ _ FIND_BLOCK) as [BLOCK _].
  unfold hopcroft_find_unstable_q1 in FIND_Q1.
  pose proof (find_some _ _ FIND_Q1) as [IN1 _].
  assert (STATE1 : q1 ∈ M.(TaggedDFA.states)) by (eapply BLOCKS; eauto).
  pose proof (TRANS_OKAY q1 c STATE1) as NEXT1_STATE.
  pose proof (COVER (M.(TaggedDFA.transition) q1 c) NEXT1_STATE) as (target & TARGET & TARGET_IN).
  pose proof (hopcroft_find_block_complete (M.(TaggedDFA.transition) q1 c) partition target TARGET TARGET_IN) as [ACTIVE _].
  exact ACTIVE.
Qed.

Lemma hopcroft_find_unstable_splitter_complete (partition : hopcroft_partition)
  (STABLEB : hopcroft_partition_stableb partition = false)
  : exists active, exists c, hopcroft_find_unstable_splitter partition = Some (active, c).
Proof.
  unfold hopcroft_partition_stableb in STABLEB.
  pose proof (forallb_false_exists _ _ STABLEB) as (block & BLOCK & BLOCK_STABLE_FALSE).
  pose proof (forallb_false_exists _ _ BLOCK_STABLE_FALSE) as (c & _ & CHAR_STABLE_FALSE).
  unfold hopcroft_block_stableb in CHAR_STABLE_FALSE.
  pose proof (forallb_false_exists _ _ CHAR_STABLE_FALSE) as (q1 & IN1 & Q1_STABLE_FALSE).
  pose proof (forallb_false_exists _ _ Q1_STABLE_FALSE) as (q2 & IN2 & SAME_BLOCK_FALSE).
  unfold hopcroft_find_unstable_q2.
  assert (EX_Q2 : exists q2', find (fun q2' : Q => negb (hopcroft_same_blockb partition (M.(TaggedDFA.transition) q1 c) (M.(TaggedDFA.transition) q2' c))) block = Some q2').
  { eapply find_some_exists with (x := q2); [exact IN2 | now rewrite SAME_BLOCK_FALSE]. }
  fold (hopcroft_find_unstable_q2 partition block c q1) in EX_Q2.
  destruct (hopcroft_find_unstable_q2 partition block c q1) as [q2' | ] eqn: FIND_Q2; [ | destruct EX_Q2 as (? & CONTRA); inv CONTRA].
  unfold hopcroft_find_unstable_q1.
  assert (EX_Q1 : exists q1', find (fun q1' : Q => match hopcroft_find_unstable_q2 partition block c q1' with | Some _ => true | None => false end) block = Some q1').
  { eapply find_some_exists with (x := q1); [exact IN1 | rewrite FIND_Q2; reflexivity]. }
  fold (hopcroft_find_unstable_q1 partition block c) in EX_Q1.
  destruct (hopcroft_find_unstable_q1 partition block c) as [q1' | ] eqn: FIND_Q1; [ | destruct EX_Q1 as (? & CONTRA); inv CONTRA].
  unfold hopcroft_find_unstable_char.
  assert (EX_CHAR : exists c', find (fun c' : ascii => match hopcroft_find_unstable_q1 partition block c' with | Some _ => true | None => false end) all_asciis = Some c').
  { eapply find_some_exists with (x := c); [eapply in_all_asciis_intro | rewrite FIND_Q1; reflexivity]. }
  fold (hopcroft_find_unstable_char partition block) in EX_CHAR.
  destruct (hopcroft_find_unstable_char partition block) as [c' | ] eqn: FIND_CHAR; [ | destruct EX_CHAR as (? & CONTRA); inv CONTRA].
  unfold hopcroft_find_unstable_block.
  assert (EX_BLOCK : exists block', find (fun block' : hopcroft_block => match hopcroft_find_unstable_char partition block' with | Some _ => true | None => false end) partition = Some block').
  { eapply find_some_exists with (x := block); [exact BLOCK | rewrite FIND_CHAR; reflexivity]. }
  fold (hopcroft_find_unstable_block partition) in EX_BLOCK.
  destruct (hopcroft_find_unstable_block partition) as [block' | ] eqn: FIND_BLOCK; [ | destruct EX_BLOCK as (? & CONTRA); inv CONTRA].
  unfold hopcroft_find_unstable_splitter.
  rewrite FIND_BLOCK.
  destruct (hopcroft_find_unstable_char partition block') as [c0 | ] eqn: FIND_CHAR'.
  - pose proof (find_some _ _ FIND_CHAR') as [_ CHAR_HAS_Q1].
    destruct (hopcroft_find_unstable_q1 partition block' c0) as [q0 | ] eqn: FIND_Q1'; [ | inv CHAR_HAS_Q1].
    exists (hopcroft_find_block (M.(TaggedDFA.transition) q0 c0) partition). exists c0. reflexivity.
  - pose proof (find_some _ _ FIND_BLOCK) as [_ BLOCK_HAS_CHAR].
    rewrite FIND_CHAR' in BLOCK_HAS_CHAR. inv BLOCK_HAS_CHAR.
Qed.

Definition hopcroft_stabilise_step (partition : hopcroft_partition) : hopcroft_partition :=
  match hopcroft_find_unstable_splitter partition with
  | Some (active, c) => fst (hopcroft_refine_partition (hopcroft_predecessors active c) partition [])
  | None => partition
  end.

Fixpoint hopcroft_stabilise (fuel : nat) (partition : hopcroft_partition) {struct fuel} : hopcroft_partition :=
  match fuel with
  | O => partition
  | S fuel' =>
    if hopcroft_partition_stableb partition then
      partition
    else
      hopcroft_stabilise fuel' (hopcroft_stabilise_step partition)
  end.

Lemma hopcroft_stabilise_step_basic_okay (partition : hopcroft_partition)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC partition)
  : HOPCROFT_PARTITION_BASIC_SPEC (hopcroft_stabilise_step partition).
Proof.
  unfold hopcroft_stabilise_step.
  destruct (hopcroft_find_unstable_splitter partition) as [[active c] | ]; [ | exact BASIC].
  eapply hopcroft_refine_partition_basic_okay. exact BASIC.
Qed.

Lemma hopcroft_stabilise_step_length_gt (partition : hopcroft_partition)
  (OKAY : okay M)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC partition)
  (STABLEB : hopcroft_partition_stableb partition = false)
  : length partition < length (hopcroft_stabilise_step partition).
Proof.
  pose proof (hopcroft_find_unstable_splitter_complete partition STABLEB) as (active & c & FIND).
  unfold hopcroft_stabilise_step. rewrite FIND.
  eapply hopcroft_find_unstable_splitter_sound; eauto.
Qed.

Lemma hopcroft_stabilise_step_preserves_right_language (partition : hopcroft_partition)
  (OKAY : okay M)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC partition)
  (PRESERVE : hopcroft_partition_preserves_right_language partition)
  : hopcroft_partition_preserves_right_language (hopcroft_stabilise_step partition).
Proof.
  unfold hopcroft_stabilise_step.
  destruct (hopcroft_find_unstable_splitter partition) as [[active c] | ] eqn: FIND; [ | exact PRESERVE].
  pose proof BASIC as BASIC_COPY.
  destruct BASIC_COPY as [_ _ BLOCKS _ _ _].
  pose proof (hopcroft_find_unstable_splitter_active_valid partition active c OKAY BASIC FIND) as ACTIVE_IN.
  eapply hopcroft_refine_partition_preserves_right_language_for_predecessors.
  - exact OKAY.
  - exact BLOCKS.
  - exact PRESERVE.
  - intros q q' IN_ACTIVE STATE_Q' SAME_Q.
    eapply PRESERVE; [exact ACTIVE_IN | exact IN_ACTIVE | exact STATE_Q' | exact SAME_Q].
Qed.

Lemma hopcroft_stabilise_basic_okay (fuel : nat) (partition : hopcroft_partition)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC partition)
  : HOPCROFT_PARTITION_BASIC_SPEC (hopcroft_stabilise fuel partition).
Proof.
  revert partition BASIC. induction fuel as [ | fuel IH]; intros partition BASIC; simpl.
  - exact BASIC.
  - destruct (hopcroft_partition_stableb partition) eqn: STABLEB; [exact BASIC | ].
    eapply IH. eapply hopcroft_stabilise_step_basic_okay. exact BASIC.
Qed.

Lemma hopcroft_stabilise_stableb (fuel : nat) (partition : hopcroft_partition)
  (OKAY : okay M)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC partition)
  (BOUND : length M.(TaggedDFA.states) <= length partition + fuel)
  : hopcroft_partition_stableb (hopcroft_stabilise fuel partition) = true.
Proof.
  revert partition BASIC BOUND. induction fuel as [ | fuel IH]; intros partition BASIC BOUND; simpl.
  - destruct (hopcroft_partition_stableb partition) eqn: STABLEB; [reflexivity | ].
    pose proof (hopcroft_stabilise_step_length_gt partition OKAY BASIC STABLEB) as LT.
    pose proof (hopcroft_stabilise_step_basic_okay partition BASIC) as BASIC_STEP.
    pose proof (hopcroft_partition_length_le_states (hopcroft_stabilise_step partition) BASIC_STEP) as LE_STEP.
    lia.
  - destruct (hopcroft_partition_stableb partition) eqn: STABLEB; [exact STABLEB | ].
    eapply IH.
    + eapply hopcroft_stabilise_step_basic_okay. exact BASIC.
    + pose proof (hopcroft_stabilise_step_length_gt partition OKAY BASIC STABLEB) as LT.
      lia.
Qed.

Lemma hopcroft_stabilise_preserves_right_language (fuel : nat) (partition : hopcroft_partition)
  (OKAY : okay M)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC partition)
  (PRESERVE : hopcroft_partition_preserves_right_language partition)
  : hopcroft_partition_preserves_right_language (hopcroft_stabilise fuel partition).
Proof.
  revert partition BASIC PRESERVE. induction fuel as [ | fuel IH]; intros partition BASIC PRESERVE; simpl.
  - exact PRESERVE.
  - destruct (hopcroft_partition_stableb partition) eqn: STABLEB; [exact PRESERVE | ].
    eapply IH.
    + eapply hopcroft_stabilise_step_basic_okay. exact BASIC.
    + eapply hopcroft_stabilise_step_preserves_right_language; eauto.
Qed.

Lemma hopcroft_find_block_final_complete (q : Q)
  (STATE : q ∈ M.(TaggedDFA.states))
  : hopcroft_find_block q hopcroft_final_partition ∈ hopcroft_final_partition /\ q ∈ hopcroft_find_block q hopcroft_final_partition.
Proof.
  pose proof hopcroft_final_partition_basic_okay as BASIC.
  destruct BASIC as [_ _ _ COVER _ _].
  pose proof (COVER q STATE) as (block & BLOCK & IN).
  eapply hopcroft_find_block_complete; eauto.
Qed.

Definition hopcroft_representative (block : hopcroft_block) : Q :=
  match block with
  | [] => M.(TaggedDFA.start_state)
  | q :: _ => q
  end.

Lemma hopcroft_representative_in_block (block : hopcroft_block)
  (NONEMPTY : nonempty block = true)
  : hopcroft_representative block ∈ block.
Proof.
  destruct block as [ | q block]; simpl in NONEMPTY |- *; [inv NONEMPTY | left; reflexivity].
Qed.

Lemma hopcroft_representative_state (block : hopcroft_block)
  (BLOCK : block ∈ hopcroft_final_partition)
  : hopcroft_representative block ∈ M.(TaggedDFA.states).
Proof.
  pose proof hopcroft_final_partition_basic_okay as BASIC.
  destruct BASIC as [_ NONEMPTY BLOCKS _ _ _].
  eapply BLOCKS; [exact BLOCK | ].
  eapply hopcroft_representative_in_block. eapply NONEMPTY. exact BLOCK.
Qed.

Lemma hopcroft_representative_state_for_partition (partition : hopcroft_partition) (block : hopcroft_block)
  (BASIC : HOPCROFT_PARTITION_BASIC_SPEC partition)
  (BLOCK : block ∈ partition)
  : hopcroft_representative block ∈ M.(TaggedDFA.states).
Proof.
  destruct BASIC as [_ NONEMPTY BLOCKS _ _ _].
  eapply BLOCKS; [exact BLOCK | ].
  eapply hopcroft_representative_in_block. eapply NONEMPTY. exact BLOCK.
Qed.

Lemma hopcroft_final_partition_block_eq_of_representative_right_language (block1 : hopcroft_block) (block2 : hopcroft_block)
  (OKAY : okay M)
  (BLOCK1 : block1 ∈ hopcroft_final_partition)
  (BLOCK2 : block2 ∈ hopcroft_final_partition)
  (SAME : right_language_equiv (hopcroft_representative block1) (hopcroft_representative block2))
  : block1 = block2.
Proof.
  pose proof hopcroft_final_partition_basic_okay as BASIC.
  destruct BASIC as [_ NONEMPTY _ _ DISJOINT _].
  pose proof (hopcroft_representative_state block1 BLOCK1) as STATE1.
  pose proof (hopcroft_representative_state block2 BLOCK2) as STATE2.
  pose proof (hopcroft_final_partition_relates_of_right_language (hopcroft_representative block1) (hopcroft_representative block2) OKAY STATE1 STATE2 SAME) as REL.
  destruct REL as (block & BLOCK & IN1 & IN2).
  assert (EQ1 : block1 = block).
  { eapply DISJOINT with (q := hopcroft_representative block1); [exact BLOCK1 | exact BLOCK | | exact IN1].
    eapply hopcroft_representative_in_block. eapply NONEMPTY. exact BLOCK1.
  }
  assert (EQ2 : block2 = block).
  { eapply DISJOINT with (q := hopcroft_representative block2); [exact BLOCK2 | exact BLOCK | | exact IN2].
    eapply hopcroft_representative_in_block. eapply NONEMPTY. exact BLOCK2.
  }
  congruence.
Qed.

Definition hopcroft_certified_final_partition : hopcroft_partition :=
  hopcroft_stabilise (length M.(TaggedDFA.states)) hopcroft_final_partition.

Lemma hopcroft_certified_final_partition_basic_okay
  : HOPCROFT_PARTITION_BASIC_SPEC hopcroft_certified_final_partition.
Proof.
  unfold hopcroft_certified_final_partition.
  eapply hopcroft_stabilise_basic_okay.
  eapply hopcroft_final_partition_basic_okay.
Qed.

Lemma hopcroft_certified_final_partition_stableb
  (OKAY : okay M)
  : hopcroft_partition_stableb hopcroft_certified_final_partition = true.
Proof.
  unfold hopcroft_certified_final_partition.
  eapply hopcroft_stabilise_stableb.
  - exact OKAY.
  - eapply hopcroft_final_partition_basic_okay.
  - lia.
Qed.

Lemma hopcroft_certified_final_partition_stable
  (OKAY : okay M)
  : hopcroft_partition_stable hopcroft_certified_final_partition.
Proof.
  eapply hopcroft_partition_stableb_sound.
  eapply hopcroft_certified_final_partition_stableb. exact OKAY.
Qed.

Lemma hopcroft_certified_final_partition_preserves_right_language
  (OKAY : okay M)
  : hopcroft_partition_preserves_right_language hopcroft_certified_final_partition.
Proof.
  unfold hopcroft_certified_final_partition.
  eapply hopcroft_stabilise_preserves_right_language.
  - exact OKAY.
  - eapply hopcroft_final_partition_basic_okay.
  - eapply hopcroft_final_partition_preserves_right_language. exact OKAY.
Qed.

Lemma hopcroft_certified_final_partition_surface_okay
  : HOPCROFT_PARTITION_SURFACE_SPEC hopcroft_certified_final_partition.
Proof.
  pose proof hopcroft_certified_final_partition_basic_okay as BASIC.
  destruct BASIC as [_ _ BLOCKS COVER _ RESPECT].
  constructor; eauto.
Qed.

Lemma hopcroft_certified_final_partition_relates_of_right_language (q1 : Q) (q2 : Q)
  (OKAY : okay M)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (SAME : right_language_equiv q1 q2)
  : hopcroft_partition_relates hopcroft_certified_final_partition q1 q2.
Proof.
  pose proof hopcroft_certified_final_partition_basic_okay as BASIC.
  destruct BASIC as [_ _ _ COVER _ _].
  pose proof (COVER q1 STATE1) as (block & BLOCK & IN1).
  exists block. split; [exact BLOCK | ].
  split; [exact IN1 | ].
  eapply hopcroft_certified_final_partition_preserves_right_language; eauto.
Qed.

Lemma hopcroft_certified_final_partition_block_eq_of_representative_right_language (block1 : hopcroft_block) (block2 : hopcroft_block)
  (OKAY : okay M)
  (BLOCK1 : block1 ∈ hopcroft_certified_final_partition)
  (BLOCK2 : block2 ∈ hopcroft_certified_final_partition)
  (SAME : right_language_equiv (hopcroft_representative block1) (hopcroft_representative block2))
  : block1 = block2.
Proof.
  pose proof hopcroft_certified_final_partition_basic_okay as BASIC.
  destruct BASIC as [_ NONEMPTY _ _ DISJOINT _].
  pose proof (hopcroft_representative_state_for_partition hopcroft_certified_final_partition block1 hopcroft_certified_final_partition_basic_okay BLOCK1) as STATE1.
  pose proof (hopcroft_representative_state_for_partition hopcroft_certified_final_partition block2 hopcroft_certified_final_partition_basic_okay BLOCK2) as STATE2.
  pose proof (hopcroft_certified_final_partition_relates_of_right_language (hopcroft_representative block1) (hopcroft_representative block2) OKAY STATE1 STATE2 SAME) as REL.
  destruct REL as (block & BLOCK & IN1 & IN2).
  assert (EQ1 : block1 = block).
  { eapply DISJOINT with (q := hopcroft_representative block1); [exact BLOCK1 | exact BLOCK | | exact IN1].
    eapply hopcroft_representative_in_block. eapply NONEMPTY. exact BLOCK1.
  }
  assert (EQ2 : block2 = block).
  { eapply DISJOINT with (q := hopcroft_representative block2); [exact BLOCK2 | exact BLOCK | | exact IN2].
    eapply hopcroft_representative_in_block. eapply NONEMPTY. exact BLOCK2.
  }
  congruence.
Qed.

Lemma hopcroft_partition_relates_trans_early (partition : hopcroft_partition) (q1 : Q) (q2 : Q) (q3 : Q)
  (DISJOINT : hopcroft_partition_disjoint partition)
  (REL12 : hopcroft_partition_relates partition q1 q2)
  (REL23 : hopcroft_partition_relates partition q2 q3)
  : hopcroft_partition_relates partition q1 q3.
Proof.
  destruct REL12 as (block12 & BLOCK12 & IN1 & IN2).
  destruct REL23 as (block23 & BLOCK23 & IN2' & IN3).
  assert (EQ : block12 = block23).
  { eapply DISJOINT with (q := q2); eauto. }
  subst block23. exists block12. eauto.
Qed.

Lemma hopcroft_partition_relates_same_accepting_tags_early (partition : hopcroft_partition) (q1 : Q) (q2 : Q)
  (SURFACE : HOPCROFT_PARTITION_SURFACE_SPEC partition)
  (REL : hopcroft_partition_relates partition q1 q2)
  : same_accepting_tags q1 q2.
Proof.
  destruct SURFACE as [_ _ RESPECT].
  destruct REL as (block & BLOCK & IN1 & IN2).
  eapply RESPECT; eauto.
Qed.

Lemma hopcroft_partition_stable_delta_relates_early (partition : hopcroft_partition) (q1 : Q) (q2 : Q) (s : Input.t)
  (STABLE : hopcroft_partition_stable partition)
  (REL : hopcroft_partition_relates partition q1 q2)
  : hopcroft_partition_relates partition (delta M q1 s) (delta M q2 s).
Proof.
  revert q1 q2 REL. induction s as [ | c s IH]; intros q1 q2 REL; simpl.
  - exact REL.
  - destruct REL as (block & BLOCK & IN1 & IN2).
    pose proof (STABLE block q1 q2 c BLOCK IN1 IN2) as REL_STEP.
    eapply IH. exact REL_STEP.
Qed.

Lemma hopcroft_partition_relates_right_language_equiv_early (partition : hopcroft_partition) (q1 : Q) (q2 : Q)
  (SURFACE : HOPCROFT_PARTITION_SURFACE_SPEC partition)
  (STABLE : hopcroft_partition_stable partition)
  (REL : hopcroft_partition_relates partition q1 q2)
  : right_language_equiv q1 q2.
Proof.
  intros s tag. split; intros ACCEPT.
  - pose proof (hopcroft_partition_stable_delta_relates_early partition q1 q2 s STABLE REL) as REL_DELTA.
    pose proof (hopcroft_partition_relates_same_accepting_tags_early partition (delta M q1 s) (delta M q2 s) SURFACE REL_DELTA) as SAME.
    unfold same_accepting_tags in SAME. unfold accepts_from. rewrite <- SAME with (tag := tag). exact ACCEPT.
  - pose proof (hopcroft_partition_stable_delta_relates_early partition q1 q2 s STABLE REL) as REL_DELTA.
    pose proof (hopcroft_partition_relates_same_accepting_tags_early partition (delta M q1 s) (delta M q2 s) SURFACE REL_DELTA) as SAME.
    unfold same_accepting_tags in SAME. unfold accepts_from. rewrite -> SAME with (tag := tag). exact ACCEPT.
Qed.

Definition hopcroft_certified_minimised_start_state : hopcroft_block :=
  hopcroft_find_block M.(TaggedDFA.start_state) hopcroft_certified_final_partition.

Definition hopcroft_certified_minimised_transition (block : hopcroft_block) (c : ascii) : hopcroft_block :=
  hopcroft_find_block (M.(TaggedDFA.transition) (hopcroft_representative block) c) hopcroft_certified_final_partition.

Definition hopcroft_certified_minimised_accept_states_of (block : hopcroft_block) : list (hopcroft_block * Token.t) :=
  accepting_tags_from (hopcroft_representative block) >>= fun tag => [(block, tag)].

Definition hopcroft_certified_minimised_accept_states : list (hopcroft_block * Token.t) :=
  hopcroft_certified_final_partition >>= hopcroft_certified_minimised_accept_states_of.

Definition hopcroft_certified_minimise : TaggedDFA.t :=
  {|
    state := hopcroft_block;
    state_hasEqDec := list_hasEqDec M.(TaggedDFA.state_hasEqDec);
    states := hopcroft_certified_final_partition;
    start_state := hopcroft_certified_minimised_start_state;
    accept_states := {| kvlist := hopcroft_certified_minimised_accept_states |};
    transition := hopcroft_certified_minimised_transition;
  |}.

Lemma hopcroft_certified_find_block_complete (q : Q)
  (STATE : q ∈ M.(TaggedDFA.states))
  : hopcroft_find_block q hopcroft_certified_final_partition ∈ hopcroft_certified_final_partition /\ q ∈ hopcroft_find_block q hopcroft_certified_final_partition.
Proof.
  pose proof hopcroft_certified_final_partition_basic_okay as BASIC.
  destruct BASIC as [_ _ _ COVER _ _].
  pose proof (COVER q STATE) as (block & BLOCK & IN).
  eapply hopcroft_find_block_complete; eauto.
Qed.

Lemma hopcroft_certified_minimised_start_state_in_states
  (OKAY : okay M)
  : hopcroft_certified_minimised_start_state ∈ hopcroft_certified_final_partition.
Proof.
  destruct OKAY as [START_OKAY _ _].
  unfold hopcroft_certified_minimised_start_state.
  pose proof (hopcroft_certified_find_block_complete M.(TaggedDFA.start_state) START_OKAY) as [BLOCK _].
  exact BLOCK.
Qed.

Lemma hopcroft_certified_minimised_transition_in_states (block : hopcroft_block) (c : ascii)
  (OKAY : okay M)
  (BLOCK : block ∈ hopcroft_certified_final_partition)
  : hopcroft_certified_minimised_transition block c ∈ hopcroft_certified_final_partition.
Proof.
  unfold hopcroft_certified_minimised_transition.
  pose proof (hopcroft_representative_state_for_partition hopcroft_certified_final_partition block hopcroft_certified_final_partition_basic_okay BLOCK) as STATE.
  destruct OKAY as [_ _ TRANS_OKAY].
  pose proof (TRANS_OKAY (hopcroft_representative block) c STATE) as STATE'.
  pose proof (hopcroft_certified_find_block_complete (M.(TaggedDFA.transition) (hopcroft_representative block) c) STATE') as [BLOCK' _].
  exact BLOCK'.
Qed.

Lemma hopcroft_certified_minimised_accept_states_of_sound (block : hopcroft_block) (block0 : hopcroft_block) (tag : Token.t)
  (ACCEPT : (block0, tag) ∈ hopcroft_certified_minimised_accept_states_of block)
  : block0 = block /\ (hopcroft_representative block, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).
Proof.
  unfold hopcroft_certified_minimised_accept_states_of in ACCEPT.
  pose proof (in_list_bind_elim _ _ _ ACCEPT) as (tag' & ACCEPT' & IN).
  simpl in IN. destruct IN as [EQ | []]. inv EQ.
  split; [reflexivity | ].
  eapply accepting_tags_from_sound. exact ACCEPT'.
Qed.

Lemma hopcroft_certified_minimised_accept_states_sound (block : hopcroft_block) (tag : Token.t)
  (ACCEPT : (block, tag) ∈ hopcroft_certified_minimised_accept_states)
  : block ∈ hopcroft_certified_final_partition /\ (hopcroft_representative block, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).
Proof.
  unfold hopcroft_certified_minimised_accept_states in ACCEPT.
  pose proof (in_list_bind_elim _ _ _ ACCEPT) as (block' & BLOCK & ACCEPT').
  pose proof (hopcroft_certified_minimised_accept_states_of_sound block' block tag ACCEPT') as (EQ & ACCEPT_Q).
  subst block'. eauto.
Qed.

Theorem hopcroft_certified_minimise_okay
  (OKAY : okay M)
  : okay hopcroft_certified_minimise.
Proof.
  constructor; simpl.
  - eapply hopcroft_certified_minimised_start_state_in_states. exact OKAY.
  - intros block tag ACCEPT. pose proof (hopcroft_certified_minimised_accept_states_sound block tag ACCEPT) as [BLOCK _]. exact BLOCK.
  - intros block c BLOCK. eapply hopcroft_certified_minimised_transition_in_states; eauto.
Qed.

Lemma hopcroft_certified_minimised_accept_states_of_complete (block : hopcroft_block) (tag : Token.t)
  (ACCEPT : (hopcroft_representative block, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  : (block, tag) ∈ hopcroft_certified_minimised_accept_states_of block.
Proof.
  unfold hopcroft_certified_minimised_accept_states_of.
  eapply in_list_bind_intro with (x := tag); [ | simpl; left; reflexivity].
  eapply accepting_tags_from_complete. exact ACCEPT.
Qed.

Lemma hopcroft_certified_minimised_accept_states_complete (block : hopcroft_block) (tag : Token.t)
  (BLOCK : block ∈ hopcroft_certified_final_partition)
  (ACCEPT : (hopcroft_representative block, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  : (block, tag) ∈ hopcroft_certified_minimised_accept_states.
Proof.
  unfold hopcroft_certified_minimised_accept_states.
  eapply in_list_bind_intro with (x := block); [exact BLOCK | ].
  eapply hopcroft_certified_minimised_accept_states_of_complete. exact ACCEPT.
Qed.

Lemma hopcroft_certified_find_block_representative_relates (q : Q)
  (STATE : q ∈ M.(TaggedDFA.states))
  : hopcroft_partition_relates hopcroft_certified_final_partition q (hopcroft_representative (hopcroft_find_block q hopcroft_certified_final_partition)).
Proof.
  pose proof (hopcroft_certified_find_block_complete q STATE) as [BLOCK IN].
  exists (hopcroft_find_block q hopcroft_certified_final_partition). split; [exact BLOCK | ].
  split; [exact IN | ].
  eapply hopcroft_representative_in_block.
  pose proof hopcroft_certified_final_partition_basic_okay as BASIC.
  destruct BASIC as [_ NONEMPTY _ _ _ _].
  eapply NONEMPTY. exact BLOCK.
Qed.

Lemma hopcroft_certified_delta_representative_relates (block : hopcroft_block) (s : Input.t)
  (OKAY : okay M)
  (BLOCK : block ∈ hopcroft_certified_final_partition)
  : hopcroft_partition_relates hopcroft_certified_final_partition (delta M (hopcroft_representative block) s) (hopcroft_representative (TaggedDFA.delta hopcroft_certified_minimise block s)).
Proof.
  pose proof hopcroft_certified_final_partition_basic_okay as BASIC.
  destruct BASIC as [_ NONEMPTY _ _ DISJOINT _].
  pose proof (hopcroft_certified_final_partition_stable OKAY) as STABLE.
  revert block BLOCK. induction s as [ | c s IH]; intros block BLOCK; simpl.
  - exists block. split; [exact BLOCK | ].
    split; eapply hopcroft_representative_in_block; eapply NONEMPTY; exact BLOCK.
  - pose proof (hopcroft_representative_state_for_partition hopcroft_certified_final_partition block hopcroft_certified_final_partition_basic_okay BLOCK) as REP_STATE.
    destruct OKAY as [_ _ TRANS_OKAY].
    pose proof (TRANS_OKAY (hopcroft_representative block) c REP_STATE) as TRANS_STATE.
    pose proof (hopcroft_certified_find_block_complete (M.(TaggedDFA.transition) (hopcroft_representative block) c) TRANS_STATE) as [NEXT_BLOCK NEXT_IN].
    pose proof (hopcroft_certified_find_block_representative_relates (M.(TaggedDFA.transition) (hopcroft_representative block) c) TRANS_STATE) as REL_REP.
    pose proof (IH (hopcroft_certified_minimised_transition block c) NEXT_BLOCK) as REL_REST.
    pose proof (hopcroft_partition_stable_delta_relates_early hopcroft_certified_final_partition (M.(TaggedDFA.transition) (hopcroft_representative block) c) (hopcroft_representative (hopcroft_certified_minimised_transition block c)) s STABLE REL_REP) as REL_STEP_REST.
    eapply hopcroft_partition_relates_trans_early; [exact DISJOINT | exact REL_STEP_REST | exact REL_REST].
Qed.

Theorem hopcroft_certified_minimise_sound (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : TaggedDFA.accepts hopcroft_certified_minimise s tag)
  : TaggedDFA.accepts M s tag.
Proof.
  unfold TaggedDFA.accepts in ACCEPT |- *. simpl in ACCEPT.
  pose proof (hopcroft_certified_minimised_start_state_in_states OKAY) as START_BLOCK.
  pose proof (hopcroft_certified_delta_representative_relates hopcroft_certified_minimised_start_state s OKAY START_BLOCK) as REL.
  pose proof (hopcroft_certified_minimised_accept_states_sound (TaggedDFA.delta hopcroft_certified_minimise hopcroft_certified_minimised_start_state s) tag ACCEPT) as [BLOCK ACCEPT_REP].
  pose proof (hopcroft_partition_relates_same_accepting_tags_early hopcroft_certified_final_partition (delta M (hopcroft_representative hopcroft_certified_minimised_start_state) s) (hopcroft_representative (TaggedDFA.delta hopcroft_certified_minimise hopcroft_certified_minimised_start_state s)) hopcroft_certified_final_partition_surface_okay REL) as SAME.
  assert (START_REL : hopcroft_partition_relates hopcroft_certified_final_partition M.(TaggedDFA.start_state) (hopcroft_representative hopcroft_certified_minimised_start_state)).
  { destruct OKAY as [START_OKAY _ _]. unfold hopcroft_certified_minimised_start_state. eapply hopcroft_certified_find_block_representative_relates. exact START_OKAY. }
  pose proof (hopcroft_partition_relates_right_language_equiv_early hopcroft_certified_final_partition M.(TaggedDFA.start_state) (hopcroft_representative hopcroft_certified_minimised_start_state) hopcroft_certified_final_partition_surface_okay (hopcroft_certified_final_partition_stable OKAY) START_REL) as START_EQUIV.
  unfold right_language_equiv, accepts_from in START_EQUIV. rewrite -> START_EQUIV with (s := s) (tag := tag).
  unfold same_accepting_tags in SAME. rewrite -> SAME with (tag := tag). exact ACCEPT_REP.
Qed.

Theorem hopcroft_certified_minimise_complete (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : TaggedDFA.accepts M s tag)
  : TaggedDFA.accepts hopcroft_certified_minimise s tag.
Proof.
  unfold TaggedDFA.accepts in ACCEPT |- *. simpl.
  pose proof (hopcroft_certified_minimised_start_state_in_states OKAY) as START_BLOCK.
  pose proof (hopcroft_certified_delta_representative_relates hopcroft_certified_minimised_start_state s OKAY START_BLOCK) as REL.
  assert (START_REL : hopcroft_partition_relates hopcroft_certified_final_partition M.(TaggedDFA.start_state) (hopcroft_representative hopcroft_certified_minimised_start_state)).
  { destruct OKAY as [START_OKAY _ _]. unfold hopcroft_certified_minimised_start_state. eapply hopcroft_certified_find_block_representative_relates. exact START_OKAY. }
  pose proof (hopcroft_partition_relates_right_language_equiv_early hopcroft_certified_final_partition M.(TaggedDFA.start_state) (hopcroft_representative hopcroft_certified_minimised_start_state) hopcroft_certified_final_partition_surface_okay (hopcroft_certified_final_partition_stable OKAY) START_REL) as START_EQUIV.
  assert (ACCEPT_REP_START : accepts_from (hopcroft_representative hopcroft_certified_minimised_start_state) s tag).
  { unfold right_language_equiv in START_EQUIV. rewrite <- START_EQUIV with (s := s) (tag := tag). exact ACCEPT. }
  pose proof (hopcroft_partition_relates_same_accepting_tags_early hopcroft_certified_final_partition (delta M (hopcroft_representative hopcroft_certified_minimised_start_state) s) (hopcroft_representative (TaggedDFA.delta hopcroft_certified_minimise hopcroft_certified_minimised_start_state s)) hopcroft_certified_final_partition_surface_okay REL) as SAME.
  eapply hopcroft_certified_minimised_accept_states_complete.
  - pose proof (hopcroft_certified_minimise_okay OKAY) as OKAY_H.
    eapply delta_okay with (M := hopcroft_certified_minimise); [exact OKAY_H | exact START_BLOCK].
  - unfold same_accepting_tags in SAME. rewrite <- SAME with (tag := tag). exact ACCEPT_REP_START.
Qed.

Theorem hopcroft_certified_minimise_states_minimal (N : TaggedDFA.t)
  (OKAY : okay M)
  (REACHABLE : all_states_reachable M)
  (OKAY_N : okay N)
  (NODUP_N : NoDup N.(TaggedDFA.states))
  (EQUIV : language_equiv M N)
  : length hopcroft_certified_minimise.(TaggedDFA.states) <= length N.(TaggedDFA.states).
Proof.
  cbn [states hopcroft_certified_minimise].
  pose proof hopcroft_certified_final_partition_basic_okay as BASIC.
  destruct BASIC as [NODUP _ _ _ _ _].
  eapply @NoDup_exists_injective_length with (R := fun block => fun n => exists s, hopcroft_representative block = delta M M.(TaggedDFA.start_state) s /\ n = delta N N.(TaggedDFA.start_state) s).
  - exact N.(TaggedDFA.state_hasEqDec).
  - exact NODUP.
  - intros block BLOCK.
    pose proof (hopcroft_representative_state_for_partition hopcroft_certified_final_partition block hopcroft_certified_final_partition_basic_okay BLOCK) as STATE.
    pose proof (REACHABLE _ STATE) as (s & EQ).
    exists (delta N N.(TaggedDFA.start_state) s). split.
    + eapply delta_okay.
      * exact OKAY_N.
      * destruct OKAY_N as [START_OKAY _ _]. exact START_OKAY.
    + exists s. split; [exact EQ | reflexivity].
  - intros block1 block2 n BLOCK1 BLOCK2 R1 R2.
    destruct R1 as (s1 & EQ1 & EQN1).
    destruct R2 as (s2 & EQ2 & EQN2).
    eapply hopcroft_certified_final_partition_block_eq_of_representative_right_language; eauto.
    intros s tag. split; intros ACCEPT.
    + assert (ACCEPT_M1 : accepts M (s1 ++ s) tag).
      { unfold accepts, accepts_from in *. rewrite delta_app. rewrite <- EQ1. exact ACCEPT. }
      pose proof (proj1 (EQUIV (s1 ++ s) tag) ACCEPT_M1) as ACCEPT_N1.
      assert (ACCEPT_N2 : accepts N (s2 ++ s) tag).
      { unfold accepts in ACCEPT_N1 |- *. rewrite !delta_app in *. rewrite <- EQN1 in ACCEPT_N1. rewrite <- EQN2. exact ACCEPT_N1. }
      pose proof (proj2 (EQUIV (s2 ++ s) tag) ACCEPT_N2) as ACCEPT_M2.
      unfold accepts, accepts_from in ACCEPT_M2 |- *. rewrite delta_app in ACCEPT_M2.
      rewrite <- EQ2 in ACCEPT_M2. exact ACCEPT_M2.
    + assert (ACCEPT_M2 : accepts M (s2 ++ s) tag).
      { unfold accepts, accepts_from in *. rewrite delta_app. rewrite <- EQ2. exact ACCEPT. }
      pose proof (proj1 (EQUIV (s2 ++ s) tag) ACCEPT_M2) as ACCEPT_N2.
      assert (ACCEPT_N1 : accepts N (s1 ++ s) tag).
      { unfold accepts in ACCEPT_N2 |- *. rewrite !delta_app in *. rewrite <- EQN2 in ACCEPT_N2. rewrite <- EQN1. exact ACCEPT_N2. }
      pose proof (proj2 (EQUIV (s1 ++ s) tag) ACCEPT_N1) as ACCEPT_M1.
      unfold accepts, accepts_from in ACCEPT_M1 |- *. rewrite delta_app in ACCEPT_M1.
      rewrite <- EQ1 in ACCEPT_M1. exact ACCEPT_M1.
Qed.

Definition hopcroft_certified_minimise_numbered : TaggedDFA.t :=
  number_states hopcroft_certified_minimise.

Theorem hopcroft_certified_minimise_numbered_sound (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : TaggedDFA.accepts hopcroft_certified_minimise_numbered s tag)
  : TaggedDFA.accepts M s tag.
Proof.
  pose proof (hopcroft_certified_minimise_okay OKAY) as OKAY_MIN.
  pose proof (number_states_sound hopcroft_certified_minimise s tag OKAY_MIN ACCEPT) as ACCEPT_MIN.
  eapply hopcroft_certified_minimise_sound; eauto.
Qed.

Theorem hopcroft_certified_minimise_numbered_complete (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : TaggedDFA.accepts M s tag)
  : TaggedDFA.accepts hopcroft_certified_minimise_numbered s tag.
Proof.
  pose proof (hopcroft_certified_minimise_okay OKAY) as OKAY_MIN.
  eapply number_states_complete; [exact OKAY_MIN | eapply hopcroft_certified_minimise_complete; eauto].
Qed.

Theorem hopcroft_certified_minimise_numbered_okay
  (OKAY : okay M)
  : okay hopcroft_certified_minimise_numbered.
Proof.
  eapply number_states_okay. eapply hopcroft_certified_minimise_okay. exact OKAY.
Qed.

Theorem hopcroft_certified_minimise_numbered_states_minimal (N : TaggedDFA.t)
  (OKAY : okay M)
  (REACHABLE : all_states_reachable M)
  (OKAY_N : okay N)
  (NODUP_N : NoDup N.(TaggedDFA.states))
  (EQUIV : language_equiv M N)
  : length hopcroft_certified_minimise_numbered.(TaggedDFA.states) <= length N.(TaggedDFA.states).
Proof.
  unfold hopcroft_certified_minimise_numbered. cbn [states number_states numbered_states].
  unfold numbered_states. rewrite length_seq. eapply hopcroft_certified_minimise_states_minimal; eauto.
Qed.

Definition hopcroft_minimised_start_state : hopcroft_block :=
  hopcroft_find_block M.(TaggedDFA.start_state) hopcroft_final_partition.

Definition hopcroft_minimised_transition (block : hopcroft_block) (c : ascii) : hopcroft_block :=
  hopcroft_find_block (M.(TaggedDFA.transition) (hopcroft_representative block) c) hopcroft_final_partition.

Definition hopcroft_minimised_accept_states_of (block : hopcroft_block) : list (hopcroft_block * Token.t) :=
  accepting_tags_from (hopcroft_representative block) >>= fun tag => [(block, tag)].

Definition hopcroft_minimised_accept_states : list (hopcroft_block * Token.t) :=
  hopcroft_final_partition >>= hopcroft_minimised_accept_states_of.

Definition hopcroft_minimise : TaggedDFA.t :=
  {|
    state := hopcroft_block;
    state_hasEqDec := list_hasEqDec M.(TaggedDFA.state_hasEqDec);
    states := hopcroft_final_partition;
    start_state := hopcroft_minimised_start_state;
    accept_states := {| kvlist := hopcroft_minimised_accept_states |};
    transition := hopcroft_minimised_transition;
  |}.

Lemma hopcroft_minimised_start_state_in_states
  (OKAY : okay M)
  : hopcroft_minimised_start_state ∈ hopcroft_final_partition.
Proof.
  destruct OKAY as [START_OKAY _ _].
  unfold hopcroft_minimised_start_state.
  pose proof (hopcroft_find_block_final_complete M.(TaggedDFA.start_state) START_OKAY) as [BLOCK _].
  exact BLOCK.
Qed.

Lemma hopcroft_minimised_transition_in_states (block : hopcroft_block) (c : ascii)
  (OKAY : okay M)
  (BLOCK : block ∈ hopcroft_final_partition)
  : hopcroft_minimised_transition block c ∈ hopcroft_final_partition.
Proof.
  unfold hopcroft_minimised_transition.
  pose proof (hopcroft_representative_state block BLOCK) as STATE.
  destruct OKAY as [_ _ TRANS_OKAY].
  pose proof (TRANS_OKAY (hopcroft_representative block) c STATE) as STATE'.
  pose proof (hopcroft_find_block_final_complete (M.(TaggedDFA.transition) (hopcroft_representative block) c) STATE') as [BLOCK' _].
  exact BLOCK'.
Qed.

Lemma hopcroft_minimised_accept_states_of_sound (block : hopcroft_block) (block0 : hopcroft_block) (tag : Token.t)
  (ACCEPT : (block0, tag) ∈ hopcroft_minimised_accept_states_of block)
  : block0 = block /\ (hopcroft_representative block, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).
Proof.
  unfold hopcroft_minimised_accept_states_of in ACCEPT.
  pose proof (in_list_bind_elim _ _ _ ACCEPT) as (tag' & ACCEPT' & IN).
  simpl in IN. destruct IN as [EQ | []]. inv EQ.
  split; [reflexivity | ].
  eapply accepting_tags_from_sound. exact ACCEPT'.
Qed.

Lemma hopcroft_minimised_accept_states_sound (block : hopcroft_block) (tag : Token.t)
  (ACCEPT : (block, tag) ∈ hopcroft_minimised_accept_states)
  : block ∈ hopcroft_final_partition /\ (hopcroft_representative block, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).
Proof.
  unfold hopcroft_minimised_accept_states in ACCEPT.
  pose proof (in_list_bind_elim _ _ _ ACCEPT) as (block' & BLOCK & ACCEPT').
  pose proof (hopcroft_minimised_accept_states_of_sound block' block tag ACCEPT') as (EQ & ACCEPT_Q).
  subst block'. eauto.
Qed.

Theorem hopcroft_minimise_okay
  (OKAY : okay M)
  : okay hopcroft_minimise.
Proof.
  constructor; simpl.
  - eapply hopcroft_minimised_start_state_in_states. exact OKAY.
  - intros block tag ACCEPT. pose proof (hopcroft_minimised_accept_states_sound block tag ACCEPT) as [BLOCK _]. exact BLOCK.
  - intros block c BLOCK. eapply hopcroft_minimised_transition_in_states; eauto.
Qed.

Lemma hopcroft_minimised_accept_states_of_complete (block : hopcroft_block) (tag : Token.t)
  (ACCEPT : (hopcroft_representative block, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  : (block, tag) ∈ hopcroft_minimised_accept_states_of block.
Proof.
  unfold hopcroft_minimised_accept_states_of.
  eapply in_list_bind_intro with (x := tag); [ | simpl; left; reflexivity].
  eapply accepting_tags_from_complete. exact ACCEPT.
Qed.

Lemma hopcroft_minimised_accept_states_complete (block : hopcroft_block) (tag : Token.t)
  (BLOCK : block ∈ hopcroft_final_partition)
  (ACCEPT : (hopcroft_representative block, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  : (block, tag) ∈ hopcroft_minimised_accept_states.
Proof.
  unfold hopcroft_minimised_accept_states.
  eapply in_list_bind_intro with (x := block); [exact BLOCK | ].
  eapply hopcroft_minimised_accept_states_of_complete. exact ACCEPT.
Qed.

Lemma hopcroft_partition_relates_sym (partition : hopcroft_partition) (q1 : Q) (q2 : Q)
  (REL : hopcroft_partition_relates partition q1 q2)
  : hopcroft_partition_relates partition q2 q1.
Proof.
  destruct REL as (block & BLOCK & IN1 & IN2).
  exists block. eauto.
Qed.

Lemma hopcroft_partition_relates_trans (partition : hopcroft_partition) (q1 : Q) (q2 : Q) (q3 : Q)
  (DISJOINT : hopcroft_partition_disjoint partition)
  (REL12 : hopcroft_partition_relates partition q1 q2)
  (REL23 : hopcroft_partition_relates partition q2 q3)
  : hopcroft_partition_relates partition q1 q3.
Proof.
  destruct REL12 as (block12 & BLOCK12 & IN1 & IN2).
  destruct REL23 as (block23 & BLOCK23 & IN2' & IN3).
  assert (EQ : block12 = block23).
  { eapply DISJOINT with (q := q2); eauto. }
  subst block23. exists block12. eauto.
Qed.

Lemma hopcroft_find_block_representative_relates (q : Q)
  (STATE : q ∈ M.(TaggedDFA.states))
  : hopcroft_partition_relates hopcroft_final_partition q (hopcroft_representative (hopcroft_find_block q hopcroft_final_partition)).
Proof.
  pose proof (hopcroft_find_block_final_complete q STATE) as [BLOCK IN].
  exists (hopcroft_find_block q hopcroft_final_partition). split; [exact BLOCK | ].
  split; [exact IN | ].
  eapply hopcroft_representative_in_block.
  pose proof hopcroft_final_partition_basic_okay as BASIC.
  destruct BASIC as [_ NONEMPTY _ _ _ _].
  eapply NONEMPTY. exact BLOCK.
Qed.

Lemma hopcroft_partition_relates_same_accepting_tags_aux (partition : hopcroft_partition) (q1 : Q) (q2 : Q)
  (SURFACE : HOPCROFT_PARTITION_SURFACE_SPEC partition)
  (REL : hopcroft_partition_relates partition q1 q2)
  : same_accepting_tags q1 q2.
Proof.
  destruct SURFACE as [_ _ RESPECT].
  destruct REL as (block & BLOCK & IN1 & IN2).
  eapply RESPECT; eauto.
Qed.

Lemma hopcroft_partition_stable_delta_relates_aux (partition : hopcroft_partition) (q1 : Q) (q2 : Q) (s : Input.t)
  (STABLE : hopcroft_partition_stable partition)
  (REL : hopcroft_partition_relates partition q1 q2)
  : hopcroft_partition_relates partition (delta M q1 s) (delta M q2 s).
Proof.
  revert q1 q2 REL. induction s as [ | c s IH]; intros q1 q2 REL; simpl.
  - exact REL.
  - destruct REL as (block & BLOCK & IN1 & IN2).
    pose proof (STABLE block q1 q2 c BLOCK IN1 IN2) as REL_STEP.
    eapply IH. exact REL_STEP.
Qed.

Lemma hopcroft_partition_relates_right_language_equiv_aux (partition : hopcroft_partition) (q1 : Q) (q2 : Q)
  (SURFACE : HOPCROFT_PARTITION_SURFACE_SPEC partition)
  (STABLE : hopcroft_partition_stable partition)
  (REL : hopcroft_partition_relates partition q1 q2)
  : right_language_equiv q1 q2.
Proof.
  intros s tag. split; intros ACCEPT.
  - pose proof (hopcroft_partition_stable_delta_relates_aux partition q1 q2 s STABLE REL) as REL_DELTA.
    pose proof (hopcroft_partition_relates_same_accepting_tags_aux partition (delta M q1 s) (delta M q2 s) SURFACE REL_DELTA) as SAME.
    unfold same_accepting_tags in SAME. unfold accepts_from. rewrite <- SAME with (tag := tag). exact ACCEPT.
  - pose proof (hopcroft_partition_stable_delta_relates_aux partition q1 q2 s STABLE REL) as REL_DELTA.
    pose proof (hopcroft_partition_relates_same_accepting_tags_aux partition (delta M q1 s) (delta M q2 s) SURFACE REL_DELTA) as SAME.
    unfold same_accepting_tags in SAME. unfold accepts_from. rewrite -> SAME with (tag := tag). exact ACCEPT.
Qed.

Lemma hopcroft_delta_representative_relates (block : hopcroft_block) (s : Input.t)
  (OKAY : okay M)
  (STABLE : hopcroft_partition_stable hopcroft_final_partition)
  (BLOCK : block ∈ hopcroft_final_partition)
  : hopcroft_partition_relates hopcroft_final_partition (delta M (hopcroft_representative block) s) (hopcroft_representative (TaggedDFA.delta hopcroft_minimise block s)).
Proof.
  pose proof hopcroft_final_partition_basic_okay as BASIC.
  destruct BASIC as [_ NONEMPTY _ _ DISJOINT _].
  revert block BLOCK. induction s as [ | c s IH]; intros block BLOCK; simpl.
  - exists block. split; [exact BLOCK | ].
    split; eapply hopcroft_representative_in_block; eapply NONEMPTY; exact BLOCK.
  - pose proof (hopcroft_representative_state block BLOCK) as REP_STATE.
    destruct OKAY as [_ _ TRANS_OKAY].
    pose proof (TRANS_OKAY (hopcroft_representative block) c REP_STATE) as TRANS_STATE.
    pose proof (hopcroft_find_block_final_complete (M.(TaggedDFA.transition) (hopcroft_representative block) c) TRANS_STATE) as [NEXT_BLOCK NEXT_IN].
    pose proof (hopcroft_find_block_representative_relates (M.(TaggedDFA.transition) (hopcroft_representative block) c) TRANS_STATE) as REL_REP.
    pose proof (IH (hopcroft_minimised_transition block c) NEXT_BLOCK) as REL_REST.
    pose proof (hopcroft_partition_stable_delta_relates_aux hopcroft_final_partition (M.(TaggedDFA.transition) (hopcroft_representative block) c) (hopcroft_representative (hopcroft_minimised_transition block c)) s STABLE REL_REP) as REL_STEP_REST.
    eapply hopcroft_partition_relates_trans; [exact DISJOINT | exact REL_STEP_REST | exact REL_REST].
Qed.

Theorem hopcroft_minimise_sound (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (STABLE : hopcroft_partition_stable hopcroft_final_partition)
  (ACCEPT : TaggedDFA.accepts hopcroft_minimise s tag)
  : TaggedDFA.accepts M s tag.
Proof.
  unfold TaggedDFA.accepts in ACCEPT |- *. simpl in ACCEPT.
  pose proof (hopcroft_minimised_start_state_in_states OKAY) as START_BLOCK.
  pose proof (hopcroft_delta_representative_relates hopcroft_minimised_start_state s OKAY STABLE START_BLOCK) as REL.
  pose proof (hopcroft_minimised_accept_states_sound (TaggedDFA.delta hopcroft_minimise hopcroft_minimised_start_state s) tag ACCEPT) as [BLOCK ACCEPT_REP].
  pose proof (hopcroft_partition_relates_same_accepting_tags_aux hopcroft_final_partition (delta M (hopcroft_representative hopcroft_minimised_start_state) s) (hopcroft_representative (TaggedDFA.delta hopcroft_minimise hopcroft_minimised_start_state s)) hopcroft_final_partition_surface_okay_aux REL) as SAME.
  assert (START_REL : hopcroft_partition_relates hopcroft_final_partition M.(TaggedDFA.start_state) (hopcroft_representative hopcroft_minimised_start_state)).
  { destruct OKAY as [START_OKAY _ _]. unfold hopcroft_minimised_start_state. eapply hopcroft_find_block_representative_relates. exact START_OKAY. }
  pose proof (hopcroft_partition_relates_right_language_equiv_aux hopcroft_final_partition M.(TaggedDFA.start_state) (hopcroft_representative hopcroft_minimised_start_state) hopcroft_final_partition_surface_okay_aux STABLE START_REL) as START_EQUIV.
  unfold right_language_equiv, accepts_from in START_EQUIV. rewrite -> START_EQUIV with (s := s) (tag := tag).
  unfold same_accepting_tags in SAME. rewrite -> SAME with (tag := tag). exact ACCEPT_REP.
Qed.

Theorem hopcroft_minimise_complete (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (STABLE : hopcroft_partition_stable hopcroft_final_partition)
  (ACCEPT : TaggedDFA.accepts M s tag)
  : TaggedDFA.accepts hopcroft_minimise s tag.
Proof.
  unfold TaggedDFA.accepts in ACCEPT |- *. simpl.
  pose proof (hopcroft_minimised_start_state_in_states OKAY) as START_BLOCK.
  pose proof (hopcroft_delta_representative_relates hopcroft_minimised_start_state s OKAY STABLE START_BLOCK) as REL.
  assert (START_REL : hopcroft_partition_relates hopcroft_final_partition M.(TaggedDFA.start_state) (hopcroft_representative hopcroft_minimised_start_state)).
  { destruct OKAY as [START_OKAY _ _]. unfold hopcroft_minimised_start_state. eapply hopcroft_find_block_representative_relates. exact START_OKAY. }
  pose proof (hopcroft_partition_relates_right_language_equiv_aux hopcroft_final_partition M.(TaggedDFA.start_state) (hopcroft_representative hopcroft_minimised_start_state) hopcroft_final_partition_surface_okay_aux STABLE START_REL) as START_EQUIV.
  assert (ACCEPT_REP_START : accepts_from (hopcroft_representative hopcroft_minimised_start_state) s tag).
  { unfold right_language_equiv in START_EQUIV. rewrite <- START_EQUIV with (s := s) (tag := tag). exact ACCEPT. }
  pose proof (hopcroft_partition_relates_same_accepting_tags_aux hopcroft_final_partition (delta M (hopcroft_representative hopcroft_minimised_start_state) s) (hopcroft_representative (TaggedDFA.delta hopcroft_minimise hopcroft_minimised_start_state s)) hopcroft_final_partition_surface_okay_aux REL) as SAME.
  eapply hopcroft_minimised_accept_states_complete.
  - pose proof (hopcroft_minimise_okay OKAY) as OKAY_H.
    eapply delta_okay with (M := hopcroft_minimise); [exact OKAY_H | exact START_BLOCK].
  - unfold same_accepting_tags in SAME. rewrite <- SAME with (tag := tag). exact ACCEPT_REP_START.
Qed.

Theorem hopcroft_minimise_states_minimal (N : TaggedDFA.t)
  (OKAY : okay M)
  (REACHABLE : all_states_reachable M)
  (OKAY_N : okay N)
  (NODUP_N : NoDup N.(TaggedDFA.states))
  (EQUIV : language_equiv M N)
  : length hopcroft_minimise.(TaggedDFA.states) <= length N.(TaggedDFA.states).
Proof.
  cbn [states hopcroft_minimise].
  pose proof hopcroft_final_partition_basic_okay as BASIC.
  destruct BASIC as [NODUP _ _ _ _ _].
  eapply @NoDup_exists_injective_length with (R := fun block => fun n => exists s, hopcroft_representative block = delta M M.(TaggedDFA.start_state) s /\ n = delta N N.(TaggedDFA.start_state) s).
  - exact N.(TaggedDFA.state_hasEqDec).
  - exact NODUP.
  - intros block BLOCK.
    pose proof (hopcroft_representative_state block BLOCK) as STATE.
    pose proof (REACHABLE _ STATE) as (s & EQ).
    exists (delta N N.(TaggedDFA.start_state) s). split.
    + eapply delta_okay.
      * exact OKAY_N.
      * destruct OKAY_N as [START_OKAY _ _]. exact START_OKAY.
    + exists s. split; [exact EQ | reflexivity].
  - intros block1 block2 n BLOCK1 BLOCK2 R1 R2.
    destruct R1 as (s1 & EQ1 & EQN1).
    destruct R2 as (s2 & EQ2 & EQN2).
    eapply hopcroft_final_partition_block_eq_of_representative_right_language; eauto.
    intros s tag. split; intros ACCEPT.
    + assert (ACCEPT_M1 : accepts M (s1 ++ s) tag).
      { unfold accepts, accepts_from in *. rewrite delta_app. rewrite <- EQ1. exact ACCEPT. }
      pose proof (proj1 (EQUIV (s1 ++ s) tag) ACCEPT_M1) as ACCEPT_N1.
      assert (ACCEPT_N2 : accepts N (s2 ++ s) tag).
      { unfold accepts in ACCEPT_N1 |- *. rewrite !delta_app in *. rewrite <- EQN1 in ACCEPT_N1. rewrite <- EQN2. exact ACCEPT_N1. }
      pose proof (proj2 (EQUIV (s2 ++ s) tag) ACCEPT_N2) as ACCEPT_M2.
      unfold accepts, accepts_from in ACCEPT_M2 |- *. rewrite delta_app in ACCEPT_M2.
      rewrite <- EQ2 in ACCEPT_M2. exact ACCEPT_M2.
    + assert (ACCEPT_M2 : accepts M (s2 ++ s) tag).
      { unfold accepts, accepts_from in *. rewrite delta_app. rewrite <- EQ2. exact ACCEPT. }
      pose proof (proj1 (EQUIV (s2 ++ s) tag) ACCEPT_M2) as ACCEPT_N2.
      assert (ACCEPT_N1 : accepts N (s1 ++ s) tag).
      { unfold accepts in ACCEPT_N2 |- *. rewrite !delta_app in *. rewrite <- EQN2 in ACCEPT_N2. rewrite <- EQN1. exact ACCEPT_N2. }
      pose proof (proj2 (EQUIV (s1 ++ s) tag) ACCEPT_N1) as ACCEPT_M1.
      unfold accepts, accepts_from in ACCEPT_M1 |- *. rewrite delta_app in ACCEPT_M1.
      rewrite <- EQ1 in ACCEPT_M1. exact ACCEPT_M1.
Qed.

Definition hopcroft_minimise_numbered : TaggedDFA.t :=
  number_states hopcroft_minimise.

Theorem hopcroft_minimise_numbered_sound (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (STABLE : hopcroft_partition_stable hopcroft_final_partition)
  (ACCEPT : TaggedDFA.accepts hopcroft_minimise_numbered s tag)
  : TaggedDFA.accepts M s tag.
Proof.
  pose proof (hopcroft_minimise_okay OKAY) as OKAY_MIN.
  pose proof (number_states_sound hopcroft_minimise s tag OKAY_MIN ACCEPT) as ACCEPT_MIN.
  eapply hopcroft_minimise_sound; eauto.
Qed.

Theorem hopcroft_minimise_numbered_complete (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (STABLE : hopcroft_partition_stable hopcroft_final_partition)
  (ACCEPT : TaggedDFA.accepts M s tag)
  : TaggedDFA.accepts hopcroft_minimise_numbered s tag.
Proof.
  pose proof (hopcroft_minimise_okay OKAY) as OKAY_MIN.
  eapply number_states_complete; [exact OKAY_MIN | eapply hopcroft_minimise_complete; eauto].
Qed.

Theorem hopcroft_minimise_sound_checked (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (STABLE : hopcroft_partition_stableb hopcroft_final_partition = true)
  (ACCEPT : TaggedDFA.accepts hopcroft_minimise s tag)
  : TaggedDFA.accepts M s tag.
Proof.
  eapply hopcroft_minimise_sound; [exact OKAY | | exact ACCEPT].
  eapply hopcroft_partition_stableb_sound. exact STABLE.
Qed.

Theorem hopcroft_minimise_complete_checked (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (STABLE : hopcroft_partition_stableb hopcroft_final_partition = true)
  (ACCEPT : TaggedDFA.accepts M s tag)
  : TaggedDFA.accepts hopcroft_minimise s tag.
Proof.
  eapply hopcroft_minimise_complete; [exact OKAY | | exact ACCEPT].
  eapply hopcroft_partition_stableb_sound. exact STABLE.
Qed.

Theorem hopcroft_minimise_numbered_sound_checked (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (STABLE : hopcroft_partition_stableb hopcroft_final_partition = true)
  (ACCEPT : TaggedDFA.accepts hopcroft_minimise_numbered s tag)
  : TaggedDFA.accepts M s tag.
Proof.
  eapply hopcroft_minimise_numbered_sound; [exact OKAY | | exact ACCEPT].
  eapply hopcroft_partition_stableb_sound. exact STABLE.
Qed.

Theorem hopcroft_minimise_numbered_complete_checked (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (STABLE : hopcroft_partition_stableb hopcroft_final_partition = true)
  (ACCEPT : TaggedDFA.accepts M s tag)
  : TaggedDFA.accepts hopcroft_minimise_numbered s tag.
Proof.
  eapply hopcroft_minimise_numbered_complete; [exact OKAY | | exact ACCEPT].
  eapply hopcroft_partition_stableb_sound. exact STABLE.
Qed.

Theorem hopcroft_minimise_numbered_okay
  (OKAY : okay M)
  : okay hopcroft_minimise_numbered.
Proof.
  eapply number_states_okay. eapply hopcroft_minimise_okay. exact OKAY.
Qed.

Theorem hopcroft_minimise_numbered_states_minimal (N : TaggedDFA.t)
  (OKAY : okay M)
  (REACHABLE : all_states_reachable M)
  (OKAY_N : okay N)
  (NODUP_N : NoDup N.(TaggedDFA.states))
  (EQUIV : language_equiv M N)
  : length hopcroft_minimise_numbered.(TaggedDFA.states) <= length N.(TaggedDFA.states).
Proof.
  unfold hopcroft_minimise_numbered. cbn [states number_states numbered_states].
  unfold numbered_states. rewrite length_seq. eapply hopcroft_minimise_states_minimal; eauto.
Qed.

Lemma hopcroft_refine_partition_surface_okay (splitter : hopcroft_block) (partition : hopcroft_partition) (worklist : hopcroft_worklist)
  (SURFACE : HOPCROFT_PARTITION_SURFACE_SPEC partition)
  : HOPCROFT_PARTITION_SURFACE_SPEC (fst (hopcroft_refine_partition splitter partition worklist)).
Proof.
  destruct SURFACE as [BLOCKS COVER RESPECT].
  constructor.
  - eapply hopcroft_refine_partition_blocks_in_states. exact BLOCKS.
  - eapply hopcroft_refine_partition_covers_states. exact COVER.
  - eapply hopcroft_refine_partition_respects_accepting_tags. exact RESPECT.
Qed.

Lemma hopcroft_step_config_surface_okay (config : hopcroft_config)
  (SURFACE : HOPCROFT_PARTITION_SURFACE_SPEC (fst config))
  : HOPCROFT_PARTITION_SURFACE_SPEC (fst (hopcroft_step_config config)).
Proof.
  destruct config as [partition worklist]. simpl in SURFACE |- *.
  destruct worklist as [ | [active c] worklist]; simpl; [exact SURFACE | ].
  eapply hopcroft_refine_partition_surface_okay. exact SURFACE.
Qed.

Lemma iter_hopcroft_step_config_surface_okay (fuel : nat) (config : hopcroft_config)
  (SURFACE : HOPCROFT_PARTITION_SURFACE_SPEC (fst config))
  : HOPCROFT_PARTITION_SURFACE_SPEC (fst (iter fuel hopcroft_step_config config)).
Proof.
  revert config SURFACE. induction fuel as [ | fuel IH]; intros config SURFACE; simpl.
  - exact SURFACE.
  - eapply IH. eapply hopcroft_step_config_surface_okay. exact SURFACE.
Qed.

Lemma hopcroft_final_partition_surface_okay
  : HOPCROFT_PARTITION_SURFACE_SPEC hopcroft_final_partition.
Proof.
  unfold hopcroft_final_partition, hopcroft_final_config.
  eapply iter_hopcroft_step_config_surface_okay.
  unfold hopcroft_initial_config. simpl. eapply hopcroft_initial_partition_surface_okay.
Qed.

Lemma hopcroft_partition_relates_same_accepting_tags (partition : hopcroft_partition) (q1 : Q) (q2 : Q)
  (SURFACE : HOPCROFT_PARTITION_SURFACE_SPEC partition)
  (REL : hopcroft_partition_relates partition q1 q2)
  : same_accepting_tags q1 q2.
Proof.
  destruct SURFACE as [_ _ RESPECT].
  destruct REL as (block & BLOCK & IN1 & IN2).
  eapply RESPECT; eauto.
Qed.

Lemma hopcroft_partition_stable_delta_relates (partition : hopcroft_partition) (q1 : Q) (q2 : Q) (s : Input.t)
  (STABLE : hopcroft_partition_stable partition)
  (REL : hopcroft_partition_relates partition q1 q2)
  : hopcroft_partition_relates partition (delta M q1 s) (delta M q2 s).
Proof.
  revert q1 q2 REL. induction s as [ | c s IH]; intros q1 q2 REL; simpl.
  - exact REL.
  - destruct REL as (block & BLOCK & IN1 & IN2).
    pose proof (STABLE block q1 q2 c BLOCK IN1 IN2) as REL_STEP.
    eapply IH. exact REL_STEP.
Qed.

Lemma hopcroft_partition_relates_right_language_equiv (partition : hopcroft_partition) (q1 : Q) (q2 : Q)
  (SURFACE : HOPCROFT_PARTITION_SURFACE_SPEC partition)
  (STABLE : hopcroft_partition_stable partition)
  (REL : hopcroft_partition_relates partition q1 q2)
  : right_language_equiv q1 q2.
Proof.
  intros s tag. split; intros ACCEPT.
  - pose proof (hopcroft_partition_stable_delta_relates partition q1 q2 s STABLE REL) as REL_DELTA.
    pose proof (hopcroft_partition_relates_same_accepting_tags partition (delta M q1 s) (delta M q2 s) SURFACE REL_DELTA) as SAME.
    unfold same_accepting_tags in SAME. unfold accepts_from. rewrite <- SAME with (tag := tag). exact ACCEPT.
  - pose proof (hopcroft_partition_stable_delta_relates partition q1 q2 s STABLE REL) as REL_DELTA.
    pose proof (hopcroft_partition_relates_same_accepting_tags partition (delta M q1 s) (delta M q2 s) SURFACE REL_DELTA) as SAME.
    unfold same_accepting_tags in SAME. unfold accepts_from. rewrite -> SAME with (tag := tag). exact ACCEPT.
Qed.

Fixpoint minimisation_equivb (fuel : nat) (q1 : Q) (q2 : Q) {struct fuel} : bool :=
  match fuel with
  | O => same_accepting_tagsb q1 q2
  | S fuel' => same_accepting_tagsb q1 q2 && forallb (fun c => minimisation_equivb fuel' (M.(TaggedDFA.transition) q1 c) (M.(TaggedDFA.transition) q2 c)) all_asciis
  end.

Definition minimisation_pair_states : list (Q * Q) :=
  bind (isMonad := B.list_isMonad) M.(TaggedDFA.states) (fun q1 => map (fun q2 => (q1, q2)) M.(TaggedDFA.states)).

Definition minimisation_fuel : nat :=
  length minimisation_pair_states.

Definition minimisation_equiv (q1 : Q) (q2 : Q) : Prop :=
  minimisation_equivb minimisation_fuel q1 q2 = true.

Lemma minimisation_equivb_refl (fuel : nat) (q : Q)
  : minimisation_equivb fuel q q = true.
Proof.
  revert q. induction fuel as [ | fuel IH]; intros q.
  - cbn [minimisation_equivb]. unfold same_accepting_tagsb; ss!; des_ifs; ss!; des_ifs; ss!.
  - cbn [minimisation_equivb]. unfold same_accepting_tagsb; ss!; des_ifs; ss!; des_ifs; ss!.
Qed.

Lemma minimisation_equivb_same_accepting_tagsb (fuel : nat) (q1 : Q) (q2 : Q)
  (EQUIV : minimisation_equivb fuel q1 q2 = true)
  : same_accepting_tagsb q1 q2 = true.
Proof.
  destruct fuel as [ | fuel]; simpl in EQUIV; [exact EQUIV | ].
  now rewrite andb_true_iff in EQUIV.
Qed.

Lemma minimisation_equivb_accepts_from_sound (fuel : nat) (q1 : Q) (q2 : Q) (s : Input.t) (tag : Token.t)
  (LENGTH : length s <= fuel)
  (EQUIV : minimisation_equivb fuel q1 q2 = true)
  (ACCEPT : accepts_from q1 s tag)
  : accepts_from q2 s tag.
Proof.
  revert fuel q1 q2 LENGTH EQUIV ACCEPT.
  induction s as [ | c s IH]; intros fuel q1 q2 LENGTH EQUIV ACCEPT.
  - eapply same_accepting_tagsb_sound; [ | exact ACCEPT].
    eapply minimisation_equivb_same_accepting_tagsb. exact EQUIV.
  - destruct fuel as [ | fuel]; simpl in LENGTH; [lia | ].
    cbn [minimisation_equivb] in EQUIV. rewrite andb_true_iff in EQUIV. destruct EQUIV as [_ EQUIV].
    simpl in ACCEPT |- *.
    eapply IH with (fuel := fuel) (q1 := M.(TaggedDFA.transition) q1 c) (q2 := M.(TaggedDFA.transition) q2 c); [lia | | exact ACCEPT].
    rewrite forallb_forall in EQUIV. eapply EQUIV. eapply in_all_asciis_intro.
Qed.

Lemma minimisation_equivb_accepts_from_complete (fuel : nat) (q1 : Q) (q2 : Q) (s : Input.t) (tag : Token.t)
  (LENGTH : length s <= fuel)
  (EQUIV : minimisation_equivb fuel q1 q2 = true)
  (ACCEPT : accepts_from q2 s tag)
  : accepts_from q1 s tag.
Proof.
  revert fuel q1 q2 LENGTH EQUIV ACCEPT.
  induction s as [ | c s IH]; intros fuel q1 q2 LENGTH EQUIV ACCEPT.
  - eapply same_accepting_tagsb_complete; [ | exact ACCEPT].
    eapply minimisation_equivb_same_accepting_tagsb. exact EQUIV.
  - destruct fuel as [ | fuel]; simpl in LENGTH; [lia | ].
    cbn [minimisation_equivb] in EQUIV. rewrite andb_true_iff in EQUIV. destruct EQUIV as [_ EQUIV].
    simpl in ACCEPT |- *.
    eapply IH with (fuel := fuel) (q1 := M.(TaggedDFA.transition) q1 c) (q2 := M.(TaggedDFA.transition) q2 c); [lia | | exact ACCEPT].
    rewrite forallb_forall in EQUIV. eapply EQUIV. eapply in_all_asciis_intro.
Qed.

Lemma minimisation_equivb_false_distinguish (fuel : nat) (q1 : Q) (q2 : Q)
  (EQUIV : minimisation_equivb fuel q1 q2 = false)
  : exists s, exists tag, length s <= fuel /\ ((accepts_from q1 s tag /\ ~ accepts_from q2 s tag) \/ (accepts_from q2 s tag /\ ~ accepts_from q1 s tag)).
Proof.
  revert q1 q2 EQUIV. induction fuel as [ | fuel IH]; intros q1 q2 EQUIV.
  - cbn [minimisation_equivb] in EQUIV.
    pose proof (same_accepting_tagsb_false_distinguish q1 q2 EQUIV) as (tag & DIFF).
    exists (@nil ascii). exists tag. simpl. split; [lia | exact DIFF].
  - cbn [minimisation_equivb] in EQUIV. rewrite andb_false_iff in EQUIV.
    destruct EQUIV as [SAME | TRANS].
    + pose proof (same_accepting_tagsb_false_distinguish q1 q2 SAME) as (tag & DIFF).
      exists (@nil ascii). exists tag. simpl. split; [lia | exact DIFF].
    + pose proof (forallb_false_exists _ _ TRANS) as (c & _ & EQUIV_C).
      pose proof (IH _ _ EQUIV_C) as (s & tag & LENGTH & DIFF).
      exists (c :: s). exists tag. simpl. split; [lia | exact DIFF].
Qed.

Definition minimisation_pair_transition (qq : Q * Q) (c : ascii) : Q * Q :=
  (M.(TaggedDFA.transition) (fst qq) c, M.(TaggedDFA.transition) (snd qq) c).

Fixpoint minimisation_pair_delta (qq : Q * Q) (s : Input.t) {struct s} : Q * Q :=
  match s with
  | [] => qq
  | c :: s' => minimisation_pair_delta (minimisation_pair_transition qq c) s'
  end.

Fixpoint minimisation_pair_trace (qq : Q * Q) (s : Input.t) {struct s} : list (Q * Q) :=
  match s with
  | [] => []
  | c :: s' =>
    let qq' := minimisation_pair_transition qq c in
    qq' :: minimisation_pair_trace qq' s'
  end.

Definition minimisation_pair_graph : GRAPH.t :=
  {|
    GRAPH.vertices := Q * Q;
    GRAPH.edges := fun '(qq, qq') => exists c, qq' = minimisation_pair_transition qq c;
  |}.

#[local] Notation " src ~~~[ w ]~~> tgt " := (@walk minimisation_pair_graph tgt src w) : type_scope.

Lemma minimisation_pair_delta_spec (q1 : Q) (q2 : Q) (s : Input.t)
  : minimisation_pair_delta (q1, q2) s = (delta M q1 s, delta M q2 s).
Proof.
  revert q1 q2. induction s as [ | c s IH]; intros q1 q2; simpl; eauto.
Qed.

Lemma minimisation_pair_trace_walk (qq : Q * Q) (s : Input.t)
  : qq ~~~[ minimisation_pair_trace qq s ]~~> minimisation_pair_delta qq s.
Proof.
  revert qq. induction s as [ | c s IH]; intros qq; simpl.
  - constructor.
  - econstructor; [exists c; reflexivity | eapply IH].
Qed.

Lemma minimisation_pair_states_complete (q1 : Q) (q2 : Q)
  (IN1 : q1 ∈ M.(TaggedDFA.states))
  (IN2 : q2 ∈ M.(TaggedDFA.states))
  : (q1, q2) ∈ minimisation_pair_states.
Proof.
  unfold minimisation_pair_states.
  eapply in_list_bind_intro with (x := q1); [exact IN1 | ].
  rewrite in_map_iff. exists q2. split; [reflexivity | exact IN2].
Qed.

Lemma minimisation_pair_walk_states (qq : Q * Q) (qq' : Q * Q) (w : list (Q * Q))
  (OKAY : okay M)
  (STATE1 : fst qq ∈ M.(TaggedDFA.states))
  (STATE2 : snd qq ∈ M.(TaggedDFA.states))
  (WALK : qq ~~~[ w ]~~> qq')
  : forall qq0, qq0 ∈ w -> (fst qq0 ∈ M.(TaggedDFA.states) /\ snd qq0 ∈ M.(TaggedDFA.states)).
Proof.
  destruct OKAY as [_ _ TRANS_OKAY].
  induction WALK as [ | qq qq1 w EDGE REST IH]; intros qq0 IN; simpl in IN; [contradiction | ].
  destruct IN as [EQ | IN].
  - subst qq0. destruct EDGE as [c EQ]. subst qq1. simpl.
    split; eapply TRANS_OKAY; eauto.
  - eapply IH; [ | | exact IN].
    + destruct EDGE as [c EQ]. subst qq1. simpl. eapply TRANS_OKAY. exact STATE1.
    + destruct EDGE as [c EQ]. subst qq1. simpl. eapply TRANS_OKAY. exact STATE2.
Qed.

Lemma minimisation_equivb_step (fuel : nat) (q1 : Q) (q2 : Q) (c : ascii)
  (EQUIV : minimisation_equivb (S fuel) q1 q2 = true)
  : minimisation_equivb fuel (M.(TaggedDFA.transition) q1 c) (M.(TaggedDFA.transition) q2 c) = true.
Proof.
  cbn [minimisation_equivb] in EQUIV. rewrite andb_true_iff in EQUIV.
  destruct EQUIV as [_ EQUIV]. rewrite forallb_forall in EQUIV.
  eapply EQUIV. eapply in_all_asciis_intro.
Qed.

Lemma minimisation_equivb_walk_same_accepting_tagsb (fuel : nat) (qq : Q * Q) (qq' : Q * Q) (w : list (Q * Q))
  (WALK : qq ~~~[ w ]~~> qq')
  (LENGTH : length w <= fuel)
  (EQUIV : minimisation_equivb fuel (fst qq) (snd qq) = true)
  : same_accepting_tagsb (fst qq') (snd qq') = true.
Proof.
  revert fuel LENGTH EQUIV.
  induction WALK as [ | qq qq1 w EDGE REST IH]; intros fuel LENGTH EQUIV.
  - eapply minimisation_equivb_same_accepting_tagsb. exact EQUIV.
  - destruct fuel as [ | fuel]; simpl in LENGTH; [lia | ].
    destruct qq as [q1 q2], qq1 as [q1' q2']; cbn [fst snd] in *.
    destruct EDGE as [c EQ]. inv EQ.
    eapply IH with (fuel := fuel); [lia | ].
    eapply minimisation_equivb_step. exact EQUIV.
Qed.

Lemma minimisation_equivb_same_accepting_tagsb_unbounded (q1 : Q) (q2 : Q) (s : Input.t)
  (OKAY : okay M)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (EQUIV : minimisation_equivb minimisation_fuel q1 q2 = true)
  : same_accepting_tagsb (delta M q1 s) (delta M q2 s) = true.
Proof.
  pose proof (minimisation_pair_trace_walk (q1, q2) s) as WALK.
  rewrite minimisation_pair_delta_spec in WALK.
  pose proof (@walk_finds_path minimisation_pair_graph (fun qq => fun qs => match L.in_dec (@eq_dec (Q * Q) _) qq qs with left IN => or_introl IN | right NOT_IN => or_intror NOT_IN end) (q1, q2) (delta M q1 s, delta M q2 s) _ WALK) as [p PATH].
  rewrite path_iff_no_dup_walk in PATH. destruct PATH as [WALK' NO_DUP].
  eapply minimisation_equivb_walk_same_accepting_tagsb with (fuel := minimisation_fuel) (qq := (q1, q2)) (qq' := (delta M q1 s, delta M q2 s)) (w := p); eauto.
  eapply L.NoDup_incl_length; [exact NO_DUP | intros qq IN].
  pose proof (minimisation_pair_walk_states (q1, q2) (delta M q1 s, delta M q2 s) p OKAY STATE1 STATE2 WALK' qq IN) as [IN1 IN2].
  destruct qq as [qq1 qq2]; simpl in *.
  eapply minimisation_pair_states_complete; eauto.
Qed.

Lemma minimisation_equivb_accepts_from_sound_unbounded (q1 : Q) (q2 : Q) (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (EQUIV : minimisation_equivb minimisation_fuel q1 q2 = true)
  (ACCEPT : accepts_from q1 s tag)
  : accepts_from q2 s tag.
Proof.
  eapply same_accepting_tagsb_sound; [ | exact ACCEPT].
  eapply minimisation_equivb_same_accepting_tagsb_unbounded; eauto.
Qed.

Lemma minimisation_equivb_accepts_from_complete_unbounded (q1 : Q) (q2 : Q) (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (EQUIV : minimisation_equivb minimisation_fuel q1 q2 = true)
  (ACCEPT : accepts_from q2 s tag)
  : accepts_from q1 s tag.
Proof.
  eapply same_accepting_tagsb_complete; [ | exact ACCEPT].
  eapply minimisation_equivb_same_accepting_tagsb_unbounded; eauto.
Qed.

Lemma minimisation_equivb_right_language_equiv (q1 : Q) (q2 : Q)
  (OKAY : okay M)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (EQUIV : minimisation_equivb minimisation_fuel q1 q2 = true)
  : right_language_equiv q1 q2.
Proof.
  intros s tag. split; intros ACCEPT.
  - eapply minimisation_equivb_accepts_from_sound_unbounded with (q1 := q1) (q2 := q2); eauto.
  - eapply minimisation_equivb_accepts_from_complete_unbounded with (q1 := q1) (q2 := q2); eauto.
Qed.

Lemma right_language_equiv_minimisation_equivb (q1 : Q) (q2 : Q)
  (SAME : right_language_equiv q1 q2)
  : minimisation_equivb minimisation_fuel q1 q2 = true.
Proof.
  destruct (minimisation_equivb minimisation_fuel q1 q2) eqn: EQUIV; [reflexivity | ].
  pose proof (minimisation_equivb_false_distinguish _ _ _ EQUIV) as (s & tag & _ & [(ACCEPT & NOT_ACCEPT) | (ACCEPT & NOT_ACCEPT)]).
  - pose proof (proj1 (SAME s tag) ACCEPT). contradiction.
  - pose proof (proj2 (SAME s tag) ACCEPT). contradiction.
Qed.

Definition minimised_state : Set :=
  list Q.

#[local]
Instance minimised_state_hasEqDec : hasEqDec minimised_state :=
  list_hasEqDec M.(TaggedDFA.state_hasEqDec).

Definition minimisation_class (q : Q) : minimised_state :=
  filter (minimisation_equivb minimisation_fuel q) M.(TaggedDFA.states).

Lemma minimisation_class_contains (q : Q)
  (IN : q ∈ M.(TaggedDFA.states))
  : q ∈ minimisation_class q.
Proof.
  unfold minimisation_class. rewrite filter_In. split; [exact IN | ].
  eapply minimisation_equivb_refl.
Qed.

Lemma minimisation_class_eq_of_right_language (q1 : Q) (q2 : Q)
  (OKAY : okay M)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (SAME : right_language_equiv q1 q2)
  : minimisation_class q1 = minimisation_class q2.
Proof.
  unfold minimisation_class. eapply L.filter_ext_in. intros q STATE.
  destruct (minimisation_equivb minimisation_fuel q1 q) eqn: EQUIV1, (minimisation_equivb minimisation_fuel q2 q) eqn: EQUIV2; try reflexivity.
  - assert (SAME2 : right_language_equiv q2 q).
    { pose proof (minimisation_equivb_right_language_equiv q1 q OKAY STATE1 STATE EQUIV1) as SAME1.
      intros s tag. split; intros ACCEPT.
      - unfold right_language_equiv in SAME, SAME1. rewrite <- SAME1 with (s := s) (tag := tag). rewrite -> SAME with (s := s) (tag := tag). exact ACCEPT.
      - unfold right_language_equiv in SAME, SAME1. rewrite <- SAME with (s := s) (tag := tag). rewrite -> SAME1 with (s := s) (tag := tag). exact ACCEPT.
    }
    exfalso. pose proof (right_language_equiv_minimisation_equivb q2 q SAME2) as EQUIV.
    rewrite EQUIV2 in EQUIV. inv EQUIV.
  - assert (SAME1 : right_language_equiv q1 q).
    { pose proof (minimisation_equivb_right_language_equiv q2 q OKAY STATE2 STATE EQUIV2) as SAME2.
      intros s tag. split; intros ACCEPT.
      - unfold right_language_equiv in SAME, SAME2. rewrite <- SAME2 with (s := s) (tag := tag). rewrite <- SAME with (s := s) (tag := tag). exact ACCEPT.
      - unfold right_language_equiv in SAME, SAME2. rewrite -> SAME with (s := s) (tag := tag). rewrite -> SAME2 with (s := s) (tag := tag). exact ACCEPT.
    }
    exfalso.
    pose proof (right_language_equiv_minimisation_equivb q1 q SAME1) as EQUIV.
    rewrite EQUIV1 in EQUIV. inv EQUIV.
Qed.

Definition minimised_states : list minimised_state :=
  L.nodup eq_dec (map minimisation_class M.(TaggedDFA.states)).

Definition representative (qs : minimised_state) : Q :=
  match qs with
  | [] => M.(TaggedDFA.start_state)
  | q :: _ => q
  end.

Definition minimised_start_state : minimised_state :=
  minimisation_class M.(TaggedDFA.start_state).

Lemma minimisation_class_representative_state (q : Q)
  (IN : q ∈ M.(TaggedDFA.states))
  : representative (minimisation_class q) ∈ M.(TaggedDFA.states).
Proof.
  destruct (minimisation_class q) as [ | q0 qs] eqn: CLASS.
  - pose proof (minimisation_class_contains q IN) as IN_CLASS.
    rewrite CLASS in IN_CLASS. contradiction.
  - simpl. assert (IN_CLASS : q0 ∈ minimisation_class q) by (rewrite CLASS; left; reflexivity).
    unfold minimisation_class in IN_CLASS. rewrite filter_In in IN_CLASS. tauto.
Qed.

Lemma representative_minimisation_class_equiv (q : Q)
  (IN : q ∈ M.(TaggedDFA.states))
  : minimisation_equivb minimisation_fuel q (representative (minimisation_class q)) = true.
Proof.
  destruct (minimisation_class q) as [ | q0 qs] eqn: CLASS.
  - pose proof (minimisation_class_contains q IN) as IN_CLASS.
    rewrite CLASS in IN_CLASS. contradiction.
  - simpl. assert (IN_CLASS : q0 ∈ minimisation_class q) by (rewrite CLASS; left; reflexivity).
    unfold minimisation_class in IN_CLASS. rewrite filter_In in IN_CLASS. tauto.
Qed.

Lemma minimisation_class_in_minimised_states (q : Q)
  (IN : q ∈ M.(TaggedDFA.states))
  : minimisation_class q ∈ minimised_states.
Proof.
  unfold minimised_states. rewrite L.nodup_In, in_map_iff.
  exists q. split; [reflexivity | exact IN].
Qed.

Lemma minimised_states_NoDup
  : NoDup minimised_states.
Proof.
  unfold minimised_states. eapply L.NoDup_nodup.
Qed.

Lemma minimised_states_representative_state (qs : minimised_state)
  (QS : qs ∈ minimised_states)
  : representative qs ∈ M.(TaggedDFA.states).
Proof.
  unfold minimised_states in QS. rewrite L.nodup_In in QS. rewrite in_map_iff in QS.
  destruct QS as (q & EQ & IN). subst qs.
  eapply minimisation_class_representative_state. exact IN.
Qed.

Lemma minimised_state_eq_minimisation_class_representative (qs : minimised_state)
  (OKAY : okay M)
  (QS : qs ∈ minimised_states)
  : qs = minimisation_class (representative qs).
Proof.
  unfold minimised_states in QS. rewrite L.nodup_In in QS. rewrite in_map_iff in QS.
  destruct QS as (q & EQ & IN). subst qs.
  eapply minimisation_class_eq_of_right_language.
  - exact OKAY.
  - exact IN.
  - eapply minimisation_class_representative_state. exact IN.
  - eapply minimisation_equivb_right_language_equiv.
    + exact OKAY.
    + exact IN.
    + eapply minimisation_class_representative_state. exact IN.
    + eapply representative_minimisation_class_equiv. exact IN.
Qed.

Lemma minimised_states_eq_of_representative_right_language (qs1 : minimised_state) (qs2 : minimised_state)
  (OKAY : okay M)
  (QS1 : qs1 ∈ minimised_states)
  (QS2 : qs2 ∈ minimised_states)
  (SAME : right_language_equiv (representative qs1) (representative qs2))
  : qs1 = qs2.
Proof.
  rewrite minimised_state_eq_minimisation_class_representative with (qs := qs1) by assumption.
  rewrite minimised_state_eq_minimisation_class_representative with (qs := qs2) by assumption.
  eapply minimisation_class_eq_of_right_language.
  - exact OKAY.
  - eapply minimised_states_representative_state. exact QS1.
  - eapply minimised_states_representative_state. exact QS2.
  - exact SAME.
Qed.

Lemma minimised_start_state_in_minimised_states
  (OKAY : okay M)
  : minimised_start_state ∈ minimised_states.
Proof.
  destruct OKAY as [START_OKAY _ _].
  unfold minimised_start_state. eapply minimisation_class_in_minimised_states. exact START_OKAY.
Qed.

Definition minimised_transition (qs : minimised_state) (c : ascii) : minimised_state :=
  minimisation_class (M.(TaggedDFA.transition) (representative qs) c).

Lemma minimised_transition_in_minimised_states (qs : minimised_state) (c : ascii)
  (OKAY : okay M)
  (QS : qs ∈ minimised_states)
  : minimised_transition qs c ∈ minimised_states.
Proof.
  unfold minimised_transition. eapply minimisation_class_in_minimised_states.
  destruct OKAY as [_ _ TRANS_OKAY]. eapply TRANS_OKAY.
  eapply minimised_states_representative_state. exact QS.
Qed.

Definition minimised_accept_states_of (qs : minimised_state) : list (minimised_state * Token.t) :=
  accepting_tags_from (representative qs) >>= fun tag => [(qs, tag)].

Definition minimised_accept_states : list (minimised_state * Token.t) :=
  minimised_states >>= minimised_accept_states_of.

Lemma minimised_accept_states_of_complete (qs : minimised_state) (tag : Token.t)
  (ACCEPT : (representative qs, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  : (qs, tag) ∈ minimised_accept_states_of qs.
Proof.
  unfold minimised_accept_states_of.
  eapply in_list_bind_intro with (x := tag); [ | simpl; left; reflexivity].
  eapply accepting_tags_from_complete. exact ACCEPT.
Qed.

Lemma minimised_accept_states_of_sound (qs : minimised_state) (qs0 : minimised_state) (tag : Token.t)
  (ACCEPT : (qs0, tag) ∈ minimised_accept_states_of qs)
  : qs0 = qs /\ (representative qs, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).
Proof.
  unfold minimised_accept_states_of in ACCEPT.
  pose proof (in_list_bind_elim _ _ _ ACCEPT) as (tag' & ACCEPT' & IN).
  simpl in IN. destruct IN as [EQ | []]. inv EQ.
  split; [reflexivity | ].
  eapply accepting_tags_from_sound. exact ACCEPT'.
Qed.

Lemma minimised_accept_states_complete (qs : minimised_state) (tag : Token.t)
  (QS : qs ∈ minimised_states)
  (ACCEPT : (representative qs, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  : (qs, tag) ∈ minimised_accept_states.
Proof.
  unfold minimised_accept_states.
  eapply in_list_bind_intro with (x := qs); [exact QS | ].
  eapply minimised_accept_states_of_complete. exact ACCEPT.
Qed.

Lemma minimised_accept_states_sound (qs : minimised_state) (tag : Token.t)
  (ACCEPT : (qs, tag) ∈ minimised_accept_states)
  : qs ∈ minimised_states /\ (representative qs, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).
Proof.
  unfold minimised_accept_states in ACCEPT.
  pose proof (in_list_bind_elim _ _ _ ACCEPT) as (qs' & QS & ACCEPT').
  pose proof (minimised_accept_states_of_sound qs' qs tag ACCEPT') as (EQ & ACCEPT_Q).
  subst qs'. eauto.
Qed.

Definition minimise : TaggedDFA.t :=
  hopcroft_certified_minimise.

Theorem minimise_sound (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : TaggedDFA.accepts minimise s tag)
  : TaggedDFA.accepts M s tag.
Proof.
  unfold minimise in ACCEPT. eapply hopcroft_certified_minimise_sound; eauto.
Qed.

Theorem minimise_complete (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : TaggedDFA.accepts M s tag)
  : TaggedDFA.accepts minimise s tag.
Proof.
  unfold minimise. eapply hopcroft_certified_minimise_complete; eauto.
Qed.

Theorem minimise_okay
  (OKAY : okay M)
  : okay minimise.
Proof.
  unfold minimise. eapply hopcroft_certified_minimise_okay. exact OKAY.
Qed.

Definition minimise_numbered : TaggedDFA.t :=
  hopcroft_certified_minimise_numbered.

Theorem minimise_numbered_sound (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : TaggedDFA.accepts minimise_numbered s tag)
  : TaggedDFA.accepts M s tag.
Proof.
  unfold minimise_numbered in ACCEPT.
  eapply hopcroft_certified_minimise_numbered_sound; eauto.
Qed.

Theorem minimise_numbered_complete (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : TaggedDFA.accepts M s tag)
  : TaggedDFA.accepts minimise_numbered s tag.
Proof.
  unfold minimise_numbered.
  eapply hopcroft_certified_minimise_numbered_complete; eauto.
Qed.

Theorem minimise_numbered_okay
  (OKAY : okay M)
  : okay minimise_numbered.
Proof.
  unfold minimise_numbered. eapply hopcroft_certified_minimise_numbered_okay. exact OKAY.
Qed.

Theorem minimise_states_minimal (N : TaggedDFA.t)
  (OKAY : okay M)
  (REACHABLE : all_states_reachable M)
  (OKAY_N : okay N)
  (NODUP_N : NoDup N.(TaggedDFA.states))
  (EQUIV : language_equiv M N)
  : length minimise.(TaggedDFA.states) <= length N.(TaggedDFA.states).
Proof.
  unfold minimise.
  eapply hopcroft_certified_minimise_states_minimal; eauto.
Qed.

Theorem minimise_numbered_states_minimal (N : TaggedDFA.t)
  (OKAY_M : okay M)
  (REACHABLE : all_states_reachable M)
  (OKAY_N : okay N)
  (NODUP_N : NoDup N.(TaggedDFA.states))
  (EQUIV : language_equiv M N)
  : length minimise_numbered.(TaggedDFA.states) <= length N.(TaggedDFA.states).
Proof.
  unfold minimise_numbered.
  eapply hopcroft_certified_minimise_numbered_states_minimal; eauto.
Qed.

End MINIMISATION.

Module Partial.

#[projections(primitive)]
Record TaggedDFA : Type :=
  mk
  { state : Set
  ; state_hasEqDec : hasEqDec@{Set} state
  ; states : list state
  ; start_state : state
  ; accept_states : list (state * Token.t)
  ; transition (q : state) (c : ascii) : state
  } as M.

End Partial.

Section DELETE_DEAD_STATE.

Variable M : TaggedDFA.t.

#[local] Abbreviation Q := M.(TaggedDFA.state).

Definition delete_state_set : Set :=
  list Q.

Definition delete_normalize (qs : delete_state_set) : delete_state_set :=
  filter (fun q => mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q qs) M.(TaggedDFA.states).

Lemma delete_normalize_complete (qs : delete_state_set) (q : Q)
  (STATES : q ∈ M.(TaggedDFA.states))
  (IN : q ∈ qs)
  : q ∈ delete_normalize qs.
Proof.
  unfold delete_normalize. rewrite filter_In. split; [exact STATES | ].
  now rewrite mem_spec.
Qed.

Lemma delete_normalize_sound (qs : delete_state_set) (q : Q)
  (IN : q ∈ delete_normalize qs)
  : q ∈ qs /\ q ∈ M.(TaggedDFA.states).
Proof.
  unfold delete_normalize in IN. rewrite filter_In in IN.
  destruct IN as [STATES MEM]. split; [ | exact STATES].
  now rewrite mem_spec in MEM.
Qed.

Definition delete_successors (q : Q) : delete_state_set :=
  map (M.(TaggedDFA.transition) q) all_asciis.

Definition delete_reachable_move (qs : delete_state_set) : delete_state_set :=
  qs >>= delete_successors.

Definition delete_reachable_step (qs : delete_state_set) : delete_state_set :=
  delete_normalize (union (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) (delete_reachable_move qs) qs).

Definition reachable_states : delete_state_set :=
  iter (length M.(TaggedDFA.states)) delete_reachable_step (delete_normalize [M.(TaggedDFA.start_state)]).

Definition accepting_stateb (q : Q) : bool :=
  existsb (fun '(q', _) => eqb q q') M.(TaggedDFA.accept_states).(kvlist).

Definition accepting_states : delete_state_set :=
  filter accepting_stateb M.(TaggedDFA.states).

Definition predecessorb (q : Q) (p : Q) : bool :=
  existsb (fun c => eqb (M.(TaggedDFA.transition) p c) q) all_asciis.

Definition predecessors (q : Q) : delete_state_set :=
  filter (predecessorb q) M.(TaggedDFA.states).

Definition live_move (qs : delete_state_set) : delete_state_set :=
  qs >>= predecessors.

Definition live_step (qs : delete_state_set) : delete_state_set :=
  delete_normalize (union (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) (live_move qs) qs).

Definition live_states : delete_state_set :=
  iter (length M.(TaggedDFA.states)) live_step accepting_states.

Lemma accepting_stateb_complete (q : Q) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  : accepting_stateb q = true.
Proof.
  unfold accepting_stateb. rewrite existsb_exists.
  exists (q, tag). split; [exact ACCEPT | simpl].
  now rewrite eqb_eq.
Qed.

Lemma accepting_states_complete (q : Q) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  : q ∈ accepting_states.
Proof.
  destruct OKAY as [_ ACCEPT_OKAY _].
  unfold accepting_states. rewrite filter_In. split.
  - eapply ACCEPT_OKAY. exact ACCEPT.
  - eapply accepting_stateb_complete. exact ACCEPT.
Qed.

Definition dead_states : delete_state_set :=
  filter (fun q => negb (mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q live_states)) M.(TaggedDFA.states).

Definition useful_states : delete_state_set :=
  filter (fun q => mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q reachable_states && mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q live_states) M.(TaggedDFA.states).

Definition delete_dead_accept_states : list (Q * Token.t) :=
  filter (fun '(q, _) => mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q live_states) M.(TaggedDFA.accept_states).(kvlist).

Lemma live_step_complete_keep (q : Q) (qs : delete_state_set)
  (STATE : q ∈ M.(TaggedDFA.states))
  (IN : q ∈ qs)
  : q ∈ live_step qs.
Proof.
  unfold live_step.
  eapply delete_normalize_complete; [exact STATE | ].
  ss!.
Qed.

Lemma iter_live_step_keeps (fuel : nat) (q : Q) (qs : delete_state_set)
  (STATE : q ∈ M.(TaggedDFA.states))
  (IN : q ∈ qs)
  : q ∈ iter fuel live_step qs.
Proof.
  revert qs IN. induction fuel as [ | fuel IH]; intros qs IN; simpl.
  - exact IN.
  - eapply IH. eapply live_step_complete_keep; eauto.
Qed.

Lemma accepting_state_live (q : Q) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  : q ∈ live_states.
Proof.
  unfold live_states.
  eapply iter_live_step_keeps.
  - destruct OKAY as [_ ACCEPT_OKAY _]. eapply ACCEPT_OKAY. exact ACCEPT.
  - eapply accepting_states_complete; eauto.
Qed.

Lemma delete_dead_accept_states_complete (q : Q) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.accept_states).(kvlist))
  (LIVE : q ∈ live_states)
  : (q, tag) ∈ delete_dead_accept_states.
Proof.
  unfold delete_dead_accept_states. rewrite filter_In. split; [exact ACCEPT | ].
  now rewrite mem_spec.
Qed.

Lemma delete_dead_accept_states_sound (q : Q) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ delete_dead_accept_states)
  : (q, tag) ∈ M.(TaggedDFA.accept_states).(kvlist) /\ q ∈ live_states.
Proof.
  unfold delete_dead_accept_states in ACCEPT. rewrite filter_In in ACCEPT.
  destruct ACCEPT as [ACCEPT LIVE]. split; [exact ACCEPT | ].
  now rewrite mem_spec in LIVE.
Qed.

Definition delete_normalize_ensemble (qs : delete_state_set) : ensemble Q :=
  fun q => q ∈ M.(TaggedDFA.states) /\ q ∈ qs.

Definition delete_successors_ensemble (q : Q) : ensemble Q :=
  fun q' => exists c, c ∈ all_asciis /\ q' = M.(TaggedDFA.transition) q c.

Definition delete_reachable_move_ensemble (qs : delete_state_set) : ensemble Q :=
  fun q' => exists q, q ∈ qs /\ (exists c, c ∈ all_asciis /\ q' = M.(TaggedDFA.transition) q c).

Definition accepting_state_ensemble (q : Q) : Prop :=
  exists tag, (q, tag) ∈ M.(TaggedDFA.accept_states).(kvlist).

Definition accepting_states_ensemble : ensemble Q :=
  fun q => q ∈ M.(TaggedDFA.states) /\ accepting_state_ensemble q.

Definition predecessor_ensemble (q : Q) : ensemble Q :=
  fun p => p ∈ M.(TaggedDFA.states) /\ (exists c, c ∈ all_asciis /\ M.(TaggedDFA.transition) p c = q).

Definition live_move_ensemble (qs : delete_state_set) : ensemble Q :=
  fun p => p ∈ M.(TaggedDFA.states) /\ (exists q, q ∈ qs /\ (exists c, c ∈ all_asciis /\ M.(TaggedDFA.transition) p c = q)).

Definition dead_states_ensemble : ensemble Q :=
  fun q => q ∈ M.(TaggedDFA.states) /\ ~ q ∈ live_states.

Definition useful_states_ensemble : ensemble Q :=
  fun q => q ∈ M.(TaggedDFA.states) /\ q ∈ reachable_states /\ q ∈ live_states.

Definition delete_dead_accept_state_ensemble : ensemble (Q * Token.t) :=
  fun qtag => let '(q, tag) := qtag in (q, tag) ∈ M.(TaggedDFA.accept_states).(kvlist) /\ q ∈ live_states.

Lemma delete_membership_similarity (qs : delete_state_set) (q : Q)
  : is_similar_to (Similarity := Similarity_bool_Prop) (mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q qs) (q ∈ qs).
Proof.
  do 2 red. des_ifs; ss!.
Qed.

Lemma delete_normalize_similarity (qs : delete_state_set)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (delete_normalize qs) (delete_normalize_ensemble qs).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q. split.
  - intros IN. pose proof (delete_normalize_sound qs q IN) as [IN_QS STATES]. split; [exact STATES | exact IN_QS].
  - intros [STATES IN_QS]. eapply delete_normalize_complete; eauto.
Qed.

Lemma delete_normalize_membership_similarity (qs : delete_state_set) (q : Q)
  : is_similar_to (Similarity := Similarity_bool_Prop) (mem (EQ_DEC := M.(TaggedDFA.state_hasEqDec)) q (delete_normalize qs)) (q ∈ M.(TaggedDFA.states) /\ q ∈ qs).
Proof.
  do 2 red. des_ifs.
  - rewrite mem_spec in Heq. pose proof (delete_normalize_sound qs q Heq) as [IN_QS STATES]. split; [exact STATES | exact IN_QS].
  - rewrite mem_spec in Heq. intros [STATES IN_QS]. eapply Heq. eapply delete_normalize_complete; eauto.
Qed.

Lemma delete_successors_similarity (q : Q)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (delete_successors q) (delete_successors_ensemble q).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q'. split.
  - intros IN. unfold delete_successors in IN. rewrite in_map_iff in IN. destruct IN as (c & EQ & CHAR). exists c. split; [exact CHAR | symmetry; exact EQ].
  - intros (c & CHAR & EQ). unfold delete_successors. rewrite in_map_iff. exists c. split; [symmetry; exact EQ | exact CHAR].
Qed.

Lemma delete_reachable_move_similarity (qs : delete_state_set)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (delete_reachable_move qs) (delete_reachable_move_ensemble qs).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q'. split.
  - intros IN. unfold delete_reachable_move in IN. pose proof (in_list_bind_elim _ _ _ IN) as (q & IN_QS & IN_SUCC). pose proof (delete_successors_similarity q) as SUCC_SIM. rewrite list_corresponds_to_finite_ensemble_iff in SUCC_SIM. pose proof (proj1 (SUCC_SIM q') IN_SUCC) as (c & CHAR & EQ). exists q. split; [exact IN_QS | exists c; split; [exact CHAR | exact EQ]].
  - intros (q & IN_QS & c & CHAR & EQ). unfold delete_reachable_move. eapply in_list_bind_intro with (x := q); [exact IN_QS | ]. pose proof (delete_successors_similarity q) as SUCC_SIM. rewrite list_corresponds_to_finite_ensemble_iff in SUCC_SIM. rewrite -> SUCC_SIM with (x := q'). exists c. split; [exact CHAR | exact EQ].
Qed.

Lemma accepting_stateb_similarity (q : Q)
  : is_similar_to (Similarity := Similarity_bool_Prop) (accepting_stateb q) (accepting_state_ensemble q).
Proof.
  change (if accepting_stateb q then accepting_state_ensemble q else ~ accepting_state_ensemble q).
  destruct (accepting_stateb q) eqn: ACCEPTING.
  - unfold accepting_stateb in ACCEPTING. rewrite existsb_exists in ACCEPTING. destruct ACCEPTING as ([q' tag] & ACCEPT & EQB). simpl in EQB. rewrite eqb_eq in EQB. subst q'. exists tag. exact ACCEPT.
  - intros (tag & ACCEPT). pose proof (accepting_stateb_complete q tag ACCEPT) as ACCEPTING_TRUE. rewrite ACCEPTING in ACCEPTING_TRUE. inv ACCEPTING_TRUE.
Qed.

Lemma accepting_states_similarity
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) accepting_states accepting_states_ensemble.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q. split.
  - intros IN. unfold accepting_states in IN. rewrite filter_In in IN. destruct IN as [STATE ACCEPTING]. split; [exact STATE | ]. pose proof (accepting_stateb_similarity q) as ACCEPTING_SIM. change (if accepting_stateb q then accepting_state_ensemble q else ~ accepting_state_ensemble q) in ACCEPTING_SIM. rewrite ACCEPTING in ACCEPTING_SIM. exact ACCEPTING_SIM.
  - intros [STATE ACCEPTING]. unfold accepting_states. rewrite filter_In. split; [exact STATE | ]. pose proof (accepting_stateb_similarity q) as ACCEPTING_SIM. change (if accepting_stateb q then accepting_state_ensemble q else ~ accepting_state_ensemble q) in ACCEPTING_SIM. destruct (accepting_stateb q) eqn: ACCEPTINGB; [reflexivity | contradiction].
Qed.

Lemma predecessorb_similarity (q : Q) (p : Q)
  : is_similar_to (Similarity := Similarity_bool_Prop) (predecessorb q p) (exists c, c ∈ all_asciis /\ M.(TaggedDFA.transition) p c = q).
Proof.
  change (if predecessorb q p then (exists c, c ∈ all_asciis /\ M.(TaggedDFA.transition) p c = q) else ~ (exists c, c ∈ all_asciis /\ M.(TaggedDFA.transition) p c = q)).
  destruct (predecessorb q p) eqn: PRED.
  - unfold predecessorb in PRED. rewrite existsb_exists in PRED. destruct PRED as (c & CHAR & EQB). rewrite eqb_eq in EQB. exists c. split; [exact CHAR | exact EQB].
  - intros (c & CHAR & EQ). assert (PRED_TRUE : predecessorb q p = true).
    { unfold predecessorb. rewrite existsb_exists. exists c. split; [exact CHAR | ]. rewrite eqb_eq. exact EQ. }
    rewrite PRED in PRED_TRUE. inv PRED_TRUE.
Qed.

Lemma predecessors_similarity (q : Q)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (predecessors q) (predecessor_ensemble q).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros p. split.
  - intros IN. unfold predecessors in IN. rewrite filter_In in IN. destruct IN as [STATE PRED]. split; [exact STATE | ]. pose proof (predecessorb_similarity q p) as PRED_SIM. change (if predecessorb q p then (exists c, c ∈ all_asciis /\ M.(TaggedDFA.transition) p c = q) else ~ (exists c, c ∈ all_asciis /\ M.(TaggedDFA.transition) p c = q)) in PRED_SIM. rewrite PRED in PRED_SIM. exact PRED_SIM.
  - intros [STATE PRED]. unfold predecessors. rewrite filter_In. split; [exact STATE | ]. pose proof (predecessorb_similarity q p) as PRED_SIM. change (if predecessorb q p then (exists c, c ∈ all_asciis /\ M.(TaggedDFA.transition) p c = q) else ~ (exists c, c ∈ all_asciis /\ M.(TaggedDFA.transition) p c = q)) in PRED_SIM. destruct (predecessorb q p) eqn: PREDB; [reflexivity | contradiction].
Qed.

Lemma live_move_similarity (qs : delete_state_set)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (live_move qs) (live_move_ensemble qs).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros p. split.
  - intros IN. unfold live_move in IN. pose proof (in_list_bind_elim _ _ _ IN) as (q & IN_QS & IN_PRED). pose proof (predecessors_similarity q) as PRED_SIM. rewrite list_corresponds_to_finite_ensemble_iff in PRED_SIM. pose proof (proj1 (PRED_SIM p) IN_PRED) as [STATE (c & CHAR & EQ)]. split; [exact STATE | exists q; split; [exact IN_QS | exists c; split; [exact CHAR | exact EQ]]].
  - intros [STATE (q & IN_QS & c & CHAR & EQ)]. unfold live_move. eapply in_list_bind_intro with (x := q); [exact IN_QS | ]. pose proof (predecessors_similarity q) as PRED_SIM. rewrite list_corresponds_to_finite_ensemble_iff in PRED_SIM. rewrite -> PRED_SIM with (x := p). split; [exact STATE | exists c; split; [exact CHAR | exact EQ]].
Qed.

Lemma dead_states_similarity
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) dead_states dead_states_ensemble.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q. split.
  - intros IN. unfold dead_states in IN. rewrite filter_In in IN. destruct IN as [STATE LIVE]. rewrite negb_true_iff in LIVE. rewrite mem_spec in LIVE. split; [exact STATE | exact LIVE].
  - intros [STATE NOT_LIVE]. unfold dead_states. rewrite filter_In. split; [exact STATE | ]. rewrite negb_true_iff. rewrite mem_spec. exact NOT_LIVE.
Qed.

Lemma useful_states_similarity
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) useful_states useful_states_ensemble.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros q. split.
  - intros IN. unfold useful_states in IN. rewrite filter_In in IN. destruct IN as [STATE USEFUL]. rewrite andb_true_iff in USEFUL. destruct USEFUL as [REACH LIVE]. rewrite mem_spec in REACH. rewrite mem_spec in LIVE. split; [exact STATE | split; [exact REACH | exact LIVE]].
  - intros [STATE [REACH LIVE]]. unfold useful_states. rewrite filter_In. split; [exact STATE | ]. rewrite andb_true_iff. split; rewrite mem_spec; assumption.
Qed.

Lemma delete_dead_accept_states_similarity
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) delete_dead_accept_states delete_dead_accept_state_ensemble.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros [q tag]. split.
  - eapply delete_dead_accept_states_sound.
  - intros [ACCEPT LIVE]. eapply delete_dead_accept_states_complete; eauto.
Qed.

Definition delete_dead_state : Partial.TaggedDFA :=
  {|
    Partial.state := Q;
    Partial.state_hasEqDec := M.(TaggedDFA.state_hasEqDec);
    Partial.states := live_states;
    Partial.start_state := M.(TaggedDFA.start_state);
    Partial.accept_states := delete_dead_accept_states;
    Partial.transition := M.(TaggedDFA.transition);
  |}.

End DELETE_DEAD_STATE.

Module Numbering.

Theorem numbered_accept_states_order (M : TaggedDFA.t)
  : numbered_accept_states M = map (fun '(q, tag) => (state_number M q, tag)) M.(TaggedDFA.accept_states).(kvlist).
Proof.
  unfold numbered_accept_states.
  remember M.(TaggedDFA.accept_states) as accept_states eqn: ACCEPT_STATES.
  clear ACCEPT_STATES.
  induction accept_states.(kvlist) as [ | [q tag] qtags IH]; simpl; f_equal; eauto.
Qed.

Theorem number_states_sound (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : accepts (number_states M) s tag)
  : accepts M s tag.
Proof.
  eapply number_states_sound; eauto.
Qed.

Theorem number_states_complete (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : accepts M s tag)
  : accepts (number_states M) s tag.
Proof.
  eapply number_states_complete; eauto.
Qed.

Theorem number_states_correct (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  : accepts (number_states M) s tag <-> accepts M s tag.
Proof.
  split.
  - intros ACCEPT. eapply number_states_sound; eauto.
  - intros ACCEPT. eapply number_states_complete; eauto.
Qed.

End Numbering.

Module Subset.

Module Abs.

Definition subset_state (M : TaggedENFA.t) : Type :=
  ensemble M.(TaggedENFA.state).

Definition eclosure (M : TaggedENFA.t) (q : M.(TaggedENFA.state)) : ensemble M.(TaggedENFA.state) :=
  TaggedENFA.eclosure M.(TaggedENFA.eps_step) q.

Definition eclose_step (M : TaggedENFA.t) (qs : TaggedDFA.subset_state M) : ensemble M.(TaggedENFA.state) :=
  fun q => q ∈ M.(TaggedENFA.states) /\ (q ∈ TaggedDFA.eps_move M qs \/ q ∈ qs).

Definition transition (M : TaggedENFA.t) (qs : TaggedDFA.subset_state M) (c : ascii) : ensemble M.(TaggedENFA.state) :=
  subset_transition_ensemble M qs c.

Definition accept_states (M : TaggedENFA.t) : ensemble (TaggedDFA.subset_state M * Token.t) :=
  subset_accept_state_ensemble M.

End Abs.

Theorem normalize_canonical (M : TaggedENFA.t) (qs : subset_state M)
  (NODUP : NoDup M.(TaggedENFA.states))
  : NoDup (normalize M qs).
Proof.
  enough (FILTER_NODUP : forall states : list M.(TaggedENFA.state), NoDup states -> NoDup (filter (fun q => mem (EQ_DEC := M.(TaggedENFA.state_hasEqDec)) q qs) states)).
  { unfold normalize. eapply FILTER_NODUP. exact NODUP. }
  clear. intros states NODUP_STATES. induction states as [ | q states IH]; simpl.
  - constructor.
  - inversion NODUP_STATES as [ | q' states' NOTIN NODUP]; subst. des_ifs.
    + constructor.
      * intros IN. rewrite filter_In in IN. tauto.
      * eapply IH. exact NODUP.
    + eapply IH. exact NODUP.
Qed.

Theorem eclose_step_refines (M : TaggedENFA.t) (qs : subset_state M)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (eclose_step M qs) (Abs.eclose_step M qs).
Proof.
  s!. intros q. split.
  - intros IN. unfold eclose_step in IN.
    rewrite in_normalize_iff in IN. destruct IN as [IN_UNION STATE].
    rewrite in_union_iff in IN_UNION. destruct IN_UNION as [IN_EPS | IN_QS]; ss!.
  - intros [STATE IN_STEP]. unfold eclose_step.
    rewrite in_normalize_iff. rewrite in_union_iff. ss!.
Qed.

Theorem subset_start_state_refines (M : TaggedENFA.t)
  (OKAY : TaggedENFA.okay M)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (subset_start_state M) (fun q : M.(TaggedENFA.state) => q \in Abs.eclosure M M.(TaggedENFA.start_state)).
Proof.
  s!. intros q. split.
  - eapply subset_start_state_sound.
  - intros CLOS. unfold subset_start_state. eapply eclose_complete with (q := M.(TaggedENFA.start_state)); eauto.
    + intros q' IN. destruct OKAY as [START_OKAY _ _ _]. destruct IN as [EQ | []]. now subst q'.
    + left. reflexivity.
Qed.

Theorem subset_construct_correct (M : TaggedENFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : TaggedENFA.okay M)
  : accepts (subset_construct M) s tag <-> TaggedENFA.accepts M s tag.
Proof.
  split.
  - intros ACCEPT. eapply subset_construct_sound; eauto.
  - intros ACCEPT. eapply subset_construct_complete; eauto.
Qed.

End Subset.

Module Minimise.

Module Abs.

Abbreviation quotient_state := minimised_state.

Abbreviation quotient_dfa := minimise.

Theorem quotient_language_equiv (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  : accepts (quotient_dfa M) s tag <-> accepts M s tag.
Proof.
  split.
  - intros ACCEPT. eapply TaggedDFA.minimise_sound; eauto.
  - intros ACCEPT. eapply TaggedDFA.minimise_complete; eauto.
Qed.

End Abs.

Module Refine.

Theorem minimisation_equiv_b_sound_unbounded (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state))
  (OKAY : okay M)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (EQUIV : minimisation_equivb M (minimisation_fuel M) q1 q2 = true)
  : right_language_equiv M q1 q2.
Proof.
  eapply minimisation_equivb_right_language_equiv; eauto.
Qed.

Theorem right_language_equiv_minimisation_equiv_b (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state))
  (EQUIV : right_language_equiv M q1 q2)
  : minimisation_equivb M (minimisation_fuel M) q1 q2 = true.
Proof.
  eapply right_language_equiv_minimisation_equivb. exact EQUIV.
Qed.

Theorem minimisation_class_refines (M : TaggedDFA.t) (q : M.(TaggedDFA.state))
  (OKAY : okay M)
  (STATE : q ∈ M.(TaggedDFA.states))
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (minimisation_class M q) (fun q' => q' ∈ M.(TaggedDFA.states) /\ right_language_equiv M q q').
Proof.
  s!. intros q'. unfold minimisation_class.
  rewrite filter_In. split.
  - intros [IN_STATE EQUIV]. split; [exact IN_STATE | eapply minimisation_equiv_b_sound_unbounded; eauto].
  - intros [IN_STATE EQUIV]. split; [exact IN_STATE | eapply right_language_equiv_minimisation_equiv_b; exact EQUIV].
Qed.

Theorem representative_choice_preserves_right_language (M : TaggedDFA.t) (q : M.(TaggedDFA.state))
  (OKAY : okay M)
  (IN : q ∈ M.(TaggedDFA.states))
  : right_language_equiv M (representative M (minimisation_class M q)) q.
Proof.
  ii; symmetry; revert s tag. eapply minimisation_equivb_right_language_equiv; eauto.
  - now eapply minimisation_class_representative_state.
  - now eapply representative_minimisation_class_equiv.
Qed.

End Refine.

Theorem minimise_correct (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  : accepts (minimise M) s tag <-> accepts M s tag.
Proof.
  split.
  - intros ACCEPT. eapply minimise_sound; eauto.
  - intros ACCEPT. eapply minimise_complete; eauto.
Qed.

Theorem minimise_numbered_correct (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  : accepts (minimise_numbered M) s tag <-> accepts M s tag.
Proof.
  split.
  - intros ACCEPT. eapply minimise_numbered_sound; eauto.
  - intros ACCEPT. eapply minimise_numbered_complete; eauto.
Qed.

Module Hopcroft.

Theorem certified_minimise_correct (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  : accepts (hopcroft_certified_minimise M) s tag <-> accepts M s tag.
Proof.
  split.
  - intros ACCEPT. eapply hopcroft_certified_minimise_sound; eauto.
  - intros ACCEPT. eapply hopcroft_certified_minimise_complete; eauto.
Qed.

End Hopcroft.

End Minimise.

Module DeleteDead.

Abbreviation delete_dead_state := delete_dead_state.

Module Abs.

Definition reachable (M : TaggedDFA.t) : ensemble M.(TaggedDFA.state) :=
  fun q => q ∈ reachable_states M.

Definition live (M : TaggedDFA.t) : ensemble M.(TaggedDFA.state) :=
  fun q => q ∈ live_states M.

Definition useful (M : TaggedDFA.t) : ensemble M.(TaggedDFA.state) :=
  useful_states_ensemble M.

End Abs.

End DeleteDead.

End TaggedDFA.

Module LGS.

Definition t : Type :=
  TaggedDFA.Partial.TaggedDFA.

Fixpoint delta (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s : Input.t) {struct s} : M.(TaggedDFA.Partial.state) :=
  match s with
  | [] => q
  | c :: s' => delta M (M.(TaggedDFA.Partial.transition) q c) s'
  end.

Definition accepts (M : LGS.t) (s : Input.t) (tag : Token.t) : Prop :=
  (delta M M.(TaggedDFA.Partial.start_state) s, tag) ∈ M.(TaggedDFA.Partial.accept_states).

Definition accepted_tags (M : LGS.t) (s : Input.t) : ensemble Token.t :=
  fun tag => accepts M s tag.

Lemma delta_app (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s1 : Input.t) (s2 : Input.t)
  : delta M q (s1 ++ s2) = delta M (delta M q s1) s2.
Proof.
  revert q. induction s1 as [ | c s1 IH]; intros q; simpl; eauto.
Qed.

Lemma delete_dead_state_delta (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) (s : Input.t)
  : delta (TaggedDFA.delete_dead_state M) q s = TaggedDFA.delta M q s.
Proof.
  revert q. induction s as [ | c s IH]; intros q; simpl; eauto.
Qed.

Theorem delete_dead_state_sound (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  (ACCEPT : accepts (TaggedDFA.delete_dead_state M) s tag)
  : TaggedDFA.accepts M s tag.
Proof.
  unfold accepts, TaggedDFA.accepts in *. rewrite delete_dead_state_delta in ACCEPT. cbn in ACCEPT.
  pose proof (TaggedDFA.delete_dead_accept_states_similarity M) as DELETE_SPEC.
  rewrite list_corresponds_to_finite_ensemble_iff in DELETE_SPEC.
  rewrite DELETE_SPEC in ACCEPT. simpl in ACCEPT. destruct ACCEPT as [ACCEPT' _]. exact ACCEPT'.
Qed.

Theorem delete_dead_state_complete (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : TaggedDFA.okay M)
  (ACCEPT : TaggedDFA.accepts M s tag)
  : accepts (TaggedDFA.delete_dead_state M) s tag.
Proof.
  unfold accepts, TaggedDFA.accepts in *. rewrite delete_dead_state_delta. cbn.
  pose proof (TaggedDFA.delete_dead_accept_states_similarity M) as DELETE_SPEC.
  rewrite list_corresponds_to_finite_ensemble_iff in DELETE_SPEC.
  rewrite DELETE_SPEC. simpl. split; [exact ACCEPT | eapply TaggedDFA.accepting_state_live; eauto].
Qed.

Theorem delete_dead_state_correct (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : TaggedDFA.okay M)
  : accepts (TaggedDFA.delete_dead_state M) s tag <-> TaggedDFA.accepts M s tag.
Proof.
  split.
  - eapply delete_dead_state_sound.
  - now eapply delete_dead_state_complete.
Qed.

Fixpoint first_accepting_token_from {Q : Set} `{Q_hasEqDec : hasEqDec@{Set} Q} (q : Q) (accept_states : list (Q * Token.t)) {struct accept_states} : option Token.t :=
  match accept_states with
  | [] => None
  | (q', tag) :: accept_states' => if eq_dec q q' then Some tag else first_accepting_token_from q accept_states'
  end.

Lemma first_accepting_token_from_sound {Q : Set} `{Q_hasEqDec : hasEqDec@{Set} Q} (q : Q) (accept_states : list (Q * Token.t)) (tag : Token.t)
  (FIND : first_accepting_token_from q accept_states = Some tag)
  : (q, tag) ∈ accept_states.
Proof.
  induction accept_states as [ | [q' tag'] accept_states IH]; simpl in FIND; [inv FIND | ].
  destruct (eq_dec q q') as [EQ | NE].
  - subst q'. inv FIND. left. reflexivity.
  - right. eapply IH. exact FIND.
Qed.

Lemma first_accepting_token_from_first {Q : Set} `{Q_hasEqDec : hasEqDec@{Set} Q} (q : Q) (accept_states : list (Q * Token.t)) (tag : Token.t)
  (FIND : first_accepting_token_from q accept_states = Some tag)
  : exists prefix, exists suffix, accept_states = prefix ++ (q, tag) :: suffix /\ (forall tag', ~ (q, tag') ∈ prefix).
Proof.
  induction accept_states as [ | [q' tag'] accept_states IH]; simpl in FIND; [inv FIND | ].
  destruct (eq_dec q q') as [EQ | NE].
  - subst q'. inv FIND. exists [], accept_states. split; [reflexivity | ].
    intros tag0 IN. contradiction.
  - pose proof (IH FIND) as (prefix & suffix & EQ & FIRST).
    exists ((q', tag') :: prefix), suffix. split.
    + rewrite EQ. reflexivity.
    + intros tag0 [HEAD | IN_PREFIX].
      * inv HEAD. contradiction.
      * eapply FIRST. exact IN_PREFIX.
Qed.

Lemma first_accepting_token_from_complete_some {Q : Set} `{Q_hasEqDec : hasEqDec@{Set} Q} (q : Q) (accept_states : list (Q * Token.t))
  (ACCEPT : exists tag, (q, tag) ∈ accept_states)
  : exists tag, first_accepting_token_from q accept_states = Some tag.
Proof.
  induction accept_states as [ | [q' tag'] accept_states IH]; simpl in ACCEPT |- *.
  - destruct ACCEPT as (tag & ACCEPT). contradiction.
  - destruct (eq_dec q q') as [EQ | NE].
    + exists tag'. reflexivity.
    + destruct ACCEPT as (tag & [EQ | ACCEPT]).
      * inv EQ. contradiction.
      * eapply IH. exists tag. exact ACCEPT.
Qed.

Definition first_accepting_token (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) : option Token.t :=
  @first_accepting_token_from M.(TaggedDFA.Partial.state) M.(TaggedDFA.Partial.state_hasEqDec) q M.(TaggedDFA.Partial.accept_states).

Lemma first_accepting_token_sound (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (tag : Token.t)
  (FIND : first_accepting_token M q = Some tag)
  : (q, tag) ∈ M.(TaggedDFA.Partial.accept_states).
Proof.
  eapply first_accepting_token_from_sound. exact FIND.
Qed.

Lemma first_accepting_token_complete_some (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.Partial.accept_states))
  : exists tag', first_accepting_token M q = Some tag'.
Proof.
  eapply first_accepting_token_from_complete_some. exists tag. exact ACCEPT.
Qed.

Fixpoint maximal_munch (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s : list ascii) (best : option (list ascii * Token.t)) {struct s} : option (list ascii * Token.t) :=
  match s with
  | [] => best
  | c :: s' =>
    let q' := M.(TaggedDFA.Partial.transition) q c in
    let best' := B.maybe (A := _) (B := fun _ => _) best (fun tag => Some (s', tag)) (first_accepting_token M q') in
    maximal_munch M q' s' best'
  end.

Lemma maximal_munch_some_if_best_some (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s : Input.t) (rest : Input.t) (tag : Token.t)
  : exists rest', exists tag', maximal_munch M q s (Some (rest, tag)) = Some (rest', tag').
Proof.
  revert q rest tag. induction s as [ | c s IH]; intros q rest tag; simpl.
  - exists rest, tag. reflexivity.
  - destruct (first_accepting_token M (M.(TaggedDFA.Partial.transition) q c)) as [tag' | ]; cbn; eauto.
Qed.

Lemma maximal_munch_some_accepted_prefix (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (consumed : Input.t) (rest : Input.t) (best : option (Input.t * Token.t)) (tag : Token.t)
  (NONEMPTY : ~ consumed = [])
  (ACCEPT : (delta M q consumed, tag) ∈ M.(TaggedDFA.Partial.accept_states))
  : exists rest', exists tag', maximal_munch M q (consumed ++ rest) best = Some (rest', tag').
Proof.
  revert q rest best tag NONEMPTY ACCEPT.
  induction consumed as [ | c consumed IH]; intros q rest best tag NONEMPTY ACCEPT; [contradiction | ].
  simpl in ACCEPT |- *.
  set (q' := M.(TaggedDFA.Partial.transition) q c) in *.
  destruct consumed as [ | c' consumed'].
  - simpl in ACCEPT. destruct (first_accepting_token M q') as [tag' | ] eqn: FIND; cbn.
    + eapply maximal_munch_some_if_best_some.
    + pose proof (first_accepting_token_complete_some M q' tag ACCEPT) as (tag' & FIND').
      rewrite FIND in FIND'. inv FIND'.
  - destruct (first_accepting_token M q') as [tag' | ] eqn: FIND; cbn.
    + eapply IH; [discriminate | exact ACCEPT].
    + eapply IH; [discriminate | exact ACCEPT].
Qed.

Definition munch_accepts (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s : Input.t) (rest : Input.t) (tag : Token.t) : Prop :=
  exists consumed, s = consumed ++ rest /\ (delta M q consumed, tag) ∈ M.(TaggedDFA.Partial.accept_states).

Lemma maximal_munch_sound_aux (M : LGS.t) (q0 : M.(TaggedDFA.Partial.state)) (s0 : Input.t) (q : M.(TaggedDFA.Partial.state)) (s : Input.t) (best : option (Input.t * Token.t)) (rest : Input.t) (tag : Token.t)
  (CUR : exists consumed, s0 = consumed ++ s /\ q = delta M q0 consumed)
  (BEST : forall rest0, forall tag0, best = Some (rest0, tag0) -> munch_accepts M q0 s0 rest0 tag0)
  (SCAN : maximal_munch M q s best = Some (rest, tag))
  : munch_accepts M q0 s0 rest tag.
Proof.
  revert q best rest tag CUR BEST SCAN.
  induction s as [ | c s IH]; intros q best rest tag CUR BEST SCAN; simpl in SCAN.
  - eapply BEST. exact SCAN.
  - destruct CUR as (consumed & EQ_INPUT & EQ_STATE). subst q.
    set (q' := M.(TaggedDFA.Partial.transition) (delta M q0 consumed) c) in *.
    assert (NEXT_INPUT : s0 = (consumed ++ [c]) ++ s).
    { rewrite EQ_INPUT. rewrite <- app_assoc. reflexivity. }
    assert (NEXT_STATE : q' = delta M q0 (consumed ++ [c])).
    { subst q'. rewrite delta_app. reflexivity. }
    destruct (first_accepting_token M q') as [tag' | ] eqn: FIND; cbn in SCAN.
    + eapply IH with (q := q') (best := Some (s, tag')); [ | | exact SCAN].
      * exists (consumed ++ [c]). split.
        { exact NEXT_INPUT. }
        { exact NEXT_STATE. }
      * intros rest0 tag0 BEST'. inv BEST'.
        exists (consumed ++ [c]). split.
        { exact NEXT_INPUT. }
        { rewrite <- NEXT_STATE. eapply first_accepting_token_sound. exact FIND. }
    + eapply IH with (q := q') (best := best); [ | | exact SCAN].
      * exists (consumed ++ [c]). split.
        { exact NEXT_INPUT. }
        { exact NEXT_STATE. }
      * intros rest0 tag0 BEST'. eapply BEST. exact BEST'.
Qed.

Theorem maximal_munch_sound (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s : Input.t) (best : option (Input.t * Token.t)) (rest : Input.t) (tag : Token.t)
  (BEST : forall rest0, forall tag0, best = Some (rest0, tag0) -> munch_accepts M q s rest0 tag0)
  (SCAN : maximal_munch M q s best = Some (rest, tag))
  : munch_accepts M q s rest tag.
Proof.
  eapply maximal_munch_sound_aux with (q := q) (s := s) (best := best); eauto.
  exists []. split; reflexivity.
Qed.

Definition scan_one (M : LGS.t) (s : list ascii) : option (list ascii * Token.t) :=
  maximal_munch M M.(TaggedDFA.Partial.start_state) s None.

Definition scan_candidate (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t) : Prop :=
  exists consumed, s = consumed ++ rest /\ (~ consumed = []) /\ accepts M consumed tag.

Lemma maximal_munch_length_le (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s : list ascii) (best : option (list ascii * Token.t)) (rest : list ascii) (tag : Token.t) (n : nat)
  (BEST_LE : forall rest0, forall tag0, best = Some (rest0, tag0) -> length rest0 <= n)
  (INPUT_LE : length s <= n)
  (SCAN : maximal_munch M q s best = Some (rest, tag))
  : length rest <= n.
Proof.
  revert q best rest tag n BEST_LE INPUT_LE SCAN.
  induction s as [ | c s IH]; intros q best rest tag n BEST_LE INPUT_LE SCAN; simpl in SCAN.
  - eapply BEST_LE. exact SCAN.
  - destruct (first_accepting_token M (M.(TaggedDFA.Partial.transition) q c)) as [tag' | ] eqn: FIND; cbn in SCAN.
    + eapply IH with (q := M.(TaggedDFA.Partial.transition) q c) (best := Some (s, tag')) (rest := rest) (tag := tag) (n := n).
      * intros rest0 tag0 BEST. injection BEST as EQ_REST EQ_TAG. subst rest0. simpl in INPUT_LE. lia.
      * simpl in INPUT_LE. lia.
      * exact SCAN.
    + eapply IH with (q := M.(TaggedDFA.Partial.transition) q c) (best := best) (rest := rest) (tag := tag) (n := n).
      * intros rest0 tag0 BEST. pose proof (BEST_LE rest0 tag0 BEST). lia.
      * simpl in INPUT_LE. lia.
      * exact SCAN.
Qed.

Lemma maximal_munch_length_le_accepted_prefix (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (consumed : Input.t) (rest : Input.t) (best : option (Input.t * Token.t)) (rest' : Input.t) (tag' : Token.t) (tag : Token.t)
  (NONEMPTY : ~ consumed = [])
  (ACCEPT : (delta M q consumed, tag) ∈ M.(TaggedDFA.Partial.accept_states))
  (SCAN : maximal_munch M q (consumed ++ rest) best = Some (rest', tag'))
  : length rest' <= length rest.
Proof.
  revert q rest best rest' tag' tag NONEMPTY ACCEPT SCAN.
  induction consumed as [ | c consumed IH]; intros q rest best rest' tag' tag NONEMPTY ACCEPT SCAN; [contradiction | ].
  simpl in ACCEPT, SCAN.
  set (q' := M.(TaggedDFA.Partial.transition) q c) in *.
  destruct consumed as [ | c' consumed'].
  - simpl in ACCEPT.
    destruct (first_accepting_token M q') as [tag0 | ] eqn: FIND; cbn in SCAN.
    + eapply maximal_munch_length_le with (M := M) (q := q') (s := rest) (best := Some (rest, tag0)) (rest := rest') (tag := tag') (n := length rest); [ | lia | exact SCAN].
      intros rest0 tag1 BEST. inv BEST. lia.
    + pose proof (first_accepting_token_complete_some M q' tag ACCEPT) as (tag0 & FIND').
      rewrite FIND in FIND'. inv FIND'.
  - destruct (first_accepting_token M q') as [tag0 | ] eqn: FIND; cbn in SCAN.
    + eapply IH; [discriminate | exact ACCEPT | exact SCAN].
    + eapply IH; [discriminate | exact ACCEPT | exact SCAN].
Qed.

Lemma scan_one_length_lt (M : LGS.t) (s : list ascii) (rest : list ascii) (tag : Token.t)
  (SCAN : scan_one M s = Some (rest, tag))
  : length rest < length s.
Proof.
  destruct s as [ | c s]; simpl in SCAN; [inv SCAN | ].
  unfold scan_one in SCAN. simpl in SCAN.
  destruct (first_accepting_token M (M.(TaggedDFA.Partial.transition) M.(TaggedDFA.Partial.start_state) c)) as [tag' | ] eqn: FIND; cbn in SCAN.
  - pose proof (maximal_munch_length_le M (M.(TaggedDFA.Partial.transition) M.(TaggedDFA.Partial.start_state) c) s (Some (s, tag')) rest tag (length s)) as LENGTH.
    assert (LE : length rest <= length s).
    { eapply LENGTH; [ | lia | exact SCAN]. intros rest0 tag0 BEST. inversion BEST; subst. lia. }
    simpl. lia.
  - pose proof (maximal_munch_length_le M (M.(TaggedDFA.Partial.transition) M.(TaggedDFA.Partial.start_state) c) s None rest tag (length s)) as LENGTH.
    assert (LE : length rest <= length s).
    { eapply LENGTH; [intros rest0 tag0 BEST; inv BEST | lia | exact SCAN]. }
    simpl. lia.
Qed.

Theorem delete_dead_state_scan_progress (M : TaggedDFA.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (SCAN : scan_one (TaggedDFA.delete_dead_state M) s = Some (rest, tag))
  : length rest < length s.
Proof.
  eapply scan_one_length_lt. exact SCAN.
Qed.

Theorem scan_one_sound (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (SCAN : scan_one M s = Some (rest, tag))
  : exists consumed, s = consumed ++ rest /\ accepts M consumed tag /\ length rest < length s.
Proof.
  pose proof SCAN as SCAN_LENGTH.
  unfold scan_one in SCAN.
  pose proof (maximal_munch_sound M M.(TaggedDFA.Partial.start_state) s None rest tag) as SOUND.
  assert (BEST : forall rest0, forall tag0, None = Some (rest0, tag0) -> munch_accepts M M.(TaggedDFA.Partial.start_state) s rest0 tag0).
  { intros rest0 tag0 BEST. inv BEST. }
  pose proof (SOUND BEST SCAN) as (consumed & EQ_INPUT & ACCEPT).
  exists consumed. repeat split; eauto.
  eapply scan_one_length_lt. exact SCAN_LENGTH.
Qed.

Lemma scan_one_maximal (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (SCAN : scan_one M s = Some (rest, tag))
  : scan_candidate M s rest tag /\ (forall rest', forall tag', scan_candidate M s rest' tag' -> length rest <= length rest').
Proof.
  split.
  - pose proof (scan_one_sound M s rest tag SCAN) as (consumed & EQ_INPUT & ACCEPT & LT).
    exists consumed. repeat split; eauto.
    intros EQ. subst consumed. simpl in EQ_INPUT. subst s. lia.
  - intros rest' tag' (consumed & EQ_INPUT & NONEMPTY & ACCEPT).
    unfold scan_one in SCAN. rewrite EQ_INPUT in SCAN.
    unfold accepts in ACCEPT.
    eapply maximal_munch_length_le_accepted_prefix; eauto.
Qed.

Theorem scan_one_complete (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (CANDIDATE : scan_candidate M s rest tag)
  : exists rest', exists tag', scan_one M s = Some (rest', tag') /\ length rest' <= length rest.
Proof.
  destruct CANDIDATE as (consumed & EQ_INPUT & NONEMPTY & ACCEPT).
  unfold scan_one. rewrite EQ_INPUT. unfold accepts in ACCEPT.
  pose proof (maximal_munch_some_accepted_prefix M M.(TaggedDFA.Partial.start_state) consumed rest None tag NONEMPTY ACCEPT) as (rest' & tag' & SCAN).
  exists rest', tag'. split; [exact SCAN | eapply maximal_munch_length_le_accepted_prefix; eauto].
Qed.

Corollary scan_one_some_iff (M : LGS.t) (s : Input.t)
  : (exists rest, exists tag, scan_one M s = Some (rest, tag)) <-> (exists rest, exists tag, scan_candidate M s rest tag).
Proof.
  split.
  - intros (rest & tag & SCAN).
    pose proof (scan_one_maximal M s rest tag SCAN) as [CANDIDATE _].
    exists rest, tag. exact CANDIDATE.
  - intros (rest & tag & CANDIDATE).
    pose proof (scan_one_complete M s rest tag CANDIDATE) as (rest' & tag' & SCAN & _).
    exists rest', tag'. exact SCAN.
Qed.

Inductive scan_all_spec (M : LGS.t) : Input.t -> list Token.t -> Prop :=
  | scan_all_spec_nil
    : scan_all_spec M [] []
  | scan_all_spec_cons s rest tag tags
    (SCAN : scan_one M s = Some (rest, tag))
    (REST : scan_all_spec M rest tags)
    : scan_all_spec M s (tag :: tags).

Inductive scan_all_accepts (M : LGS.t) : Input.t -> list Token.t -> Prop :=
  | scan_all_accepts_nil
    : scan_all_accepts M [] []
  | scan_all_accepts_cons consumed rest tag tags
    (ACCEPT : accepts M consumed tag)
    (REST : scan_all_accepts M rest tags)
    : scan_all_accepts M (consumed ++ rest) (tag :: tags).

Definition input_lt (s1 : Input.t) (s2 : Input.t) : Prop :=
  length s1 < length s2.

Fixpoint scan_all' (M : LGS.t) (s : list ascii) (H_Acc : Acc input_lt s) {struct H_Acc} : option (list Token.t) :=
  if L.null s then
    Some []
  else
    match scan_one M s with
    | None => None
    | Some (rest, tag) =>
      match lt_dec (length rest) (length s) with
      | left LT =>
        match scan_all' M rest (Acc_inv H_Acc rest LT) with
        | None => None
        | Some tags => Some (tag :: tags)
        end
      | right _ => None
      end
    end.

Definition scan_all (M : LGS.t) (s : list ascii) : option (list Token.t) :=
  scan_all' M s (L.length_lt_wf s).

Lemma scan_all'_sound (M : LGS.t) (s : Input.t) (H_Acc : Acc input_lt s) (tags : list Token.t)
  (SCAN : scan_all' M s H_Acc = Some tags)
  : scan_all_spec M s tags.
Proof.
  revert s H_Acc tags SCAN.
  refine (fix IH (s : Input.t) (H_Acc : Acc input_lt s) (tags : list Token.t) (SCAN : scan_all' M s H_Acc = Some tags) {struct H_Acc} : scan_all_spec M s tags := _).
  destruct H_Acc as [H_Acc_inv].
  destruct s as [ | c s]; simpl in SCAN.
  - inv SCAN. constructor.
  - destruct (scan_one M (c :: s)) as [[rest tag] | ] eqn: SCAN_ONE; [ | inv SCAN].
    destruct (lt_dec (length rest) (S (length s))) as [LT | NLT]; cbn in SCAN; [ | inv SCAN].
    destruct (scan_all' M rest (H_Acc_inv rest LT)) as [tags' | ] eqn: SCAN_REST; cbn in SCAN; inv SCAN.
    eapply scan_all_spec_cons with (rest := rest); [exact SCAN_ONE | ].
    eapply IH. exact SCAN_REST.
Qed.

Theorem scan_all_sound (M : LGS.t) (s : Input.t) (tags : list Token.t)
  (SCAN : scan_all M s = Some tags)
  : scan_all_spec M s tags.
Proof.
  unfold scan_all in SCAN. eapply scan_all'_sound. exact SCAN.
Qed.

Theorem scan_all'_complete (M : LGS.t) (s : Input.t) (H_Acc : Acc input_lt s) (tags : list Token.t)
  (SPEC : scan_all_spec M s tags)
  : scan_all' M s H_Acc = Some tags.
Proof.
  revert H_Acc.
  induction SPEC; intros H_Acc.
  - destruct H_Acc as [H_Acc_inv]. simpl. reflexivity.
  - destruct H_Acc as [H_Acc_inv].
    destruct s as [ | c s']; simpl in SCAN.
    + inv SCAN.
    + simpl. rewrite SCAN.
      destruct (lt_dec (length rest) (S (length s'))) as [LT | NLT].
      * rewrite IHSPEC. reflexivity.
      * exfalso. pose proof (scan_one_length_lt M (c :: s') rest tag SCAN). simpl in H. lia.
Qed.

Corollary scan_all_complete (M : LGS.t) (s : Input.t) (tags : list Token.t)
  (SPEC : scan_all_spec M s tags)
  : scan_all M s = Some tags.
Proof.
  unfold scan_all. eapply scan_all'_complete. exact SPEC.
Qed.

Corollary scan_all_spec_iff (M : LGS.t) (s : Input.t) (tags : list Token.t)
  : scan_all M s = Some tags <-> scan_all_spec M s tags.
Proof.
  split.
  - eapply scan_all_sound.
  - eapply scan_all_complete.
Qed.

Lemma scan_all_spec_accepts (M : LGS.t) (s : Input.t) (tags : list Token.t)
  (SCAN : scan_all_spec M s tags)
  : scan_all_accepts M s tags.
Proof.
  induction SCAN.
  - constructor.
  - pose proof (scan_one_sound M s rest tag SCAN) as (consumed & EQ_INPUT & ACCEPT & _).
    subst s. econstructor; eauto.
Qed.

Theorem scan_all_accepts_sound (M : LGS.t) (s : Input.t) (tags : list Token.t)
  (SCAN : scan_all M s = Some tags)
  : scan_all_accepts M s tags.
Proof.
  eapply scan_all_spec_accepts. eapply scan_all_sound. exact SCAN.
Qed.

Inductive scan_all_rules (rules : list Rule.t) : Input.t -> list Token.t -> Prop :=
  | scan_all_rules_nil
    : scan_all_rules rules [] []
  | scan_all_rules_cons consumed rest tag tags rule
    (NONEMPTY : ~ consumed = [])
    (IN_RULE : rule ∈ rules)
    (TOKEN : rule.(Rule.token) = tag)
    (REGEX : consumed \in eval_regex rule.(Rule.regex))
    (REST : scan_all_rules rules rest tags)
    : scan_all_rules rules (consumed ++ rest) (tag :: tags).

Definition build : BuildErrorM LGS.t :=
  bind (isMonad := BuildErrorM_isMonad@{Type}) Rule.compileds (fun rules => pure (isMonad := BuildErrorM_isMonad@{Type}) (TaggedDFA.delete_dead_state (TaggedDFA.minimise_numbered (TaggedDFA.subset_construct (TaggedENFA.mkUnitedTaggedENFA rules))))).

Theorem build_sound (M : LGS.t)
  (BUILD : build = inr M)
  : exists rules, Rule.compileds = inr rules /\ M = TaggedDFA.delete_dead_state (TaggedDFA.minimise_numbered (TaggedDFA.subset_construct (TaggedENFA.mkUnitedTaggedENFA rules))).
Proof.
  unfold build in BUILD. destruct Rule.compileds as [err | rules] eqn: COMPILED; inv BUILD.
  exists rules. split; eauto.
Qed.

Theorem build_complete (rules : list Rule.t)
  (COMPILED : Rule.compileds = inr rules)
  : build = inr (TaggedDFA.delete_dead_state (TaggedDFA.minimise_numbered (TaggedDFA.subset_construct (TaggedENFA.mkUnitedTaggedENFA rules)))).
Proof.
  unfold build. rewrite COMPILED. reflexivity.
Qed.

Lemma build_accepts_sound (M : LGS.t) (s : Input.t) (tag : Token.t)
  (BUILD : build = inr M)
  (ACCEPT : accepts M s tag)
  : exists rules, Rule.compileds = inr rules /\ exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex).
Proof.
  pose proof (build_sound M BUILD) as (rules & COMPILED & EQ). subst M.
  exists rules. split; eauto.
  pose proof (TaggedDFA.delete_dead_accept_states_similarity (TaggedDFA.minimise_numbered (TaggedDFA.subset_construct (TaggedENFA.mkUnitedTaggedENFA rules)))) as DELETE_SPEC.
  unfold accepts, TaggedDFA.accepts in ACCEPT. rewrite delete_dead_state_delta in ACCEPT. cbn in ACCEPT.
  rewrite list_corresponds_to_finite_ensemble_iff in DELETE_SPEC.
  rewrite DELETE_SPEC in ACCEPT. simpl in ACCEPT. destruct ACCEPT as [ACCEPT_DFA _].
  pose proof (TaggedDFA.minimise_numbered_sound _ _ _ (TaggedDFA.subset_construct_okay _ (TaggedENFA.mkUnitedTaggedENFA_okay rules)) ACCEPT_DFA) as ACCEPT_SUBSET.
  pose proof (TaggedDFA.subset_construct_sound _ _ _ ACCEPT_SUBSET) as ACCEPT_ENFA.
  assert (COMPILE : fmap TaggedENFA.mkUnitedTaggedENFA Rule.compileds = inr (TaggedENFA.mkUnitedTaggedENFA rules)).
  { unfold fmap, mkFunctorFromMonad. simpl. rewrite COMPILED. reflexivity. }
  pose proof (TaggedENFA.mkUnitedTaggedENFA_sound _ COMPILE) as (rules' & COMPILED' & SOUND).
  rewrite COMPILED in COMPILED'. inv COMPILED'.
  eapply SOUND. exact ACCEPT_ENFA.
Qed.

Lemma build_accepts_sound_with_rules (M : LGS.t) (rules : list Rule.t) (s : Input.t) (tag : Token.t)
  (BUILD : build = inr M)
  (COMPILED : Rule.compileds = inr rules)
  (ACCEPT : accepts M s tag)
  : exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex).
Proof.
  pose proof (build_accepts_sound M s tag BUILD ACCEPT) as (rules' & COMPILED' & ACCEPT').
  rewrite COMPILED in COMPILED'. inv COMPILED'. exact ACCEPT'.
Qed.

Lemma build_scan_one_sound (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (BUILD : build = inr M)
  (SCAN : scan_one M s = Some (rest, tag))
  : exists rules, Rule.compileds = inr rules /\ (exists consumed, exists rule, s = consumed ++ rest /\ (~ consumed = []) /\ rule ∈ rules /\ rule.(Rule.token) = tag /\ consumed \in eval_regex rule.(Rule.regex) /\ length rest < length s).
Proof.
  pose proof (build_sound M BUILD) as (rules & COMPILED & _).
  pose proof (scan_one_sound M s rest tag SCAN) as (consumed & EQ_INPUT & ACCEPT & LT).
  pose proof (build_accepts_sound_with_rules M rules consumed tag BUILD COMPILED ACCEPT) as (rule & IN_RULE & TOKEN & REGEX).
  exists rules. split; [exact COMPILED | exists consumed, rule].
  repeat split; eauto. intros EQ. subst consumed. simpl in EQ_INPUT. subst s. lia.
Qed.

Lemma build_accepts_complete (M : LGS.t) (rules : list Rule.t) (s : Input.t) (tag : Token.t)
  (BUILD : build = inr M)
  (COMPILED : Rule.compileds = inr rules)
  (ACCEPT : exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex))
  : accepts M s tag.
Proof.
  rewrite build_complete with (rules := rules) in BUILD by assumption. inv BUILD.
  assert (COMPILE : fmap TaggedENFA.mkUnitedTaggedENFA Rule.compileds = inr (TaggedENFA.mkUnitedTaggedENFA rules)).
  { unfold fmap, mkFunctorFromMonad. simpl. rewrite COMPILED. reflexivity. }
  pose proof (TaggedENFA.mkUnitedTaggedENFA_okay rules) as OKAY_ENFA.
  pose proof (TaggedENFA.mkUnitedTaggedENFA_complete _ COMPILE) as (rules' & COMPILED' & COMPLETE).
  rewrite COMPILED in COMPILED'. injection COMPILED' as EQ_RULES. subst rules'.
  pose proof (COMPLETE s tag ACCEPT) as ACCEPT_ENFA.
  pose proof (TaggedDFA.subset_construct_complete (TaggedENFA.mkUnitedTaggedENFA rules) s tag OKAY_ENFA ACCEPT_ENFA) as ACCEPT_SUBSET.
  pose proof (TaggedDFA.subset_construct_okay _ OKAY_ENFA) as OKAY_SUBSET.
  pose proof (TaggedDFA.minimise_numbered_complete _ _ _ OKAY_SUBSET ACCEPT_SUBSET) as ACCEPT_MIN.
  pose proof (TaggedDFA.minimise_numbered_okay _ OKAY_SUBSET) as OKAY_MIN.
  pose proof (TaggedDFA.delete_dead_accept_states_similarity (TaggedDFA.minimise_numbered (TaggedDFA.subset_construct (TaggedENFA.mkUnitedTaggedENFA rules)))) as DELETE_SPEC.
  unfold accepts, TaggedDFA.accepts in *. rewrite delete_dead_state_delta. cbn.
  rewrite list_corresponds_to_finite_ensemble_iff in DELETE_SPEC.
  rewrite DELETE_SPEC. simpl. split; [exact ACCEPT_MIN | ].
  eapply TaggedDFA.accepting_state_live; eauto.
Qed.

Lemma build_scan_all_spec_sound (M : LGS.t) (rules : list Rule.t) (s : Input.t) (tags : list Token.t)
  (BUILD : build = inr M)
  (COMPILED : Rule.compileds = inr rules)
  (SPEC : scan_all_spec M s tags)
  : scan_all_rules rules s tags.
Proof.
  induction SPEC.
  - constructor.
  - pose proof (scan_one_sound M s rest tag SCAN) as (consumed & EQ_INPUT & ACCEPT & LT).
    pose proof (build_accepts_sound_with_rules M rules consumed tag BUILD COMPILED ACCEPT) as (rule & IN_RULE & TOKEN & REGEX).
    subst s. econstructor; eauto.
    intros EQ. subst consumed. simpl in LT. lia.
Qed.

Lemma build_scan_all_sound (M : LGS.t) (s : Input.t) (tags : list Token.t)
  (BUILD : build = inr M)
  (SCAN : scan_all M s = Some tags)
  : exists rules, Rule.compileds = inr rules /\ scan_all_rules rules s tags.
Proof.
  pose proof (build_sound M BUILD) as (rules & COMPILED & _).
  exists rules. split; [exact COMPILED | ].
  eapply build_scan_all_spec_sound; [exact BUILD | exact COMPILED | ].
  eapply scan_all_sound. exact SCAN.
Qed.

Section MAIN_THEOREMS.

Theorem build_correct (M : LGS.t)
  : build = inr M <-> (exists rules, Rule.compileds = inr rules /\ M = TaggedDFA.delete_dead_state(TaggedDFA.minimise_numbered(TaggedDFA.subset_construct (TaggedENFA.mkUnitedTaggedENFA rules)))).
Proof.
  split.
  - exact (build_sound M).
  - intros (rules & COMPILED & EQ). subst M.
    eapply build_complete. exact COMPILED.
Qed.

Theorem build_accepts_correct (M : LGS.t)
  (BUILD : build = inr M)
  : exists rules, Rule.compileds = inr rules /\ (forall s, forall tag, accepts M s tag <-> (exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex))).
Proof.
  pose proof (build_sound M BUILD) as (rules & COMPILED & _).
  exists rules. split; [exact COMPILED | ].
  intros s tag. split.
  - intros ACCEPT. eapply build_accepts_sound_with_rules; eauto.
  - intros ACCEPT. eapply build_accepts_complete; eauto.
Qed.

Theorem scan_one_correct (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (SCAN_ONE : scan_one M s = Some (rest, tag))
  : scan_candidate M s rest tag /\ (forall rest', forall tag', scan_candidate M s rest' tag' -> length rest <= length rest').
Proof.
  eapply scan_one_maximal; eauto.
Qed.

Theorem scan_one_success_correct (M : LGS.t) (s : Input.t)
  : (exists rest, exists tag, scan_one M s = Some (rest, tag)) <-> (exists rest, exists tag, scan_candidate M s rest tag).
Proof.
  eapply scan_one_some_iff.
Qed.

Theorem scan_all_correct (M : LGS.t) (s : Input.t) (tags : list Token.t)
  : scan_all M s = Some tags <-> scan_all_spec M s tags.
Proof.
  eapply scan_all_spec_iff.
Qed.

Variant build_scan_one_spec (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t) : Prop :=
  | build_scan_one_spec_intro rules consumed rule
    (COMPILED : Rule.compileds = inr rules)
    (EQ_INPUT : s = consumed ++ rest)
    (NONEMPTY : ~ consumed = [])
    (IN_RULE : rule ∈ rules)
    (TOKEN : rule.(Rule.token) = tag)
    (REGEX : consumed \in eval_regex rule.(Rule.regex))
    (LENGTH : length rest < length s)
    (MAXIMAL : forall rest', forall tag', scan_candidate M s rest' tag' -> length rest <= length rest')
    : build_scan_one_spec M s rest tag.

Theorem build_scan_one_correct (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (BUILD : build = inr M)
  (SCAN : scan_one M s = Some (rest, tag))
  : build_scan_one_spec M s rest tag.
Proof.
  pose proof (build_scan_one_sound M s rest tag BUILD SCAN) as (rules & COMPILED & consumed & rule & EQ_INPUT & NONEMPTY & IN_RULE & TOKEN & REGEX & LT).
  pose proof (scan_one_maximal M s rest tag SCAN) as [_ MAXIMAL].
  econstructor; eauto.
Qed.

Theorem build_scan_one_complete_correct (M : LGS.t) (rules : list Rule.t) (s : Input.t) (consumed : Input.t) (rest : Input.t) (rule : Rule.t)
  (BUILD : build = inr M)
  (COMPILED : Rule.compileds = inr rules)
  (EQ_INPUT : s = consumed ++ rest)
  (NONEMPTY : ~ consumed = [])
  (IN_RULE : rule ∈ rules)
  (REGEX : consumed \in eval_regex rule.(Rule.regex))
  : exists rest', exists tag', scan_one M s = Some (rest', tag') /\ length rest' <= length rest.
Proof.
  eapply scan_one_complete.
  exists consumed. repeat split; eauto.
  eapply build_accepts_complete with (rules := rules); eauto.
Qed.

Theorem build_scan_all_correct (M : LGS.t) (s : Input.t) (tags : list Token.t)
  (BUILD : build = inr M)
  (SCAN : scan_all M s = Some tags)
  : exists rules, Rule.compileds = inr rules /\ scan_all_rules rules s tags.
Proof.
  eapply build_scan_all_sound; eauto.
Qed.

Theorem minimise_numbered_minimal_correct (M : TaggedDFA.t) (N : TaggedDFA.t)
  (OKAY_M : TaggedDFA.okay M)
  (REACHABLE : TaggedDFA.all_states_reachable M)
  (OKAY_N : TaggedDFA.okay N)
  (NODUP_N : NoDup N.(TaggedDFA.states))
  (EQUIV : TaggedDFA.language_equiv M N)
  : length (TaggedDFA.minimise_numbered M).(TaggedDFA.states) <= length N.(TaggedDFA.states).
Proof.
  eapply TaggedDFA.minimise_numbered_states_minimal; eauto.
Qed.

End MAIN_THEOREMS.

End LGS.

Module Scanner.

Module Abs.

Abbreviation accepts := LGS.accepts.

Abbreviation scan_candidate := LGS.scan_candidate.

Definition maximal_scan_candidate (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t) : Prop :=
  scan_candidate M s rest tag /\ (forall rest', forall tag', scan_candidate M s rest' tag' -> length rest <= length rest').

Definition priority_candidate (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t) : Prop :=
  exists consumed, exists prefix, exists suffix, s = consumed ++ rest /\ (~ consumed = []) /\ M.(TaggedDFA.Partial.accept_states) = prefix ++ (LGS.delta M M.(TaggedDFA.Partial.start_state) consumed, tag) :: suffix /\ forall tag', ~ (LGS.delta M M.(TaggedDFA.Partial.start_state) consumed, tag') ∈ prefix.

Abbreviation scan_all_spec := LGS.scan_all_spec.

Abbreviation scan_all_rules := LGS.scan_all_rules.

End Abs.

Module Impl.

Abbreviation first_accepting_token_from := LGS.first_accepting_token_from.

Abbreviation first_accepting_token := LGS.first_accepting_token.

Abbreviation maximal_munch := LGS.maximal_munch.

Abbreviation scan_one := LGS.scan_one.

Abbreviation scan_all := LGS.scan_all.

End Impl.

Module Refine.

Theorem first_accepting_token_from_sound {Q : Set} `{Q_hasEqDec : hasEqDec@{Set} Q} (q : Q) (accept_states : list (Q * Token.t)) (tag : Token.t)
  (FIND : LGS.first_accepting_token_from q accept_states = Some tag)
  : (q, tag) ∈ accept_states.
Proof.
  eapply LGS.first_accepting_token_from_sound. exact FIND.
Qed.

Theorem first_accepting_token_from_complete_some {Q : Set} `{Q_hasEqDec : hasEqDec@{Set} Q} (q : Q) (accept_states : list (Q * Token.t))
  (ACCEPT : exists tag, (q, tag) ∈ accept_states)
  : exists tag, LGS.first_accepting_token_from q accept_states = Some tag.
Proof.
  eapply LGS.first_accepting_token_from_complete_some. exact ACCEPT.
Qed.

Theorem first_accepting_token_from_first {Q : Set} `{Q_hasEqDec : hasEqDec@{Set} Q} (q : Q) (accept_states : list (Q * Token.t)) (tag : Token.t)
  (FIND : LGS.first_accepting_token_from q accept_states = Some tag)
  : exists prefix, exists suffix, accept_states = prefix ++ (q, tag) :: suffix /\ forall tag', ~ (q, tag') ∈ prefix.
Proof.
  eapply LGS.first_accepting_token_from_first. exact FIND.
Qed.

Theorem scan_one_correct (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (SCAN : LGS.scan_one M s = Some (rest, tag))
  : Abs.maximal_scan_candidate M s rest tag.
Proof.
  eapply LGS.scan_one_correct. exact SCAN.
Qed.

Theorem scan_one_complete (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (CANDIDATE : LGS.scan_candidate M s rest tag)
  : exists rest', exists tag', LGS.scan_one M s = Some (rest', tag') /\ length rest' <= length rest.
Proof.
  eapply LGS.scan_one_complete. exact CANDIDATE.
Qed.

Theorem scan_all_correct (M : LGS.t) (s : Input.t) (tags : list Token.t)
  : LGS.scan_all M s = Some tags <-> LGS.scan_all_spec M s tags.
Proof.
  eapply LGS.scan_all_correct.
Qed.

End Refine.

Module API.

Abbreviation first_accepting_token := Impl.first_accepting_token.

Abbreviation maximal_munch := Impl.maximal_munch.

Abbreviation scan_one := Impl.scan_one.

Abbreviation scan_all := Impl.scan_all.

Abbreviation scan_candidate := Abs.scan_candidate.

Abbreviation priority_candidate := Abs.priority_candidate.

Abbreviation scan_all_spec := Abs.scan_all_spec.

End API.

End Scanner.

Module Builder.

Definition pipeline (rules : list Rule.t) : LGS.t :=
  TaggedDFA.delete_dead_state (TaggedDFA.minimise_numbered (TaggedDFA.subset_construct (TaggedENFA.mkUnitedTaggedENFA rules))).

Abbreviation build := LGS.build.

Theorem build_sound (M : LGS.t)
  (BUILD : build = inr M)
  : exists rules, Rule.compileds = inr rules /\ M = pipeline rules.
Proof.
  pose proof (LGS.build_sound M BUILD) as (rules & COMPILED & EQ).
  exists rules. split; [exact COMPILED | exact EQ].
Qed.

Theorem build_complete (rules : list Rule.t)
  (COMPILED : Rule.compileds = inr rules)
  : build = inr (pipeline rules).
Proof.
  unfold pipeline. eapply LGS.build_complete. exact COMPILED.
Qed.

Theorem pipeline_okay_before_delete (rules : list Rule.t)
  : TaggedDFA.okay (TaggedDFA.minimise_numbered (TaggedDFA.subset_construct (TaggedENFA.mkUnitedTaggedENFA rules))).
Proof.
  eapply TaggedDFA.minimise_numbered_okay.
  eapply TaggedDFA.subset_construct_okay.
  eapply TaggedENFA.mkUnitedTaggedENFA_okay.
Qed.

Theorem pipeline_accepts_sound (rules : list Rule.t) (s : Input.t) (tag : Token.t)
  (COMPILED : Rule.compileds = inr rules)
  (ACCEPT : LGS.accepts (pipeline rules) s tag)
  : exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex).
Proof.
  eapply LGS.build_accepts_sound_with_rules.
  - eapply build_complete. exact COMPILED.
  - exact COMPILED.
  - exact ACCEPT.
Qed.

Theorem pipeline_accepts_complete (rules : list Rule.t) (s : Input.t) (tag : Token.t)
  (COMPILED : Rule.compileds = inr rules)
  (ACCEPT : exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex))
  : LGS.accepts (pipeline rules) s tag.
Proof.
  eapply LGS.build_accepts_complete with (rules := rules).
  - eapply build_complete. exact COMPILED.
  - exact COMPILED.
  - exact ACCEPT.
Qed.

Theorem build_failure_nullable_rule (err : BuildError.t)
  (BUILD : build = inl err)
  : exists rule, rule ∈ Rule.raws /\ nullable rule.(Rule.regex) = true /\ err = BuildError.NullableTokenRule rule.(Rule.index).
Proof.
  unfold build in BUILD.
  destruct Rule.compileds as [err_rules | rules] eqn: COMPILED; cbn in BUILD; [ | discriminate].
  inv BUILD. unfold Rule.compileds in COMPILED.
  eapply Rule.compileRules_failure_elim. exact COMPILED.
Qed.

Theorem nullable_rule_build_failure
  (EXISTS : exists rule, rule ∈ Rule.raws /\ nullable rule.(Rule.regex) = true)
  : exists idx, build = inl (BuildError.NullableTokenRule idx).
Proof.
  unfold build, Rule.compileds.
  pose proof (Rule.compile_rules_failure_intro Rule.raws EXISTS) as (idx & FAILURE).
  rewrite FAILURE. exists idx. reflexivity.
Qed.

End Builder.

End MkLGS.
