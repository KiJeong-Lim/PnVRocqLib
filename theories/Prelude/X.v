Require Import PnV.Prelude.Prelude.

Notation "lhs ≠ rhs" := (~ (lhs = rhs)) : type_scope.

Tactic Notation "use" uconstr( H ) :=
  hexploit H; cycle -1; [i | eauto with * ..]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) :=
  hexploit H; cycle -1; [intros p | try eassumption ..]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) :=
  hexploit H; cycle -1; [intros p | use_exact H1]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) :=
  hexploit H; cycle -1; [intros p | use_exact H1 | use_exact H2]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) :=
  hexploit H; cycle -1; [intros p | use_exact H1 | use_exact H2 | use_exact H3]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) :=
  hexploit H; cycle -1; [intros p | use_exact H1 | use_exact H2 | use_exact H3 | use_exact H4]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) :=
  hexploit H; cycle -1; [intros p | use_exact H1 | use_exact H2 | use_exact H3 | use_exact H4 | use_exact H5]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) :=
  hexploit H; cycle -1; [intros p | use_exact H1 | use_exact H2 | use_exact H3 | use_exact H4 | use_exact H5 | use_exact H6]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) ident( H7 ) :=
  hexploit H; cycle -1; [intros p | use_exact H1 | use_exact H2 | use_exact H3 | use_exact H4 | use_exact H5 | use_exact H6 | use_exact H7]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) ident( H7 ) ident( H8 ) :=
  hexploit H; cycle -1; [intros p | use_exact H1 | use_exact H2 | use_exact H3 | use_exact H4 | use_exact H5 | use_exact H6 | use_exact H7 | use_exact H8]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) ident( H7 ) ident( H8 ) ident( H9 ) :=
  hexploit H; cycle -1; [intros p | use_exact H1 | use_exact H2 | use_exact H3 | use_exact H4 | use_exact H5 | use_exact H6 | use_exact H7 | use_exact H8 | use_exact H9]; cycle 1.

Tactic Notation "use?" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) :=
  hexploit H; cycle -1; [intros p | try (revert H1; clear; i; eassumption) ..]; cycle 1.

Tactic Notation "use?" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) :=
  hexploit H; cycle -1; [intros p | try (revert H1 H2; clear; i; eassumption) ..]; cycle 1.

Tactic Notation "use?" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) :=
  hexploit H; cycle -1; [intros p | try (revert H1 H2 H3; clear; i; eassumption) ..]; cycle 1.

Tactic Notation "use?" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) :=
  hexploit H; cycle -1; [intros p | try (revert H1 H2 H3 H4; clear; i; eassumption) ..]; cycle 1.

Tactic Notation "use?" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) :=
  hexploit H; cycle -1; [intros p | try (revert H1 H2 H3 H4 H5; clear; i; eassumption) ..]; cycle 1.

Tactic Notation "use?" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) :=
  hexploit H; cycle -1; [intros p | try (revert H1 H2 H3 H4 H5 H6; clear; i; eassumption) ..]; cycle 1.

Tactic Notation "use?" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) ident( H7 ) :=
  hexploit H; cycle -1; [intros p | try (revert H1 H2 H3 H4 H5 H6 H7; clear; i; eassumption) ..]; cycle 1.

Tactic Notation "use?" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) ident( H7 ) ident( H8 ) :=
  hexploit H; cycle -1; [intros p | try (revert H1 H2 H3 H4 H5 H6 H7 H8; clear; i; eassumption) ..]; cycle 1.

Tactic Notation "use?" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) ident( H7 ) ident( H8 ) ident( H9 ) :=
  hexploit H; cycle -1; [intros p | try (revert H1 H2 H3 H4 H5 H6 H7 H8 H9; clear; i; eassumption) ..]; cycle 1.

Ltac done :=
  des; subst; done!.

Lemma S_lt_S_intro (n : nat) (m : nat)
  (H_lt : n < m)
  : S n < S m.
Proof.
  lia.
Qed.

#[projections(primitive)]
Class isFinite@{u} (A : Type@{u}) : Type@{u} :=
  { finite_hasEqDec : hasEqDec@{u} A
  ; finite_enumeration : list A
  ; finite_enumeration_complete
    : forall x : A, L.In x finite_enumeration
  ; finite_enumeration_NoDup
    : NoDup finite_enumeration
  }.

#[global] Existing Instance finite_hasEqDec.

Lemma inject_pair_eq (A : Type) (B : Type) (x : A) (x' : A) (y : B) (y' : B)
  : (x, y) = (x', y') <-> (x = x' /\ y = y').
Proof.
  split; [intros EQ; split | intros [EQ1 EQ2]]; congruence.
Qed.

#[global] Hint Rewrite inject_pair_eq : simplication_hints.

Fixpoint iter {A : Type} (fuel : nat) (step : A -> A) (x : A) {struct fuel} : A :=
  match fuel with
  | O => x
  | S fuel' => iter fuel' step (step x)
  end.

Lemma iter_succ (A : Type) (fuel : nat) (step : A -> A) (x : A)
  : iter (S fuel) step x = step (iter fuel step x).
Proof.
  revert x; induction fuel as [ | fuel IH]; intros x; simpl.
  - reflexivity.
  - eapply IH.
Qed.

#[global] Hint Rewrite iter_succ : simplication_hints.

Definition nonempty {A : Type} (xs : list A) : bool :=
  negb (L.null xs).

Lemma nonempty_exists {A : Type} (xs : list A)
  (NONEMPTY : nonempty xs = true)
  : exists x, L.In x xs.
Proof.
  unfold nonempty in NONEMPTY. destruct xs; done.
Qed.

Lemma nonempty_of_exists {A : Type} (xs : list A) (x : A)
  (IN : L.In x xs)
  : nonempty xs = true.
Proof.
  unfold nonempty. destruct xs; done.
Qed.
