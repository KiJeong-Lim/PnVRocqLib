Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.X.
Require Export PnV.Math.ThN.

Universe u_1.

#[universes(polymorphic=yes)]
Definition fin_ensemble@{u | } (Elem : Type@{u}) : Type@{u} :=
  list Elem.

#[global] Typeclasses Opaque fin_ensemble.

#[local] Hint Resolve S_lt_S_intro : core.
#[global] Hint Rewrite L.in_concat : simplication_hints.
#[global] Hint Rewrite L.in_map_iff : simplication_hints.
#[global] Hint Rewrite L.in_flat_map : simplication_hints.
#[global] Hint Rewrite length_app : simplication_hints.
#[global] Hint Rewrite length_map : simplication_hints.

#[local] Infix "=~=" := is_similar_to : type_scope.
#[local] Infix "\in" := E.In.
#[local] Infix "∈" := L.In.

Definition Similarity_list_finite_ensemble {ELEM : Type} {ELEM' : Type} (ELEM_sim : Similarity ELEM ELEM') : Similarity (fin_ensemble ELEM) (ensemble ELEM') :=
  fun xs : list ELEM => fun X' : ensemble ELEM' => ⟪ SUBSET1 : forall x, x ∈ xs -> (exists x', x =~= x' /\ x' \in X') ⟫ /\ ⟪ SUBSET2 : forall x', x' \in X' -> (exists x, x =~= x' /\ x ∈ xs) ⟫.

#[global]
Instance list_corresponds_to_finite_ensemble {ELEM : Type} : Similarity (list ELEM) (ensemble ELEM) :=
  Similarity_list_finite_ensemble eq.

Theorem list_corresponds_to_finite_ensemble_iff (A : Type) (xs : list A) (X : ensemble A)
  : xs =~= X <-> (forall x, x ∈ xs <-> x \in X).
Proof.
  done!.
Qed.

#[global] Hint Rewrite list_corresponds_to_finite_ensemble_iff : simplication_hints.

#[global, program]
Instance fin_ensemble_isSetoid (Elem : Type@{u_1}) (Elem_isSetoid : isSetoid Elem) : isSetoid (fin_ensemble@{u_1} Elem) :=
  { eqProp (lhs : list Elem) (rhs : list Elem) := (forall e : Elem, forall IN : e ∈ lhs, exists e', e' ∈ rhs /\ e == e') /\ (forall e : Elem, forall IN : e ∈ rhs, exists e', e' ∈ lhs /\ e' == e) }.
Next Obligation.
  split; [intros xs | intros xs ys [xs_ys ys_xs] | intros xs ys zs [xs_ys ys_xs] [ys_zs zs_ys]]; split; i.
  - exists e. splits; auto. reflexivity; eauto.
  - exists e. splits; auto. reflexivity; eauto.
  - use ys_xs as (e1 & H_in & H_eq) with IN. exists e1. splits; auto. symmetry; eauto.
  - use xs_ys as (e1 & H_in & H_eq) with IN. exists e1. splits; auto. symmetry; eauto.
  - use xs_ys as (e1 & H_in & H_eq) with IN. use ys_zs as (e2 & H_in' & H_eq') with H_in. exists e2. splits; auto. transitivity e1; eauto.
  - use zs_ys as (e1 & H_in & H_eq) with IN. use ys_xs as (e2 & H_in' & H_eq') with H_in. exists e2. splits; auto. transitivity e1; eauto.
Qed.

#[global]
Instance fin_ensemble_isSetoid1 : isSetoid1 fin_ensemble@{u_1} :=
  fin_ensemble_isSetoid.

Lemma fin_ensemble_isSetoid1_eq_iff (A : Type@{u_1}) (xs : fin_ensemble@{u_1} A) (xs' : fin_ensemble@{u_1} A)
  : eqProp (isSetoid := fromSetoid1 fin_ensemble_isSetoid) xs xs' <-> (forall e : A, e ∈ xs <-> e ∈ xs').
Proof.
  ii; ss!.
Qed.

#[global]
Instance fin_ensemble_isMonad : isMonad fin_ensemble :=
  { pure {A : Type} (x : A) := (@L.cons A x (@L.nil A))
  ; bind {A : Type} {B : Type} (xs : list A) (k : A -> list B) := (@flat_map A B k xs)
  }.

#[global]
Instance fin_ensemble_MonadLaws
  : MonadLaws fin_ensemble (SETOID1 := fin_ensemble_isSetoid1) (MONAD := fin_ensemble_isMonad).
Proof.
  split; i; rewrite fin_ensemble_isSetoid1_eq_iff in *; i; ss!; ss!; exists x0; ss!.
Qed.

Theorem list_corresponds_to_finite_ensemble_flat_map {A : Type} {B : Type} (xs : list A) (X : ensemble A) (f : A -> list B) (F : A -> ensemble B)
  (xs_sim : xs =~= X)
  (f_sim : forall x, x ∈ xs -> f x =~= F x)
  : L.flat_map f xs =~= (X >>= F).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff.
  intros b. rewrite L.in_flat_map. split.
  - intros [x [x_in b_in]].
    exists x. split.
    + pose proof xs_sim as XS_SIM.
      rewrite list_corresponds_to_finite_ensemble_iff in XS_SIM.
      exact (proj1 (XS_SIM x) x_in).
    + pose proof (f_sim x) as F_SIM.
      rewrite list_corresponds_to_finite_ensemble_iff in F_SIM.
      exact (proj1 (F_SIM x_in b) b_in).
  - intros [x [x_in b_in]].
    exists x. split.
    + pose proof xs_sim as XS_SIM.
      rewrite list_corresponds_to_finite_ensemble_iff in XS_SIM.
      exact (proj2 (XS_SIM x) x_in).
    + pose proof (f_sim x) as F_SIM.
      rewrite list_corresponds_to_finite_ensemble_iff in F_SIM.
      assert (x ∈ xs) as HH by done.
      exact (proj2 (F_SIM HH b) b_in).
Qed.

Fact existsb_iff (A : Type) (p : A -> bool) (xs : list A)
  : existsb p xs = true <-> (exists x : A, x ∈ xs /\ p x = true).
Proof.
  eapply L.existsb_exists.
Qed.

Fact forallb_iff (A : Type) (p : A -> bool) (xs : list A)
  : forallb p xs = true <-> (forall x : A, x ∈ xs -> p x = true).
Proof.
  eapply L.forallb_forall.
Qed.

Definition mem {A : Type@{u_1}} `{EQ_DEC : hasEqDec@{u_1} A} (x : A) (xs : list A) : bool :=
  if in_dec eq_dec@{u_1} x xs then true else false.

Theorem mem_spec (A : Type) `(EQ_DEC : hasEqDec A) (x : A) (xs : list A)
  : forall b, mem x xs = b <-> (if b then x ∈ xs else ~ x ∈ xs).
Proof.
  unfold mem; intros [ | ]; revert x; induction xs; intros; simpl; des_ifs; done.
Qed.

#[global] Hint Rewrite mem_spec : simplication_hints.

Definition add {A : Type@{u_1}} `{EQ_DEC : hasEqDec@{u_1} A} (x : A) (xs : list A) : list A :=
  if mem x xs then xs else x :: xs.

Theorem in_add_iff (A : Type) `(EQ_DEC : hasEqDec A) (x : A) (xs : list A)
  : forall y, y ∈ add x xs <-> (x = y \/ y ∈ xs).
Proof.
  i; unfold add, mem; des_ifs; done.
Qed.

#[global] Hint Rewrite in_add_iff : simplication_hints.

Fixpoint union {A : Type@{u_1}} `{EQ_DEC : hasEqDec@{u_1} A} (xs : list A) (ys : list A) {struct xs} : list A :=
  match xs with
  | [] => ys
  | x :: xs' => union xs' (add x ys)
  end.

Theorem in_union_iff (A : Type) `(EQ_DEC : hasEqDec A) (xs : list A) (ys : list A)
  : forall z, z ∈ union xs ys <-> (z ∈ xs \/ z ∈ ys).
Proof.
  revert ys; induction xs as [ | x xs IH]; ii; simpl; s!.
  - tauto.
  - rewrite IH; s!; tauto.
Qed.

#[global] Hint Rewrite in_union_iff : simplication_hints.

Fixpoint normalize {A : Type@{u_1}} `{EQ_DEC : hasEqDec@{u_1} A} (xs : list A) {struct xs} : list A :=
  match xs with
  | [] => []
  | x :: xs' => add x (normalize xs')
  end.

Theorem in_normalize_iff (A : Type) `(EQ_DEC : hasEqDec A) (xs : list A)
  : forall z, z ∈ normalize xs <-> z ∈ xs.
Proof.
  induction xs as [ | x xs IH]; simpl; ii; done.
Qed.

#[global] Hint Rewrite in_normalize_iff : simplication_hints.

Fixpoint unions {A : Type@{u_1}} `{EQ_DEC : hasEqDec@{u_1} A} (xss : list (list A)) {struct xss} : list A :=
  match xss with
  | [] => []
  | xs :: xss' => union xs (unions xss')
  end.

Lemma in_unions_iff (A : Type) `(EQ_DEC : hasEqDec A) (xss : list (list A))
  : forall z, z ∈ unions xss <-> (exists xs, xs ∈ xss /\ z ∈ xs).
Proof.
  induction xss as [ | xs xss IH]; simpl; i; s!.
  - done.
  - rewrite IH. clear IH. done.
Qed.

#[global] Hint Rewrite in_unions_iff : simplication_hints.

Lemma remove_length_lt {A : Type} `{EQ_DEC : hasEqDec A} (x : A) (xs : list A)
  (IN : x ∈ xs)
  : length (remove eq_dec x xs) < length xs.
Proof.
  revert x IN; induction xs as [ | y ys IH]; simpl; ii.
  - contradiction.
  - destruct (eq_dec _ _) as [EQ | NE]; simpl.
    + pose proof (remove_length_le eq_dec ys x); done.
    + destruct IN as [EQ | IN]; done.
Qed.

Fixpoint powerset {A : Type@{u_1}} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: xs' =>
    let ps := powerset xs' in
    ps ++ map (fun ys => x :: ys) ps
  end.

Lemma filter_in_powerset {A : Type} (p : A -> bool) (xs : list A)
  : filter p xs ∈ powerset xs.
Proof.
  induction xs as [ | x xs IH]; simpl; des_ifs; ss!.
Qed.

Lemma powerset_length@{u} {A : Type@{u}} (xs : list A)
  : length (powerset xs) = pow2 (length xs).
Proof.
  induction xs as [ | x xs IH]; simpl; ss!.
Qed.

Fixpoint index_of {A : Type@{u_1}} `{EQ_DEC : hasEqDec@{u_1} A} (x : A) (xs : list A) {struct xs} : nat :=
  match xs with
  | [] => O
  | x' :: xs' => if eq_dec@{u_1} x x' then O else S (index_of x xs')
  end.

Definition lookup {A : Type@{u_1}} (default : A) (n : nat) (xs : list A) : A :=
  nth n xs default.

Lemma lookup_index_of {A : Type} `{EQ_DEC : hasEqDec A} (x : A) (xs : list A) (default : A)
  (IN : x ∈ xs)
  : lookup default (index_of x xs) xs = x.
Proof.
  revert x IN; induction xs as [ | x' xs IH]; simpl; ii; des_ifs; done!.
Qed.

Lemma index_of_lt {A : Type} `{EQ_DEC : hasEqDec A} (x : A) (xs : list A)
  (IN : x ∈ xs)
  : index_of x xs < length xs.
Proof.
  revert x IN; induction xs as [ | x' xs IH]; simpl; ii; des_ifs; done.
Qed.

Lemma index_of_in_seq {A : Type} `{EQ_DEC : hasEqDec A} (x : A) (xs : list A)
  (IN : x ∈ xs)
  : index_of x xs ∈ seq 0 (length xs).
Proof.
  rewrite in_seq. pose proof (index_of_lt x xs IN). lia.
Qed.

Lemma index_of_inj {A : Type} `{EQ_DEC : hasEqDec A} (x : A) (y : A) (xs : list A) (default : A)
  (IN_X : x ∈ xs)
  (IN_Y : y ∈ xs)
  (EQ : index_of x xs = index_of y xs)
  : x = y.
Proof.
  pose proof (lookup_index_of x xs default IN_X) as Hx.
  pose proof (lookup_index_of y xs default IN_Y) as Hy.
  congruence.
Qed.

Lemma lookup_in {A : Type} (default : A) (n : nat) (xs : list A)
  (LT : n < length xs)
  : lookup default n xs ∈ xs.
Proof.
  now eapply nth_In.
Qed.

#[universes(polymorphic=yes)]
Definition product@{u v} {A : Type@{u}} {B : Type@{v}} (xs : list A) (ys : list B) : list (A * B) :=
  xs >>= fun x => ys >>= fun y => pure (x, y).

Theorem product_iff (A : Type) (B : Type) (xs : list A) (ys : list B)
  : forall x, forall y, (x, y) ∈ product xs ys <-> x ∈ xs /\ y ∈ ys.
Proof.
  ii; unfold product; split; intros H_in.
  - repeat ss!.
  - s!. exists (concat (map (fun y0 : B => pure (x, y0)) ys)). s!. split.
    + exists x. ss!.
    + exists [(x, y)]. ss!.
Qed.

#[global] Hint Rewrite product_iff : simplication_hints.

Lemma in_list_bind_intro {A : Type} {B : Type} (xs : list A) (k : A -> list B) (x : A) (y : B)
  (x_in : x ∈ xs)
  (y_in : y ∈ k x)
  : y ∈ (xs >>= k).
Proof.
  rewrite L.list_bind_flat_map. rewrite in_flat_map; eauto.
Qed.

Lemma in_list_bind_elim {A : Type} {B : Type} (xs : list A) (k : A -> list B) (y : B)
  (IN : y ∈ (xs >>= k))
  : exists x, x ∈ xs /\ y ∈ k x.
Proof.
  induction xs as [ | x xs IH]; ss!.
Qed.

Lemma in_list_pure_intro {A : Type} (x : A)
  : x ∈ pure x.
Proof.
  now simpl; left.
Qed.

Lemma forallb_false_exists {A : Type} (p : A -> bool) (xs : list A)
  (FORALL : forallb p xs = false)
  : exists x, x ∈ xs /\ p x = false.
Proof.
  induction xs as [ | x xs IH]; s!; [congruence | des; ss!].
Qed.

Lemma find_some_exists {A : Type} (p : A -> bool) (xs : list A) (x : A)
  (IN : x ∈ xs)
  (YES : p x = true)
  : exists y, find p xs = Some y.
Proof.
  revert x IN YES; induction xs as [ | x0 xs IH]; ss!; des_ifs; eauto.
Qed.

Theorem NoDup_exists_injective_length {A : Type} {B : Type} `{B_hasEqDec : hasEqDec B} (xs : list A) (ys : list B) (R : A -> B -> Prop)
  (xs_NoDup : NoDup xs)
  (R_total : forall x, x ∈ xs -> (exists y, y ∈ ys /\ R x y))
  (R_functional : forall x1, forall x2, forall y, x1 ∈ xs -> x2 ∈ xs -> R x1 y -> R x2 y -> x1 = x2)
  : length xs <= length ys.
Proof.
  revert ys R_total R_functional; induction xs_NoDup as [ | x xs NOT_IN NO_DUP IH]; intros ys TOTAL INJ; simpl; [lia | ].
  pose proof (TOTAL x (or_introl eq_refl)) as (y & IN_Y & R_XY).
  enough (LE : length xs <= length (remove eq_dec y ys)).
  { pose proof (remove_length_lt y ys IN_Y). lia. }
  eapply IH.
  - intros x' IN_XS.
    pose proof (TOTAL x' (or_intror IN_XS)) as (y' & IN_Y' & R_XY').
    exists y'. split; eauto. rewrite L.in_remove_iff. split; eauto; ii.
    enough (x' = x) by done!.
    eapply INJ; ss!.
  - ii; eapply INJ; ss!.
Qed.
