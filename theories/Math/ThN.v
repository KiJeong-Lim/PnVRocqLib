Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Export Coq.Arith.Wf_nat.

Lemma S_eq_O_elim {A : Type} {n : nat}
  (S_eq_O : S n = O)
  : A.
Proof.
  set (f := fun n : nat => match n with O => True | S n' => False end).
  apply f_equal with (f := f) in S_eq_O. simpl in S_eq_O.
  enough (H_contra : False) by contradiction H_contra.
  rewrite S_eq_O. econstructor.
Defined.

Lemma case_le_n {n : nat} (phi : n <= n -> Prop)
  (phi_le_n : phi (@le_n n))
  : forall H_le : n <= n, phi H_le.
Proof.
  intros H_le. refine ((fun claim : forall EQ : n = n, phi (eq_ind n (fun m' : nat => n <= m') H_le n EQ) => claim eq_refl) (match H_le in le _ m return forall H_obs : m = n, phi (@eq_ind _ _ (fun m' : nat => n <= m') H_le _ H_obs) with @le_n _ => fun H_obs: n = n => _ | @le_S _ m' H_le' => fun H_obs: S m' = n => _ end)).
  - rewrite eq_pirrel_fromEqDec with (EQ1 := H_obs) (EQ2 := eq_refl). exact (phi_le_n).
  - lia.
Qed.

Lemma case_le_S {n : nat} {m : nat} (H_le : m <= n) (phi : m <= S n -> Prop)
  (phi_le_S : forall H_le' : m <= n, phi (@le_S m n H_le'))
  : forall H_lt : m <= S n, phi H_lt.
Proof.
  intros H_lt. refine ((fun claim : forall EQ : S n = S n, phi (eq_ind (S n) (fun n' : nat => m <= n') H_lt (S n) EQ) => claim eq_refl) (match H_lt in le _ n' return forall H_obs : n' = S n, phi (@eq_ind _ _ (fun n' => m <= n') H_lt _ H_obs) with @le_n _ => fun H_obs : m = S n => _ | @le_S _ m' H_le' => fun H_obs : S m' = S n => _ end)).
  - lia.
  - assert (m' = n) as H_eq by now apply f_equal with (f := pred) in H_obs. subst m'.
    rewrite eq_pirrel_fromEqDec with (EQ1 := H_obs) (EQ2 := eq_refl). exact (phi_le_S H_le').
Qed.

Theorem le_pirrel (n : nat) (m : nat)
  (LE1 : n <= m)
  (LE2 : n <= m)
  : LE1 = LE2.
Proof.
  assert (m = (m - n) + n)%nat as claim by lia.
  remember (m - n)%nat as k eqn: H_eq in claim.
  clear H_eq. revert n m LE1 LE2 claim.
  induction k as [ | k IH]; simpl.
  - i. subst m.
    induction LE1 using case_le_n.
    induction LE2 using case_le_n.
    reflexivity.
  - i. subst m.
    assert (n <= k + n) as LE by lia.
    induction LE1 using (case_le_S LE).
    induction LE2 using (case_le_S LE).
    eapply f_equal. eapply IH. reflexivity.
Qed.

Lemma greater_than_iff (x : nat) (y : nat)
  : x > y <-> (exists z : nat, x = S (y + z)).
Proof with try (lia || eauto).
  split.
  - intros Hgt. induction Hgt as [ | m Hgt [z x_eq]]; [exists 0 | rewrite x_eq]...
  - intros [z Heq]...
Qed.

Section CANTOR_PAIRING.

Import Nat.

Fixpoint sum_from_0_to (n : nat) {struct n} : nat :=
  match n with
  | O => 0
  | S n' => n + sum_from_0_to n'
  end.

Lemma sum_from_0_to_spec (n : nat)
  : 2 * sum_from_0_to n = n * (S n).
Proof.
  induction n; simpl in *; lia.
Qed.

Fixpoint cp (n : nat) {struct n} : nat * nat :=
  match n with
  | O => (O, O)
  | S n' =>
    match cp n' with
    | (O, y) => (S y, O)
    | (S x, y) => (x, S y)
    end
  end.

Definition cpInv (x : nat) (y : nat) : nat :=
  sum_from_0_to (x + y) + y.

Lemma cpInv_leftInv (n : nat)
  : cpInv (fst (cp n)) (snd (cp n)) = n.
Proof with lia || eauto.
  induction n as [ | n IH]; simpl...
  destruct (cp n) as [x y] eqn: H_OBS. simpl in *. destruct x as [ | x']; subst n; cbn.
  - repeat rewrite add_0_r...
  - rewrite add_comm with (n := x'). simpl. rewrite add_comm with (m := x')... 
Qed.

Lemma cpInv_rightInv (x : nat) (y : nat)
  : cp (cpInv x y) = (x, y).
Proof with lia || eauto.
  unfold cpInv. remember (x + y) as z eqn: z_eq. revert y x z_eq. induction z as [ | z IH].
  - simpl; ii. destruct x as [ | x'], y as [ | y']...
  - induction y as [ | y IHy]; ii.
    + rewrite z_eq. rewrite add_0_r with (n := x). rewrite add_0_r with (n := x) in z_eq. subst x.
      rewrite add_0_r with (n := sum_from_0_to (S z)). simpl. rewrite <- add_comm. erewrite -> IH with (x := 0)...
    + assert (claim1 : z = x + y) by lia. subst z. clear z_eq. rename x into n, y into m. rewrite add_comm with (m := S m).
      assert (claim2 : S (n + m) = (S n) + m) by lia. apply IHy in claim2.
      simpl in *. rewrite add_comm. simpl. destruct (cp (n + m + sum_from_0_to (n + m) + m)) as [x y] eqn: H_OBS.
      destruct x as [ | x']; inv claim2...
Qed.

Theorem cp_spec (n : nat) (x : nat) (y : nat)
  : cp n = (x, y) <-> n = cpInv x y.
Proof.
  split; intros EQ.
  - rewrite <- cpInv_leftInv with (n := n). rewrite EQ. reflexivity.
  - subst n. rewrite <- cpInv_rightInv with (x := x) (y := y). reflexivity.
Qed.

Lemma fst_cp_le (n : nat)
  : fst (cp n) <= n.
Proof.
  destruct (cp n) as [x y] eqn: H_OBS. rewrite cp_spec in H_OBS.
  subst n. unfold cpInv. simpl. enough (ENOUGH : x + y <= sum_from_0_to (x + y)) by lia.
  induction (x + y) as [ | z IH]; simpl; lia.
Qed.

Lemma snd_cp_le (n : nat)
  : snd (cp n) <= n.
Proof.
  destruct (cp n) as [x y] eqn: H_OBS. rewrite cp_spec in H_OBS.
  subst n. unfold cpInv. simpl. enough (ENOUGH : x + y <= sum_from_0_to (x + y)) by lia.
  induction (x + y) as [ | z IH]; simpl; lia.
Qed.

Lemma cpInv_inj (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat)
  (EQ : cpInv x1 y1 = cpInv x2 y2)
  : x1 = x2 /\ y1 = y2.
Proof.
  enough (ENOUGH : (x1, y1) = (x2, y2)) by now inv ENOUGH.
  rewrite <- cp_spec in EQ. rewrite <- EQ. symmetry. eapply cp_spec. reflexivity.
Qed.

Corollary cpInv_inj1 {x1 : nat} {x2 : nat} {y1 : nat} {y2 : nat}
  (EQ : cpInv x1 y1 = cpInv x2 y2)
  : x1 = x2.
Proof.
  now apply cpInv_inj in EQ.
Qed.

Corollary cpInv_inj2 {x1 : nat} {x2 : nat} {y1 : nat} {y2 : nat}
  (EQ : cpInv x1 y1 = cpInv x2 y2)
  : y1 = y2.
Proof.
  now apply cpInv_inj in EQ.
Qed.

End CANTOR_PAIRING.

Lemma div_mod_uniqueness a b q r
  (H_DIVISION : a = b * q + r)
  (r_lt_b : r < b)
  : (a / b = q /\ a mod b = r)%nat.
Proof with try (lia || now (firstorder; eauto)).
  assert (claim1 : a = b * (a / b) + (a mod b)) by now eapply (Nat.div_mod a b); lia.
  assert (claim2 : 0 <= a mod b /\ a mod b < b) by now eapply (Nat.mod_bound_pos a b); lia.
  assert (claim3 : ~ q > a / b).
  { intros H_false. pose proof (proj1 (greater_than_iff q (a / b)) H_false) as [z q_eq].
    enough (so_we_obatain : b * q + r >= b * S (a / b) + r)...
  }
  assert (claim4 : ~ q < a / b).
  { intros H_false. pose proof (proj1 (greater_than_iff (a / b) q) H_false) as [z a_div_b_eq].
    enough (so_we_obtain: b * q + a mod b >= b * S (a / b) + a mod b)...
  }
  enough (therefore : q = a / b)...
Qed.

Theorem div_mod_inv a b q r
  (b_ne_0 : b <> 0)
  : (a = b * q + r /\ r < b)%nat <-> (q = (a - r) / b /\ r = a mod b /\ a >= r)%nat.
Proof with lia || eauto.
  pose proof (lemma1 := @Nat.div_mod). pose proof (lemma2 := @greater_than_iff). split.
  - intros [H_a H_r_bound].
    assert (claim1 : a = b * (a / b) + (a mod b))...
    assert (claim2 : 0 <= a mod b /\ a mod b < b). 
    { eapply (Nat.mod_bound_pos a b)... }
    assert (claim3 : a >= r)...
    enough (claim4 : ~ q > a / b). enough (claim5: ~ q < a / b). enough (claim6: q = a / b)...
    + split... replace (a - r) with (q * b)... symmetry; eapply Nat.div_mul...
    + intros H_false. pose proof (proj1 (lemma2 (a / b) q) H_false) as [x Hx]...
    + intros H_false. pose proof (proj1 (lemma2 q (a / b)) H_false) as [x Hx]...
  - intros [H_q [H_r H_a_ge_r]].
    pose proof (claim1 := Nat.mod_bound_pos a b). split...
    assert (claim2 : r < b)... assert (claim3 := Nat.div_mod a b b_ne_0).
    rewrite <- H_r in claim3. enough (claim4: q = a / b)...
    rewrite H_q; symmetry. eapply Nat.div_unique with (r := 0)...
Qed.

Theorem sqrt2irrat (p : nat) (q : nat)
  : (p = 0 /\ q = 0) <-> (p * p = 2 * q * q).
Proof with try lia.
  assert (forall P : nat -> Prop,
    (forall n : nat, (forall m : nat, m < n -> P m) -> P n) ->
    forall n, P n
  ) as STRONG_INDUCTION.
  { intros P IH_claim n. eapply IH_claim with (n := n).
    induction n as [ | n IH]; simpl...
    intros m m_lt_S_n. eapply IH_claim with (n := m).
    intros i i_lt_S_m. eapply IH with (m := i)...
  }
  split; [lia | revert p q].
  assert (lemma1 : forall n : nat, n mod 2 = 1 <-> (exists k : nat, n = 2 * k + 1)).
  { intros n. split.
    - pose proof (Nat.div_mod n 2) as H1. intros H2.
      rewrite H2 in H1. exists (n / 2)...
    - intros [k ->]. eapply div_mod_uniqueness with (q := k)...
  }
  assert (lemma2 : forall n : nat, n mod 2 = 0 <-> (exists k : nat, n = 2 * k)).
  { intros n. split.
    - pose proof (Nat.div_mod n 2) as H1. intros H2.
      rewrite H2, Nat.add_0_r in H1. exists (n / 2)...
    - intros [k ->]. eapply div_mod_uniqueness with (q := k)...
  }
  assert (lemma3 : forall n : nat, n mod 2 = 0 \/ n mod 2 = 1).
  { intros n. pose proof (Nat.mod_bound_pos n 2) as H1... }
  assert (lemma4 : 0 <> 1)...
  assert (claim1 : forall p : nat, forall q : nat, p * p = 2 * q * q -> p mod 2 = 0).
  { intros p q pp_eq_2qq.
    enough (to_show : p mod 2 <> 1) by now pose proof (lemma3 p) as H2; lia...
    intros H_contradiction. pose proof (proj1 (lemma1 p) H_contradiction) as [k H2]...
  }
  - intros p q pp_eq_2qq. enough (p_eq_0 : p = 0)... revert p q pp_eq_2qq.
    induction p as [p IH] using @STRONG_INDUCTION. unnw. ii.
    pose proof (proj1 (lemma2 p) (claim1 p q pp_eq_2qq)) as [p' p_eq_2p'].
    assert (p <= 0 \/ p > 0) as [p_le_0 | p_gt_0]...
    assert (p_gt_p' : p' < p)...
    assert (H1 : q * q = 2 * p' * p')...
    pose proof (proj1 (lemma2 q) (claim1 q p' H1)) as [q' p_eq_2q'].
    assert (H2 : p' * p' = 2 * q' * q')...
    assert (therefore: p' = 0) by exact (IH p' p_gt_p' q' H2)...
Qed.

Theorem mod_congruence_r (a : nat) (b : nat) (q : nat) (r : nat)
  (b_ne_0 : b <> 0)
  (a_b_q_r : a = b * q + r)
  : a mod b = r mod b.
Proof with lia || eauto.
  revert a b q b_ne_0 a_b_q_r. induction r as [r IH] using lt_wf_ind.
  i. assert (r < b \/ r >= b) as [r_lt_b | r_ge_b] by lia.
  - pose proof (div_mod_inv a b q r b_ne_0) as [H1 H2].
    pose proof (H1 (conj a_b_q_r r_lt_b)) as [H3 [H4 H5]].
    clear H1 H2. rename H3 into H1, H4 into H2, H5 into H3.
    rewrite <- H2. clear IH a q a_b_q_r H1 H2 H3.
    pose proof (div_mod_inv r b 0 r b_ne_0) as [? ?]...
  - pose proof (Nat.mod_bound_pos r b) as H0.
    assert (H1 : r - b < r)... clear H0.
    pose proof (IH (r - b) H1 a b (q + 1) b_ne_0) as IH'.
    assert (H2 : a = b * (q + 1) + (r - b))...
    pose proof (IH' H2) as H3. rewrite H3.
    remember (r - b) as r' eqn: H_r'.
    assert (H_r: r = r' + b)... subst r.
    rename r' into r; clear H_r' IH'.
    symmetry. eapply IH with (q := 1)...
Qed.

Corollary mod_eq_intro (a1 : nat) (a2 : nat) (b : nat) q1 q2
  (b_ne_0 : b <> 0)
  (a_b_q : a1 + b * q1 = a2 + b * q2)
  : a1 mod b = a2 mod b.
Proof.
  remember (a2 + b * q2) as n eqn: H_n.
  symmetry in a_b_q. rename H_n into H_n2, a_b_q into H_n1.
  pose proof (claim1 := mod_congruence_r n b q1 a1 b_ne_0).
  pose proof (claim2 := mod_congruence_r n b q2 a2 b_ne_0).
  lia.
Qed.

Lemma n_mod_b_le_n (n : nat) (b : nat)
  (b_ne_0 : b <> 0)
  : n mod b <= n.
Proof with lia || eauto.
  revert b b_ne_0. induction n as [n IH] using lt_wf_ind.
  i. assert (n <= b \/ n > b) as [H_le | H_gt] by lia.
  - pose proof (Nat.div_mod n b b_ne_0) as H. rewrite H at 2...
  - transitivity ((n mod b) + b)... enough (n mod b <= n - b)...
    erewrite mod_congruence_r with (q := 1) (r := n - b)... eapply IH...
Qed.

Lemma mod_eq_elim (a1 : nat) (a2 : nat) (b : nat)
  (b_ne_0 : b <> 0)
  (H_mod_eq : a1 mod b = a2 mod b)
  : exists q1, exists q2, a1 + b * q1 = a2 + b * q2.
Proof with lia || eauto.
  remember (a2 mod b) as r eqn: H_kr.
  symmetry in H_mod_eq. rename H_kr into H_r2, H_mod_eq into H_r1.
  exists (a2 / b), (a1 / b). transitivity (a1 + a2 - r).
  - pose proof (n_mod_b_le_n r b b_ne_0).
    enough (b * (a2 / b) + r = a2)... symmetry. rewrite H_r2.
    pose proof (Nat.div_mod a2 b)...
  - pose proof (n_mod_b_le_n r b b_ne_0).
    enough (b * (a1 / b) + r = a1)... symmetry. rewrite H_r1.
    pose proof (Nat.div_mod a1 b)...
Qed.

Lemma mod_add (a : nat) (b : nat) (c : nat)
  (c_ne_0 : c <> 0)
  : (a + b * c) mod c = a mod c.
Proof.
  eapply mod_congruence_r with (q := b); lia.
Qed.

Lemma plus_a_b_divmod_b a b
  (b_ne_0 : b <> 0)
  : ((a + b) / b = (a / b) + 1)%nat /\ ((a + b) mod b = a mod b)%nat.
Proof with try lia.
  eapply div_mod_uniqueness with (a := a + b) (b := b) (q := (a / b) + 1) (r := a mod b).
  - replace (b * (a / b + 1) + a mod b) with ((b * (a / b) + a mod b) + b)...
    enough (claim1 : a = b * (a / b) + a mod b) by congruence.
    exact (Nat.div_mod a b b_ne_0).
  - assert (claim2 : b > 0)... eapply Nat.mod_bound_pos...
Qed.

Lemma positive_odd (n_odd : nat) n
  : (n_odd = 2 * n + 1)%nat <-> (n = (n_odd - 1) / 2 /\ n_odd mod 2 = 1 /\ n_odd > 0)%nat.
Proof.
  pose proof (div_mod_inv n_odd 2 n 1); lia.
Qed.

Lemma positive_even (n_even : nat) n
  : (n_even = 2 * n + 2)%nat <-> (n = (n_even - 2) / 2 /\ n_even mod 2 = 0 /\ n_even > 0)%nat.
Proof with lia || eauto.
  pose proof (claim1 := div_mod_inv (n_even - 2) 2 n 0). split.
  - intros ->.
    assert (claim2 : n = (2 * n + 2 - 2 - 0) / 2 /\ 0 = (2 * n + 2 - 2) mod 2 /\ 2 * n + 2 - 2 >= 0)...
    split. rewrite (proj1 claim2) at 1. replace (2 * n + 2 - 2 - 0) with (2 * n + 2 - 2)...
    split... replace (2 * n + 2) with (2 + n * 2)... rewrite mod_add...
  - intros [H_n [H_r H_gt_0]].
    assert (claim2 : n_even >= 2).
    { destruct n_even as [ | [ | n_even]]... inversion H_r. }
    assert (claim3 : n_even = 2 * (n_even / 2) + n_even mod 2).
    { eapply Nat.div_mod... }
    enough (claim4 : (n_even - 2) mod 2 = 0).
    + assert (claim5 : n_even - 2 = 2 * n + 0 /\ 0 < 2)...
      rewrite H_r, Nat.add_0_r in claim3. eapply claim1...
      replace (n_even - 2 - 0) with (n_even - 2)...
    + transitivity (n_even mod 2)...
      symmetry; replace (n_even) with ((n_even - 2) + 1 * 2) at 1...
      eapply mod_add...
Qed.

Section LOGARITHM.

Lemma log_aux1 b n
  (b_gt_1 : b > 1)
  (n_gt_0 : n > 0)
  : n / b < n.
Proof.
  pose proof (Nat.div_mod n b) as H.
  rewrite H at 2; try lia.
  destruct b as [ | [ | b]]; lia.
Qed.

Fixpoint log1 (b : nat) (n : nat) (b_gt_1 : b > 1) (n_gt_0 : n > 0) (H_Acc : Acc lt n) {struct H_Acc} : nat :=
  match le_lt_dec (n / b) 0 with
  | left H_LE => 0
  | right H_GT => 1 + log1 b (n / b) b_gt_1 H_GT (Acc_inv H_Acc (log_aux1 b n b_gt_1 n_gt_0))
  end.

Fixpoint log1_pirrel b n b_gt_1 n_gt_0 H_Acc H_Acc' {struct H_Acc} : log1 b n b_gt_1 n_gt_0 H_Acc = log1 b n b_gt_1 n_gt_0 H_Acc'.
Proof.
  destruct H_Acc, H_Acc'; simpl. destruct (le_lt_dec (n / b) 0); [reflexivity | f_equal; eapply log1_pirrel].
Qed.

Definition log (b : nat) (n : nat) (b_gt_1 : b > 1) (n_gt_0 : n > 0) : nat :=
  log1 b n b_gt_1 n_gt_0 (lt_wf n).

Lemma log_unfold (b : nat) (n : nat) (b_gt_1 : b > 1) (n_gt_0 : n > 0) :
  log b n b_gt_1 n_gt_0 =
  match le_lt_dec (n / b) 0 with
  | left H_LE => 0
  | right H_GT => 1 + log b (n / b) b_gt_1 H_GT
  end.
Proof.
  unfold log at 1; simpl. destruct (le_lt_dec _ _) as [H_LE | H_GT]; simpl.
  - reflexivity.
  - f_equal. eapply log1_pirrel.
Qed.

Lemma exp_r_0 (b : nat)
  : b ^ 0 = 1.
Proof.
  reflexivity.
Qed.

Lemma exp_r_S (b : nat) (x : nat)
  : b ^ (S x) = b * (b ^ x).
Proof.
  reflexivity.
Qed.

Lemma exp_gt_0 (b : nat) (x : nat) (b_gt_1 : b > 1)
  : b ^ x > 0.
Proof.
  induction x as [ | x IH]; simpl in *; lia.
Qed.

Lemma exp_log_upper_bound (b : nat) (x : nat) (b_gt_1 : b > 1) (x_gt_0 : x > 0)
  (y := log b x b_gt_1 x_gt_0)
  : b ^ y <= x.
Proof.
  subst y. induction (lt_wf x) as [x _ IH]. rewrite log_unfold. destruct (le_lt_dec (x / b) 0) as [YES | NO].
  - rewrite exp_r_0; lia.
  - simpl. pose proof (IH (x / b) (log_aux1 b x b_gt_1 x_gt_0) NO) as LE. transitivity (b * (x / b)).
    + erewrite <- Nat.mul_le_mono_pos_l; lia.
    + erewrite Nat.div_mod with (x := x) (y := b) at 2; lia. 
Qed.

Lemma exp_log_lower_bound (b : nat) (x : nat) (b_gt_1 : b > 1) (x_gt_0 : x > 0)
  (y := log b x b_gt_1 x_gt_0)
  : x / b < b ^ y.
Proof.
  subst y. induction (lt_wf x) as [x _ IH]. rewrite log_unfold. destruct (le_lt_dec (x / b) 0) as [YES | NO].
  - rewrite exp_r_0; lia.
  - simpl. pose proof (IH (x / b) (log_aux1 b x b_gt_1 x_gt_0) NO) as LE.
    rewrite Nat.div_mod with (x := x / b) (y := b) at 1; try lia. red in LE |- *.
    transitivity (b * (x / b / b) + b).
    { pose proof (Nat.mod_bound_pos (x / b) b); lia. }
    transitivity (b * S (x / b / b)); try lia.
    erewrite <- Nat.mul_le_mono_pos_l; lia.
Qed.

Theorem exp_log_sandwitch (b : nat) (x : nat) (b_gt_1 : b > 1) (x_gt_0 : x > 0)
  (y := log b x b_gt_1 x_gt_0)
  : b ^ y <= x /\ b ^ (1 + y) > x.
Proof.
  subst y. simpl. split; [eapply exp_log_upper_bound | unfold ">"].
  induction (lt_wf x) as [x _ IH]. rewrite log_unfold. destruct (le_lt_dec (x / b) 0) as [YES | NO].
  - rewrite exp_r_0. pose proof (Nat.div_mod x b) as claim1. replace (x / b) with 0 in claim1 by lia.
    rewrite Nat.mul_comm in claim1. rewrite Nat.mul_comm. simpl in *. pose proof (Nat.mod_bound_pos x b); lia. 
  - simpl. pose proof (IH (x / b) (log_aux1 b x b_gt_1 x_gt_0) NO) as LE.
    rewrite Nat.div_mod with (x := x) (y := b) at 1; try lia. red in LE |- *.
    transitivity (b * (x / b) + b).
    { pose proof (Nat.mod_bound_pos x b); lia. }
    transitivity (b * S (x / b)); try lia.
    erewrite <- Nat.mul_le_mono_pos_l; lia.
Qed.

Lemma log_pirrel (a : nat) (b : nat) (n : nat) (m : nat) (a_gt_1 : a > 1) (b_gt_1 : b > 1) (n_gt_0 : n > 0) (m_gt_0 : m > 0)
  (EQ1 : a = b)
  (EQ2 : n = m)
  : log a n a_gt_1 n_gt_0 = log b m b_gt_1 m_gt_0.
Proof.
  subst m. subst a.
  rewrite le_pirrel with (LE1 := a_gt_1) (LE2 := b_gt_1).
  rewrite le_pirrel with (LE1 := m_gt_0) (LE2 := n_gt_0).
  reflexivity.
Qed.

Lemma log_exp (b : nat) (x : nat) (b_gt_1 : b > 1)
  : log b (b ^ x) b_gt_1 (exp_gt_0 b x b_gt_1) = x.
Proof.
  induction x as [ | x IH]; simpl.
  - rewrite log_unfold. destruct (le_lt_dec _ _) as [H_LE | H_GT]; trivial.
    pose proof (Nat.div_mod 1 b). lia.
  - rewrite log_unfold. destruct (le_lt_dec _ _) as [H_LE | H_GT]; simpl.
    + pose proof (div_mod_uniqueness (b * b ^ x) b (b ^ x) 0); pose proof (exp_gt_0 b x b_gt_1); lia.
    + assert (EQ : b * (b ^ x) / b = b ^ x).
      { pose proof (div_mod_uniqueness (b * b ^ x) b (b ^ x) 0). lia. }
      f_equal. rewrite <- IH at 2. eapply log_pirrel; trivial.
Qed.

End LOGARITHM.

Section section_for_maxs.

#[local] Notation In := List.In.

Definition maxs : list nat -> nat := fold_right max 0.

Lemma in_maxs_ge (ns : list nat) (n : nat)
  (H_IN : In n ns)
  : maxs ns >= n.
Proof with (lia || eauto).
  unfold maxs. revert n H_IN. induction ns as [ | n' ns IH]; simpl...
  intros n [H_eq | H_in]... enough (ENOUGH: fold_right max 0 ns >= n)...
Qed.

Lemma maxs_app (ns1 : list nat) (ns2 : list nat)
  : maxs (ns1 ++ ns2) = max (maxs ns1) (maxs ns2).
Proof with (lia || eauto).
  unfold maxs. revert ns2.
  induction ns1 as [ | n1 ns1 IH]; simpl... 
  intros n; rewrite IH...
Qed.

Lemma maxs_ind (phi : nat -> Prop) (ns : list nat)
  (phi_dec : forall i, {phi i} + {~ phi i})
  (phi_in : forall i, phi i -> In i ns)
  : forall n, phi n -> maxs ns >= n.
Proof with try now (lia || firstorder; eauto).
  unfold maxs. induction ns as [ | n1 ns1 IH]; simpl... intros n phi_n.
  destruct (le_gt_dec n n1) as [H_le | H_gt]... enough (claim1 : fold_right max 0 ns1 >= n)...
  destruct (phi_dec n) as [H_yes | H_no]... destruct (phi_in n H_yes)...
  enough (claim2 : forall ks : list nat, forall k : nat, In k ks -> fold_right max 0 ks >= k)...
  induction ks; simpl... intros k [H_eq | H_in]... enough (claim3: fold_right Init.Nat.max 0 ks >= k)...
Qed.

Lemma maxs_lt_iff (ns : list nat)
  : forall z, maxs ns > z <-> exists i, In i ns /\ i > z.
Proof with try now (lia || firstorder; eauto).
  unfold maxs. induction ns as [ | n1 ns1 IH]; simpl... intros n.
  destruct (le_gt_dec n1 (fold_right Init.Nat.max 0 ns1)); split.
  - intros H_gt. assert (claim1: fold_right Init.Nat.max 0 ns1 > n)...
  - intros [i [[H_eq | H_in] H_gt]]... enough (claim2: fold_right max 0 ns1 > n)...
  - intros H_gt. exists n1...
  - intros [i [[H_eq | H_in] H_gt]]... enough (claim3: fold_right Init.Nat.max 0 ns1 > n)...
Qed.

Lemma maxs_subset (ns1 : list nat) (ns2 : list nat)
  (H_SUBSET : forall n, In n ns1 -> In n ns2)
  : maxs ns1 <= maxs ns2.
Proof with try now (lia || firstorder; eauto).
  unfold maxs. revert ns2 H_SUBSET; induction ns1 as [ | n1 ns1 IH]; simpl...
  intros ns2 H. destruct (le_gt_dec n1 (fold_right max 0 ns1)).
  - enough (ENOUGH : fold_right max 0 ns1 <= fold_right max 0 ns2)...
  - enough (ENOUGH : n1 <= fold_right max 0 ns2)... eapply in_maxs_ge...
Qed.

Lemma maxs_ext (ns1 : list nat) (ns2 : list nat)
  (H_EXT_EQ : forall n, In n ns1 <-> In n ns2)
  : maxs ns1 = maxs ns2.
Proof with try now firstorder.
  unfold maxs. enough (claim1 : fold_right max 0 ns1 <= fold_right max 0 ns2 /\ fold_right max 0 ns2 <= fold_right max 0 ns1) by lia.
  split; eapply maxs_subset...
Qed.

Lemma maxs_sim ns1 ns2
  (SIM : forall n, In n ns1 -> exists n', In n' ns2 /\ n <= n')
  : maxs ns1 <= maxs ns2.
Proof.
  revert ns2 SIM. induction ns1 as [ | n1 ns1 IH]; simpl; ii.
  - lia.
  - pose proof (SIM n1 (or_introl eq_refl)) as [n2 [IN LE]].
    enough (n1 <= maxs ns2 /\ maxs ns1 <= maxs ns2) by lia.
    split.
    + transitivity n2.
      * exact LE.
      * eapply in_maxs_ge. exact IN.
    + eapply IH. intros n H_in.
      pose proof (SIM n (or_intror H_in)) as [n' [H_in' LE']].
      exists n'. split.
      * exact H_in'.
      * exact LE'.
Qed.

End section_for_maxs.

Lemma eq_by_lt_ext (x : nat) (y : nat)
  (LT_EXT : forall z, z < x <-> z < y)
  : x = y.
Proof.
  pose proof (LT_EXT x); pose proof (LT_EXT y); lia.
Qed.

#[local] Notation zero := O.
#[local] Notation suc := S.

Definition is_suc (n : nat) : Prop :=
  match n with
  | zero => False
  | suc n' => True
  end.

Definition not_S_n_eq_0 {n : nat} (hyp_eq : S n = 0) : False :=
  match hyp_eq in eq _ x return is_suc x with
  | eq_refl => I
  end.

Definition suc_n_eq_zero_elim {A : Type} {n : nat} (hyp_eq : S n = 0) : A :=
  False_rect A (not_S_n_eq_0 hyp_eq).

Definition suc_n_eq_suc_m_elim {n : nat} {m : nat} (hyp_eq : S n = S m) : n = m :=
  f_equal Nat.pred hyp_eq.

Definition not_S_n_le_0 {n : nat} (hyp_le : S n <= 0) : False :=
  match hyp_le in le _ x return is_suc x with
  | le_n _ => I
  | le_S _ m' hyp_lt' => I
  end.

Definition lt_elim_n_lt_0 {A : Type} {n : nat} (hyp_lt : n < 0) : A :=
  False_rect A (not_S_n_le_0 hyp_lt).

Definition suc_pred_n_eq_n_if_m_lt_n {n : nat} {m : nat} (hyp_lt : m < n) : S (pred n) = n :=
  match hyp_lt in le _ x return S (pred x) = x with
  | le_n _ => @eq_refl _ (S m)
  | le_S _ n' hyp_lt' => @eq_refl _ (S n')
  end.

Fixpoint n_le_pred_m_if_n_lt_m {n : nat} {m : nat} (hyp_le : S n <= m) {struct hyp_le} : n <= pred m :=
  match hyp_le in le _ x return n <= pred x with
  | le_n _ => le_n n
  | le_S _ m' hyp_le' => eq_ind (S (pred m')) (le n) (le_S n (pred m') (n_le_pred_m_if_n_lt_m hyp_le')) m' (suc_pred_n_eq_n_if_m_lt_n hyp_le')
  end.

Definition lt_elim_n_lt_S_m {n : nat} {m : nat} (hyp_lt : n < S m) : n <= m :=
  n_le_pred_m_if_n_lt_m hyp_lt.

Definition le_reflexivity {n1 : nat} : n1 <= n1 :=
  le_n n1.

Fixpoint le_transitivity {n1 : nat} {n2 : nat} {n3 : nat} (hyp1 : n1 <= n2) {struct hyp1} : n2 <= n3 -> n1 <= n3 :=
  match hyp1 in le _ x return x <= n3 -> n1 <= n3 with
  | le_n _ => fun hyp2 : n1 <= n3 => hyp2
  | le_S _ n2' hyp1' => fun hyp2 : n2' < n3 => le_transitivity hyp1' (eq_ind (S (pred n3)) (fun x : nat => n2' <= x) (le_S n2' (pred n3) (n_le_pred_m_if_n_lt_m hyp2)) n3 (suc_pred_n_eq_n_if_m_lt_n hyp2))
  end.

Fixpoint le_antisymmetry {n1 : nat} {n2 : nat} {struct n1} : n1 <= n2 -> n1 >= n2 -> n1 = n2 :=
  match n1 as x, n2 as y return x <= y -> y <= x -> x = y with
  | O, O => fun hyp1 : O <= O => fun hyp2 : O <= O => @eq_refl _ 0
  | O, S n2' => fun hyp1 : O <= S n2' => fun hyp2 : S n2' <= O => lt_elim_n_lt_0 hyp2
  | S n1', O => fun hyp1 : S n1' <= O => fun hyp2 : O <= S n1' => lt_elim_n_lt_0 hyp1
  | S n1', S n2' => fun hyp1 : n1' < S n2' => fun hyp2 : n2' < S n1' => f_equal S (le_antisymmetry (lt_elim_n_lt_S_m hyp1) (lt_elim_n_lt_S_m hyp2))
  end.

Fixpoint le_intro_S_n_le_S_m {n : nat} {m : nat} (hyp_LE : n <= m) {struct hyp_LE} : S n <= S m :=
  match hyp_LE in le _ x return le (S n) (S x) with
  | le_n _ => le_n (S n)
  | le_S _ m' hyp_LE' => le_S (S n) (S m') (le_intro_S_n_le_S_m hyp_LE')
  end.

Fixpoint le_intro_0_le_n {n : nat} {struct n} : 0 <= n :=
  match n with
  | O => le_n O
  | S n' => le_S O n' le_intro_0_le_n
  end.

Fixpoint not_n_lt_n (n : nat) {struct n} : ~ n < n :=
  match n with
  | O => lt_elim_n_lt_0
  | S n' => fun hyp_lt : S n' < S n' => not_n_lt_n n' (lt_elim_n_lt_S_m hyp_lt)
  end.

Fixpoint n1_le_max_n1_n2 (n1 : nat) (n2 : nat) {struct n1} : n1 <= max n1 n2 :=
  match n1 as n return n <= max n n2 with
  | O => le_intro_0_le_n
  | S n1' =>
    match n2 as m return S n1' <= max (S n1') m with
    | O => le_n (S n1')
    | S n2' => le_intro_S_n_le_S_m (n1_le_max_n1_n2 n1' n2')
    end
  end.

Fixpoint n2_le_max_n1_n2 (n1 : nat) (n2 : nat) {struct n1} : n2 <= max n1 n2 :=
  match n1 as n return n2 <= max n n2 with
  | O => le_n n2
  | S n1' =>
    match n2 as m return m <= max (S n1') m with
    | O => le_intro_0_le_n
    | S n2' => le_intro_S_n_le_S_m (n2_le_max_n1_n2 n1' n2')
    end
  end.

Fixpoint le_intro_plus_l (n1 : nat) (n2 : nat) {struct n1} : n1 <= n1 + n2 :=
  match n1 with
  | O => le_intro_0_le_n
  | S n1' => le_intro_S_n_le_S_m (le_intro_plus_l n1' n2)
  end.

Fixpoint le_intro_plus_r (n1 : nat) (n2 : nat) {struct n1} : n2 <= n1 + n2 :=
  match n1 with
  | O => le_reflexivity
  | S n1' => le_transitivity (le_intro_plus_r n1' n2) (le_S (n1' + n2) (n1' + n2) le_reflexivity)
  end.

Definition le_elim_max_n1_n2_le_m (n1 : nat) (n2 : nat) (m : nat) (hyp_le : max n1 n2 <= m) : n1 <= m /\ n2 <= m :=
  @conj _ _ (le_transitivity (n1_le_max_n1_n2 n1 n2) hyp_le) (le_transitivity (n2_le_max_n1_n2 n1 n2) hyp_le).

Lemma le_unfold {n : nat} {m : nat} :
  n <= m <->
  match m with
  | O => n = 0
  | S m' => n = S m' \/ n <= m'
  end.
Proof.
  split; destruct m as [ | m'].
  - intros hyp_le.
    exact (le_antisymmetry hyp_le le_intro_0_le_n).
  - intros hyp_le.
    exact (
      match hyp_le in le _ x return n = x \/ n <= Nat.pred x with
      | le_n _ => or_introl (@eq_refl _ n)
      | le_S _ m' hyp_le' => or_intror hyp_le'
      end
    ).
  - exact (eq_ind n (le n) (le_n n) 0).
  - intros [hyp_eq | hyp_le].
    + exact (eq_ind n (le n) (le_n n) (suc m') hyp_eq).
    + exact (le_S n m' hyp_le).
Qed.

Theorem nat_strong_recursion (A : nat -> Type) (P : forall n : nat, A n -> Prop)
  (SREC : forall REC : (forall n, option (A n)), forall x : nat, ⟪ REC_SPEC : forall x', x' < x -> { RET : { y' : A x' | P x' y' } | REC x' = Some (proj1_sig RET) } ⟫ -> { y : A x | P x y })
  : { f : (forall n, A n) | forall n, P n (f n) }.
Proof.
  enough (WTS : forall x : nat, { y : A x | P x y }).
  { exists (fun n => proj1_sig (WTS n)). exact (fun n => proj2_sig (WTS n)). }
  intros x. induction (lt_wf x) as [x _ IH]. pose (REC := fun x' => match le_gt_dec x x' with left LE => None | right GT => Some (proj1_sig (IH x' GT)) end).
  eapply SREC with (REC := REC). intros y LT. exists (IH y LT). unfold REC. destruct (le_gt_dec x y) as [LE | GT].
  - lia.
  - rewrite le_pirrel with (LE1 := LT) (LE2 := GT). reflexivity.
Defined.

Theorem nat_strong_recursion' (A : nat -> Type) (P : forall n : nat, A n -> Type)
  (SREC : forall REC : (forall n, option (A n)), forall x : nat, ⟪ REC_SPEC : forall x', x' < x -> { RET : { y' : A x' & P x' y' } | REC x' = Some (projT1 RET) } ⟫ -> { y : A x & P x y })
  : { f : (forall n, A n) & forall n, P n (f n) }.
Proof.
  enough (WTS : forall x : nat, { y : A x & P x y }).
  { exists (fun n => projT1 (WTS n)). exact (fun n => projT2 (WTS n)). }
  intros x. induction (lt_wf x) as [x _ IH]. pose (REC := fun x' => match le_gt_dec x x' with left LE => None | right GT => Some (projT1 (IH x' GT)) end).
  eapply SREC with (REC := REC). intros y LT. exists (IH y LT). unfold REC. destruct (le_gt_dec x y) as [LE | GT].
  - lia.
  - rewrite le_pirrel with (LE1 := LT) (LE2 := GT). reflexivity.
Defined.

#[local] Obligation Tactic := idtac.
#[local] Opaque "/" "mod".

#[global, program]
Instance sum_isEnumerable {A : Type} {A' : Type} `{ENUMERABLE : isEnumerable A} `{ENUMERABLE' : isEnumerable A'} : isEnumerable (A + A') :=
  { enum n := if Nat.eqb (n mod 2) 0 then inl (enum (n / 2)) else inr (enum (n / 2)) }.
Next Obligation.
  intros ? ? ? ? [x | x].
  - exists (2 * proj1_sig (enum_spec x)). destruct (enum_spec x) as [n n_spec]; simpl proj1_sig. obs_eqb ((2 * n) mod 2) 0; f_equal.
    + rewrite <- n_spec. f_equal. symmetry. pose proof (Nat.div_mod (2 * n) 2). lia.
    + contradiction H_OBS. rewrite Nat.mul_comm. eapply Nat.Div0.mod_mul.
  - exists (2 * proj1_sig (enum_spec x) + 1). destruct (enum_spec x) as [n n_spec]; simpl proj1_sig. obs_eqb ((2 * n + 1) mod 2) 0; f_equal.
    + pose proof (claim := @mod_congruence_r (2 * n + 1) 2 n 1). rewrite H_OBS in claim. discriminate claim; lia.
    + rewrite <- n_spec. f_equal. symmetry. pose proof (div_mod_uniqueness (2 * n + 1) 2 n 1 eq_refl). lia.
Qed.

#[global, program]
Instance prod_isEnumerable {A : Type} {A' : Type} `{ENUMERABLE : isEnumerable A} `{ENUMERABLE' : isEnumerable A'} : isEnumerable (A * A') :=
  { enum n := (enum (fst (cp n)), enum (snd (cp n))) }.
Next Obligation.
  intros ? ? ? ? [x y]. exists (cpInv (proj1_sig (enum_spec x)) (proj1_sig (enum_spec y))). destruct (enum_spec x) as [n n_spec], (enum_spec y) as [m m_spec]; simpl proj1_sig. f_equal.
  - rewrite <- n_spec. f_equal. rewrite cpInv_rightInv. reflexivity.
  - rewrite <- m_spec. f_equal. rewrite cpInv_rightInv. reflexivity.
Qed.

#[local] Obligation Tactic := i.

#[global, program]
Instance sum_isCountable {A : Type} {A' : Type} `{COUNTABLE : isCountable A} `{COUNTABLE' : isCountable A'} : isCountable (A + A') :=
  { encode it := match it with inl y => 2 * encode y | inr z => 2 * encode z + 1 end
  ; decode n := if Nat.eqb (n mod 2) 0 then fmap inl (decode (n / 2)) else fmap inr (decode (n / 2))
  }.
Next Obligation.
  destruct x as [y | z]; cbn beta zeta.
  - obs_eqb ((2 * encode y) mod 2) 0.
    + exploit (Nat.div_mod (2 * encode y) 2). lia. rewrite H_OBS. rewrite Nat.add_0_r. intros EQ.
      assert (claim1 : encode y = 2 * encode y / 2) by lia.
      rewrite <- claim1. rewrite decode_encode. reflexivity.
    + contradiction H_OBS. rewrite Nat.mul_comm. eapply Nat.Div0.mod_mul.
  - obs_eqb ((2 * encode z + 1) mod 2) 0.
    + pose proof (claim := @mod_congruence_r (2 * encode z + 1) 2 (encode z) 1). rewrite H_OBS in claim. discriminate claim; lia.
    + exploit (div_mod_uniqueness (2 * encode z + 1) 2 (encode z) 1); try lia. intros [claim1 claim2]. rewrite claim1. rewrite decode_encode; reflexivity.
Qed.

#[global, program]
Instance prod_isCountable {A : Type} {A' : Type} `{COUNTABLE : isCountable A} `{COUNTABLE' : isCountable A'} : isCountable (A * A') :=
  { encode it := cpInv (encode (fst it)) (encode (snd it))
  ; decode n := liftM2 (@pair A A') (decode (fst (cp n))) (decode (snd (cp n)))
  }.
Next Obligation.
  destruct x as [y z]; cbn beta; simpl fst; simpl snd.
  rewrite cpInv_rightInv. simpl fst; simpl snd.
  do 2 rewrite decode_encode. reflexivity.
Qed.

Fixpoint downto (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => n' :: downto n'
  end.

Lemma in_downto_iff n
  : forall x, L.In x (downto n) <-> x < n.
Proof.
  induction n as [ | n IH]; s!.
  - lia.
  - intros x. rewrite IH. lia.
Qed.

#[global] Hint Rewrite in_downto_iff : simplication_hints.

Definition ne (x : nat) (y : nat) : Prop :=
  x < y \/ y < x.

Infix "≠" := ne : nat_scope.

Lemma ne_pirrel (x : nat) (y : nat)
  (NE1 : x ≠ y)
  (NE2 : x ≠ y)
  : NE1 = NE2.
Proof.
  destruct NE1 as [LT1 | GT1], NE2 as [LT2 | GT2]; try lia; f_equal; eapply le_pirrel.
Qed.

Lemma ne_iff (x : nat) (y : nat)
  : x ≠ y <-> x <> y.
Proof.
  unfold ne. lia.
Qed.

Section SET_LEVEL_LE.

Inductive lessthanequalto (n : nat) : nat -> Set :=
  | lessthanequalto_refl
    : n ≦ n
  | lessthanequalto_step m
    (LE : n ≦ m)
    : n ≦ S m
  where "n ≦ m" := (lessthanequalto n m) : nat_scope.

Lemma lessthanequalto_to_le n m
  (LE : n ≦ m)
  : n <= m.
Proof.
  induction LE; simpl.
  - econs 1.
  - econs 2. eassumption.
Defined.

Fixpoint le_to_lessthanequalto (m : nat) {struct m} : forall n, n <= m -> n ≦ m.
Proof.
  destruct m as [ | m].
  - intros [ | n] H.
    + econs 1.
    + exfalso. lia.
  - intros [ | n] H.
    + econs 2. eapply le_to_lessthanequalto. lia.
    + assert (n <= m) as IH by lia.
      apply le_to_lessthanequalto in IH.
      revert IH. clear. intros ?. induction IH.
      * econs 1.
      * econs 2. eassumption.
Defined.

Theorem lessthanequalto_proof_unique {n1 : nat} {n2 : nat}
  (hyp1 : n1 ≦ n2)
  (hyp2 : n1 ≦ n2)
  : hyp1 = hyp2.
Proof.
  revert n2 hyp1 hyp2.
  refine (
    fix le_pirrel_fix (n2 : nat) (hyp1 : n1 ≦ n2) {struct hyp1} : forall hyp2 : n1 ≦ n2, hyp1 = hyp2 :=
    match hyp1 as hyp1' in lessthanequalto _ n2' return forall hyp2 : n1 ≦ n2', hyp1' = hyp2 with
    | lessthanequalto_refl _ => fun hyp2 : n1 ≦ n1 => _
    | lessthanequalto_step _ n1' hyp1' => fun hyp2 : n1 ≦ S n1' => _
    end
  ).
  - refine ((fun claim1 => _)
      match hyp2 as hyp2' in lessthanequalto _ n2' return forall h_eq : n1 = n2', eq_rec n1 (lessthanequalto n1) (lessthanequalto_refl n1) n2' h_eq = hyp2' with
      | lessthanequalto_refl _ => _
      | lessthanequalto_step _ n2' hyp2' => _
      end
    ).
    + exact (claim1 eq_refl).
    + intros h_eq.
      rewrite eq_pirrel_fromEqDec with (EQ1 := h_eq) (EQ2 := eq_refl).
      reflexivity.
    + intros h_eq. exfalso. contradiction (not_n_lt_n n2').
      unfold "<". rewrite <- h_eq. eapply lessthanequalto_to_le; eassumption.
  - refine ((fun claim2 => _)
      match hyp2 as hyp2' in lessthanequalto _ n2' return forall h_eq : n2' = S n1', lessthanequalto_step n1 n1' hyp1' = eq_rec n2' (lessthanequalto n1) hyp2' (S n1') h_eq with
      | lessthanequalto_refl _ => _
      | lessthanequalto_step _ n2' hyp2' => _
      end
    ).
    + exact (claim2 eq_refl).
    + intros h_eq. contradiction (not_n_lt_n n1').
      unfold "<". rewrite <- h_eq. eapply lessthanequalto_to_le; eassumption.
    + intros h_eq.
      pose proof (suc_n_eq_suc_m_elim h_eq) as hyp_eq; subst n2'.
      rewrite eq_pirrel_fromEqDec with (EQ1 := h_eq) (EQ2 := eq_refl).
      exact (f_equal (lessthanequalto_step n1 n1') (le_pirrel_fix n1' hyp1' hyp2')).
Qed.

#[global, program]
Instance lessthanequalto_retracts_le (n : nat) (m : nat) : B.retracts (lessthanequalto n m) (le n m) :=
  { section := lessthanequalto_to_le n m
  ; retraction := le_to_lessthanequalto m n
  }.
Next Obligation.
  eapply lessthanequalto_proof_unique.
Defined.
Next Obligation.
  eapply le_pirrel.
Defined.

End SET_LEVEL_LE.
