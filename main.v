From Coq Require Import Arith Program Omega.

Inductive four_expr : Set :=
| Four : four_expr
| Factorial : four_expr -> four_expr
| SqrtF : four_expr -> four_expr
| SqrtC : four_expr -> four_expr
| LogF : four_expr -> four_expr
| LogC : four_expr -> four_expr
.

Fixpoint fact (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => n * fact n'
  end.

Lemma fact_pos : forall n, fact n > 0.
Proof.
  induction n.
  simpl; omega.
  simpl.
  apply Nat.lt_lt_add_r.
  trivial.
Qed.

Lemma fact_inc : forall n, n > 0 -> fact (S n) > fact n.
Proof.
  intros.
  simpl.
  assert (n * fact n > 0).
  assert (fact n > 0).
  apply fact_pos.
  apply Nat.mul_pos_pos; trivial.
  omega.
Qed.

Lemma fact_inc' : forall n m, n > 0 -> n < m -> fact n < fact m.
Proof.
  intros.
  induction H0.
  apply fact_inc.
  assumption.
  assert (fact m < fact (S m)).
  apply fact_inc.
  omega.
  omega.
Qed.

Lemma fact_nondec : forall n m, n < m -> fact n <= fact m.
Proof.
  intros.
  induction n.
  simpl.
  assert (fact m > 0).
  apply fact_pos.
  omega.
  assert (fact (S n) < fact m).
  apply fact_inc'; try assumption; try omega.
  omega.
Qed.

Inductive Op : Type :=
| EQ
| LE
| GE.

Fixpoint gwp (n : nat) (g : nat) (cond : nat -> nat -> nat) : nat :=
  match g with
  | 0 => 0
  | S g' => match cond n g' with
           | 0 => g
           | S k => gwp n g' cond
           end
  end.
    
Definition logf (n : nat) : nat :=
  n - gwp n n (fun n g' => 1 + n - Nat.pow 10 (n - g')).

Definition logc (n : nat) : nat :=
  n - gwp n n (fun n g' => n - Nat.pow 10 (n - S g')).

Compute logc 10.

Fixpoint comp (f : four_expr) : nat :=
  match f with
  | Four => 4
  | Factorial f' => fact (comp f')
  | SqrtF f' => Nat.sqrt (comp f')
  | SqrtC f' => Nat.sqrt_up (comp f')
  | LogF f' => Nat.log2 (comp f')
  | LogC f' => Nat.log2_up (comp f')
  end.

Fixpoint fact_tower (n : nat) :=
  match n with
  | 0 => Four
  | S n' => Factorial (fact_tower n')
  end.

Lemma fact_tower_pos : forall n, comp (fact_tower n) > 0.
Proof.
  intros.
  induction n.
  simpl; omega.
  simpl.
  apply fact_pos.
Qed.

Definition sqrt_ft (n : nat) :=
  SqrtF (fact_tower n).

Lemma mul2_gt : forall n, n > 0 -> n < 2 * n.
Proof.
  intros.
  omega.
Qed.

Lemma sqrt_nondec : forall n, Nat.sqrt n <= Nat.sqrt (S n).
Proof.
  intros.
  apply Nat.sqrt_le_mono.
  omega.
Qed.

Lemma sqrt_pos : forall n, n > 0 -> Nat.sqrt n > 0.
Proof.
  intros.
  induction H.
  rewrite Nat.sqrt_1; omega.
  assert (Nat.sqrt (S m) >= Nat.sqrt m).
  apply sqrt_nondec.
  omega.
Qed.

Lemma sqrt_lt' : forall n, n > 0 -> Nat.sqrt n < Nat.sqrt (4 * n).
Proof.
  intros.
  assert (Nat.sqrt 4 * Nat.sqrt n <= Nat.sqrt(4 * n)).
  apply Nat.sqrt_mul_below.
  assert (Nat.sqrt n < Nat.sqrt 4 * Nat.sqrt n).
  apply mul2_gt.
  apply sqrt_pos; trivial.
  omega.
Qed.

Lemma sqrt_lt : forall m n, n > 0 -> m > 4 * n -> Nat.sqrt m > Nat.sqrt n.
Proof.
  intros.
  assert (Nat.sqrt n < Nat.sqrt (4 * n)).
  apply sqrt_lt'; apply H.
  assert (Nat.sqrt m >= Nat.sqrt (4 * n)).
  apply Nat.sqrt_le_mono.
  omega.
  omega.
Qed.

Lemma sqrt_fold_below : forall m n, n * Nat.sqrt m <= Nat.sqrt (n * n * m).
Proof.
  intros.
  assert (Nat.sqrt (n * n) = n).
  apply Nat.sqrt_square.
  rewrite <- H at 1.
  apply Nat.sqrt_mul_below.
Qed.
  
Lemma sqrt_fold_above : forall m n, S n * S (Nat.sqrt m) >= S (Nat.sqrt (n * n * m)).
Proof.
  intros.
  assert (Nat.sqrt (n * n) = n).
  apply Nat.sqrt_square.
  rewrite <- H at 1.
  apply Nat.sqrt_mul_above.
Qed.

Lemma sqrt_sqrt_lt : forall m n, n > 0 -> m > 25 * n -> Nat.sqrt (Nat.sqrt m) > Nat.sqrt (Nat.sqrt n).
Proof.
  intros.
  apply sqrt_lt.
  apply sqrt_pos; trivial.
  assert (Nat.sqrt m >= Nat.sqrt (25 * n)).
  apply Nat.sqrt_le_mono; omega.
  assert (Nat.sqrt (25 * n) >= 5 * Nat.sqrt n).
  apply sqrt_fold_below.
  assert (5 * Nat.sqrt n > 4 * Nat.sqrt n).
  apply mult_lt_compat_r.
  auto.
  apply sqrt_pos.
  trivial.
  omega.
Qed.

Lemma mul_nondec : forall n p, p > 0 -> p * n >= n.
Proof.
  intros.
  induction p.
  inversion H.
  assert (S p * n = n + n * p).
  simpl.
  ring.
  rewrite H0.
  case (n * p).
  omega.
  intros.
  omega.
Qed.


Theorem exists_increasing_seq :
  exists (f : nat -> four_expr),
    comp (f 0) = 2
    /\ forall n, comp (f n) < comp (f (S n)).
Proof.
  exists sqrt_ft.
  split.
  trivial.
  intros.
  simpl.
  case n.
  unfold Nat.sqrt; simpl; omega.
  intros.
  apply sqrt_lt.
  apply fact_tower_pos.
  assert (comp (fact_tower (S n0)) >= 24).
  induction n0.
  simpl; omega.
  simpl in *.
  assert (24 = fact 4).
  simpl; trivial.
  rewrite H.
  apply fact_nondec.
  omega.
  induction H.
  assert (fact 24 = 24 * (23 * fact 22)).
  unfold fact.
  trivial.
  rewrite H.
  assert (24 * (23 * fact 22) = 24 * 23 * fact 22).
  omega.
  rewrite H0.
  assert (24 * 23 * 22 > 4 * 24).
  omega.
  assert (fact 22 > 0).
  apply fact_pos.
  omega.
  simpl (fact (S m)).
  assert (4 * S m = 4 + 4 * m).
  omega.
  rewrite H0.
  assert (m * fact m > 25).
  assert (fact m > 25).
  omega.
  assert (m * fact m >= fact m).
  apply mul_nondec.
  omega.
  omega.
  omega.
Qed.

Fixpoint sqrt_repeated' (l : nat) (n : four_expr) (c : nat) : four_expr :=
  match c with
  | 0 => n
  | S c' => match comp n - l * l with
           | 0 => n
           | S k => sqrt_repeated' l (SqrtC n) c'
           end
  end.


Definition sqrt_repeated (l : nat) (n : four_expr) : four_expr :=
  sqrt_repeated' l n (comp n).

Fixpoint sqrt_repeated_elem (seq : nat -> four_expr) (n : nat) :=
  match n with
  | 0 => seq 0
  | S n' => sqrt_repeated (comp (sqrt_repeated_elem seq n')) (seq n)
  end.


Lemma sqrt_repeated_increasing' :
  forall x y z, x < comp y -> x < comp (sqrt_repeated' x y z).
Proof.
  intros.
  dependent induction z generalizing y.
  simpl.
  apply H.
  simpl.
  remember (comp y - x * x) as d.
  destruct d.
  apply H.
  apply IHz.
  simpl.
  assert (x * x < comp y).
  omega.
  assert (comp y <= Nat.sqrt_up (comp y) * Nat.sqrt_up (comp y)).
  apply Nat.sqrt_sqrt_up_spec.
  omega.
  assert (x * x < Nat.sqrt_up (comp y) * Nat.sqrt_up (comp y)).
  omega.
  apply Nat.square_lt_mono.
  apply H2.
Qed.

Lemma sqrt_repeated_increasing :
  forall x y, x < comp y -> x < comp (sqrt_repeated x y).
Proof.
  intros.
  unfold sqrt_repeated.
  apply sqrt_repeated_increasing'.
  apply H.
Qed.

Lemma sqrt_repeated_dec' :
  forall l n z, comp (sqrt_repeated' l n z) <= comp n.
Proof.
  intros.
  dependent induction z generalizing n.
  auto.
  simpl.
  destruct (comp n - l * l).
  auto.
  specialize IHz with (n := (SqrtC n)).
  assert (comp (SqrtC n) <= comp n).
  simpl.
  apply Nat.sqrt_up_le_lin.
  omega.
  omega.
Qed.


Lemma sqrt_repeated_dec :
  forall l n, comp (sqrt_repeated l n) <= comp n.
Proof.
  intros.
  apply sqrt_repeated_dec'.
Qed.


Lemma sqrt_repeated_elem_dec :
  forall seq n, comp (sqrt_repeated_elem seq n) <= comp (seq n).
Proof.
  intros.
  induction n.
  auto.
  simpl.
  apply sqrt_repeated_dec.
Qed.

Lemma sqrt_repeated_elem_inc :
  forall seq n, comp (seq 0) = 2 -> (forall p, comp (seq p) < comp (seq (S p))) -> comp (sqrt_repeated_elem seq n) > 1.
Proof.
  intros.
  induction n.
  simpl.
  omega.
  assert (comp (sqrt_repeated_elem seq (S n)) > comp (sqrt_repeated_elem seq n)).
  simpl.
  apply sqrt_repeated_increasing.
  assert (comp (sqrt_repeated_elem seq n) <= comp (seq n)).
  apply sqrt_repeated_elem_dec.
  specialize H0 with (p := n).
  omega.
  omega.
Qed.


Lemma sqrt_repeated_bound' :
  forall l n z , l > 1 -> z >= comp n \/ comp n <= 2 -> l * l >= comp (sqrt_repeated' l n z).
Proof.
  intros.
  dependent induction z generalizing n.
  simpl.
  destruct H0.
  inversion H0.
  rewrite H2.
  apply Nat.le_0_l.
  assert (l * l >= l).
  apply mul_nondec.
  omega.
  omega.
  simpl.
  remember (comp n - l * l) as d.
  destruct d.
  omega.
  apply IHz.
  assumption.
  simpl.
  destruct H0.
  remember (comp n - 2) as c.
  destruct c.
  assert (comp n <= 2).
  omega.
  right.
  assert (Nat.sqrt_up (comp n) <= (comp n)).
  apply Nat.sqrt_up_le_lin.
  omega.
  omega.
  assert (comp n > 2).
  omega.
  left.
  assert (Nat.sqrt_up (comp n) < comp n).
  apply Nat.sqrt_up_lt_lin.
  trivial.
  omega.
  right.
  assert (Nat.sqrt_up (comp n) <= comp n).
  apply Nat.sqrt_up_le_lin.
  omega.
  omega.
Qed.

Lemma sqrt_repeated_bound :
  forall l n, l > 1 -> l * l >= comp (sqrt_repeated l n).
Proof.
  intros.
  apply sqrt_repeated_bound'.
  assumption.
  left.
  omega.
Qed.


Theorem exists_square_bound_seq' :
  (exists (f : nat -> four_expr),
    comp (f 0) = 2
    /\ forall n, comp (f n) < comp (f (S n)))
   -> (exists (f : nat -> four_expr),
    comp (f 0) = 2
    /\ forall n, comp (f n) < comp (f (S n)) /\ comp (f n) * comp (f n) >= comp (f (S n))).
Proof.
  intros.
  inversion H.
  rename x into seq.
  exists (sqrt_repeated_elem seq).
  split.
  simpl.
  apply H0.
  intros.
  split.
  simpl.
  apply sqrt_repeated_increasing.
  destruct H0.
  specialize H1 with (n := n).
  assert (comp (sqrt_repeated_elem seq n) <= comp (seq n)).
  dependent induction n.
  simpl.
  trivial.
  apply sqrt_repeated_elem_dec.
  omega.
  simpl.
  remember (comp (sqrt_repeated_elem seq n)) as x.
  destruct n.

  apply sqrt_repeated_bound.
  simpl in Heqx.
  omega.
  apply sqrt_repeated_bound.
  induction n.
  simpl in Heqx.
  destruct H0.
  rewrite H0 in Heqx.
  assert (2 < comp (sqrt_repeated 2 (seq 1))).
  apply sqrt_repeated_increasing.
  specialize H1 with (n := 0).
  omega.
  omega.
  rewrite Heqx.
  apply sqrt_repeated_elem_inc.
  apply H0.
  apply H0.
Qed.

Theorem exists_square_bound_seq :
(exists (f : nat -> four_expr),
    comp (f 0) = 2
    /\ forall n, comp (f n) < comp (f (S n)) /\ comp (f n) * comp (f n) >= comp (f (S n))).
Proof.
  apply exists_square_bound_seq'.
  apply exists_increasing_seq.
Qed.

Definition logloglog_seq (seq : nat -> four_expr) (n : nat) :=
  LogF (LogF (LogF (seq n))).

Ltac cases N :=
  match type of N with
  | ?n <= S ?k => remember (n - k) as n';
                destruct n';
                try assert (n = S k) as N' by omega;
                try assert (n <= k) as N' by omega;
                clear N;
                rename N' into N
  end.

Lemma loglog_ok_5 :
  forall n, n <= 5 -> n > 3 -> Nat.log2 (Nat.log2 (n * n)) <= 2 * Nat.log2 (Nat.log2 n).
Proof.
  intros.
  do 2 try cases H; match goal with
                | [ H : n = ?k |- _ ] => rewrite H; simpl; trivial
                | _ => idtac
                end.
Qed.

Lemma loglog_ok_10 :
  forall n, n <= 10 -> n > 3 -> Nat.log2 (Nat.log2 (n * n)) <= 2 * Nat.log2 (Nat.log2 n).
Proof.
  intros.
  do 5 try cases H; match goal with
                | [ H : n = ?k |- _ ] => rewrite H; simpl; trivial
                | _ => idtac
                end.
  apply loglog_ok_5; trivial.
Qed.

Lemma loglog_ok_15 :
  forall n, n <= 15 -> n > 3 -> Nat.log2 (Nat.log2 (n * n)) <= 2 * Nat.log2 (Nat.log2 n).
Proof.
  intros.
  do 5 try cases H; match goal with
                | [ H : n = ?k |- _ ] => rewrite H; simpl; trivial
                | _ => idtac
                end.
  apply loglog_ok_10;
  trivial.
Qed.

Lemma loglog_ok :
  forall n, n > 3 -> Nat.log2 (Nat.log2 (n * n)) <= 2 * (Nat.log2 (Nat.log2 n)).
Proof.
  intros.
  rename H into Hgt3.
  assert (Nat.log2 (n * n) <= Nat.log2 n + Nat.log2 n + 1).
  apply Nat.log2_mul_above; omega.
  remember (n-1) as nm1.
  destruct nm1.
  assert (n = 1 \/ n = 0).
  omega.
  destruct H0.
  rewrite H0.
  auto.
  rewrite H0.
  auto.
  assert (n > 1).
  omega.
  assert (Nat.log2 n >= Nat.log2 2).
  apply Nat.log2_le_mono.
  omega.
  assert (Nat.log2 2 = 1). auto.
  assert (Nat.log2 n + Nat.log2 n + 1 <= 3 * Nat.log2 n).
  omega.
  assert (Nat.log2 (3 * Nat.log2 n) <= Nat.log2 3 + Nat.log2 (Nat.log2 n) + 1).
  apply Nat.log2_mul_above; omega.
  assert (Nat.log2 3 = 1); auto.
  rewrite H5 in H4.
  apply Nat.log2_le_mono in H.
  apply Nat.log2_le_mono in H3.
  assert (1 + Nat.log2 (Nat.log2 n) + 1 = Nat.log2 (Nat.log2 n) + 2).
  omega.
  rewrite H6 in H4.
  remember (n - 15) as nm15.
  destruct nm15.
  2: {
    assert (16 <= n).
    omega.
    assert (2 <= Nat.log2 (Nat.log2 n)).
    apply Nat.log2_le_pow2.
    omega.
    simpl.
    apply Nat.log2_le_pow2.
    omega.
    simpl.
    trivial.
    assert (Nat.log2 (Nat.log2 n) + 2 <= 2 * Nat.log2 (Nat.log2 n)).
    omega.
    omega.
  }
  assert (n <= 15) by omega.
  apply loglog_ok_15; trivial.
Qed.  


Theorem exists_cover_seq' : 
(exists (f : nat -> four_expr),
    comp (f 0) = 2
    /\ (forall n, comp (f n) < comp (f (S n)) /\ comp (f n) * comp (f n) >= comp (f (S n))))
-> (exists (f : nat -> four_expr),
      comp (f 0) = 0
      /\ (forall n, (comp (f n) <= comp (f (S n)) /\ comp (f (S n)) <= S (comp (f n))))
      /\ forall n, exists m, comp (f m) > n).

Proof.
  intros.
  inversion H.
  rename x into seq.
  exists (logloglog_seq seq).
  split.
  simpl.
  destruct H0.
  rewrite H0.
  auto.
  split.
  split.
  simpl.
  do 3 apply Nat.log2_le_mono.
  destruct H0.
  specialize (H1 n).
  omega.
  simpl.
  destruct H0.
  specialize (H1 n).
  remember (comp (seq n)) as cn.
  remember (comp (seq (S n))) as csn.
  remember (cn - 3) as cnm3.
  destruct H1.
  destruct cnm3.
  assert (cn <= 3).
  omega.
  do 4 try cases H3;
  match type of H3 with
  | cn <= 0 => assert (cn = 0) as H3'; try omega; clear H3; rename H3' into H3
  | _ => idtac
  end;
  match type of H3 with
  | cn = ?k =>
      rewrite H3 in *;
      assert (csn <= k * k);
      try omega;
      assert (Nat.log2 (Nat.log2 (Nat.log2 csn)) <= Nat.log2 (Nat.log2 (Nat.log2 (k * k))));
      try do 3 apply Nat.log2_le_mono; auto
  | _ => idtac
  end.
  assert (cn > 3).
  omega.
  rewrite <- Nat.log2_double.
  apply Nat.log2_le_mono.
  assert (Nat.log2 csn <= Nat.log2 (cn * cn)).
  apply Nat.log2_le_mono.
  omega.
  apply Nat.log2_le_mono in H4.
  assert (Nat.log2 (Nat.log2 (cn * cn)) <= 2 * Nat.log2 (Nat.log2 cn)).
  apply loglog_ok.
  trivial.
  omega.
  do 2 apply Nat.log2_le_mono in H3.
  auto.
  intros.
  simpl.
  destruct H0.
  assert (forall n, comp (seq n) >= n).
  intros.
  induction n0.
  omega.
  assert (comp (seq (S n0)) > comp (seq n0)).
  apply H1.
  omega.
  exists (2 ^ 2 ^ 2 ^ (n + 1)).
  assert (comp (seq (2 ^ 2 ^ 2 ^ (n + 1))) >= 2 ^ 2 ^ 2 ^ (n + 1)).
  trivial.
  do 3 apply Nat.log2_le_mono in H3.
  assert (Nat.log2 (2 ^ 2 ^ 2 ^ (n + 1)) = 2 ^ 2 ^ (n + 1)).
  apply Nat.log2_pow2.
  omega.
  assert (Nat.log2 (2 ^ 2 ^ (n + 1)) = 2 ^ (n + 1)).
  apply Nat.log2_pow2.
  omega.
  assert (Nat.log2 (2 ^ (n + 1)) = n + 1).
  apply Nat.log2_pow2.
  omega.
  assert (Nat.log2 (Nat.log2 (Nat.log2 (2 ^ 2 ^ 2 ^ (n + 1)))) = (n + 1)).
  rewrite H4.
  rewrite H5.
  rewrite H6.
  trivial.
  omega.
Qed.

Theorem exists_cover_seq :
  exists (f : nat -> four_expr),
      comp (f 0) = 0
      /\ (forall n, (comp (f n) <= comp (f (S n)) /\ comp (f (S n)) <= S (comp (f n))))
      /\ forall n, exists m, comp (f m) > n.
Proof.
  apply exists_cover_seq'.
  apply exists_square_bound_seq.
Qed.

Lemma seq_no_jump :
  (forall seq,
      (comp (seq 0) = 0
      /\ forall n, (comp (seq n) <= comp (seq (S n)) /\ comp (seq (S n)) <= S (comp (seq n)))
      /\ forall n, exists m, comp (seq m) > n)
  -> forall n, forall m, m < comp (seq n) -> exists p, comp (seq p) = m).
Proof.
  intros until 1.
  inversion H.
  clear H.
  induction n; intros.
  rewrite H0 in H.
  inversion H.
  specialize (H1 n).
  destruct H1.
  destruct H1.
  remember (comp (seq (S n)) - comp (seq n)) as dseq. 
  destruct dseq.
  assert (comp (seq (S n)) = comp (seq n)).
  omega.
  rewrite <- H4 in IHn.
  auto.
  assert (comp (seq (S n)) = S (comp (seq n))).
  omega.
  assert (m <= comp (seq n)).
  omega.
  apply le_lt_or_eq in H5.
  destruct H5.
  auto.
  exists n.
  auto.
Qed.


Lemma seq_cover :
  (forall seq,
      comp (seq 0) = 0
      -> (forall n, comp (seq n) <= comp (seq (S n)) /\ comp (seq (S n)) <= S (comp (seq n)))
      -> (forall n, exists m, comp (seq m) > n)
      -> (forall n, exists p, comp (seq p) = n)).
Proof.
  intros.
  assert ((forall n, forall m, m < comp (seq n) -> exists p, comp (seq p) = m)).
  apply seq_no_jump.
  auto.
  intros.
  specialize (H1 n).
  destruct H1.
  specialize (H2 x n).
  auto.
Qed.

Theorem four_seq_express_all_n :
  forall a, exists f, comp f = a.
Proof.
  intros.
  pose proof seq_cover.
  pose proof exists_cover_seq.
  destruct H0.
  rename x into seq.
  specialize (H seq).
  destruct H0.
  destruct H1.
  assert (forall n0 : nat, exists p : nat, comp (seq p) = n0).
  apply H.
  apply H0.
  apply H1.
  apply H2.
  clear H.
  specialize (H3 a).
  destruct H3.
  exists (seq x).
  auto.
Qed.
