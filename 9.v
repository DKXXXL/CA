Definition extract (A:Set) (P:A->Prop) :=
        fun (x: sig P) =>
        match x with
        | exist b h => b
        end.

Print extract.

Goal forall (A:Set) (P:A -> Prop) (y:{x:A | P x}),
                P (extract A (fun x:A => P x) y).
intros. elim y. intros. simpl. trivial.
Qed.

Definition sig_rec_simple:
        forall (A:Set) (P:A->Prop)(B:Set),
                (forall x:A, P x -> B) -> sig P -> B.
Proof.
        intros. elim H0. trivial.
Defined.


Print sig_rec_simple.

Require Import Omega.

Definition eq_dec (A:Type) := forall x y:A, {x = y} + {x <> y}.

Theorem nat_decidable:
        eq_dec nat.
Proof.
        unfold eq_dec.
        intro. elim x. intros. elim y. left;trivial. intros. inversion H. right. omega. right. omega.
        intros. destruct y. right; try omega. cut ({n=y} + {n<>y}). intro. inversion H0. left; try omega. right; try omega. trivial.
Qed.


Fixpoint occurenceof (l :list nat) (a : nat) : nat :=
        match l with
        | nil => O
        |cons  x  l' => match nat_decidable x a with
                        | left _ => S (occurenceof l' a)
                        | right _  => occurenceof l' a
        end
        end.

Definition pred' :
        forall n:nat, {p:nat | n = S p} + {n=0}.
intros. elim n. right;trivial. intros. inversion H. inversion H0. left; exists (S x). omega. left. exists 0. omega.
Defined.

Definition pred_partial :
        forall n:nat, n <> 0 -> nat.
intros.  destruct n. elim H. trivial. apply n.
Defined.

Theorem le_2_n_not_zero :
        forall n:nat, 2 <= n -> n <> 0.
Proof.
        intros; omega.
Qed.

Theorem le_2_n_pred:
        forall (n:nat) (h: 2<=n), pred_partial n (le_2_n_not_zero n h ) <> 0.
intros.
Abort.
Theorem le_2_n_pred' :
        forall n:nat, 2 <= n -> forall h:n <> 0, pred_partial n h <> 0.
intros n H. elim H. intros; simpl; omega.
intros. simpl. elim H0. omega. intros. unfold not; intro HH; inversion HH.
Qed.

Theorem le_2_n_pred :
        forall (n:nat)(h:2<=n), pred_partial n (le_2_n_not_zero n h) <> 0.
intros. apply le_2_n_pred'; auto.
Qed.

Definition pred_partial_2 (n:nat) (h:2<=n) : nat :=
        pred_partial (pred_partial n (le_2_n_not_zero n h)) (le_2_n_pred n h).

Definition pred_strong:
        forall n:nat, n <> 0 -> {v:nat | n  = S v}.
intro. case n. intro H; elim H; trivial.
intros; exists n0; trivial.
Defined.

Theorem pred_strong2_th1 :
        forall n p :nat, 2 <= n -> n = S p -> p <> 0.
intros; omega.
Qed.

Theorem pred_th1:
        forall n p q:nat, n = S p -> p = S q -> n = S (S q).
intros ; omega.
Qed.

Definition pred_strong2 (n:nat) (h:2 <= n): {v:nat | n = S ( S v)}.
intros. destruct n. omega. destruct n. omega. exists n; trivial.
Qed.

Print pred_strong2.

Definition pred_strong2_2: forall n:nat, 2 <= n -> {v:nat| n = S (S v)}.
intros n h; case (pred_strong n).
apply le_2_n_not_zero; assumption.
intros p h'; case (pred_strong p).
apply (pred_strong2_th1 n); assumption.
intros p' h''; exists p'.
eapply pred_th1; eauto.
Qed.

Print pred_strong2_2.

Section minimal_specification_strengthening.
        Variable prime : nat -> Prop.
        Definition divides (n p : nat) : Prop := exists q : _, q * p = n.
        Definition prime_divisor (n p :nat) := prime p /\ divides p n.
        Variable prime_test : nat -> bool.
        Hypothesis 
                (prime_test_t : forall n:nat, prime_test n = true -> prime n)
                (prime_test_f : forall n:nat, prime_test n = false -> ~prime n).
        Variable get_primediv_weak : forall n:nat, ~prime n -> nat.
        Hypothesis get_primediv_weak_ok :
                forall (n:nat) (H: ~prime n), 1 < n -> prime_divisor n (get_primediv_weak n H).

        Theorem divides_refl : forall n:nat, divides n n.
        intros; exists 1. simpl. rewrite <- plus_comm. simpl;trivial.
        Qed.
Hint Resolve divides_refl.

Definition stronger_prime_test :
        forall n:nat, {(prime_test n) = true} + {(prime_test n) = false}.
intro n; case (prime_test n); [left | right] ;trivial.
Defined.

Definition get_prime (n:nat) : nat :=
        match stronger_prime_test n with
        | left H => n
        | right H => get_primediv_weak n (prime_test_f n H)
        end.

Theorem get_primediv_ok :
        forall n:nat, 1 < n -> prime_divisor n (get_prime n).
Proof.
        intros n H; unfold get_prime.
        destruct (stronger_prime_test n); auto.
        split; auto.
Qed.

End minimal_specification_strengthening.

Definition pred_partial' : forall n:nat, n<>0 -> nat.
refine (fun n =>
        match n as x return x <> 0 ->  nat with
        | O => fun h: O <> O => _
        | S k => fun h: S k <> O => k
        end).
        omega.
Defined.

Print pred_partial'.

Definition pred_partial_2' :
        forall n:nat, le 2 n -> nat.
refine (fun n h => pred_partial (pred_partial n _) _).
apply (le_2_n_pred n h).
Defined.

Definition pred_partial_22':
        forall n:nat, le 2 n -> nat.
refine (fun n h =>
        (fun h': n <> 0 => pred_partial (pred_partial n h') _) _).
Abort.

Definition pred_strong2'' :
        forall n:nat, 2 <= n -> {v:nat | n = S(S v)}.
refine (fun n h => 
        match pred_strong n _ with
        | exist p h' =>
             match pred_strong p _ with
             | exist p' h'' => exist _ p' _
             end
        end); omega.
Defined.

Fixpoint div2 (n:nat) : nat :=
        match n with 
        | O => O
        | 1 => O
        | S (S p) => S (div2 p)
        end.

Theorem div2_le : forall n:nat, div2 n <= n.
intros. cut (div2 n <= n /\ div2 (S n) <= S n); try tauto.
elim n. split; simpl; omega. intros. split. elim H; trivial. simpl. omega.
Qed.

Fixpoint div3 (n:nat) : nat :=
        match n with
        | O => O
        | 1 => O
        | 2 => O
        | S(S(S x)) => S(div3 x)
        end.

Theorem div3_le : forall n:nat, div3 n <= n.
intros. cut (div3 n <= n /\ div3 (S n) <= S n /\ div3 (S (S n)) <= S( S n)); try tauto.
elim n. simpl; omega. intros. elim H. intros. elim H1. intros. repeat split; try tauto. simpl; omega.
Qed.

Fixpoint mod2 (n:nat) : nat :=
        match n with
        | O => O
        | 1 => 1
        | S (S x) => mod2 x
        end.

Theorem p9p7: forall n:nat, n = 2*(div2 n) + (mod2 n).
intros. cut (n = 2 *(div2 n) + mod2 n /\ S n =2*( div2 (S n)) + mod2 (S n)); try tauto. elim n. simpl; omega. intros. elim H. intros. split; try tauto. simpl; omega.
Qed.

Fixpoint fib(n:nat) {struct n} : nat :=
        match n with
        | O => 1
        | S x => match x with
                 | O => 1
                 | S y => fib x + fib y
        end
        end.

Theorem nat_2_ind :
        forall (P: nat -> Prop), P 0 -> P 1 -> (forall n: nat, P n -> P (S (S n))) -> (forall n:nat, P n).
intros. cut (P n /\ P (S n)); try tauto.
elim n; intuition.
Qed.

Fixpoint div2'_aux (n:nat) : nat*nat :=
        match n with
        | O => (0, 0)
        | S p => let (v1, v2) := div2'_aux p in (v2, S v1) end.

Definition div2'(n:nat) := fst (div2'_aux n).

Definition div2_mod2 :
        forall n:nat, {q:nat & {r:nat |n = (2*q) + r /\ r <= 1}}.
refine (fun n => existS _ (div2 n) (exist _ (mod2 n) _)). split. apply p9p7. cut (mod2 n <= 1 /\ mod2 (S n) <= 1); try tauto.
elim n. simpl; omega.
intros. elim H; intros; split; try omega. simpl; trivial.
Defined.

Fixpoint plus'' (n m:nat) {struct m} :nat :=
        match m with O => n | S p => plus'' (S n) p end.

Lemma plus''_Sout:
        forall n m :nat, plus'' (S n) m = S (plus'' n m).
intros n m; generalize n. elim m. intros. simpl; trivial.
intros. simpl. rewrite -> H. trivial.
Qed.



Theorem plus''_comm :
        forall n m:nat, plus'' n m = plus'' m n.
intros n m; generalize n. elim m. intros. elim n0. trivial. intros. rewrite -> plus''_Sout. rewrite -> H. simpl. rewrite -> plus''_Sout. trivial.
intros. simpl. rewrite -> plus''_Sout. rewrite -> H. rewrite -> plus''_Sout. trivial.
Qed.

Theorem plus''_assoc:
        forall n m l:nat, plus'' (plus'' n m) l = plus'' n (plus'' m l).
intros n m l. generalize n m. elim l. intros. simpl. trivial. intros. simpl. rewrite -> plus''_Sout. rewrite ->plus''_Sout. simpl. rewrite -> plus''_Sout. auto.
Qed.

Fixpoint fib''' (times n m:nat):=
        match times with
        | O => m
        | S x => fib''' x m (n+m)
        end.

Definition fib' (x:nat) := fib''' x 0 1.

 
Inductive is_fib : nat -> Prop :=
| fib1 : is_fib 1
| fibS : forall x y:nat, is_fib x -> is_fib y -> is_fib (x+y).

Theorem fib'''_transform:
        forall x n0 m0 n1 m1 :nat, fib''' (S (S x)) n0 m0 + fib''' (S (S x)) n1 m1 = fib''' (S (S x)) (n0+n1) (m0+m1).
intro; elim x. intros; simpl; omega.
intros. change (fib''' (S (S n)) m0 (n0 + m0) + fib''' (S (S n)) m1 (n1 + m1) = fib''' (S (S n)) (m0 + m1) ((n0 + n1) + (m0 + m1))). assert (n0 + n1 + (m0 + m1) = ((n0 + m0) + (n1 + m1))). omega. rewrite -> H0. apply H.
Qed.

Theorem fib_fib'' :
        forall n:nat, fib n = fib' n.
intros n. cut (fib n = fib' n /\ fib (S n) = fib' (S n)); try tauto.
elim n. try tauto; omega.
intros. elim H. intros. split; try auto. change(fib (S n0) + fib n0 = fib' (S (S n0))). unfold fib' in H1. simpl fib''' in H1.  rewrite -> H0. rewrite -> H1. unfold fib'. simpl. destruct n0. simpl; trivial. destruct n0. simpl; trivial. apply fib'''_transform.
Qed.

Open Scope Z_scope.

Fixpoint div_bin (n m : positive) {struct n}: Z*Z :=
  match n with
    | 1%positive => match m with 1%positive => (1, 0) | v => (0, 1) end
    | xO n' => let (q', r') := div_bin n' m in
               match Z_lt_ge_dec (2*r') (Zpos m) with
                 | left Hlt => (2*q', 2*r')
                 | right Hge => (2*q' + 1, 2*r' - (Zpos m))
               end
    | xI n' => let (q', r') := div_bin n' m in
               match Z_lt_ge_dec (2*r' + 1) (Zpos m) with
                 | left Hlt => ((2*q') %Z, 2*r'+1)
                 | right Hge => (2*q'+1, (2*r' + 1) - Zpos m)
               end
  end.

Theorem div_bin_th:
  forall (n m : positive) (q r :Z), Zpos m <> 0 -> div_bin n m = (q, r) -> Zpos n = q * (Zpos m) + r /\ 0 <= r < (Zpos m).
Proof.
Abort.


Theorem rem_1_1_interval : 0 <= 0 < 1.
Proof.
  omega.
Qed.

Theorem rem_1_even_interval :
  forall m:positive, 0 <= 1 < Zpos (xO m).
  intros.
  Locate "_ < _".
  Print Z.lt.
  compute. split;[discriminate | trivial].
Qed.

Theorem rem_1_odd_interval :
  forall m:positive, 0 <= 1 < Zpos (xI m).
  intros.
  compute.
  split;[intro; discriminate | trivial].
Qed.

Theorem rem_even_ge_interval :
  forall (m r:Z), 0<= r <m -> 2*r >= m -> 0 <= 2*r - m < m.
  intros.
  omega.
Qed.


Theorem rem_even_lt_interval :
  forall m r : Z, 0 <= r < m -> 2*r < m -> 0 <= 2*r < m.
  intros.
  omega.
Qed.

Theorem rem_odd_ge_interval :
  forall m r:Z, 0 <= r < m -> 2*r + 1 >= m -> 2*r + 1 - m < m.
  intros.
  omega.
Qed.

Theorem rem_odd_lt_interval:
  forall m r:Z, 0 <= r < m -> 2*r + 1 < m -> 0 <= 2*r + 1 < m.
  intros.
  omega.
Qed.

Hint Resolve rem_odd_ge_interval rem_even_ge_interval rem_odd_lt_interval rem_even_lt_interval rem_1_odd_interval rem_1_even_interval rem_1_1_interval.


Ltac div_bin_tac arg1 arg2 :=
  elim arg1;
  [intros p; lazy beta iota delta [div_bin]; fold div_bin ;
   case (div_bin p arg2); unfold snd; intros q' r' Hrec;
   case (Z_lt_ge_dec (2*r' + 1) (Zpos arg2)); intros H
  | intros p; lazy beta iota delta [div_bin]; fold div_bin;
    case (div_bin p arg2); unfold snd; intros q' r' Hrec;
    case (Z_lt_ge_dec (2*r') (Zpos arg2)); intros H
  | case arg2; lazy beta iota delta [div_bin]; intros].

Theorem div_bin_rem_lt :
  forall n m :positive, 0<= snd(div_bin n m) < Zpos m.
  intros n m; div_bin_tac n m; unfold snd; auto.
  omega.
Qed.


Inductive div_data (n m :positive) : Set :=
  div_data_def :
    forall (q r:Z), Zpos n = q*(Zpos m) + r -> 0 <= r < Zpos m -> div_data n m.


Require Import ZArith.

Lemma posAlwaysGE1:
  forall x:positive, Zpos x >= 1.
  intros x.
  elim x.
intros; rewrite Zpos_xI.
omega.
intros; rewrite Zpos_xO.
omega.
omega.
Qed.
Definition div_bin2: forall n m:positive, div_data n m.
  intros n. elim n.
  intros p h. intro m. elim (h m).  intros.
  case (Z_lt_ge_dec (2*r + 1) (Zpos m)). intros.
  exists (2*q) (2*r + 1). rewrite Zpos_xI. rewrite e. ring.
  auto.
  intros. assert (0<= 2*(r) + 1 - (Z.pos m) < ( Z.pos m)). omega.
  exists (2*q+1) (2*r+1-(Z.pos m)).
  rewrite Zpos_xI. rewrite e. ring. auto.
  intros p h m. elim (h m). intros.
  case (Z_lt_ge_dec (2*r) (Zpos m)). intros. exists (2*q) (2*r).
  rewrite Zpos_xO. rewrite e. ring. auto.
  intros. assert (0 <= 2*r - (Zpos m) < (Zpos m)). omega.
  exists (2*q + 1) (2*r - (Zpos m)). rewrite Zpos_xO. rewrite e. ring. auto.
  intros. case (Z_le_gt_dec (Zpos m) 1). intros. assert (Zpos m = 1). pose (posAlwaysGE1 m). omega.
  exists 1 0. rewrite H. omega. omega.
  intros. exists 0 1. omega. omega.
Qed.

Definition div_bin3 :
  forall n m : positive, div_data n m.
  refine
    ((fix div_bin3 (n: positive) : forall m: positive, div_data n m :=
        fun m =>
          match n return div_data n m with
            | 1%positive =>
              match m return div_data 1 m with
                | 1%positive => div_data_def 1 1 1 0 _ _
                | xO p => div_data_def 1 (xO p) 0 1 _ _
                | xI p => div_data_def 1 (xI p) 0 1 _ _
              end
            | xO p =>
              match div_bin3 p m with
                |(div_data_def q' r' _ _ ) =>
                 match (Z_lt_ge_dec (2*r') (Zpos m)) with
                   | left Hlt => div_data_def (xO p) m (2*q') (2*r') _ _
                   | right Hge => div_data_def (xO p) m (2*q' + 1) (2*r' - (Zpos m)) _ _
                 end
              end
            | xI p =>
              match div_bin3 p m with
                |(div_data_def q' r' _ _) =>
                 match (Z_lt_ge_dec (2*r' + 1) (Zpos m)) with
                   | left Hlt => div_data_def (xI p) m (2*q') (2*r' + 1) _ _
                   | right Hge => div_data_def (xI p) m (2*q' + 1) (2*r' + 1 - (Zpos m)) _ _
                 end
              end
          end));
  (try (((try rewrite Zpos_xI);(try rewrite Zpos_xO)); rewrite e; ring; omega)).
  omega. omega. omega. omega. omega.  rewrite Zpos_xI. pose (posAlwaysGE1 p). omega. omega.
  rewrite Zpos_xO. pose (posAlwaysGE1 p). omega. omega. omega.
Qed.

Inductive sqr_data (n:positive) : Z -> Set :=
  sqr_def : forall (m r:Z), (Zpos n) = m*m + r /\ m*m < Zpos n <(m+1) * (m+1) -> sqr_data n m.

Locate "{ x | P }".
Print existT.

Definition sqr_bin :
  forall p:positive,
    {s:Z & {r:Z | Zpos p = s*s + r /\ s*s <= Zpos p < (s + 1) * (s+1)}}.
  refine (fix sqr_bin (p:positive) : {s:Z & {r:Z | Zpos p = s*s + r /\ s*s <= Zpos p < (s+1)*(s+1)}} :=
            match p with
              | 1%positive => existS _ 1 (exist _ 0 _)
              | 2%positive => existS _ 1 (exist _ 1 _)
              | 3%positive => existS _ 1 (exist _ 2 _)
              | xO (xO p') =>
                match (sqr_bin p') with
                  | existS s (exist r _) =>
                    match (Z_lt_ge_dec (4*r) (4*s + 1)) with
                      | left Hlt => existS  _ (2*s) (exist  _ (4*r) _)
                      | right Hge => existS  _ (2*s + 1) (exist  _ (4*r - (4*s + 1)) _)
                    end
                end
              | xI (xO p') =>
                match (sqr_bin p') with
                  | existS s (exist r _) =>
                    match (Z_lt_ge_dec (4*r + 1) (4*s + 1)) with
                      | left Hlt => existS _ (2*s) (exist  _ (4*r + 1) _)
                      | right Hge => existS _ (2*s + 1) (exist _ (4*r + 1 - (4*s + 1)) _)
                    end
                end
              | xO (xI p') =>
                match (sqr_bin p') with
                  | existS s (exist r _) =>
                    match (Z_lt_ge_dec (4*r + 2) (4*s + 1)) with
                      | left Hlt => existS  _ (2*s) (exist  _ (4*r + 2) _)
                      | right Hge => existS  _ (2*s+ 1) (exist  _ (4*r +2 - (4*s + 1)) _ )
                    end
                end
              | xI (xI p') =>
                match sqr_bin p' with
                  | existS s (exist r _) =>
                    match (Z_lt_ge_dec (4*r + 3) (4*s + 1)) with
                      | left Hlt => existS _ (2*s) (exist _ (4*r + 3) _ )
                      | right Hge => existS _ (2*s + 1) (exist _ (4*r + 3 - (4*s + 1)) _)
                    end
                end
            end).

  split. rewrite Zpos_xI. rewrite Zpos_xI. elim a. intros. rewrite H. ring.
  rewrite Zpos_xI; rewrite Zpos_xI. elim a. intros. rewrite H. rewrite H in H0.
  assert (4*s*s <= 4*s*s + 4*r + 3 < 4*s*s + 4*s + 1). omega.
  assert (2*s*(2*s) = 4*s*s). ring.
  assert (2*(2*(s*s+r) + 1) + 1 = 4*s*s + 4*r + 3). ring.
  assert ((2*s + 1)*(2*s+1) = 4*s*s + 4*s + 1). ring.
  rewrite H2; rewrite H3; rewrite H4. auto.
  repeat (rewrite Zpos_xI). elim a. intros. rewrite H. split; try ring; try omega.
  rewrite H in H0.
  assert ((2*s+1)*(2*s+1) = 4*s*s + 4*s + 1). ring.
  assert ((2*(2*(s*s+r) + 1) + 1 = 4*s*s + 4*r + 3)). ring.
  assert ((2*s + 1 + 1) * (2*s + 1 + 1) = 4*s*s + 8*s + 4). ring.
  rewrite H1; rewrite H2; rewrite H3. 
  assert ((s+1) * (s+1) = s*s + 2*s + 1). ring.
  rewrite H4 in H0. assert (4*r <= 8*s). omega.
  omega.
Abort.

