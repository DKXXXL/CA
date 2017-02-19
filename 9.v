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




