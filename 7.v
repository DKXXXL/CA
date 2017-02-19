Theorem le_0_n:
        forall n:nat, 0 <= n.
Proof.
        intros. elim n.
        auto.
        intros. auto.
Qed.

Theorem le_n_0_eq:
        forall n:nat, n <= 0 -> n =0.
Proof.
        intros n h.
        inversion h.
        trivial.
Qed.

Theorem le_plus_minus' :
        forall n m : nat, m <= n -> n = m + (n - m).
Proof.
        intro n. elim n.
        intros m h. inversion h. trivial.        induction m.
        intros; trivial.
        intros. simpl. 
        assert (forall n m : nat, n = m -> S n = S m).
        intros; auto.
        apply H1. apply H. apply le_S_n.
        trivial.
Qed.

Theorem le_plus_minus2' :
        forall n m:nat, m <= n -> n = m + (n - m).
Proof.
        intro n. elim n.
        intros m h; inversion h; simpl; trivial.
        intro. intro. intro. case m. intros; simpl; trivial. intro. intro. simpl. assert (h: forall m n:nat,  m = n -> S m = S n). intros; simpl; rewrite <- H1; simpl ; trivial.
        apply h; apply H; apply le_S_n; trivial.
Qed.

Section primes.
        Definition divides (n m : nat) := exists p:nat, p*n = m.
        Theorem divides_0 :
                forall n: nat, divides n 0.
        Proof.
                intro.
                unfold divides.
                exists 0;trivial.
        Qed.

        Theorem divides_plus:
                forall n m : nat, divides n m -> divides n (n + m).
        Proof.
                unfold divides.
                intros.
                inversion H.
                exists (S x). simpl. rewrite <- H0. trivial.
        Qed.

Require Import Arith.

        Theorem not_divides_plus:
                forall n m:nat, 0 < m -> m < n -> ~divides n m.
        Proof.
                unfold divides.
                unfold not.
                intros n m h1 h2 h3. inversion h3.
                destruct x. simpl in H; rewrite <- H in h1; inversion h1. assert ( S x >= S O). change ( 1 + x  >= 0 + 1).  SearchPattern (_ + _ = _ + _). rewrite <- plus_comm. SearchPattern(_ <= _ -> _ <= _). apply plus_le_compat_r. apply le_0_n.  assert (S x * n >= 1 * n). apply mult_le_compat_r. apply H0. rewrite -> H in H1. simpl in H1. unfold lt in h2. assert ( S m >= S (n + 0)). change (1 + m >= 1 + n + 0). SearchPattern (_ <= _ -> _ <= _). rewrite <- plus_assoc. apply plus_le_compat_l. apply H1. assert ( S(n + 0) <= n). eapply le_trans. apply H2. apply h2. rewrite <- plus_comm in H3. simpl in H3. assert (forall n, ~(S n <= n)). intro n0; elim n0. intro h7; inversion h7. unfold not; intros. apply H4. apply le_S_n. apply H5. unfold not in H4. eapply H4; apply H3. 
         Qed.

        Theorem not_divides_lt:
                forall n m : nat, 0 < m -> m < n -> ~divides n m.
        Proof.
                unfold not.
                intros n m h1 h2 h3.
                unfold divides in h3.
                inversion h3.
                destruct x. simpl in H; rewrite <- H in h1; inversion h1.
                assert (forall x, S x >= S O).
                intros; change (1 + x0 >= 1 + 0). SearchPattern (_ <= _ -> _ <= _). apply plus_le_compat_l; apply le_0_n. assert (S x * n >= 1 * n). apply mult_le_compat_r; apply H0. rewrite -> H in H1; simpl in H1; rewrite plus_comm in H1; simpl in H1. SearchPattern (_ <= _ -> ~ _ < _). assert (~m < n). apply le_not_lt. apply H1. contradiction.
                Qed.
        Lemma le_1_Sn:
                forall x, S x >= S O.
        Proof.
                intro x; elim x. apply le_n. intros n h1; apply le_S; trivial.
        Qed.

        Theorem not_lt_2_divides :
                forall n m : nat, n <> 1 -> n < 2 -> 0 < m -> ~divides n m.
        Proof.
                unfold not; unfold divides; intros n m h1 h2 h3 h4.
                inversion h4. inversion h2. contradiction. inversion H1. rewrite -> H3 in H; rewrite -> mult_comm in H; simpl in H. rewrite <- H in h3; inversion h3. inversion H3.
        Qed.

        Definition le_plus_minus :
               forall n m:nat, le m n -> n = m +(n-m) := le_plus_minus'.

        Theorem lt_lt_or_eq:
                forall n m : nat, n < S m -> n < m \/ n = m.
        Proof.
                intros n m h1.
                unfold lt in h1. assert (n <= m). apply le_S_n. apply h1. inversion H. right;trivial. left; unfold lt. change (1 + n <= 1 + m0). apply plus_le_compat_l. apply H0.
        Qed.


Require Import ZArith.
        Ltac tactic7p2 :=
                match goal with
                | [ |- context [( (xI ?X1))] ] => rewrite (Zpos_xI X1); tactic7p2
                | [ |- context [( (xO ?X2))]] => match X2 with
                | xH => fail 1
                | _ => rewrite (Zpos_xO X2); tactic7p2 
                end
                | [ |- _] => idtac
                end.

        Theorem testtactic7p2:
                forall x,Zpos(xI( xO (xO x))) =Zpos (xI( xO (xO x))).
        Proof.
                intros x.
                tactic7p2.
                Check Zpos_xI.
        Abort.







                
                


                             
               
                


        
       
       
        

