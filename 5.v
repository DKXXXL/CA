Theorem vp31: ~False.
Proof.
        intro a.
        assumption.
Qed.

Theorem vp32:
        forall P:Prop, ~~~P -> ~P.
Proof.
        intros P h1 p.
        apply h1.
        intro h2.
        auto.
Qed.

Theorem vp32_:
        forall P:Prop, ~~~P -> ~P.
Proof.
        unfold not.
        intros P h1 p.
        elim h1.
        intros h2.
        elim h2.
        assumption.
Qed.

Theorem vp33:
        forall P Q : Prop, ~~~P -> P -> Q.
Proof.
        unfold not.
        intros P Q h1 p.
        elim h1.
        intros h2.
        elim h2.
        assumption.
Qed.

Theorem vp34:
        forall P Q:Prop, (P -> Q) -> ~Q -> ~ P.
Proof.
        unfold not.
        intros P Q h1 h2 p.
        elim h2.
        apply h1;assumption.
Qed.
Lemma test1:
        forall P Q:Prop, (P -> P/\Q) -> ~(P /\ Q) -> (P \/ Q) -> ~(P \/ Q) -> Q.
Proof.
        unfold not.
        intros P Q h1 h2 h3 h4.
        elim h1.
Abort.

Theorem vp35:
        forall P Q R:Prop, (P -> Q) -> (P -> ~ Q) -> P -> R.
Proof.
        unfold not.
        intros P Q R h1 h2 p.
        elim h2.
        assumption.
        apply h1; assumption.
Qed.

Axiom dyslexic_imp : forall P Q:Prop, (P -> Q) -> (Q -> P).

Axiom dyslexic_contrap : forall P Q:Prop,(P -> Q) -> (~P -> ~ Q).

Lemma wrongLemma1:
        False.
Proof.
        assert(H1 : forall P: Prop, P -> False).
        assert(H2 : forall P: Prop, False -> P).
        intros P h1;elim h1.
        intro P;apply dyslexic_imp;apply H2.
        apply(H1 (1+1=2) eq_refl).
Qed.

Lemma wongLemma2:
        False.
Proof.
        assert(H2: forall Q:Prop, ~Q).
        intros Q;apply dyslexic_contrap with (Q:= Q)(P:= False).
        intro h1; elim h1.
        intro h1; elim h1.
        apply(H2 (1+1=2) eq_refl).
Qed.

Theorem vp5:
        forall (A:Set) (a b c d:A) ,a = c \/ b = c \/ c = c \/ d = c.
Proof.
        intros A a b c d.
        right;right;left;reflexivity.
Qed.

Theorem vp61:
        forall A B C:Prop, A/\(B/\C) -> (A/\ B)/\C.
Proof.
        intros A B C h1.
        split.
        split.
        elim h1.
        intros;assumption.
        elim h1;intros h2 h3;elim h3;intros;assumption.
        elim h1;intros h2 h3;elim h3;intros;assumption.
Qed.

Theorem vp62:
        forall A B C D : Prop, (A -> B) /\ (C -> D)/\A/\C -> B /\ D.
Proof.
        intros A B C D h1.
        elim h1.
        intros h2 h3.
        elim h3 .
        intros h4 h5.
        elim h5;intros h6 h7.
        split;[apply h2;assumption|apply h4;assumption].
Qed.

Theorem vp63:
        forall A:Prop, ~(A/\~A).
Proof.
        unfold not.
        intros A h1.
        elim h1;intros h3 h4;apply h4;assumption.
Qed.

Theorem vp64 :
        forall A B C:Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
        intros A B C h1.
        elim h1.
        intro h2;left;left;assumption.
        intro h2;elim h2;[intro h3;left;right;assumption | intro h3;right;assumption].
Qed.


Theorem vp65 :
        forall A:Prop, ~~(A\/~A).
Proof.
        unfold not.
        intros A h1.
        apply h1.
        right.
        intros a.
        apply h1.
        left;assumption.
Qed.

Theorem vp66 :
        forall A B :Prop,(A \/B) /\ ~A -> B.
Proof.
        unfold not.
        intros A B h1.
        elim h1.
        intros h2 h3.
        elim h2.
        intro h4;elim h3;assumption.
        intro;assumption.
Qed.


Axiom classic :
        forall P:Prop, ~~P -> P.

Theorem excluded_middle :
        forall P:Prop, P \/ ~P.
Proof.
        intros P.
        unfold not.
        apply (classic _ (vp65 P) ).
Qed.

Theorem de_morgan_not_and_not:
        forall P Q:Prop, ~(~P /\ ~Q) -> P\/ Q.
Proof.
        unfold not.
        intros P Q h1.
        assert (P \/ ~P).
        apply excluded_middle.
        assert (Q \/ ~Q).
        apply excluded_middle.
        elim H.
        intro;left;assumption.
        elim H0.
        intros;right;assumption.
        intros;elim h1;split;assumption.
Qed.

Theorem implies_to_or:
        forall P Q:Prop,
        (P -> Q) -> (~P \/ Q).
Proof.
        intros P Q h1.
        apply de_morgan_not_and_not.
        unfold not.
        intro h2.
        elim h2.
        intros h3 h4.
        assert P.
        assert (hc : P \/ ~P).
        apply de_morgan_not_and_not.
        apply vp63.
        elim hc.
        intro;assumption.
        intro;elim h3;assumption.
        apply h4;apply h1;assumption.
Qed.

Theorem peirce:
        forall P Q:Prop, ((P -> Q) -> P) -> P.
Proof.
        intros P Q h1.
        assert (h2: ~P \/ P).
        apply implies_to_or.
        intro;assumption.
        elim h2.
        unfold not.
        intro h3.
        apply h1.
        intro p;elim h3;assumption.
        intro;assumption.
Qed.

Theorem classic__:
        forall P:Prop, ~~P -> P.
Proof.
        unfold not.
        intros P h1.
        apply peirce with (Q:= ~~P).
        assert (h2: (((~P -> False) -> ~P) -> ~P)).
        apply peirce with (Q:=False) (P := ~P).
        intro h3.
        assert (h4: (((P \/ ~P) -> False) -> (P \/ ~P)) -> P \/~P).
        apply peirce with (P:= (P \/ ~P)) (Q := False).
        assert (h5 : ((P \/ ~P) -> False) -> (P \/ ~P)).
        intro h5.
        assert (h6 : ~~(P \/ ~P)).
        unfold not.
        intro h7.
        apply h7.
        elim h7.
        right.
        intro;apply h7;left;assumption.
        elim h6.
        assumption.
        assert (h8 : P\/~P).
        apply h4;assumption.
        elim h8.
        intro;assumption.
        intro;elim h1;assumption.
Qed.
Theorem ex_imp_ex :
        forall (A:Type) (P Q : A -> Prop), (ex P) -> (forall x : A, P x -> Q x) ->(ex Q).
Proof.
        intros A P Q h1 h2.
        elim h1.
        intros a h3.
        apply (ex_intro) with (x := a).
        apply h2;assumption.
Qed.

Section vp9.
        Variable A:Set.
        Variable (P Q : A -> Prop).
Theorem vp91:
        (exists x:A, P x \/ Q x) -> (ex P) \/ (ex Q).
Proof.
        intros h1.
        elim h1.
        intros a h2.
        elim h2.
        intro h3;left;exists a;assumption.
        intro h3;right;exists a;assumption.
Qed.

Theorem vp92:
        (ex P)\/(ex Q) -> exists x : A, P x \/ Q x.
Proof.
        intro h1.
        elim h1.
        intro h2;elim h2;intros a h3;exists a;left;assumption.
        intro h2;elim h2;intros a h3;exists a;right;assumption.
Qed.

Theorem vp93:
        (exists x:A, (forall R:A -> Prop, R x)) -> 2 = 3.
Proof.
        intros h1.
        elim h1.
        intros a h2.
        assert False.
        apply (h2 (fun (a:A) => False)).
        elim H.
Qed.

Theorem vp94:
        (forall x: A, P x) -> ~(exists y:A, ~ P y).
Proof.
        unfold not.
        intros h1 h2.
        elim h2.
        intros a h3.
        apply h3;apply h1.
Qed.


End vp9.

Require Import Arith.

Theorem plus_permute2:
        forall n m p: nat, n + m + p = n + p + m.
Proof.
        intros n m p.
        rewrite <- plus_assoc.
        pattern (m+p) at 1.
        rewrite -> plus_comm.
        rewrite -> plus_assoc.
        reflexivity.
Qed.

Theorem vp11:
        forall (A:Type)(x y z : A), x = y -> y = z -> x = z.
Proof.
        intros A x y z h1 h2.
        rewrite -> h1; rewrite -> h2;reflexivity.
Qed.

Definition my_True: Prop :=
        forall P : Prop, P -> P.

Definition my_I : my_True :=
        fun (P : Prop) (a : P) => a.

Definition my_False : Prop :=
        forall P : Prop, P.

Definition my_False_ind : 
        forall P : Prop, my_False -> P :=
        fun (P : Prop) (a : my_False) => (a P).


Definition my_not (P:Prop) : Prop := P -> my_False.

Section vp13.
Theorem vp131: my_not(my_False).
Proof.
        unfold my_not.
        intro;assumption.
Qed.

Theorem vp132 :forall P: Prop, my_not(my_not(my_not(P))) -> my_not(P).
Proof.
        unfold my_not.
        intros P h1 p.
        apply h1.
        intro h2.
        apply h2;assumption.
Qed.

Theorem vp133:
        forall P Q:Prop, my_not(my_not(my_not(P))) -> P -> Q.
Proof.
        unfold my_not.
        intros P Q h1 p.
        assert (h0: my_False).
        apply h1.
        intros h2;apply h2;assumption.
        apply (h0 Q).
Qed.

Theorem vp134:
        forall P Q : Prop, (P -> Q) -> my_not (Q) -> my_not (P).
Proof.
        unfold my_not.
        intros P Q h1 h2 p.
        apply h2;apply h1;assumption.
Qed.

Theorem vp135:
        forall P Q R:Prop, (P -> Q) -> (P -> my_not(Q)) -> P -> R.
Proof.
        unfold my_not.
        intros P Q R h1 h2 p.
        assert (h0: my_False).
        apply h2;[assumption|apply h1;assumption].
        apply (h0 R).
Qed.

Section leibniz.
Set Implicit Arguments.
Unset Strict Implicit.
Variable A:Set.

Definition leibniz (a b : A) : Prop :=
        forall P : A -> Prop, P a -> P b.

Require Import Relations.

Theorem leibniz_sym : symmetric A leibniz.
Proof.
        unfold symmetric.
        intros x y h1.
        assert (h0: leibniz x x).
        unfold leibniz;intros;assumption.
        apply (h1 _ h0).
        assumption.
Qed.

Theorem leibniz_refl : reflexive A leibniz.
Proof.
        unfold reflexive.
        unfold leibniz; intros;assumption.
Qed.

Theorem leibniz_trans : transitive A leibniz.
Proof.
        unfold transitive.
        intros x y z h1 h2.
        apply h2;assumption.
Qed.

Theorem leibniz_equiv : equiv A leibniz.
Proof.
        unfold equiv.
        split.
        apply leibniz_refl.
        split;[apply leibniz_trans|apply leibniz_sym].    
Qed.

Theorem leibniz_least_reflexive :
        forall R: relation A, reflexive A R -> inclusion A leibniz R.
Proof.
        unfold inclusion.
        intros R h1 x y h2.
        apply h2.
        apply h1.
Qed.

Theorem leibniz_eq :
        forall a b : A, leibniz a b -> a = b.
Proof.
        intros a b h1.
        apply h1.
        reflexivity.
Qed.

Theorem eq_leibniz_ind :
        forall a b : A, a = b -> leibniz a b.
Proof.
        intros a b h1;rewrite <- h1;apply leibniz_refl.
Qed.

Theorem leibniz_ind :
        forall (x : A) ( P : A -> Prop) , P x -> forall y : A, leibniz x y -> P y.
Proof.
        intros a P h1 y h2.
        apply h2.
        apply h1.
Qed.

Unset Implicit Arguments.
End leibniz.

Definition my_and (P Q:Prop) :=
        forall R:Prop, (P -> Q -> R) -> R.

Definition my_or (P Q:Prop) :=
        forall R:Prop, (P -> R) -> (Q -> R) -> R.

Definition my_ex (A:Set) (P : A -> Prop) :=
        forall R:Prop, (forall a:A, P a -> R) -> R.

Theorem vp151:
        forall P Q:Prop, my_and P Q -> P.
Proof.
        intros P Q h1.
        apply h1.
        intros;assumption.
Qed.

Theorem vp152:
        forall P Q:Prop, my_and P Q -> Q.
Proof.
        intros P Q h1;apply h1;intros;assumption.
Qed.

Theorem vp153:
        forall P Q R:Prop, (P -> Q -> R) -> my_and P Q -> R.

Proof.
        intros P Q R h1 h2.
        apply h1.
        apply h2;intros;assumption.
        apply h2;intros;assumption.
Qed.

Theorem vp154:
        forall P Q:Prop, P -> my_or P Q.

Proof.
        intros P Q p.
        unfold my_or.
        intros R h1 h2;apply h1;assumption.
Qed.

Theorem vp155:
        forall P Q:Prop, Q -> my_or P Q.
Proof.
        unfold my_or.
        intros P Q q R h1 h2.
        apply h2;assumption.
Qed.

Theorem vp156:
        forall P Q R:Prop, (P -> R) -> (Q -> R) -> my_or P Q -> R.

Proof.
        intros P Q R h1 h2.
        unfold my_or.
        intros h3.
        apply h3;assumption.
Qed.

Theorem vp158:
        forall P Q:Prop, my_or P Q -> my_or Q P.
Proof.
        unfold my_or;intros P Q h1.
        intros R h3 h2;apply h1;assumption.
Qed.

Theorem vp157:
        forall P:Prop,my_or P my_False -> P.
Proof.
        unfold my_or;intros P h1;apply h1;intros.
        assumption.
        apply (H P).
Qed.

Theorem vp159:
       forall (A:Set) (P: A -> Prop) (a : A), P a -> my_ex A P.
Proof.
        intros A P a h1.
        unfold my_ex.
        intros R h2.
        apply h2 with (a:=a).
        assumption.
Qed.

Theorem vp1510:
        forall (A:Set) (P:A->Prop),
                my_not (my_ex A P) -> forall a: A, my_not (P a).
Proof.
        unfold my_not.
        unfold my_ex.
        intros A P h1 h2 h3.
        apply h1.
        intros R h4.
        apply h4 with (a:=h2).
        assumption.
Qed.

Definition my_le (n p :nat):=
        forall P: nat -> Prop, P n -> (forall q: nat, P q -> P (S q)) -> P p.

Lemma my_le_n :
        forall n:nat ,my_le n n.
Proof.
        intros n.
        unfold my_le.
        intros P h1 h2.
        assumption.
Qed.

Lemma my_le_S :
        forall n p : nat , my_le n p -> my_le n (S p).
Proof.
        unfold my_le.
        intros n p h1 P h2 h3.
        apply h3.
        apply h1.
        assumption.
        assumption.
Qed.

Lemma my_le_le :
        forall n p : nat, my_le n p -> n <= p.
Proof.
        intros n p h1.
        apply h1.
        reflexivity.
        apply le_S.
Qed.


