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

