Section sec_for_cut.
        Variable (P Q R T : Prop).
        Hypotheses (H : P -> Q)
                (H0 : Q -> R)
                (H1 : (P -> R) -> T -> Q)
                (H2 : (P -> R) -> T).

Theorem cut_example : Q.
Proof.
        cut (P -> R).
        intros H3.
        apply H1;[assumption | apply H2; assumption].
        intro.
        apply H0; apply H ;assumption.
Qed.

Theorem without_cut : Q.
Proof.
        apply H1;[intro H3; apply H0; apply H; assumption | apply H2;  intro H4; apply H0; apply H; assumption].
Qed.


