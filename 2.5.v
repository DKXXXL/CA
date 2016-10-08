Require Import Arith.
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
Definition twopfive (a b c d e : Z) : Z := a + b + c + d + e.
Check twopfive.
Section mab.
        Variables a b c d e : Z.
        Definition f :Z := a + b + c+d+e.
        Check f.
End mab.

Check f.
Definition twopseven (x : Z) : Z :=
        2 * (x*x) + 3 * x + 3.

Check nat.

Inductive kkk : Set :=
| k : kkk
| kk : kkk -> kkk.

Check k.
Check nat.
Check kkk.
Check Type.
Check Set.



Lemma id_P:forall P, P -> P.
Proof.
        intros.
        assumption.
Qed.

Lemma id_PP:forall P, (P -> P) -> (P ->P).
Proof.
        intros P pf.
        assumption.
Qed.

Lemma imp_trans:
        forall P Q R,(P -> Q) -> (Q -> R) -> P -> R.
Proof.
        intros P Q R h1 h2 p.
        apply h2.
        apply h1.
        assumption.
Qed.

Lemma imp_perm:
        forall P Q R,
        (P -> Q -> R) -> (Q -> P -> R).
Proof.
        intros P Q R h1 q p.
        apply h1.
        assumption.
        assumption.
Qed.    

Lemma ignore_Q :
        forall P Q R, (P -> R) -> P -> Q -> R.
Proof.
        intros P Q R h1 p q.
        apply h1.
        assumption.
Qed.

Lemma delta_imp :
        forall P Q, (P -> P -> Q) -> P -> Q.
Proof.
        intros P Q h1 p.
        apply h1.
        assumption.
        assumption.
Qed.    

Lemma delta_impR:
        forall P Q, (P -> Q) -> (P -> P -> Q).
Proof.
        intros P Q h1 p p'.
        apply h1.
        assumption.
Qed.

Lemma diamond :
        forall P Q R T, (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
        intros P Q R T h1 h2 h3 p.
        apply h3.
        apply h1.
        assumption.
        apply h2.
        assumption.
Qed.

Lemma weak_peirce:
        forall P Q,
        ((((P-> Q) -> P) -> P) -> Q) -> Q.
Proof.
        intros P Q h.
        apply h.
        intros h1.
        apply h1.
        intros p.
        apply h.
        intro.
        assumption.
Qed.

