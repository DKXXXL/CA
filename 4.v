Require Import ZArith.
Section A_declared.

        Variables (A:Set) (P Q: A-> Prop) (R: A -> A -> Prop).
        Theorem all_imp_dist:
                (forall a: A, P a -> Q a)-> (forall a, P a) -> (forall a: A, Q a).
        intros h1 h2.
        intro a.
        apply h1.
        apply h2.
        Qed.

        Theorem all_perm:
                (forall (a b: A), R a b) -> (forall (a b : A), R b a).
        intros h1.
        intros a b.
        apply h1.
        Qed.

        Theorem all_delta :
                (forall (a b :A), R a b) -> (forall (a : A), R a a).
        intros h1 a.
        apply h1.
        Qed.

End A_declared.
Section fourpfour_sec.
        Theorem fpf_id:
                forall A:Set, A -> A.
                Proof.  
        intros A a.
        assumption.
                Qed.
       

Theorem fpf_diag:
               forall A B : Set, (A -> A -> B) -> A -> B.
               Proof.
                       intros A B h1.
                       intro a.
                       apply h1.
                       assumption.
                       assumption.
               Qed.
               Theorem fpf_permute:
                       forall A B C: Set,(A -> B -> C) -> B ->A ->C.
                       Proof.
                               intros A B C h1 b c.
                               apply h1;assumption.
                       Qed.

                       Theorem fpf_f_nat_Z:
                               forall A:Set,(nat -> A) -> Z -> A.
                               Proof.
intros A h1 b.
apply h1;apply(fun (a: Z) => 0);assumption.
                               Qed.
End fourpfour_sec.

Section fourpfive.
        Theorem fpfv_all_perm :
                forall (A:Type) (P:A -> A -> Prop),
                (forall x y : A, P x y) -> (forall x y :A, P y x).
        Proof.
                intros A h1 h2 x y.
                apply h2.
        Qed.
        Theorem fpfv_resolution :
                forall (A:Type) (P Q R S : A -> Prop), (forall a:A,Q a -> R a -> S a) -> (forall b:A, P b -> Q b) -> (forall c : A,P c -> R c -> S c).
        Proof.
                intros A P Q R S h1 h2 c p r.
                apply h1;[(apply h2;assumption)| assumption ].

        Qed.

