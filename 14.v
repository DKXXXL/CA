Section update_def.
  Variables (A:Set) (A_eq_dec : forall x y :A, {x=y} + {x<>y}).
  Variables (B:A -> Set) (a:A) (v:B a) (f:forall x:A, B x).
  Definition update (x:A) : B x :=
    match A_eq_dec a x with
      | left h => eq_rec a B v x h
      | right h' => f x
    end.
End update_def.

Require Import Eqdep.

Theorem update_eq :
  forall (A:Set) (eq_dec:forall x y:A, {x = y} + {x<>y})
         (B:A->Set) (a:A) (v:B a) (f:forall x:A, B x),
    update A eq_dec B a v f a = v.
  intros. unfold update. case (eq_dec a a). intros.  symmetry. apply eq_rec_eq.
  unfold not. intros. elim (n (eq_refl a)).
Qed.

