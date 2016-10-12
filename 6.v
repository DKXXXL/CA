Inductive Season: Set :=
        Spring : Season
        | Summer : Season
        | Autumn : Season
        | Winter : Season.

Inductive month : Set :=
| January
| February
| March
| April
| May
| June
| July 
| August
| September
| October
| November
| December.

Check month_rec.

Definition monthtoseason :=
        month_rec (fun (a : month) => Season) Winter Winter Spring Spring Spring Summer Summer Summer Autumn Autumn Autumn Winter.

Eval compute in (monthtoseason January).

Check bool_ind.

Theorem month_equal:
        forall m : month,
        m = January \/ m = February \/ m = March \/ m = April \/ m = May \/ m = June \/ m = July \/ m = August \/ m = September \/ m = October \/ m = November \/ m = December.
Proof.
        intro m.
        elim m;auto 12.
Qed.

Theorem bool_equal_2 :
        (forall b:bool, b = true \/ b = false).
Proof.
        intros b.
        Check bool_ind.
        apply bool_ind with (b:= b).
        left;reflexivity.
        right;reflexivity.
Qed.

Check bool_ind.
Check refl_equal.

Check (or_introl  refl_equal).

Definition bool_equal_1 :
        (forall b: bool, b = true \/ b = false) :=
        fun (b: bool) => bool_ind (fun (b:bool) => b= true \/ b=false) (or_introl  refl_equal ) (or_intror  refl_equal) b.

Print bool_equal_2.
Check eq_refl.

Definition bool_not : bool -> bool :=
        fun (a : bool) =>
        match a with
        | true => false
        | false => true
        end.

Definition bool_xor : bool -> bool -> bool :=
        fun (a b : bool) =>
        match a with
        | true => bool_not b
        | false => b
        end.
Definition bool_and :=
        fun (a b : bool) =>
        match a with
        | true => match b with
                | true => true
                | _ => false
                end     
        | _ => false
        end.
Definition bool_or :=
        fun (a b : bool) =>
        bool_not( bool_and (bool_not a) (bool_not b)).

Definition bool_eq :=
        fun (a b : bool) =>
        bool_not(bool_xor a b).

Theorem vip61:
        forall b1 b2: bool, bool_xor b1 b2 = bool_not (bool_eq b1 b2).
Proof.
        intros b1 b2;elim b1;elim b2;simpl;reflexivity.
Qed.

Theorem vip62:
        forall b1 b2: bool, bool_not (bool_and b1 b2) = 
        bool_or(bool_not b1) (bool_not b2).
Proof.
        intros b1 b2;elim b1;elim b2;simpl;reflexivity.
Qed.

Theorem vip63:
        forall b:bool, bool_not(bool_not b) = b.
Proof.
        intros b.
        elim b;simpl;reflexivity.
Qed.

Theorem vip64:
        forall b:bool, bool_or b (bool_not b) = true.
Proof.
        intros b;elim b;simpl;reflexivity.
Qed.

Theorem vip65:
        forall b1 b2:bool, bool_eq b1 b2 = true -> b1 = b2.
Proof.
        intros b1 b2.
        elim b1;elim b2;(try intros;simpl;(try reflexivity)).
        unfold bool_eq in H;simpl in H.
        rewrite <- H;reflexivity.
        unfold bool_eq in H;simpl in H.
        rewrite <- H;reflexivity.
Qed.

Theorem vip66:
        forall b1 b2: bool, b1 = b2 -> bool_eq b1 b2 =true.
Proof.
        intros b1 b2 h1;rewrite <- h1;elim b1;simpl;reflexivity.
Qed.

Theorem vip67:
        forall b1 b2:bool ,
        bool_not(bool_or b1 b2) = bool_and(bool_not b1) (bool_not b2).
Proof.
        intros b1 b2;elim b1;elim b2;simpl;reflexivity.
Qed.

Theorem vip68:
        forall b1 b2 b3:bool,
        bool_or(bool_and b1 b3) (bool_and b2 b3) = 
        bool_and(bool_or b1 b2) b3.
Proof.
        intros b1 b2 b3;elim b1;elim b2;elim b3;simpl;reflexivity.
Qed.

Require Import ZArith.

Inductive plane : Set :=
        point : Z -> Z -> plane.

Check plane_ind.
Check Zabs.
Check Zplus.
Definition Manhattan (a b: plane) :=
        match a with
        | point x1 y1 => match b with point x2 y2 => Zplus (Zabs( x1 - x2)) (Zabs(y1 - y2)) end
        end.

Inductive vehicle : Set :=
| bicycle : nat -> vehicle
| motorized : nat -> nat -> vehicle.

Check vehicle_rec.

Definition nb_seats( v: vehicle) : nat :=
        (vehicle_rec (fun (v:vehicle) => nat) (fun n=> n) (fun (a b : nat) => a) v).

Theorem aaa:
        February = January -> False.
Proof.
        intros H1;discriminate H1.
Qed.

Print aaa.

Definition is_January (m : month) : Prop := month_rect (fun (m:month) => Prop) True False False False False False False False False False False False m.

Theorem vip11: ~(true = false).
Proof.
        unfold not.
        intros h1.
        change ((fun (a : bool) =>
                match a with 
                | true => True
                | false => False
                end) false).
        rewrite <- h1.
        apply I.
Qed.

Theorem vip12:
        forall a b c:nat, ~(bicycle a = motorized b c).
Proof.
        unfold not;intros a b c h1.
        change ((fun (a : vehicle) =>
                match a with
                | bicycle _ => False
                | motorized _ _ => True
                end) (bicycle a)).
        rewrite -> h1.
        trivial.
Qed.

Require Import Arith.
Record RatPlus : Set :=
        mkRat { top:nat; bottom:nat; bottom_condition: ~(bottom = 0) }.

Axiom eq_RatPlus :
        forall r r':RatPlus,
        top r * bottom r' = top r' * bottom r -> r = r'.

Theorem vip13_a1:
        ~(2=0).
Proof.
        intros h1;discriminate h1.
Qed.

Theorem vip13_a2:
        ~(4=0).
Proof.
        intros h1;discriminate h1.
Qed.


Theorem realFalse:
        mkRat 1 2 (vip13_a1) = mkRat 2 4 (vip13_a2).
Proof.
        apply eq_RatPlus with (r:= mkRat 1 2 (vip13_a1)).
        simpl.
        reflexivity.
Qed.

Theorem FFFALSE:
        False.
        assert (h1 : 1 = 2).
        assert (h2 : mkRat 1 2 (vip13_a1) = mkRat 2 4 (vip13_a2)).
        apply realFalse.
        change (1 = top(mkRat 2 4 (vip13_a2))).
        rewrite <- h2.
        simpl;reflexivity.
        change ((fun (a:nat) =>
                match a with
                | 2 => False
                | _ => True end) 2 ).
        rewrite <- h1.
        apply I.
Qed.

Theorem plus_assoc__:
        forall a b c:nat ,
        (a + b) + c = a + (b + c).
Proof.
        intros a b c.
        elim a.
        reflexivity.
        intros n h1.
        simpl.
        rewrite <- h1.
        reflexivity.
Qed.
Definition vip15 (n:nat) : bool :=
        match n with
        | 3 => true
        | _ => false
        end.
                                       
Fixpoint vip16 (a b :nat) {struct  b}:nat :=
        match b with
        | O => a
        | S x => S (vip16 a x)
        end.

Fixpoint vip17 (f: nat -> Z) (n : nat) {struct n} : Z :=
        match n with
        | O => f O
        | S x => Zplus (f (S x)) (vip17 f x)
        end.

Fixpoint two_power (n : nat) {struct n} : nat :=
        match n with 
        | O => S O
        | S x => 2 * (two_power x)
        end.

Fixpoint pos_even_bool (p : positive) : bool :=
        match p with
        | xO x' => true
        | _ => false
        end.

Fixpoint pos_div4 (p : positive) : Z :=
        match p with
        | xO (xO x') => Zpos x'
        | xO (xI x') => Zpos x'
        | xO xH => 0%Z
        | xI (xO x') => Zpos x'
        | xI (xI x') => Zpos x'
        | xI xH => 0%Z
        | xH => 0%Z
        end.

Fixpoint pos_acc (a : positive) : positive :=
        match a with
        | xH => xO xH
        | xO x' => xI x'
        | xI x' => xO (pos_acc x')
        end.

Fixpoint pos_add_ (a b :positive) {struct a} : positive :=
        match a with
        | xH => pos_acc b
        | xO x' => match b with
                   | xH => xI x'
                   | xO y' => xO (pos_add_ x' y')
                   | xI y' => pos_acc (xO (pos_add_ x' y')) end
        | xI x' => pos_acc (pos_add_ x' b)
        end.

Fixpoint pos_mult_ (a b:positive) {struct a} : positive :=
        match a with
        | xO x' => xO (pos_mult_ x' b)
        | xI x' => pos_add_ b (xO (pos_mult_ x' b))
        | xH => b
        end.  
Fixpoint z_mult_ (a b:Z) {struct a} : Z:=
        match a with
        | Zpos a' => match b with
                      | Zpos b' => Zpos (pos_mult_ a' b')
                      | Zneg b' => Zneg (pos_mult_ a' b')
                      | Z0 => 0%Z
                        end
        | Zneg a' => match b with
                        | Zpos b' => Zneg (pos_mult_ a' b')
                        | Zneg b' => Zpos (pos_mult_ a' b')
                        | ZO => 0%Z
                        end
        | ZO => 0%Z
        end.
Inductive pplg : Set :=
| ppand : pplg -> pplg -> pplg
| ppor : pplg -> pplg -> pplg
| ppnot : pplg -> pplg
| ppimply : pplg -> pplg -> pplg
| ppTrue : pplg
| ppFalse : pplg.

Inductive posRat : Set :=
| one : posRat
| N : posRat -> posRat
| D : posRat -> posRat.

Fixpoint z_power (a : Z) (to : nat) : Z :=
        match to with
        | O => Zpos xH
        | S x => z_mult_ a (z_power a x)
        end.

Fixpoint discrete_log (n:positive) {struct n} : nat :=
        match n with
        | xH => O
        | xO x' => S(discrete_log x')
        | xI x' => S(discrete_log x')
        end.



