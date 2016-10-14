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

Inductive Z_inf_branch_tree : Set :=
| Z_inf_leaf : Z_inf_branch_tree
| Z_inf_node : Z -> (nat -> Z_inf_branch_tree) -> Z_inf_branch_tree.

Fixpoint vip28_a1 (n:nat) (f: nat -> bool) {struct n} :bool :=
        match n with
        | O => f O
        | S x => match f (S x) with
                | true => true
                | false => vip28_a1 x f
        end
        end.


Fixpoint vip28 (n:nat) (tree: Z_inf_branch_tree) {struct tree} : bool :=
        match tree with
        | Z_inf_leaf => false
        | Z_inf_node z f => match z with
                             | 0%Z => true
                             | _ => vip28_a1 n (fun x:nat => vip28 n (f x))
                        end
        end.

Theorem vip29:
        forall n : nat, n = n +0.
Proof.
        intro n;elim n.
        simpl;reflexivity.
        intros n0 h1.
        simpl.
        Check eq_ind.
        apply (eq_ind n0 (fun k:nat => S n0 = S k)). 
        reflexivity.
        assumption.
Qed.


Inductive Z_btree : Set :=
        Z_leaf : Z_btree 
        | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

Inductive Z_fbtree : Set :=
        Z_fleaf : Z_fbtree
        | Z_fnode : Z -> (bool -> Z_fbtree) -> Z_fbtree.

Fixpoint f1 (tree :Z_btree) {struct tree} : Z_fbtree :=
        match tree with
        | Z_leaf => Z_fleaf
        | Z_bnode v l r => 
                        Z_fnode v 
                        (fun (b:bool) => match b with true => (f1 l) | false => (f1 r) end)
        end.

Fixpoint f2 (tree : Z_fbtree) {struct tree} : Z_btree :=
        match tree with 
        | Z_fleaf => Z_leaf
        | Z_fnode v f => Z_bnode v (f2 (f true)) (f2 (f false))
        end.

Theorem vip30_a:
        forall t:Z_btree , f2(f1 t) = t.
Proof.
        intros t.
        elim t.
        simpl;reflexivity.
        intros z z0 h1 z1 h2.
        simpl.
        rewrite -> h1.
        rewrite -> h2.
        reflexivity.
Qed.

Theorem vip30_b:
        forall t:Z_fbtree, f1(f2 t) = t.
Proof.
        intros t;elim t.
        simpl;reflexivity.
        intros z z0 h1.
        simpl.
Abort.

Fixpoint sum_n (n:nat) : nat :=
        match n with
        | 0 => 0
        | S p => S p + sum_n p
        end.

Theorem vip32:
        forall n:nat, 2* sum_n n = n * S n.
Proof.
        intros n;elim n.
        simpl;reflexivity.
        intros n0 h1.
        simpl sum_n.
        rewrite <- plus_Sn_m.
        rewrite -> mult_plus_distr_l.
        rewrite -> h1.
        rewrite <- mult_plus_distr_r.
        simpl (2+n0).
        rewrite -> mult_comm.
        reflexivity.
Qed.

Theorem vip33:
        forall n:nat, le n (sum_n n).
Proof.
        intros n;elim n.
        simpl;trivial.
        intros n0 h1.
        simpl sum_n.
        apply le_n_S.
        assert (h2 : 0 <= n0).
        apply le_0_n.
        pattern n0 at 1.
        rewrite <- plus_O_n.
        apply plus_le_compat;assumption.
Qed.

Definition h : nat -> nat -> nat :=
        fix g (n m : nat) {struct n} : nat :=
        match n with O => m | S x => S (g x m) end.
Section define_lists.
        Variable A : Set.
        Variable B : Set.
        Inductive list' : Set :=
        | nil' : list'
        | cons' : A -> list' -> list'.
Check list'.
Print list'.
End define_lists.
Print list'.
Print list'_ind.

Check list.
Definition vip34 (A : Set) (l : list' A)  : list' A :=
       match l with
       | nil' => nil' A
       | cons'  a l' => match l' with
                        | nil' => nil' A
                        | cons' b l'' => cons' A a (cons' A b (nil' A))
                        end
       end.
Fixpoint vip35 (A : Set) (n : nat)(l : list' A) {struct n} : list' A :=
       match n with
       | O => nil' A
       | S x => match l with
                | nil' => nil' A
                | cons' c l' => cons' A c (vip35 A x l')
                end 
       end.

Fixpoint vip36 (l : list' Z) {struct l}: Z :=
        match l with
        | nil' => 0%Z
        | cons' x l' => Zplus x (vip36 l')
        end.
        
Fixpoint vip37 (n : nat) (l : list' nat) {struct l} : list' nat :=
        match l with
        | nil' => nil' nat
        | cons' x l' => match leb x n with
                        |true => cons' nat  x (vip37 n l')
                        |false => vip37 n l'
                        end
        end.

Theorem vip30_b:
        (forall (A B:Set) (f1 f2:A -> B), (forall a:A, f1 a = f2 a) -> f1 = f2) -> 
        forall t: Z_fbtree, f1 (f2 t) = t.
Proof.
        intros h0.
        intros t;elim t.
        simpl;reflexivity.
        intros z f h1.

        simpl.
        rewrite -> h1.
        rewrite -> h1.
        assert (h2: (fun b:bool => if b then f true else f false) = f).
        apply h0.
        intros a;elim a;simpl;reflexivity.
        rewrite -> h2;reflexivity.
Qed.
        

Fixpoint nth_option (A:Set) (n:nat) (l:list A) {struct l} :option A :=
        match n, l with
        | O, cons a tl => Some a
        | S p, cons a tl => nth_option A p tl
        | n, nil => None
        end.

Fixpoint nth_option' (A:Set) (n:nat) (l:list A) {struct n} :option A:=
        match n, l with
        | O, nil => None
        | O, cons a l' => Some a
        | S x, nil => None
        | S x, cons a l' => nth_option' A x l'
        end.

Theorem vip39:
        forall (A:Set) (n:nat) (l:list A), nth_option' A n l = nth_option A n l.
Proof.
        intros A n.
        elim n.
        intros l;elim l;simpl;reflexivity.
        intros n1 h1.
        intros l;elim l.
        simpl;reflexivity.
        intros a l0 h2.
        simpl.
        apply h1.
Qed.

Theorem vip640:
        forall (A:Set) (n:nat) (l:list A),
                nth_option A n l = None -> length l <= n.
Proof.
        intros A n.
        elim n.
        intros l;elim l.
        simpl;intros;reflexivity.
        intros a l0 h1.
        simpl. intros h2;discriminate h2.
        intros n0 h1 l.
        simpl. elim l.
        intros;simpl;apply le_O_n.
        intros a l0 h2. simpl. intros;apply le_n_S;apply h1;assumption.
Qed.

Fixpoint vip41 (A:Set) (f : A -> bool) (l : list A) {struct l} : option A :=
        match l with
        | nil => None
        | cons x l' => if f x then Some x else vip41 A f l'
        end.

Fixpoint split_ (A B:Set) (l :list (A*B)) {struct l} : list A * list B :=
        match l with
        | nil => pair nil nil
        | cons x l' => match split_ A B l' with
                        | pair a b => pair (cons (fst x) a) (cons (snd x) b)
                        end
        end.       

Fixpoint combine_ (A B:Set) (l1: (list A)) (l2 : list B) {struct l1} : list (A*B) :=
        match l1 ,l2 with
        | nil, _ => nil
        | _, nil => nil
        | (cons a l1'), (cons b l2') => cons (pair a b) (combine_ A B l1' l2')
        end.

Inductive pos_rat : Set :=
| Rr : pos_rat
| Nr : pos_rat -> pos_rat
| Dr : pos_rat -> pos_rat
.

Fixpoint ratio_posrat (m: pos_rat) {struct m} : nat*nat :=
        match m with
        | Rr => (1,1)
        | Nr m' => match ratio_posrat m' with (x,y) => (x+y,y)end
        | Dr m' => match ratio_posrat m' with (x,y) => (x,x+y)end
        end.

Inductive cmp: Set :=
        Less : cmp
        | Equal : cmp
        | Greater : cmp.
Fixpoint three_way_compare (n m :nat ) {struct n} : cmp :=
        match n,m with
        | O, O => Equal
        | O, S _ => Less
        | S _, O => Greater
        | S x, S y => three_way_compare x y
        end.
   

Fixpoint update_primes (n:nat) (l:list (nat*nat)) {struct l} : (list (nat*nat)) * bool :=
match l with
| nil => pair nil false
| cons aa l' => 
   match aa with
   | pair p m => 
      match three_way_compare m n with
      | Equal =>
        match update_primes n l' with
        | pair l'' _ => 
             pair (cons (pair p (p+m)) l'') true
        end
      | _ => 
        match update_primes n l' with
        | pair l'' b =>
             pair (cons (pair p m) l'') b
        end
      end 
   end
end.
Fixpoint prime_sieve (n:nat) {struct n} :list (nat*nat) :=
        match n with
        | O => nil
        | S O => nil
        | S (S O) => cons (pair 2 2) nil
        | S x => 
            match update_primes x (prime_sieve x) with
            | pair l'' b => 
               match b with
               | true => l''
               | false => cons (pair x x) l''
               end
            end
          
        end.

Inductive htree (A:Set) : nat -> Set :=
| hleaf : A -> htree A 0
| hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n).
Inductive Empty_set : Set :=.
Theorem vip51:
        forall x y:Empty_set, x = y.
Proof.
        intros x y.
        elim x.
Qed.

Theorem vip51_2:
        forall x y:Empty_set, ~(x=y).
Proof.
        intros x y;elim x.
Qed.



