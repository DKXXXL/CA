Inductive last (A: Set) (a : A) : list A -> Prop :=
| last_single : last A a (cons a nil)
| last_step : forall (y:A) (l:list A), last A a l -> last A a (cons y l).

Print option.
Print list.
Fixpoint last_fun {A: Set} (l : list A) : option A := match l with
        | nil => None
        | cons a nil => Some a
        | cons a b => last_fun b
end.


Fixpoint append {A : Set} (l1 l2 : list A): list A :=
        match l1 with
        | nil => l2
        | cons a b => cons a (append b l2)
        end.

Inductive palindrome (A:Set) : list A -> Prop :=
| palin_nil : palindrome A nil
| palin_single : forall x, palindrome A (cons x nil)
| palin_nnil : forall (x:A) (l:list A), palindrome A l -> palindrome A (cons x (append l (cons x nil))).

Theorem last_step_add:
        forall (A:Set) (a x y: A) (l:list A), last A a (x::y::l)%list -> last A a (y::l).
       Proof.
              intros A a x y l h1.
             inversion h1.  apply H0.
       Qed.

Theorem p2138p1:
        forall (A: Set)(a: A)(l: list A),last _ ((fun c => match c with Some b => b | None => a  end) (last_fun (cons a l))) (cons a l).
       Proof.
           intros A a l.
           change( last A (match (last_fun (a :: l)) with |Some b => b | None => a end) (a :: l)). 
           elim l. simpl; apply last_single.
           intros a0 l0 h1. destruct l0. simpl. apply last_step. apply last_single. change (last A match last_fun (a :: (a1 :: l0)%list) with |Some b => b |None => a end (a :: (a0 :: a1 :: l0)%list)).
           apply last_step. apply last_step. eapply last_step_add. apply h1.
       Qed.

Definition relation (A: Type) := A -> A -> Prop. 

Inductive sorted {A:Set} (R: A-> A -> Prop): list A -> Prop :=
| sorted0 : sorted R nil
| sorted1 : forall (x: A), sorted R (cons x nil)
| sorted2 : forall (x y:A) (l:list A),
                R x y -> sorted R (cons y l) -> sorted R (cons x (cons y l)).

Hint Resolve sorted0 sorted1 sorted2 : sorted_base.

Theorem sorted_nat_123 : sorted le ((1 :: 2 :: 3 :: nil)%list).
Proof.
        auto with sorted_base.
Qed.

Theorem xy_ord :
        forall x y:nat, le x y -> sorted le (x::y::nil)%list.
Proof.
        auto with sorted_base.
Qed.

Require Import Arith.

Theorem zero_cons_ord :
        forall l:list nat, sorted le l -> sorted le (cons 0 l).
Proof.
        induction l; auto with sorted_base arith.
Qed.

Theorem sorted1_inv :
        forall (A:Set) (le:A->A->Prop) (x:A) (l:list A),
                sorted le (cons x l) -> sorted le l.
Proof.
        intros A r x l h1; inversion h1; auto with sorted_base.
Qed.

Theorem sorted2_inv :
        forall (A:Set) (le:A -> A -> Prop) (x y :A) (l:list A),
                sorted le (cons x (cons y l)) -> le x y.
        Proof.
                inversion 1; auto with sorted_base.
        Qed.


Inductive cons_trans {A:Type} : nat -> list A -> list A -> Prop :=
| cont0 : forall (l:list A), cons_trans   0 l l
| cont1 :forall (n:nat) (x:A) (l1 l2:list A), cons_trans n l1 l2 -> cons_trans n (x::l1)%list (x::l2)%list
| cont2 : forall (n:nat) (x y:A) (l1 l2:list A), cons_trans n l1 l2 -> cons_trans (S n) (x::y::l1)%list (y::x::l2)%list 
|cont3 : forall (n m:nat) (l1 l2 l3: list A), (cons_trans n l1 l2) -> (cons_trans m l2 l3) -> (cons_trans (n+m) l1 l3).

Definition permutation {A:Type} (x y: list A) : Prop := exists n : nat, cons_trans n x y.

Require Import Relations.


Hint Resolve cont0 cont1 cont2: perm_base.
Theorem perm_refl:
        forall (A:Type), reflexive (list A) permutation.
Proof.
        unfold reflexive; unfold permutation.
        intros A x. elim x. exists 0; auto with perm_base.
        intros a l h1; inversion h1. exists x0; auto with perm_base.
Qed.

Theorem perm_symm:
        forall (A:Type), symmetric (list A) permutation.
Proof.
        unfold symmetric; unfold permutation.
        intros A. induction 1. induction H. exists 0; auto with perm_base.
        inversion IHcons_trans. exists x0; auto with perm_base. inversion IHcons_trans. exists (S x0); auto with perm_base. inversion IHcons_trans1. inversion IHcons_trans2. exists (x0 + x); eapply cont3. apply H2. apply H1.
Qed.


Hint Resolve perm_refl perm_symm : perm_base.

Theorem perm_tran:
        forall (A:Type), transitive (list A) permutation.
Proof.
        unfold transitive; unfold permutation.
        intros A x y z h1 h2. inversion h1. inversion h2. exists (x0 + x1); eapply cont3; [apply H | trivial].
Qed.

Hint Resolve perm_tran : perm_base.        
Theorem perm_equiv:
        forall (A:Type), equiv (list A) permutation.
        unfold equiv. intro A; auto with perm_base.
Qed.

Inductive par : Set := open | close.

Inductive wp : list par -> Prop:=
| wp0 : wp nil
| wp1 : forall (l1 l2 : list par), wp l1-> wp l2 -> wp (cons open (app l1 (cons close l2))).

Hint Resolve wp0 wp1 : wp_base.


Theorem wp_oc : wp (cons open (cons close nil)).
Proof.
        change (wp (open :: (app nil (close :: nil)%list))).
        auto with wp_base.
Qed.

Theorem wp_o_head_c :
        forall l1 l2 : list par, wp l1 -> wp l2 -> wp (cons open (app l1 (cons close l2))).
Proof.
        auto with wp_base.
Qed.

Require Import List.
SearchRewrite (_ ++ (_ ++ _))%list.

Hint Resolve app_assoc:wp_base.

Theorem wp_o_tail_c:
        forall l1 l2:list par, wp l1 -> wp l2 ->
                wp (app l1 (cons open (app l2 (cons close nil)))).
Proof.
        induction 1; simpl; auto with wp_base.
        intros. simpl. rewrite <- app_assoc. 
        change (wp ((open :: l1 ++ (close :: (l0 ++ (open :: l2 ++ close :: nil))))%list)).
        auto with wp_base.
Qed.

Hint Resolve wp_o_tail_c : wp_base.

Inductive bin : Set := L : bin | N' : bin -> bin -> bin.

Fixpoint bin_to_string (t:bin) : list par :=
        match t with
        | L => nil
        | N' u v => cons open (app (bin_to_string u) (cons close (bin_to_string v)))
        end.

Theorem wp_bin_to_string :
        forall (t : bin), wp (bin_to_string t).
Proof.
        induction t; simpl ; auto with wp_base.
Qed.

Fixpoint bin_to_string'  (t:bin) : list par:=
        match t with
        | L => nil
        | N' u v => app (bin_to_string' u) (cons open (app (bin_to_string' v) (cons close nil)))
        end.

Theorem wp_bin_to_string' :
        forall (t:bin), wp (bin_to_string' t).
Proof.
        induction t; simpl; auto with wp_base.
Qed.

Require Import JMeq.

Theorem JMEQHELPER1:
        forall (x y : nat), JMeq x y -> JMeq (S x) (S y).
Proof.
        intros.
        elim H. trivial.
Qed.


Goal forall (x y z:nat), JMeq (x+(y+z)) ((x+y)+z).
Proof.
        induction x. simpl. auto. intros. simpl. apply JMEQHELPER1. trivial.
Qed.

Inductive even : nat -> Prop :=
| even0 : even 0
| even1 : forall (n:nat), even n -> even (S (S n)).



Theorem even_double :
        forall (x:nat), even x -> exists n:nat, x = 2*n.
Proof.
        intros. induction H. exists 0;trivial.
        inversion IHeven. exists (S x). rewrite -> H0. simpl; trivial. rewrite -> plus_assoc. rewrite -> plus_comm. simpl. pattern (x+0). rewrite -> plus_comm. simpl. pattern (x + S x). rewrite -> plus_comm. simpl. trivial.
Qed.

Theorem double_even:
        forall (x:nat), even (2 * x).
Proof.
        intros. induction x. simpl; apply even0. simpl. pattern (x+0). rewrite -> plus_comm. simpl. rewrite -> plus_comm. simpl. apply even1. assert (forall x, x + x = 2 * x). induction x0;simpl; auto. rewrite -> H; trivial.
Qed.

Require Import Omega.

Open Scope Z_scope.
Inductive Pfact : Z -> Z -> Prop :=
        pfact0 : Pfact 0 1
        | pfact1 : forall n v: Z, n <> 0 -> Pfact (n-1) v -> Pfact n (n*v).

Goal Pfact 3 6.
apply (pfact1 3 2).
discriminate.
apply (pfact1 2 1).
discriminate.
apply (pfact1 1 1).
discriminate. 
apply pfact0.
Qed.

Theorem fact_dom : forall x y: Z, Pfact x y -> 0 <= x.
Proof.
        intros. elim H. omega.
        intros. omega.
Qed.

Require Import ZArith.
Require Import Zwf.
Check Zwf_well_founded.

Theorem dom_fact_ex :
        forall x: Z, 0<=x -> exists y : Z, Pfact x y.
Proof.
        intro x0.
        Check well_founded_ind.
        elim x0 using (well_founded_ind (Zwf_well_founded 0)).
        intros. elim (Zle_lt_or_eq _ _ H0). intros . elim (H (x-1)). intros. exists (x*x1). apply pfact1. omega. trivial. unfold Zwf. omega. omega. intros. exists 1. rewrite <- H1. apply pfact0.
Qed.




Print N.
Print bin.
Inductive parse_rel : list par -> list par -> bin -> Prop:=
| parse_node : forall (l1 l2 l3:list par) (t1 t2 : bin), parse_rel l1 (cons close l2) t1 -> parse_rel l2 l3 t2 -> parse_rel (cons open l1) l3 (N' t1 t2)
| parse_leaf_nil : parse_rel nil nil L
| parse_leaf_close :
                forall l:list par, parse_rel (cons close l) (cons close l) L.

SearchRewrite (_ ++_)%list.

Theorem parse_rel_sound_anx :
        forall (l1 l2:list par) (t:bin),
        parse_rel l1 l2 t -> l1 = app (bin_to_string t) l2.
Proof.
        induction 1. simpl. rewrite <- app_assoc. pattern ((close :: bin_to_string t2) ++ l3). rewrite <- app_comm_cons. rewrite <- IHparse_rel2. rewrite <- IHparse_rel1. trivial. simpl;trivial. simpl;trivial.
Qed.

Theorem parse_rel_sound :
        forall l: list par, (exists t:bin, parse_rel l nil t) -> wp l.
Proof.
        inversion 1. assert (l = app (bin_to_string x) nil). apply parse_rel_sound_anx. trivial. rewrite <- app_nil_end in H1. rewrite -> H1. apply wp_bin_to_string.
Qed.


Section little_semantics.
Variables Var aExp bExp : Set.
Inductive inst : Set :=
| Skip : inst
| Assign : Var -> aExp -> inst
| Sequence : inst -> inst -> inst
| WhileDo : bExp -> inst -> inst.

Variables
 (state : Set)
 (update : state -> Var-> Z -> option state)
 (evalA : state -> aExp -> option Z)
 (evalB : state -> bExp -> option bool).

Inductive exec : state -> inst -> state -> Prop :=
| execSkip : forall s:state, exec s Skip s
| execAssign :
    forall (s s1:state)(v:Var)(n:Z)(a:aExp),
    evalA s a = Some n -> update s v n = Some s1 -> exec s (Assign v a) s1
| execSequence :
    forall (s s1 s2:state)(i1 i2:inst),
    exec s i1 s1 -> exec s1 i2 s2 -> exec s (Sequence i1 i2) s2
| execWhileFalse :
    forall (s :state) (e: bExp)(i:inst),
    evalB s e = Some false -> exec s (WhileDo e i) s
| execWhileTrue :
    forall (s s1 s2 : state)(i:inst) (e:bExp),
    evalB s e = Some true -> exec s i s1 ->  exec s1 (WhileDo e i) s2 -> exec s (WhileDo e i) s2.

Theorem some_true:
        forall x:option bool, x = Some true \/ x = Some false \/ x = None.
Proof.
        intro x; destruct x; try tauto. destruct b; try tauto.
Qed.


Theorem HoareWhileRule_1:
        forall (P:state -> Prop) (b:bExp)(i:inst)(s s':state),
        (forall s1 s2:state, P s1 -> evalB s1 b = Some true -> exec s1 i s2 -> P s2) -> P s -> exec s (WhileDo b i) s' -> P s' /\ evalB s' b = Some false.
Proof.
        intros P b i s s' H.
        cut (forall i',exec s i' s' -> i' = WhileDo b i -> P s -> P s' /\ evalB s' b = Some false).
        eauto.
        intros i' h. elim h; try (intros; discriminate).
        intros. injection H1. intros. rewrite <- H4. split; trivial.
        intros. injection H5. intros. assert (h2 : P s1). rewrite -> H8 in H0; rewrite -> H7 in H1. apply (H s0 s1 H6 H0 H1). apply H4; trivial.
Qed.

Theorem NeverHalt:
        forall (s s': state) (b:bExp),
        exec s (WhileDo b Skip) s' -> evalB s b = Some true -> False.
Proof.
        cut (forall (s s':state) (b:bExp) (i:inst), exec s i s' -> i = WhileDo b Skip -> evalB s b = Some true -> False). intro. eauto.
        intros s s' b i h1. elim h1; try (intros; discriminate).
        intros. injection H0. intros. rewrite <-H3 in H1. rewrite -> H1 in H. discriminate.
        intros. injection H4; intros. rewrite -> H6 in H0; inversion H0. rewrite -> H10 in H5. apply H3; trivial.
Qed.


Theorem HoareSeqRule:
        forall (P: state -> Prop) (i1 i2:inst),
        (forall (s s':state), P s -> exec s i1 s' -> P s') -> (forall (s s':state),P s -> exec s i2 s' -> P s') -> (forall (s1 s2:state), P s1 -> exec s1 (Sequence i1 i2) s2 -> P s2).
Proof.
        intros. inversion H2.
        apply (H0 s0 s2);trivial.
        apply (H s1 s0);trivial.
Qed.

End little_semantics.


Close Scope Z_scope.

Goal ~sorted le ((1::3::2::nil)%list).
unfold not.
intros.
inversion H. inversion H4. 
inversion H7. inversion H11. inversion H13.
Qed.

Goal ~(even 1).
unfold not; intros.
generalize (eq_refl 1). pattern 1 at -2. 
elim H. intros; discriminate.
intros; discriminate.
Qed.

Inductive stampprice : nat -> Prop:=
| sp0 : stampprice 3
| sp1 : stampprice 5
| sp2 : forall (n m:nat), stampprice n -> stampprice m -> stampprice (n+m).

Hint Resolve sp0 sp1 sp2: sp_base.

Theorem StrongInd:
        forall (P:nat -> Prop),
        P 0 ->
        (forall m:nat, (forall n:nat, n < m -> P n) -> P m) -> (forall m:nat, P m).
Proof.
        intros.
        assert (forall n, (forall m, m < n -> P m)).
        intro. induction n. intros. inversion H1.
        intros. inversion H1. apply H0. apply IHn.
        apply IHn. omega.
        generalize m. clear m. intros m. induction m; trivial. apply H1 with (n:= S (S m)). omega.
Qed.

Goal forall n, n >= 8 -> stampprice n. 
intro. pattern n. elim n using StrongInd. intros; omega.
intros.inversion H0. change (stampprice (3+5)). auto with sp_base arith. inversion H1. change (stampprice (3 + 3 + 3)). auto with sp_base arith. inversion H3. change (stampprice (5 + 5)). auto with sp_base arith. change (stampprice (3 + m2)). apply sp2. apply sp0. apply H; omega.
Qed.








