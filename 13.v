CoInductive LList (A:Set) : Set :=
 | LNil : LList A
 | LCons : A -> LList A -> LList A.

CoFixpoint repeat (A:Set) (x:A) : LList A :=
  LCons _ x (repeat A x).

CoFixpoint Lappend (A:Set) (l1 l2: LList A) : LList A :=
  match l1 with
    | LNil => l2
    | LCons x l1' => LCons _ x (Lappend _ l1' l2)
  end.

CoFixpoint repeat_General (A:Set) (l : LList A) : LList A :=
  (* Lappend _ l (repeat_General _ l).  <- This is wrong*)
  let cofix rpg (l l' : LList A) : LList A :=
      match l with
        | LCons x l'' => LCons _ x (rpg l'' l')
        | LNil =>
          match l' with
            | LNil => LNil _
            | LCons x l'' => LCons _ x (rpg l'' l')
          end
      end in rpg l l.

CoInductive LBT (A:Set) : Set :=
| lleaf : LBT A
| llbnode : A -> LBT A -> LBT A -> LBT A.

Definition Nats : LList nat :=
  let cofix natc (n : nat) : LList nat := LCons _ n (natc (S n)) in natc O.

CoFixpoint graft (A:Set) (t t': LBT A) : LBT A :=
  match t with
    | lleaf  => t'
    | llbnode x tl tr => llbnode _ x (graft _ tl t') (graft _ tr t')
  end.

CoInductive Stream (A:Set) : Set :=
  SCons : A -> Stream A -> Stream A.

Fixpoint CNth (n:nat) (A:Set) (l : Stream A) {struct n} : A :=
  match n with
    | O => match l with SCons x _ => x end
    | S n' => match l with SCons _ l' => CNth n' _ l' end
  end.

Definition NatS : Stream nat :=
  let cofix NatSC (n:nat) := SCons _ n (NatSC (S n)) in NatSC O.

Definition NatBTree : LBT nat :=
  let positive := match NatS with SCons _ x => x end in
  let cofix buildtree (n:nat) : LBT nat :=
      llbnode _ (CNth n _ positive) (buildtree (2*n+1)) (buildtree(2*n+2)) in
  buildtree 0.



CoFixpoint LMap (A B:Set) (f: A -> B) (l: LList A) : LList B :=
  match l with
    | LNil => LNil _
    | LCons x y => LCons _ (f x) (LMap _ _ f y)
  end.

Fixpoint LList_decompose_n (n:nat) (A:Set) (l:LList A) {struct n} : LList A :=
  match n with
    | O => l
    | S n' =>
      match l with
        | LNil => LNil _
        | LCons x l' => LCons _ x (LList_decompose_n n' _ l')
      end
  end.

Eval simpl in (repeat _ 33).
Eval simpl in (LList_decompose_n 5 _ (repeat _ 33)).

Theorem id_L_Decompose:
  forall (n:nat) (A:Set) (l:LList A),
    l = LList_decompose_n n A l.
  intro n. elim n. intros; simpl; trivial.
  intros. simpl. case l; auto. intros.
  rewrite <- (H _ l0). auto.  
Qed.
Ltac LList_decompose term := apply trans_equal with (1 := id_L_Decompose 1 _ term). 

Ltac LList_unfold := LList_decompose.

Ltac LList_unfold2 term := pattern term; rewrite (id_L_Decompose 1 _ term); simpl.
Theorem LAppend_LNil:
  forall (A:Set) (l:LList A), Lappend _ (LNil _) l = l.
  intros. LList_decompose (Lappend A (LNil A) l). simpl. case l; auto.
Qed.

Definition LAppend := Lappend.

Theorem LAppend_LCons :
  forall (A:Set) (a:A) (u v:LList A),
    LAppend _ (LCons _ a u) v = LCons _ a (LAppend _ u v).
  intros.
  LList_unfold (LAppend _ (LCons _ a u) v). auto.
Qed.

Hint Rewrite LAppend_LNil LAppend_LCons : llists.

CoFixpoint from (n:nat) : LList nat := LCons _ n (from (S n)).

Lemma from_unfold :
  forall (n:nat),
    from n = LCons _ n (from (S n)).
  intros.
  LList_unfold (from n); auto.
Qed.

Lemma repeat_unfold:
  forall (A:Set) (a:A),
    repeat _ a = LCons _ a (repeat _ a).
  intros; LList_unfold (repeat _ a); auto.
Qed.

CoFixpoint general_omega (A:Set) (u v:LList A) : LList A :=
  match v with
    | LNil => u
    | LCons b v' =>
      match u with
        | LNil => LCons _ b (general_omega _ v' v)
        | LCons a u' => LCons _ a (general_omega _ u' v)
      end
  end.

Definition omega (A:Set) (u: LList A) := general_omega _ u u.

Lemma general_omega_LNil :
  forall A:Set, omega _ (LNil A) = LNil _.
  intros. LList_unfold (omega A (LNil A)). simpl; auto.
Qed.

Lemma general_omega_LCons :
  forall (A:Set) (a:A) (u v:LList A),
    general_omega _ (LCons _ a u) v =  LCons _ a (general_omega _ u v).
  intros; autorewrite with llists. LList_unfold2 (general_omega A (LCons A a u) v).
  case v. LList_unfold2 (general_omega A u (LNil A)). case u; auto.
  trivial.
Qed.

Lemma general_omega_LNil_LCons :
  forall (A:Set) (a:A) (u:LList A),
    general_omega _ (LNil _) (LCons _ a u) = LCons _ a (general_omega _ u (LCons _ a u)).
  intros.
  LList_unfold2 (general_omega A (LNil A) (LCons A a u)). trivial.
Qed.

Lemma graft_works:
  forall (A:Set) (t:LBT A),
    graft _ (lleaf _) t = t.
  intros.
  refine
    ((fun (x: LBT A) (h : x = graft A (lleaf A) t) => _ ) (graft A (lleaf A) t) _).
Abort.

(* refine tactic -> remeber tactic *)

Inductive Finite (A:Set) : LList A -> Prop :=
| Finite_LNil : Finite A (LNil _)
| Finite_LCons :
    forall (a:A) (l:LList A), Finite A l -> Finite A (LCons _ a l).

Hint Resolve Finite_LNil Finite_LCons : llists.

Lemma one_two_three:
  Finite _ (LCons _ 1 (LCons _ 2 (LCons _ 3 (LNil _)))).
  auto with llists.
Qed.

Lemma Finite_of_LCons :
  forall (A:Set) (a:A) (l:LList A), Finite _ (LCons _ a l) -> Finite _ l.
  intros.
  inversion H; trivial.
Qed.

Lemma LAppend_of_Finite :
  forall (A:Set) (l l' :LList A),
    Finite _ l -> Finite _ l' -> Finite _ (LAppend _ l l').
  intros. generalize l' H0. elim H.
  intros. autorewrite with llists. trivial.
  intros. autorewrite with llists. auto with llists.
Qed.


Hint Rewrite from_unfold repeat_unfold general_omega_LNil general_omega_LCons general_omega_LNil_LCons: llists.


Lemma general_omega_shoots_again :
  forall (A:Set) (v:LList A),
    general_omega _ (LNil _) v = general_omega _ v v.
  intros.
  LList_unfold2 (general_omega A (LNil A) v). simpl. case v; autorewrite with llists.
  LList_unfold2 (general_omega A (LNil A) (LNil A)). trivial.
  intros. autorewrite with llists. trivial.
Qed.

Hint Rewrite general_omega_shoots_again : llists.

Theorem omega_and_append:
  forall (A:Set) (l1 l2:LList A),
    Finite _ l1 ->
    LAppend _ l1 (general_omega _ (LNil _) l2) = general_omega _ l1 l2.
  intros. elim H. autorewrite with llists; trivial.
  intros. autorewrite with llists. rewrite <- general_omega_shoots_again. rewrite H1. trivial.
Qed.

Theorem omega_of_Finite:
  forall (A:Set) (u:LList A),
    Finite _ u -> omega _ u = LAppend _ u (omega _ u). 
  intros. elim H.   autorewrite with llists using auto with llists.
  intros. unfold omega. rewrite <- general_omega_shoots_again.
  pose (Finite_LCons _ a l H0). pose (omega_and_append _ (LCons _ a l) (LCons _ a l) f).
  rewrite e. autorewrite with llists. trivial.
Qed.

CoInductive Infinite {A:Set} : LList A -> Prop :=
  Infinite_LCons:
    forall (a:A) (x: LList A) , Infinite x -> Infinite (LCons _ a x).


Theorem LNil_dec:
  forall (A:Set) (l:LList A), {l = LNil _} + {l <> LNil _}.
  intros. case l. left; trivial.
  right. unfold not. intros. inversion H.
Qed.



Goal forall a:nat, Infinite (from a).
  refine
    (cofix inffrom (a:nat) : Infinite (from a) :=
       (fun (l : LList nat) (h: l = from a) =>
          match (LNil_dec _ l) return Infinite (from a) with
            | left HNil => _
            | right HNNil => _
          end) (from a) (eq_refl (from a))).
  rewrite h in HNil. generalize HNil. LList_unfold2 (from a).
  intros. inversion HNil0.
  LList_unfold2 (from a).
  apply Infinite_LCons.
  apply (inffrom (S a)).
Defined.



Lemma infinite_from :forall a:nat, Infinite (from a).
  refine
    (cofix inffrom (a:nat) : Infinite (from a) :=
       _).
  LList_unfold2 (from a).
  apply Infinite_LCons. apply (inffrom (S a)).
Defined.

Goal forall a:nat, Infinite (from a).
  cofix H.
  intros. LList_unfold2 (from a). apply Infinite_LCons.
  apply H.
Qed.

Lemma repeat_infinite:
  forall (A:Set) (a:A),
    Infinite (repeat _ a).
  cofix H.
  intros. LList_unfold2 (repeat A a). apply Infinite_LCons.
  apply H. Guarded.
Defined.


Lemma general_omega_infinite:
  forall (A:Set) (a:A) (u v:LList A),
    Infinite (general_omega _ v (LCons _ a u)).
  cofix H.
  intros.
  LList_unfold2 (general_omega A v (LCons A a u)).
  case v. apply Infinite_LCons. apply H.
  intros.
  apply Infinite_LCons. apply H.
Defined.

Theorem omega_infinite:
  forall (A:Set) (a:A) (l:LList A),
    Infinite (omega _ (LCons _ a l)).
  intros.
  unfold omega. apply general_omega_infinite.
Defined.

Theorem Infinite_of_LCons:
  forall (A:Set) (a:A) (u:LList A),
    Infinite (LCons _ a u) -> Infinite u.
  intros. inversion H. trivial.

Qed.

Theorem LNil_not_Infinite:
  forall A:Set, ~Infinite (LNil A).
  unfold not; intros.
  inversion H.
Qed.

Theorem LAppend_of_Infinite:
  forall (A:Set) (u:LList A),
    Infinite u -> forall v:LList A, Infinite (LAppend _ u v).
  cofix H.
  intros. inversion H0. autorewrite with llists. apply Infinite_LCons.
  apply H. auto.
Defined.

Theorem Finite_not_Infinite:
  forall (A:Set) (l:LList A),
    Finite _ l -> ~Infinite l.
  unfold not. intros A l h1. elim h1. intros h; inversion h.
  intros. apply H0. inversion H1; auto.
Qed.

Theorem Infinite_not_Finite:
  forall (A:Set) (l:LList A),
    Infinite l -> ~Finite _ l.
  unfold not; intros.
  pose (Finite_not_Infinite _ l H0).
  auto.
Qed.

Theorem not_Finite_Infinite:
  forall (A:Set) (l:LList A),
    ~Finite _ l -> Infinite l.
  cofix H.
  intros A l. case l. Focus 2.
  intros. apply Infinite_LCons.
  assert (~Finite A l0). auto with llists.
  apply (H _ l0 H1).
  unfold not. intros.
  assert (Finite A (LNil A)). auto with llists.
  elim (H0 H1).
Defined.


Require Import Classical.
(*
Lemma Not_Infinite_Finite:
  forall (A:Set) (l:LList A),
    ~Infinite l -> Finite _ l.
  pose not_Finite_Infinite.
  intros A l. apply or_to_imply.
  SearchPattern (_ -> ~~_).*)

Theorem PPNN:
  forall p:Prop, p -> ~~p.
  intros. unfold not. intros. elim (H0 H).
Qed.

(*
Theorem negation_truth:
  forall p q:Prop,
    (~p -> q) -> (~q -> p). 
  intros.
*)


  (*
Lemma Not_Infinite_Finite:
  forall (A:Set) (l:LList A),
    ~Infinite l -> Finite _ l.
  pose not_Finite_Infinite.
  intros A l. apply or_to_imply.
  SearchPattern (_ \/ _ ->).*)

Theorem negation_truth:
  forall p q:Prop,
    (~p -> q) -> (~q -> p). 
  intros. pose (imply_to_or _ _ H).
  elim o. apply NNPP.
  intros. elim (H0 H1).
Qed.


 
Lemma Not_Infinite_Finite:
  forall (A:Set) (l:LList A),
    ~Infinite l -> Finite _ l.
  intros A l. apply negation_truth.
  apply not_Finite_Infinite.
Qed.

Lemma imply_transitive_in_or:
  forall p q r:Prop,
    (p \/ q) -> (p -> r) -> (r \/ q).
  intros.
  elim H; tauto.
Qed.

Lemma Finite_or_Infinite:
  forall (A:Set) (l:LList A),
    Finite _ l \/ Infinite l.
  intros. apply imply_transitive_in_or with (p := ~Infinite l).
  tauto. apply Not_Infinite_Finite.
Qed.

Print ex.

Definition Infinite_ok (A:Set) (X:LList A -> Prop) :=
  forall l:LList A,
    X l -> exists a:A, (exists l' :LList A, l = LCons _ a l' /\ X l'). 

Definition Infinite1 (A:Set) (l:LList A) :=
  exists X:LList A -> Prop, Infinite_ok A X /\ X l.


CoInductive bisimilar {A:Set} : LList A -> LList A -> Prop :=
| bisim0 : bisimilar (LNil _) (LNil _)
| bisim1 : forall (a:A) (l l' :LList A), bisimilar l l' -> bisimilar (LCons _ a l) (LCons _ a l').

Hint Resolve bisim0 bisim1 : llists.

Require Import Relations.

Print equivalence.

Theorem equiv_bisimilar:
  forall (A:Set), equivalence (LList A) bisimilar.
  intros. split.
  unfold reflexive.  cofix H. intros. case x. apply bisim0. intros; apply bisim1; auto. Guarded.
  unfold transitive. cofix H. intros x y z. case x;case y; case z; try (intros; try (inversion H1); try (inversion H0)).
  apply bisim0. rewrite H5. apply bisim1. eapply H. apply H8. apply H3. Guarded.
  unfold symmetric. cofix H. intros x y.
  case x; case y; try (intros; try (inversion H0); try (inversion H1)).
  apply bisim0. apply bisim1. apply H. apply H2.
Qed.

Fixpoint LNth {A:Set} (n:nat) (l:LList A) {struct n} : option A :=
  match l with
    | LNil => None
    | LCons a l' =>
      match n with O => Some a | S p => LNth p l' end
  end.

Lemma bisimilar_LNth :
  forall (A:Set) (n:nat) (u v:LList A),
    bisimilar u v -> LNth n u = LNth n v.
  intros A n. elim n. intros; inversion H; auto.
  intros. inversion H0; auto. simpl. auto.
Qed.

Lemma LNth_bisimilar :
  forall (A:Set) (u v:LList A),
    (forall n:nat, LNth n u = LNth n v) -> bisimilar u v.
  cofix hh.
  intros A u v. case u;case v; intros. apply bisim0.
  pose (H 0). inversion e.
  pose (H 0). inversion e.
  pose (H 0). inversion e.
  apply bisim1.
  assert (forall n:nat, LNth n l0 = LNth n l).
  intros. pose (H (S n)). simpl in e0. apply e0.
  apply hh; apply H0.
Qed.


Theorem bisimilar_of_Finite_is_Finite :
  forall (A:Set) (l:LList A),
    Finite _ l -> forall l' :LList A, bisimilar l l' -> Finite _ l'.

  intros A l h1. elim h1. intros.  inversion H. auto with llists.
  intros a l0 h2 h3 l'. case l'. intros h; inversion h.
  intros. inversion H. auto with llists.
Qed.

Theorem bisimilar_of_Infinite_is_Infinite :
  forall (A:Set) (l:LList A),
    Infinite l -> forall l' : LList A, bisimilar l l' -> Infinite l'.

  cofix hh.
  intros A l h1 l'. inversion h1. case l; case l'; intros; try (inversion H0); try (inversion H1).
  apply Infinite_LCons. eapply hh. apply H. apply H4.
  apply Infinite_LCons. eapply hh. apply H. apply H4.
Qed.

Theorem bisimilar_of_Finite_is_eq:
  forall (A:Set) (l:LList A),
    Finite _ l -> forall l' :LList A, bisimilar l l' -> l = l'.
  intros A l h1. elim h1.
  intros. inversion H; auto.
  intros. inversion H1. pose (H0 l'0 H5).
  rewrite e; auto.
Qed.

Theorem LAppend_assoc:
  forall (A:Set) (u v w:LList A),
    bisimilar (LAppend _ u (LAppend _ v w)) (LAppend _ (LAppend _ u v) w).

  cofix hh.
  intros. case u;  case v. autorewrite with llists. apply equiv_bisimilar.
  intros; autorewrite with llists. apply equiv_bisimilar.
  intros; autorewrite with llists. apply bisim1. pose (hh A l (LNil _) w).
  assert (LAppend _ (LNil A) w = w). LList_unfold2 (LAppend _ (LNil A) w). case w; auto.
  rewrite H in b. apply b. Guarded.
  intros. autorewrite with llists. apply bisim1.
  assert (LCons _ a (LAppend A l w) = LAppend A (LCons _ a l) w); autorewrite with llists; trivial. Guarded.
  rewrite H. apply hh.
  Guarded.
Qed.

Lemma LAppend_of_Infinite_bisim :
  forall (A:Set) (u:LList A),
    Infinite u -> forall v:LList A, bisimilar u (LAppend _ u v).
  cofix hh.
  intros A u. case u. intros h1; inversion h1.
  intros. inversion H. autorewrite with llists. apply bisim1.
  apply hh. apply H1.
Qed.

Lemma general_omega_and_append:
  forall (A:Set) (l l' : LList A),
    bisimilar (LAppend _ l (general_omega _ (LNil _) l')) (general_omega _ l l').
  cofix hh.
  intros. case l. autorewrite with llists. apply equiv_bisimilar.
  intros; autorewrite with llists. apply bisim1.  rewrite <- general_omega_shoots_again.
  apply hh.
Qed.

Lemma omega_lappend:
  forall (A:Set) (u:LList A),
    bisimilar (omega _ u) (LAppend _ u (omega _ u)).
  unfold omega. intros. pattern (general_omega A u u). rewrite <- general_omega_shoots_again.
  pose general_omega_and_append.
  pose (b A u u).
  apply equiv_bisimilar. pattern (general_omega A (LNil A) u) at 2. rewrite general_omega_shoots_again. apply b0.
Qed.

Section LTL.
  Variables (A:Set) (a b c:A).
  Definition satisfies (l:LList A) (P: LList A -> Prop) := P l.

  Hint Unfold satisfies : llists.

  Inductive Atomic (At: A -> Prop) : LList A -> Prop :=
    Atomic_intro:
      forall (a:A) (l:LList A), At a -> Atomic At (LCons _ a l).

  Inductive Next (P : LList A -> Prop) : LList A -> Prop :=
    Next_intro :
      forall (a:A) (l:LList A), P l -> Next P (LCons _ a l).

  Hint Resolve Atomic_intro Next_intro : llists.

  Theorem Next_example :
    satisfies (LCons _ a (repeat _ b)) (Next (Atomic (eq b))).
    unfold satisfies. apply Next_intro. LList_unfold2 (repeat _ b). auto with llists.
  Qed.

  Inductive Eventually (P:LList A -> Prop ) : LList A -> Prop :=
  | Eventually_here :
      forall (a:A) (l:LList A), P (LCons _ a l) -> Eventually P (LCons _ a l)
  | Eventually_further :
      forall (a:A) (l:LList A), Eventually P l ->
                                Eventually P (LCons _ a l).

  CoInductive Always (P : LList A -> Prop) : LList A -> Prop :=
    Always_LCons :
      forall (a:A) (l:LList A),
        P (LCons _ a l) -> Always P l -> Always P (LCons _ a l).

Hint Resolve Eventually_here Eventually_further: llists.
  
  Lemma always_a :
    satisfies (repeat _ a) (Always (Atomic (eq a))).
    unfold satisfies. cofix hh.
    LList_unfold2 (repeat _ a).
    apply Always_LCons. apply Atomic_intro. reflexivity.
    apply hh. Guarded.
  Qed.

  Definition F_infinite (P:LList A -> Prop) : LList A -> Prop :=
    Always (Eventually P).

  Theorem always_a' :
      F_infinite (Atomic (eq a)) (omega _ (LCons _ a (LCons _ b (LNil _)))).
    unfold F_infinite.
    cofix hh.
    LList_unfold2 (omega _ (LCons _ a (LCons _ b (LNil _)))).
    apply Always_LCons. auto with llists.
    rewrite general_omega_LCons. apply Always_LCons. apply Eventually_further.
    rewrite general_omega_shoots_again. rewrite general_omega_LCons. apply Eventually_here. apply Atomic_intro. trivial. rewrite general_omega_shoots_again. apply hh. Guarded.
  Qed.

  Definition G_Infinite (P:LList A -> Prop) : LList A -> Prop :=
    Eventually (Always P).

  Lemma LAppend_G_Infinite :
    forall (P:LList A -> Prop) (u v :LList A),
      Finite _ u -> satisfies v (G_Infinite P) ->
      satisfies (LAppend _ u v) (G_Infinite P).
  Abort.

  Lemma LAppend_G_Infinite_R :
    forall (P:LList A -> Prop) (u v : LList A),
      Finite _ u -> satisfies (LAppend _ u v) (G_Infinite P) ->
      satisfies v (G_Infinite P).
  Abort.

End LTL.

Record automaton : Type :=
  mk_auto {
      states : Set ;
      actions : Set ;
      initial : states ;
      transitions : states -> actions -> list states
    }.

Definition deadlock (A:automaton) (q:states A) :=
  forall a:actions A, @transitions A q a = nil.

Require Import List.

CoInductive Trace (A:automaton) : states A -> LList (actions A) -> Prop :=
| empty_trace :
    forall q: states A, deadlock A q -> Trace A q (LNil _)
| lcons_trace :
    forall (q q' :states A) (a:actions A) (l:LList (actions A)),
      In q' (transitions A q a) -> Trace A q' l -> Trace A q' (LCons _ a l).

Set Implicit Arguments.

(* states *)
Inductive st : Set := q0 | q1 | q2.

(* actions *)
Inductive acts : Set := a | b.

(* transitions *)
Definition trans (q:st) (x:acts) : list st :=
  match q, x with
    | q0, a => cons q1 nil
    | q0, b => cons q1 nil
    | q1, a => cons q2 nil
    | q2, b => cons q2 (cons q1 nil)
    | _, _ => nil
  end.

Print mk_auto.

Definition A1 := mk_auto _ _ q0 trans.

Theorem Infinite_bs :
  forall (q:st) (t:LList acts),
    Trace A1 q t ->
    satisfies _ t (F_infinite _ (Atomic _ (eq b))).
  unfold satisfies.
  unfold F_infinite. cofix hh.
  intros. inversion H.
Abort.

