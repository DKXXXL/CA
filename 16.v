Require Export Zdiv.

Axiom verify_divide :
  forall m p:nat,
    0<m -> 0 < p -> (exists q:nat, m = q*p) -> (Z_of_nat m mod Z_of_nat p = 0)%Z.

Axiom divisor_smaller :
  forall m p:nat,
    0<m -> forall q:nat, m = q*p -> q <= m.

Fixpoint check_range (v:Z) (r:nat) (sr:Z) {struct r} : bool :=
  match r with
    | O => true
    | S r' =>
      match (v mod sr)%Z with
        | Z0 => false
        | _ => check_range v r' (Zpred sr)
      end
  end.

Definition check_primality (n:nat) :=
  check_range (Z_of_nat n) (pred (pred n)) (Z_of_nat (pred n)).

Eval compute in (check_primality 2333).

Axiom check_correct :
  forall p:nat, 0 < p -> check_primality p = true ->
                ~(exists k:nat, k <> 1 /\ k <> p /\ (exists q:nat, p = q*k)).

Axiom check_range_correct :
  forall (v:Z) (r:nat) (rz:Z),
    (0<v)%Z ->
    Z_of_nat (S r) = rz ->
    check_range v r rz = true ->
    ~(exists k:nat, k <= S r /\ k <> 1 /\ (exists q:nat, Zabs_nat v = q*k)).

Theorem prime_2333:
  ~(exists k:nat, k <> 1 /\ k <> 2333 /\ (exists q:nat,  2333 = q*k)).
Abort.

Theorem reflextion_test:
  forall x y z t u:nat, x + (y + z + (t + u)) = x + y + (z + (t+u)).

  intros; repeat rewrite plus_assoc; auto.
Qed.

Inductive bin : Set := node : bin -> bin -> bin | leaf : nat -> bin.

Fixpoint flatten_aux (t fin:bin) {struct t} : bin :=
  match t with
    | node t1 t2 => flatten_aux t1 (flatten_aux t2 fin)
    | x => node x fin
  end.

Fixpoint flatten (t:bin) : bin :=
  match t with
    | node t1 t2 => flatten_aux t1 (flatten t2)
    | x => x
  end.

Fixpoint bin_nat (t:bin) : nat :=
  match t with
    | node t1 t2 => bin_nat t1 + bin_nat t2
    | leaf n => n
  end.

Theorem flatten_aux_valid :
  forall t t':bin,
    bin_nat t + bin_nat t' = bin_nat (flatten_aux t t').
  intro. elim t; auto.
  intros. simpl. rewrite <- plus_assoc. rewrite H0. rewrite H. auto.
Qed.


Theorem flatten_valid :
  forall t:bin,
    bin_nat t = bin_nat (flatten t).

  intro. elim t; auto.
  intros. simpl. rewrite H. rewrite H0. pose (flatten_aux_valid (flatten b) (flatten b0)). rewrite <- flatten_aux_valid. rewrite H. auto.
Qed.

Fixpoint righten (t:bin) {struct t} : bin :=
  match t with
(*    | node  t1 t2 => (fun x => righten (node t1 x)) (righten t2) 
 *)
    | node t1 t2 =>
      match (righten t2) with
        | newr => match righten t1 with
                    | newl => let fix totheend t'' :=
                                  match t'' with
                                    | (leaf x) => node (leaf x) newr
                                    | node y k => node y (totheend k)
                                  end in (totheend newl)

                  end
      end
    | leaf t => leaf t
  end.
                              
Eval compute in (righten (node (leaf 1) (node (node (leaf 2) (leaf 3)) (leaf 4)))).

Theorem flatten_valid_2 :
  forall t t' : bin,
    bin_nat (flatten t) = bin_nat (flatten t') ->
    bin_nat t = bin_nat t'.
  intros.
  rewrite flatten_valid. rewrite H. symmetry. apply flatten_valid.
Qed.

Ltac model v:=
  match v with
    | (?X1 + ?X2) =>
      let r1 := model X1 in
      let r2 := model X2 in
      constr:(node r1 r2)
    | ?X1 => constr: (leaf X1)
  end.


Ltac assoc_eq_nat :=
  match goal with
    | [ |- (?X1 = ?X2 :> nat) ] =>
      let term1 := model X1 in
      let term2 := model X2 in
      (change (bin_nat term1 = bin_nat term2);
       apply flatten_valid_2;
       lazy beta iota zeta delta [flatten flatten_aux bin_nat];
       auto)
  end.


Theorem reflection_test'' :
  forall x y z t u:nat,
    x + (y + z + (t+u)) = x+y + (z + (t+u)).
  intros. assoc_eq_nat.
Qed.

Require Import List.

Section assoc_eq.

  Variable (A:Set) (f:A -> A -> A)
           (assoc : forall x y z:A, f x (f y z) = f (f x y) z).
  Fixpoint bin_A (l:list A) (def:A) (t:bin) {struct t} :A :=
    match t with
      | node t1 t2 => f (bin_A l def t1) (bin_A l def t2)
      | leaf n => nth n l def
    end.

  Theorem flatten_aux_valid_A :
    forall (l:list A) (def :A ) (t t':bin),
      f (bin_A l def t) (bin_A l def t') =
      bin_A l def (flatten_aux t t').
    intros l def t. elim t; intros; auto.
    simpl.
  Abort.

  