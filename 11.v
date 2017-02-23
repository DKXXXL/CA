Require Import ZArith.
Open Scope Z_scope.

Inductive Z_btree : Set :=
| Z_leaf : Z_btree
| Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

Inductive occ (n:Z): Z_btree -> Prop :=
| occ_root : forall t1 t2: Z_btree, occ n (Z_bnode n t1 t2)
| occ_left : forall (m:Z) (t1 t2: Z_btree), occ n t1 -> occ n (Z_bnode m t1 t2)
| occ_right : forall (m:Z)(t1 t2: Z_btree), occ n t2 -> occ n (Z_bnode m t1 t2).

Theorem naive_occ_dec:
  forall (n:Z) (t: Z_btree), {occ n t} + {~occ n t}.
  intros n t. generalize n.
  elim t. intros. right. cut(forall x, x = Z_leaf -> ~ occ n0 x).
  intros. apply (H Z_leaf). trivial.
  unfold not. intros. generalize H. elim H0; intros; discriminate.
  intros.
  elim (H n0). intros.
  elim (H0 n0). intros. left. apply occ_left. auto.
  intros. left; apply occ_left; auto.
  elim (H0 n0). intros. left; apply occ_right; auto.
  intros.
  case (Z_eq_dec n0 z). intros. left. rewrite <- e. apply occ_root.
  intros. right.
  cut( forall x y u, x = z0->y = z1 -> u = Z_bnode z x y -> ~occ n0 u); intros. apply (H1 z0 z1 (Z_bnode z z0 z1)); trivial.
  unfold not; intros; generalize H1 H2 H3. elim H4. intros. injection H7. intros; contradiction.
  intros. injection H9. intros. rewrite H11 in H5. rewrite H1 in H5. apply b0; apply H5.
  intros. injection H9. intros. rewrite H10 in H5; rewrite H2 in H5. apply b; apply H5.
Qed.


Print naive_occ_dec.

Inductive min (n:Z) (t:Z_btree) : Prop :=
  min_intro : (forall p:Z, occ p t -> n < p) -> min n t.

Inductive maj (n:Z) (t:Z_btree) : Prop :=
  maj_intro : (forall p:Z, occ p t -> p < n) -> maj n t.

Inductive search_tree : Z_btree -> Prop :=
| leaf_search_tree : search_tree Z_leaf
| bnode_search_tree :
    forall (n:Z) (t1 t2:Z_btree),
      search_tree t1 -> search_tree t2 -> maj n t1 -> min n t2 -> search_tree (Z_bnode n t1 t2).

Definition occ_dec_spec (p:Z) (t:Z_btree) : Set :=
  search_tree t -> {occ p t} + {~occ p t}.

Inductive INSERT (n:Z) (t t':Z_btree) : Prop :=
  insert_intro :
    (forall p:Z, occ p t -> occ p t') -> occ n t' ->
    (forall p:Z, occ p t' -> occ p t \/ n = p) -> search_tree t' -> INSERT n t t'.

Definition insert_spec (n:Z) (t:Z_btree) : Set :=
  search_tree t -> {t' :Z_btree | INSERT n t t'}.

Inductive RM (n:Z) (t t' :Z_btree) : Prop :=
  rm_intro :
    ~occ n t' ->
    (forall p : Z, occ p t' -> occ p t) ->
    (forall p : Z, occ p t -> occ p t' \/ n = p) ->
    search_tree t' ->
    RM n t t'.

Definition rm_spec (n:Z) (t:Z_btree) : Set :=
  search_tree t -> {t' : Z_btree | RM n t t'}.

Section search_tree_basic_properties.
  Variable n:Z.
  Variable t1 t2: Z_btree.
  Hypothesis se: search_tree (Z_bnode n t1 t2).

  Lemma search_tree_l:
    search_tree t1.

    remember t1 as x; remember t2 as y; remember (Z_bnode n x y) as z.
    generalize Heqx Heqy Heqz. elim se.
    intros _ _ h1; discriminate h1.
    intros. injection Heqz0. intros _ h; rewrite h in H; auto.
  Qed.

  Lemma search_tree_r:
    search_tree t2.
    remember t1 as x; remember t2 as y; remember (Z_bnode n x y) as z.
    generalize Heqx Heqy Heqz. elim se.
    intros _ _ h; discriminate h.
    intros. injection Heqz0. intros h; rewrite h in H1; auto.
  Qed.

  Lemma maj_l : maj n t1.
    remember t1 as x; remember t2 as y; remember (Z_bnode n x y) as z.
    generalize Heqx Heqy Heqz.
    elim se. intros _ _ h1; discriminate h1.
    intros. injection Heqz0. intros _ h h1; rewrite h in H3; rewrite h1 in H3; assumption.
  Qed.

  Lemma min_r :min n t2.
    remember t1 as x; remember t2 as y; remember (Z_bnode n x y) as z.
    generalize Heqz Heqy Heqz.
    elim se. intro; discriminate.
    intros. injection Heqz1. intros h _ h1; rewrite h in H4; rewrite h1 in H4; assumption.
  Qed.

  Lemma not_right :
    forall p:Z, p <= n -> ~occ p t2.
    remember t1 as x; remember t2 as y; remember (Z_bnode n x y) as z.
    generalize Heqz Heqy Heqz.
    elim se. intro; discriminate.
    intros. injection Heqz0. intros. rewrite H8 in H4; rewrite H6 in H4.
    elim H4. intros. unfold not. intros h; pose (H9 p h). omega.
  Qed.

  Lemma not_left :
    forall p:Z, p >= n -> ~occ p t1.
    remember t1 as x; remember t2 as y; remember (Z_bnode n x y) as z.
    generalize Heqz Heqy Heqz.
    elim se. intro; discriminate.
    intros. injection Heqz0. intros. rewrite H7 in H3; rewrite H8 in H3.
    elim H3. unfold not; intros. pose (H9 p H10); omega.
  Qed.

  Lemma go_left:
    forall p:Z, occ p (Z_bnode n t1 t2) -> p < n -> occ p t1.
    remember t1 as x; remember t2 as y; remember (Z_bnode n x y) as z.
    generalize Heqz Heqy Heqz.
    elim se. intro; discriminate.
    intros. generalize Heqx Heqy Heqz. rewrite Heqz1 in H5; rewrite <- Heqz in H5.
    elim H5. intros. injection Heqz2. intros; omega.
    intros. injection Heqz2. intros _ h _; rewrite h in H7; assumption.
    assert (p <= n). omega.
    pose (not_right p H7). intros. injection Heqz2. intros h; rewrite h in H8; rewrite Heqy1 in H8; contradiction.
  Qed.

  Lemma go_right :
    forall p:Z, occ p (Z_bnode n t1 t2) -> p > n -> occ p t2.
    remember t1 as x; remember t2 as y; remember (Z_bnode n x y) as z.
    generalize Heqz Heqy Heqz.
    elim se. intro; discriminate.
    intros. rewrite Heqz0 in H5; rewrite <- Heqz in H5.
    generalize Heqx Heqy Heqz. elim H5. intros. injection Heqz2; omega.
    intros. injection Heqz2; intros. rewrite H10 in H7.
    assert (p >= n). omega.
    pose (not_left p H12). rewrite Heqx0 in H7. contradiction.
    intros. injection Heqz2; intros. rewrite H9 in H7; assumption.
  Qed.

  Lemma not_occ_leaf:
    forall x, ~occ x Z_leaf.
    unfold not.
    remember Z_leaf as y.
    intros; generalize Heqy. elim H; intros; discriminate.
Qed.
    
End search_tree_basic_properties.

Hint Resolve occ_root occ_left occ_right go_left go_right not_left not_right search_tree_l search_tree_r maj_l min_r : searchtrees.

Definition occ_dec : forall (p:Z) (t:Z_btree) , occ_dec_spec p t.
  unfold occ_dec_spec.
  refine
    (fix occ_dec (p:Z) (t:Z_btree) {struct t} :=
       match t return occ_dec_spec p t with
         | Z_bnode n leftt rightt =>
           (fun hsearch_tree =>
              match (Z_le_gt_dec p n) with
                | left Hle =>
                  match (Z_le_lt_eq_dec p n Hle) with
                    | left Hlt =>
                      match (occ_dec p leftt _) with
                        | left Hfound => left _ _
                        | right HnotFound => right _ _
                      end
                    | right Heq => left _ _
                  end
                | right Hgt =>
                  match (occ_dec p rightt _) with
                    | left Hfound => left _ _
                    | right Hnotfound => right _ _
                  end
              end)
         | Z_leaf => (fun h => right _ _)
       end); try (eauto with searchtrees).
  remember Z_leaf as x. unfold not; intros ; generalize Heqx.
  elim H; intros; discriminate.
  rewrite Heq; apply occ_root.
Qed.

  
  Lemma insert_leaf :
    forall n:Z, INSERT n Z_leaf (Z_bnode n Z_leaf Z_leaf).
    intros.
    apply insert_intro.
    intros. apply occ_left; assumption.
    apply occ_root.
    remember Z_leaf as x.  remember (Z_bnode n x x) as y.     
    intros. generalize Heqx Heqy; elim H.
    intros. right; injection Heqy0; auto.
    intros; pose (not_occ_leaf p). injection Heqy0. intros. rewrite H3 in H0; rewrite Heqx0 in H0; contradiction.
    intros. injection Heqy0. intros. rewrite H2 in H0; left; assumption.
    apply bnode_search_tree; try apply leaf_search_tree.
    apply maj_intro. intros; pose (not_occ_leaf p); contradiction.
    apply min_intro. intros; pose (not_occ_leaf p); contradiction.
Qed.


  Lemma insert_l :
    forall (n p :Z) (t1 t'1 t2:Z_btree),
      n < p ->
      search_tree (Z_bnode p t1 t2) ->
      INSERT n t1 t'1 ->
      INSERT n (Z_bnode p t1 t2) (Z_bnode p t'1 t2).

    intros.
    apply insert_intro.
    intros.
    remember t1 as x; remember t2 as y; remember (Z_bnode p x y) as z.
    generalize Heqx Heqy Heqz. elim H2.
    intros. injection Heqz0. intros. rewrite H5. apply occ_root.
    intros. injection Heqz0. intros. rewrite H6 in H3; rewrite Heqx0 in H3; rewrite Heqx0 in H1.
    apply occ_left. elim H1. intros. apply H8. assumption.
    intros. injection Heqz0. intros. rewrite H5 in H3. apply occ_right. assumption.
    elim H1. intros. apply occ_left. assumption.
    intros. remember t'1 as x; remember t2 as y; remember (Z_bnode p x y) as z.
    generalize Heqx Heqy Heqz. elim H2.
    intros. injection Heqz0. intros; left. rewrite H5; apply occ_root.
    intros.  elim H1. intros.  injection Heqz0. intros. rewrite H10 in H3. pose (H7 p0 H3).
    elim o. intros. left. apply occ_left; assumption. intros; right; assumption.
    intros. injection Heqz0; intros; left. apply occ_right; rewrite H5 in H3; assumption.
    remember (Z_bnode p t1 t2) as z. generalize Heqz; elim H0. intros; discriminate.
    intros.  apply bnode_search_tree. injection Heqz0. intros. rewrite H9 in H2.
    elim H1. intros. assumption.
    injection Heqz0; intros. rewrite H8 in H4; assumption.
    injection Heqz0; intros. rewrite H10 in H6; rewrite H9 in H6. apply maj_intro.
    intros. elim H6. intros. pose (H12 p0). elim H1. intros. elim (H15 p0 H11). apply H12. intros. rewrite <- H17; auto.
    injection Heqz0; intros. rewrite H10 in H7; rewrite H8 in H7; auto.
  Qed.

  Lemma insert_r:
    forall (n p:Z) (t1 t2 t'2:Z_btree),
      n>p ->
      search_tree (Z_bnode p t1 t2) ->
      INSERT n t2 t'2 ->
      INSERT n (Z_bnode p t1 t2) (Z_bnode p t1 t'2). 

    intros. apply insert_intro. intros.
    remember t1 as x; remember t2 as y; remember (Z_bnode p x y) as z. generalize Heqx Heqy Heqz.
    elim H2. intros. injection Heqz0. intros. rewrite H5; apply occ_root.
    intros. injection Heqz0; intros. rewrite H6 in H3. eauto with searchtrees.
    intros. injection Heqz0. intros. rewrite H5 in H3; rewrite Heqy0 in H3; rewrite Heqy0 in H1. apply occ_right. elim H1. intros; auto.
    elim H1. intros; apply occ_right; auto.
    intros. remember t1 as x;remember t'2 as y; remember (Z_bnode p x y) as z; generalize Heqx Heqy Heqz; elim H2. intros. injection Heqz0. intros. rewrite H5. left; apply occ_root.
    intros. left. injection Heqz0; intros. rewrite H6 in H3; eauto with searchtrees.
    intros. injection Heqz0; intros. rewrite H5 in H3; rewrite Heqy0 in H3. rewrite Heqy0 in H1. elim H1. intros. pose (H10 p0 H3). elim o; [eauto with searchtrees | auto].
    apply bnode_search_tree; try eauto with searchtrees.
    elim H1. intros; auto.
    apply min_intro. intros. elim H1. intros. pose (H5 p0 H2).  elim o. intros. remember t1 as x; remember t2 as y; remember (Z_bnode p x y) as z. generalize Heqx Heqy Heqz. elim H0;intros; try discriminate. injection Heqz0. intros. rewrite H16 in H13. elim H13. intros. rewrite H14 in H17. pose (H17 p0); auto.
    intros hh; rewrite hh in H; omega.
  Qed.

  Lemma insert_eq :
    forall (n:Z) (t1 t2:Z_btree),
      search_tree (Z_bnode n t1 t2) ->
      INSERT n (Z_bnode n t1 t2) (Z_bnode n t1 t2).

    intros.
    apply insert_intro; try auto ; try eauto with searchtrees; try auto.
  Qed.

  Hint Resolve insert_leaf insert_l insert_r insert_eq : searchtrees.

  Definition insert_bst : forall (n:Z) (t:Z_btree), insert_spec n t.
    refine
      (fix insert_bst (n:Z) (t: Z_btree) {struct t} :=
         match t return insert_spec n t with
           | Z_leaf => fun h =>  _
           | Z_bnode p leftt rightt =>
             (fun Hst =>
                match (Z_le_gt_dec n p) with
                  | left Hle =>
                    match (Z_le_lt_eq_dec n p Hle) with
                      | left Hlt =>
                        match insert_bst n leftt _ with
                          | exist t' h => _
                        end
                      | right Heq => _ 
                    end
                  | right Hgt =>
                    match insert_bst n rightt _ with
                      | exist t' h => _
                    end
                end)
         end); eauto with searchtrees.
    rewrite Heq. eauto with searchtrees.
  Qed.


  Inductive RMAX (t t' : Z_btree) (n:Z) :Prop :=
    rmax_intro :
      occ n t ->
      (forall p:Z, occ p t -> p <= n) ->
      (forall q:Z, occ q t' -> occ q t) ->
      (forall q:Z, occ q t -> occ q t' \/ n = q) ->
      ~occ n t' -> search_tree t' -> RMAX t t' n.

  Definition rmax_sig (t:Z_btree) (q:Z):=
    {t' : Z_btree | RMAX t t' q}.



  Import List.



  Definition list2tree_spec (l:list Z) : Set :=
    {t' : Z_btree | search_tree t' /\ (forall p :Z, In p l <-> occ p t')}.

  Definition list2tree_aux_spec (l:list Z) (t:Z_btree) :=
    search_tree t ->
    {t' :Z_btree | search_tree t' /\
                   (forall p:Z, In p l \/ occ p t <-> occ p t')}.



  Definition list2tree_aux:
    forall (l:list Z) (t:Z_btree), list2tree_aux_spec l t.

    refine
      (fix list2tree_aux (l:list Z) :
         forall t :Z_btree, list2tree_aux_spec l t :=
         fun t =>
           match l return list2tree_aux_spec l t with
             | nil => fun s =>  exist _ t _
             | cons p l' =>
               fun s =>
                 match insert_bst p t s with
                   | exist t' _ =>
                     match list2tree_aux l' t' _ with
                       | exist t'' _ => exist _ t'' _
                     end
                 end
           end).
    split; try tauto.
    split; intros. elim H. intros h; elim h. trivial.
    right; trivial.
    elim i. intros; auto.
    split. elim a; auto.
    elim a. split; intros.
    elim H1. intros; apply H0. elim H2. intros; right. elim i. rewrite H3; auto.
    tauto.
    elim i. intros. apply H0. right; apply H2; auto.
    case (Z_eq_dec p0 p). intros hh; left; rewrite hh; simpl; trivial.
    left; trivial.
    intros. elim (H0 p0). intros. elim (H3 H1). intros. left; simpl; right; auto. elim i. intros. elim (H6 p0 H8); try tauto. intros h; rewrite h in n; elim (n (eq_refl p0)).
  Defined.

 
    
  
  
  Definition list2tree_aux_2 :
    forall (l:list Z) (t:Z_btree), list2tree_aux_spec l t.

    refine
      (fix list2tree_aux (l:list Z)  :=
         fun t =>
           
           match l return list2tree_aux_spec l t with
             | nil => fun s => exist _ t _
             | cons x l' =>
               fun Hst =>
                 match insert_bst x t _ with
                   | exist t' Hins =>
                     match list2tree_aux l' t' _ with
                       | exist rett Hret => exist _ rett _
                     end
                 end
           end); eauto with searchtrees.
    split; try auto.
    intros; split. intros.
    elim H.
    intros h; elim h.
    trivial.
    intros; right; auto.
    elim Hins. intros; auto.
    split.
    elim Hret; auto.
    elim Hret; split; intros.
    apply (H0 p). elim H1. intros. simpl in H2. elim H2. elim Hins. intros. rewrite <- H7; right; auto.
    tauto.
    elim Hins. intros. right; apply (H2 p H6).
    elim (H0 p). intros. elim (H3 H1). intros; left; simpl; right;auto.
    elim Hins. intros. elim (H6 p H8). intros; try tauto.
    intros h; rewrite h; simpl; try tauto.
  Defined.

  Definition list2tree:
    forall l:list Z, list2tree_spec l.
    refine
      (fun (l:list Z) =>
         match (list2tree_aux_2 l Z_leaf _) return list2tree_spec l with
           | exist t h => exist _ t _
         end); eauto with searchtrees.
    apply leaf_search_tree.
    elim h. split; try tauto.
    intros. elim (H0 p). intros. split. intros; try tauto.
    intros h1; elim (H2 h1); try auto. intro. pose (not_occ_leaf). unfold not in n. elim (n p H3).
  Defined.


  Theorem naive_occ_dec_re:
    forall (n:Z) (t:Z_btree), {occ n t}+ {~occ n t}.
    intros. elim t. right; apply not_occ_leaf.
    intros. elim H. intros; left. apply occ_left; trivial.
    elim H0. intros; left; apply occ_right; trivial.
    case (Z_eq_dec n z).
    intros h; intros; left; rewrite  h; apply occ_root.
    intros. right. unfold not; intros. inversion H1.
  Abort.

  