Require Import Bool Arith List.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* Inductive tuple (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X). *)


Definition table_T (tuple_T: Type) := list tuple_T.
Definition non_empty {tuple_T: Type} (l: table_T tuple_T) :=
  match l with
   | nil => False
   | h :: t => True
  end.


Fixpoint fold_f {tuple_T aggr_T: Type} 
(f : tuple_T->aggr_T->aggr_T) (l : table_T tuple_T) (b : aggr_T) : aggr_T :=
  match l with
  | nil => b
  | h :: t => f h (fold_f f t b)
  end.

Fixpoint filter {tuple_T: Type} 
(f : tuple_T -> bool) (l : table_T tuple_T) : table_T tuple_T:=
  match l with
  | nil => nil
  | h :: t => if f h then h :: (filter f t) else (filter f t)
  end.

Definition agg_commutative {tuple_T aggr_T : Type} 
(agg : tuple_T->aggr_T->aggr_T) (initv: aggr_T) :=
  forall (t1 t2: tuple_T) (initv: aggr_T), agg t2 (agg t1 initv) = agg t1 (agg t2 initv).
  
Definition agg_assumption {tuple_T aggr_T : Type} 
(len : nat) (agg : tuple_T->aggr_T->aggr_T) (initv : aggr_T) := 
forall (t : table_T tuple_T) (tup : tuple_T) , 
(length t = len /\ non_empty t) -> (exists (t1 : table_T tuple_T), length t1 = len /\ 
                        (fold_f agg (tup :: t) initv) = (fold_f agg (t1) initv)).

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.


Lemma gt_S_1 : forall (n: nat), S n >= 1.
  Proof. intros. induction n. auto. auto. Qed.

Theorem agg_assumption_small_model : 
forall (tuple_T aggr_T : Type)  (len : nat) (agg : tuple_T->aggr_T->aggr_T) (initv : aggr_T),
(len >= 1 /\ (agg_commutative agg initv) /\ (agg_assumption 1 agg initv)) 
    -> (agg_assumption len agg initv).
Proof.
intros.
destruct H.
destruct H0.
induction len.
  + inversion H.
  + induction len.
    { exact H1. }
    { unfold agg_assumption.
      intros. simpl. destruct t.
      { destruct H2. simpl in H2. discriminate. }
      { unfold agg_assumption in IHlen. destruct H2 as [H2 Hnon_empty]. 
        assert (Hlength_helper: length t0 = S len). { simpl in H2. inversion H2. reflexivity. }
        assert (Hexists: (exists t3 : table_T tuple_T, 
          length t3 = S len /\ fold_f agg (t :: t0) initv = fold_f agg t3 initv)).
        (* apply only works like (A->B and try to prove B), If assumptions has A->B and A
        use "assert" to get B into assumption. *) 
          { apply IHlen. apply gt_S_1. 
            split. simpl in H2. inversion H2. reflexivity.
            destruct t0. simpl in Hlength_helper. discriminate. auto.  }
        destruct Hexists as [t3 H5]. (* destruct convert exists xx in H4 into concrete table *)
        destruct H5.
        rewrite H4. 
        unfold agg_commutative in H. 
        exists (tup :: t3).
        split. { simpl.  rewrite H3. reflexivity. }
               { simpl. reflexivity. } }
    } 
Qed.

Lemma length_concat :
forall (X: Type) (t1 t2: table_T X), length (t1 ++ t2) = length t1 + length t2.
Proof.
induction t1. 
  + simpl. reflexivity.
  + intros. simpl. apply f_equal. apply IHt1. 
Qed.

(*
Lemma list_size_zero : 
forall (X: Type) (t1 t2: table_T X), length (t1 ++ t2) <= 0 -> (length t1 = 0) /\ (length t2 = 0).
Proof.
intros.
rewrite length_concat in H.
split.
  + induction t1. simpl. reflexivity. simpl in H. 
    assert (Hx: ~ (S (length t1 + length t2) <= 0)). simpl. apply gt_Sn_O. contradiction.
  + induction t2. simpl. reflexivity. simpl in H. rewrite plus_comm in H. discriminate.
Qed.
*)
      

Lemma helper_contradict_nonempty_length0 :
  forall {tuple_T: Type} (table: table_T tuple_T), ((non_empty table) /\ (length table = 0)) -> False.
Proof. intros. destruct H. induction table. simpl in H. contradiction.
  simpl in H0. discriminate. Qed.

 
(* f(agg(T+U))=false <-> f(agg(T))=false and f(agg(U))=false *)
Definition assumption1 {tuple_T aggr_T : Type} (len : nat) (agg : tuple_T->aggr_T->aggr_T)  (initv : aggr_T) (f : aggr_T -> bool):= 
forall (t3 t4 : table_T tuple_T), 
  (length (t3 ++ t4) <= len /\ non_empty t3 /\ non_empty t4) -> ( f (fold_f agg (t3 ++ t4) initv) = false) 
          <-> ((f (fold_f agg t3 initv) = false) /\ (f (fold_f agg t4 initv) = false)).

Lemma helper_add_le_zero :
  forall (a b : nat), a + b <= 0 -> (a = 0 /\ b = 0).
Proof. intros. destruct a. split. reflexivity.  induction b. reflexivity. inversion H. 
split. inversion H. inversion H. Qed.

Lemma helper_le_split :
  forall (a b : nat), a <= S b -> (a <= b \/ a = S b).
Admitted.

Lemma helper_fold_nil : 
  forall (tuple_T aggr_T : Type) (agg : tuple_T->aggr_T->aggr_T) (initv: aggr_T) (t : table_T tuple_T),
    fold_f agg (t++nil) initv = fold_f agg t initv.
Proof. induction t. simpl. reflexivity. simpl. rewrite IHt. reflexivity. Qed.

Lemma helper_fold_append_nil:
  forall (tuple_T aggr_T : Type) (agg : tuple_T->aggr_T->aggr_T) (initv: aggr_T) (table : table_T tuple_T) (t : tuple_T),
    agg_commutative agg initv -> agg t (fold_f agg table initv) = fold_f agg (table++t::nil) initv.
Proof. intros. induction table. simpl. reflexivity.
  simpl. rewrite <- IHtable. unfold agg_commutative in H. rewrite H. reflexivity.
Qed.

Lemma helper_fold_append_value:
  forall (tuple_T aggr_T : Type) (agg : tuple_T->aggr_T->aggr_T) (initv: aggr_T) 
        (table1 table2: table_T tuple_T) (t : tuple_T),
    agg_commutative agg initv -> agg t (fold_f agg (table1++table2) initv) = fold_f agg (table1++t::table2) initv.
Proof. intros. induction table1. simpl. reflexivity. 
    simpl. rewrite <- IHtable1. unfold agg_commutative in H. rewrite H. reflexivity.
Qed.

Lemma aggr_associative_table :
  forall (tuple_T aggr_T : Type) (agg : tuple_T->aggr_T->aggr_T) (initv: aggr_T),
  agg_commutative agg initv -> 
    (forall (table1 table2 table3: table_T tuple_T), 
    (fold_f agg (table1 ++ table2 ++ table3) initv) = (fold_f agg ((table1 ++ table2) ++ table3) initv)).
Proof. intros. induction table1. simpl. reflexivity.
  simpl. rewrite IHtable1.
     reflexivity. Qed.

Lemma aggr_commutative_table : 
forall (tuple_T aggr_T : Type) (agg : tuple_T->aggr_T->aggr_T) (initv: aggr_T),
  agg_commutative agg initv -> 
  (forall (table1 table2: table_T tuple_T), 
    (fold_f agg (table1 ++ table2) initv) = (fold_f agg (table2 ++ table1) initv)) .
Proof. intros. unfold agg_commutative in H.
induction table1. 
  + simpl. induction table2. simpl. reflexivity. simpl. rewrite IHtable2. reflexivity.
  + simpl. rewrite IHtable1. induction table1.
      { rewrite helper_fold_nil. apply helper_fold_append_nil. unfold agg_commutative. exact H. } 
      { apply helper_fold_append_value. unfold agg_commutative. exact H.   }
Qed.

(* fold_f agg ((t0 :: table2) ++ t :: t1 :: table1) initv =
fold_f agg ((t0 :: table2) ++ tabley) initv *)
Lemma aggr_sub_eq_to_eq : 
  forall (tuple_T aggr_T : Type) (agg : tuple_T->aggr_T->aggr_T) (initv: aggr_T) 
    (t1 t2 t3 : table_T tuple_T),
  agg_commutative agg initv -> 
    (fold_f agg t1 initv = fold_f agg t2 initv -> 
      fold_f agg (t1++t3) initv = fold_f agg (t2++t3) initv).
Proof. intros. induction t3. rewrite helper_fold_nil. rewrite helper_fold_nil. exact H0.
rewrite aggr_commutative_table with (table1 := t2). rewrite aggr_commutative_table.
simpl. rewrite aggr_commutative_table. rewrite IHt3. rewrite aggr_commutative_table.
reflexivity. auto. auto. auto. auto.
Qed.

      
Lemma aggr_associative_table_extended_132 : 
forall (tuple_T aggr_T : Type) (agg : tuple_T->aggr_T->aggr_T) (initv: aggr_T),
  agg_commutative agg initv -> 
  (forall (table1 table2 table3: table_T tuple_T), 
    (fold_f agg (table1 ++ table2 ++ table3) initv) = (fold_f agg (table1 ++ table3 ++ table2) initv)) .
Admitted.

Lemma aggr_associative_table_extended_21_3 : 
forall (tuple_T aggr_T : Type) (agg : tuple_T->aggr_T->aggr_T) (initv: aggr_T),
  agg_commutative agg initv -> 
  (forall (table1 table2 table3: table_T tuple_T), 
    (fold_f agg ((table1 ++ table2) ++ table3) initv) = (fold_f agg ((table2 ++ table1) ++ table3) initv)).
Admitted.



Lemma aggr_partial_collapse :
forall (tuple_T aggr_T : Type)  (len : nat) (agg : tuple_T->aggr_T->aggr_T) (initv : aggr_T)
        (table some_table : table_T tuple_T) (t : tuple_T),
  (agg_assumption len agg initv /\ agg_commutative agg initv) -> 
  (length table = len /\ non_empty table) -> (exists (t1 : table_T tuple_T), length t1 = len /\ 
           (fold_f agg (t :: table ++ some_table) initv) = (fold_f agg (t1 ++ some_table) initv)).
Admitted.

Lemma length_commutative :
  forall (tuple_T : Type) (t1 t2 : table_T tuple_T),
    length (t1 ++ t2) = length (t2 ++ t1).
Proof. intros. induction t1. simpl. rewrite length_concat. simpl. auto.
simpl. rewrite IHt1. rewrite length_concat. rewrite length_concat. rewrite <- length_concat.
simpl. rewrite Nat.add_succ_r. rewrite length_concat. reflexivity.
Qed.



Lemma fold_subset_eq : 
  forall (tuple_T aggr_T: Type) (t1 t2 t3 : table_T tuple_T) (agg : tuple_T->aggr_T->aggr_T) (initv : aggr_T),
    agg_commutative agg initv ->
   (fold_f agg (t1++t3) initv = fold_f agg (t2++t3) initv -> fold_f agg t1 initv = fold_f agg t2 initv).
Admitted.

(* Proof. intros. induction t3. rewrite helper_fold_nil in H0. rewrite helper_fold_nil in H0.
exact H0. apply IHt3. rewrite aggr_commutative_table in H0. 
assert (H4: fold_f agg (t2 ++ a :: t3) initv = fold_f agg (a :: t3 ++ t2) initv).
{ rewrite aggr_commutative_table. reflexivity. auto. }
rewrite H4 in H0. simpl in H0. rewrite f_equal in H0. *)


Theorem assumption1_small_model: 
forall (tuple_T aggr_T : Type) (len : nat) (agg : tuple_T->aggr_T->aggr_T) (initv : aggr_T)
(f : aggr_T -> bool),
((assumption1 2 agg initv f) /\ (agg_commutative agg initv) /\ (agg_assumption 1 agg initv))
-> (assumption1 len agg initv f).
Proof.
  intros.
  destruct H.
  destruct H0.
  assert (Hagg: forall (len : nat), agg_assumption (S len) agg initv).
    {  intros. apply agg_assumption_small_model. split. 
        induction len0. auto. auto. 
        split. auto. auto. }
  induction len.
    { unfold assumption1. intros. destruct H2 as [H2a H2b]. rewrite length_concat in H2a.
      apply helper_add_le_zero in H2a. destruct H2a as [H2a0 H2a1]. destruct H2b as [H2b0 H2b1].
      assert (H4: False). apply helper_contradict_nonempty_length0 with (t3). auto. contradiction. }
    { induction len. 
      { unfold assumption1. intros. destruct H2 as [H2a H2b]. rewrite length_concat in H2a.
        destruct t3. destruct H2b as [H2b0 H2b1]. simpl in H2b0. contradiction.
        simpl in H2a. rewrite Nat.le_1_r in H2a. destruct H2a. discriminate. 
        inversion H2. apply plus_is_O in H4. destruct H4 as [H41 H42]. destruct H2b as [H2b1 H2b2].
        assert (H5: False). apply helper_contradict_nonempty_length0 with (t4). auto. contradiction.  }
      { induction len. 
          { exact H. }
          { unfold assumption1. intros table1 table2.
            split. destruct H2. apply helper_le_split in H2. destruct H2.
              {  unfold assumption1 in IHlen. rewrite IHlen. intros. exact H4.
                 split. exact H2. exact H3. }
              (* direction 1 -> *) 
              { destruct table1.
                  { simpl. destruct H3 as [H20 H21]. simpl in H20. contradiction. }
                  destruct table2. 
                  { simpl. destruct H3 as [H20 H21]. simpl in H21. contradiction. }

intros.

remember (table1 ++ table2) as tableu.
assert (Hunion_length : length tableu = S len).
    { rewrite Heqtableu.  rewrite app_length in H2. 
      simpl in H2. rewrite Nat.add_succ_r in H2. 
      inversion H2.  rewrite app_length. reflexivity. }
assert (Haggr_collapse: forall (len:nat), len >= 1 -> agg_assumption len agg initv).
    { intros. apply agg_assumption_small_model. split. exact H5. split. exact H0. exact H1.  } 
unfold agg_commutative in H0.
unfold assumption1 in IHlen.

(* f (fold_f agg (t0 :: nil) initv) = false *)
assert (Ht0_final : f (fold_f agg (t0::nil) initv) = false). 
{
assert (Ht_list_reform : (fold_f agg ((t::table1) ++ t0::table2) initv) = (fold_f agg ((t::(table1++table2)) ++ (t0::nil)) initv)).
    { assert (Hlist_reorg1: ((t::table1) ++ t0::table2) = (t::table1) ++ (t0::nil)++table2).
        { simpl. reflexivity. } 
      rewrite Hlist_reorg1. rewrite aggr_associative_table_extended_132. rewrite aggr_associative_table. reflexivity.
      auto. auto.  }

assert (Ht_rewrite : exists (tablex : table_T tuple_T), 
            length tablex = S len /\ 
            (fold_f agg ((t::tableu) ++ (t0::nil)) initv) = (fold_f agg (tablex ++ (t0::nil)) initv)).
    { unfold agg_assumption in Haggr_collapse. apply aggr_partial_collapse. 
      split. apply Hagg. auto. split. exact Hunion_length. destruct tableu. simpl in Hunion_length. discriminate. simpl. auto. }
destruct Ht_rewrite as [tablex Ht_rewrite].


    { destruct Ht_rewrite as [Ht_length Ht_rewrite]. 
      assert (Hfrewrite_false: f (fold_f agg (tablex ++ (t0::nil)) initv) = false).
        { rewrite Ht_list_reform in H4. rewrite Heqtableu in Ht_rewrite. rewrite Ht_rewrite in H4. exact H4. }
      rewrite IHlen in Hfrewrite_false. destruct Hfrewrite_false. exact H6.
      split. rewrite length_concat. simpl. rewrite Nat.add_1_r. apply Peano.le_n_S. rewrite Ht_length. auto.
      split. induction tablex. simpl in Ht_length. discriminate. simpl. auto. simpl. auto. 
    }
}

assert (Ht_final : f (fold_f agg (t::nil) initv) = false).
{
(* f (fold_f agg (t :: nil) initv) = false *)
assert (Ht_list_reform : (fold_f agg ((t::table1) ++ t0::table2) initv) = (fold_f agg ((t0::(table1++table2)) ++ (t::nil)) initv)).
    { assert (Hlist_reorg: ((t::table1) ++ t0::table2) = (t::nil) ++ (table1 ++ (t0::table2))).
        { simpl. reflexivity. } 
      rewrite Hlist_reorg. rewrite aggr_commutative_table. rewrite aggr_associative_table_extended_21_3. simpl. 
      rewrite aggr_associative_table_extended_21_3. reflexivity. auto. auto. auto.
    }

assert (Ht_rewrite : exists (tablex : table_T tuple_T), 
            length tablex = S len /\ 
            (fold_f agg ((t0::tableu) ++ (t::nil)) initv) = (fold_f agg (tablex ++ (t::nil)) initv)).
    { unfold agg_assumption in Haggr_collapse. apply aggr_partial_collapse. 
      split. apply Hagg. auto. split. exact Hunion_length. destruct tableu. simpl in Hunion_length. discriminate. simpl. auto. }
destruct Ht_rewrite as [tablex Ht_rewrite].

    { destruct Ht_rewrite as [Ht_length Ht_rewrite]. 
      assert (Hfrewrite_false: f (fold_f agg (tablex ++ (t::nil)) initv) = false).
        { rewrite Ht_list_reform in H4. rewrite Heqtableu in Ht_rewrite. rewrite Ht_rewrite in H4. exact H4. }
      rewrite IHlen in Hfrewrite_false. destruct Hfrewrite_false. exact H6.
      split. rewrite length_concat. simpl. rewrite Nat.add_1_r. apply Peano.le_n_S. rewrite Ht_length. auto.
      split. induction tablex. simpl in Ht_length. discriminate. simpl. auto. simpl. auto. 
    }
}

(* f (fold_f agg table1 initv) = false *)
assert (Htable1_final : non_empty table1 -> f (fold_f agg table1 initv) = false).
intros. 
{
assert (Ht_list_reform : (fold_f agg ((t::table1) ++ t0::table2) initv) = (fold_f agg ((t::(t0::table2))++table1) initv)).
    {
       simpl. rewrite aggr_commutative_table. simpl. reflexivity. auto.
    }
assert (Ht_rewrite : exists (tablex : table_T tuple_T),
          length tablex = S (length table2) /\
          (fold_f agg ((t::(t0::table2))++table1) initv) = (fold_f agg (tablex ++ table1) initv)).
    {
      unfold agg_assumption in Haggr_collapse. apply aggr_partial_collapse.
      split. apply Hagg. auto. 
      split. simpl. reflexivity. simpl. auto.
    }
destruct Ht_rewrite as [tablex Ht_rewrite].

    {
      destruct Ht_rewrite as [Ht_length Ht_rewrite].
      assert (Hfrewrite_false : f (fold_f agg (tablex++table1) initv) = false).
        { rewrite Ht_list_reform in H4. rewrite Ht_rewrite in H4. auto. }
      rewrite IHlen in Hfrewrite_false. destruct Hfrewrite_false as [Hf_false1 Hf_false2].
      exact Hf_false2. 
      split. rewrite length_concat. rewrite Ht_length. simpl. rewrite <- length_concat.
            rewrite length_commutative. rewrite <- Heqtableu. rewrite Hunion_length. reflexivity.   
      split. destruct tablex. simpl in Ht_length. discriminate. simpl. auto. exact H5.
    }
}

(* f (fold_f agg table2 initv) = false *)
assert (Htable2_final : non_empty table2 -> f (fold_f agg table2 initv) = false).
intros. 
{
assert (Ht_list_reform : (fold_f agg ((t::table1) ++ t0::table2) initv) = (fold_f agg ((t::(table1++t0::nil))++table2) initv)).
    {
       simpl. rewrite aggr_commutative_table. rewrite <- aggr_associative_table_extended_21_3. simpl. 
       rewrite aggr_commutative_table. reflexivity. auto. auto. auto.
    }
assert (Ht_rewrite : exists (tablex : table_T tuple_T),
          length tablex = S (length table1) /\
          (fold_f agg ((t::(table1++t0::nil))++table2) initv) = (fold_f agg (tablex ++ table2) initv)).
    {
      unfold agg_assumption in Haggr_collapse. apply aggr_partial_collapse.
      split. apply Hagg. auto. 
      split. rewrite length_concat. simpl. rewrite Nat.add_1_r. reflexivity. 
          induction table1. simpl. auto. simpl. auto.
    }
destruct Ht_rewrite as [tablex Ht_rewrite].

    {
      destruct Ht_rewrite as [Ht_length Ht_rewrite].
      assert (Hfrewrite_false : f (fold_f agg (tablex++table2) initv) = false).
        { rewrite Ht_list_reform in H4. rewrite Ht_rewrite in H4. auto. }
      rewrite IHlen in Hfrewrite_false. destruct Hfrewrite_false as [Hf_false1 Hf_false2].
      exact Hf_false2. 
      split. rewrite length_concat. rewrite Ht_length. simpl. rewrite <- length_concat.
            rewrite <- Heqtableu. rewrite Hunion_length. reflexivity.
      split. destruct tablex. simpl in Ht_length. discriminate. simpl. auto. exact H5.
    }
}

split.

{
  assert (Hreshape: t::table1 = (t::nil)++table1). { simpl. reflexivity. }
  destruct table1. exact Ht_final.
  rewrite Hreshape.
  apply <- IHlen. split. exact Ht_final. apply Htable1_final. simpl. auto.
    split. simpl. simpl in H2. inversion H2. apply Peano.le_n_S. rewrite length_concat. 
      simpl. rewrite Nat.add_succ_r. apply Peano.le_n_S. apply Nat.le_add_r.
    split. simpl. auto. simpl. auto.
}

{
  assert (Hreshape: t0::table2 = (t0::nil)++table2). { simpl. reflexivity. }
  destruct table2. exact Ht0_final.
  rewrite Hreshape.
  apply <- IHlen. split. exact Ht0_final. apply Htable2_final. simpl. auto.
    split. simpl. simpl in H2. inversion H2. rewrite H6. apply Peano.le_n_S. apply Peano.le_n_S.
    rewrite Heqtableu in Hunion_length. rewrite length_concat in Hunion_length.
    simpl in Hunion_length. rewrite Nat.add_succ_r in Hunion_length.
    rewrite Nat.add_comm in Hunion_length. inversion Hunion_length. 
    apply Nat.le_add_r.    
    split. simpl. auto. simpl. auto.
}
}

(* direction 2 <- *) 
intros.
destruct H3 as [H3 H4].
destruct H2 as [H2len H2_t].
apply helper_le_split in H2len.
destruct H2len. 
  {  unfold assumption1 in IHlen. rewrite IHlen. intros. split. exact H3. exact H4.
    split. exact H2. exact H2_t.
  }
destruct H2_t as [H2_t1 H2_t2].
destruct table1. simpl in H2_t1. contradiction.
destruct table2. simpl in H2_t2. contradiction.
assert (Hlist_add_nil_helper : forall (tuple_t: Type) (table: table_T tuple_T) (tup: tuple_T),
        tup::table = (tup::nil)++table).
  { intros. simpl. reflexivity. }

assert (Hlist_reorg : fold_f agg ((t::table1)++t0::table2) initv = fold_f agg (t::(table1++table2)++(t0::nil)) initv).
  {
    rewrite Hlist_add_nil_helper with (tup := t0). 
    rewrite aggr_associative_table_extended_132. simpl. 
    rewrite aggr_associative_table. reflexivity. auto. auto. auto.
  }
assert (Ht1_t2_len : length (table1++table2) = S len).
    { simpl in H2. apply eq_add_S in H2.  
      rewrite length_concat in H2. simpl in H2. rewrite Nat.add_succ_r in H2.
      apply eq_add_S in H2. rewrite length_concat. exact H2. }
assert (Hsmaller_table: exists (tablex : table_T tuple_T),
    length tablex = length (table1++table2) /\ (fold_f agg ((t::(table1++table2)++t0::nil)) initv) = fold_f agg (tablex++t0::nil) initv).
  {
    apply aggr_partial_collapse. 
   
    split. 
    rewrite Ht1_t2_len. apply Hagg. exact H0. split. reflexivity.
    remember (table1 ++ table2) as tableu.
    destruct tableu. simpl in Ht1_t2_len. discriminate. simpl. auto.
  }
destruct Hsmaller_table as [tablex Ht_rewrite].
destruct Ht_rewrite as [Ht_rewrite1 Ht_rewrite2].

destruct table1.
destruct table2.
  { simpl in H2. apply Nat.succ_inj in H2. apply Nat.succ_inj in H2. discriminate.
  } (* both empty *)
  { unfold assumption1 in IHlen.
    rewrite aggr_commutative_table.
assert (Hsmall_table : exists (tablex : table_T tuple_T), 
      length tablex = S len /\
      fold_f agg ((t0::t1::table2)) initv = fold_f agg (tablex) initv).
{
  apply Hagg.
  split. auto. auto.
}
destruct Hsmall_table as [tabley Hsmall_table].
destruct Hsmall_table as [Htabley_size Hsmall_table].
rewrite Hsmall_table in H4.
assert (Hhelper1 : fold_f agg ((t0::t1::table2)++(t::nil)) initv = fold_f agg (tabley++t::nil) initv).
  { rewrite aggr_commutative_table. 
    assert (Hh1 : fold_f agg (tabley ++ t :: nil) initv = fold_f agg ((t::nil) ++ tabley) initv).
    {rewrite aggr_commutative_table. reflexivity. auto. }
    rewrite Hh1. simpl. simpl in Hsmall_table.  rewrite Hsmall_table. reflexivity. auto.  }
rewrite Hhelper1.
apply IHlen. simpl. split.
simpl. rewrite length_concat. simpl. rewrite Nat.add_succ_r. apply Peano.le_n_S. 
rewrite Htabley_size. 
assert (nat_add_0: forall (n : nat), n+0=n).
{ intros n. induction n. auto. rewrite Nat.add_succ_l. rewrite IHn. reflexivity. }
rewrite nat_add_0. auto.
split. destruct tabley. simpl in Htabley_size. discriminate. simpl. auto. auto.
split. exact H4. exact H3. auto.
    } (* table1 empty, table2 not empty *)

  { unfold assumption1 in IHlen.
    rewrite aggr_commutative_table.
assert (Hsmall_table : exists (tablex : table_T tuple_T), 
      length tablex = S (length table1) /\
      fold_f agg ((t::t1::table1)) initv = fold_f agg (tablex) initv).
{
  apply Hagg.
  split. simpl. reflexivity. simpl. auto.
}
destruct Hsmall_table as [tabley Hsmall_table].
destruct Hsmall_table as [Htabley_size Hsmall_table].
rewrite Hsmall_table in H3.
assert (Hhelper1 : fold_f agg ((t0::table2) ++ t::t1::table1) initv = fold_f agg ((t0::table2) ++ tabley) initv).
  { rewrite aggr_commutative_table. 
    assert (Hh1 : fold_f agg (tabley ++ t :: nil) initv = fold_f agg ((t::nil) ++ tabley) initv).
    {rewrite aggr_commutative_table. reflexivity. auto. }
rewrite aggr_commutative_table with (table1 := (t0::table2)). apply aggr_sub_eq_to_eq.
auto. exact Hsmall_table. auto. auto.
  }
rewrite Hhelper1.
apply IHlen. simpl. split.
simpl. rewrite length_concat. apply Peano.le_n_S. rewrite Htabley_size.
simpl in Ht1_t2_len. apply Nat.succ_inj in Ht1_t2_len. 
rewrite Nat.add_succ_r. apply Peano.le_n_S. rewrite <- Ht1_t2_len.
rewrite length_concat. rewrite Nat.add_comm. auto. split. auto.
destruct tabley. simpl in Htabley_size. discriminate. simpl. auto.
split. exact H4. exact H3. auto.
  } (* both not empty. *)
}}} 
Qed.

(*
f(agg(T)) = false <-> g(T)=\emptyset
*)


Definition assumption2 {tuple_T aggr_T : Type} 
  (len : nat) (agg : tuple_T->aggr_T->aggr_T)  (initv : aggr_T) 
  (f : aggr_T -> bool) (g : tuple_T -> bool):=
  forall (table : table_T tuple_T) ,
    (length table <= len /\ non_empty table) -> ((f (fold_f agg table initv) = false <-> filter g table = nil)).


Lemma table_breakdown : 
  forall (tuple_T aggr_T : Type) (table : table_T tuple_T),
    2 <= length table -> (exists (t1 t2 : table_T tuple_T), 
      non_empty t1 /\ non_empty t2 /\ table = t1++t2).
Proof. intros. destruct table. simpl in H. inversion H. 
destruct table. simpl in H. inversion H. inversion H1.
exists (t::nil). exists (t0::table). simpl. split.
auto. auto.
Qed.

Lemma filter_distribute : 
forall (tuple_T : Type) (t1 t2 : table_T tuple_T) (g : tuple_T -> bool),
  filter g (t1 ++ t2) = (filter g t1) ++ (filter g t2).
Admitted.

Lemma plus_equal_to_le : 
forall (a b c : nat),
  a + b = c -> a <= c.
Proof. intros. induction a. induction c. auto. apply Nat.le_0_l. apply Nat.add_sub_eq_r in H. 
rewrite <- H. apply Nat.le_sub_l. Qed.


 
Lemma app_eq_nil_rev :
forall (tuple_T : Type) (t1 t2 : table_T tuple_T),
  (t1=nil /\ t2=nil) -> t1++t2=nil.
Proof. intros. destruct H. induction t1. auto. simpl in H. inversion H. 
Qed.
  

Theorem assumption2_small_model :
forall (tuple_T aggr_T : Type) (len : nat) (agg : tuple_T->aggr_T->aggr_T) (initv : aggr_T)
(f : aggr_T -> bool) (g : tuple_T -> bool),
  ((forall (slen : nat), assumption1 slen agg initv f) /\ (assumption2 1 agg initv f g)) 
    -> assumption2 len agg initv f g.
Proof. intros. destruct H as [H1 H2]. 
intros. 
destruct len. 
  { unfold assumption2. intros. 
    destruct H as [H3 H4]. inversion H3. destruct table. simpl in H4. contradiction. 
    simpl in H3. discriminate. }
induction len. exact H2.
  { unfold assumption2. intros. destruct H as [H3 H4].
    apply helper_le_split in H3. destruct H3.
    { unfold assumption2 in IHlen. apply IHlen. split. exact H. exact H4. }
    { 
      unfold assumption1 in H1. 
      assert (Hlen_helper : 2 <= length table). 
          { rewrite H. apply Peano.le_n_S. apply Peano.le_n_S. apply Nat.le_0_l. }
      split.
      { intros.
      apply table_breakdown in Hlen_helper. 
      destruct Hlen_helper. destruct H3. destruct H3 as [H31 H32]. destruct H32 as [H32 H33].
      assert(Hbreak: f (fold_f agg x initv) = false /\ f (fold_f agg x0 initv) = false).
        { apply -> H1. rewrite H33 in H0. exact H0. split. auto. split. exact H31. exact H32.  }
      destruct Hbreak as [Hbreak1 Hbreak2].
      assert (exists (somelen : nat), length x = S somelen).
        { destruct x. simpl in H31. contradiction. simpl. exists (length x). reflexivity. } 
      assert (exists (somelen : nat), length x0 = S somelen). 
        { destruct x0. simpl in H31. contradiction. simpl. exists (length x0). reflexivity. }
      destruct H3 as [somelen1]. destruct H5 as [somelen2].
  
      apply IHlen in Hbreak1.
      apply IHlen in Hbreak2.
      
      rewrite H33. rewrite filter_distribute.
      apply app_eq_nil_rev. 
      split. exact Hbreak1. exact Hbreak2.
      split. rewrite H33 in H. rewrite length_concat in H.
      
       { rewrite H3 in H. rewrite Nat.add_succ_l in H. apply Nat.succ_inj in H. rewrite <- H. rewrite Nat.add_comm. apply le_plus_l.  }
      exact H32.
      split.
      { rewrite H33 in H. rewrite length_concat in H.
        rewrite H5 in H. rewrite Nat.add_succ_r in H. apply Nat.succ_inj in H. rewrite <- H. rewrite Nat.add_comm. apply le_plus_r.  }
      exact H31. auto.
      }

      { intros.
      apply table_breakdown in Hlen_helper.
      destruct Hlen_helper. destruct H3. destruct H3 as [H31 H32]. destruct H32 as [H32 H33].
      assert(Hbreak: f (fold_f agg x initv) = false /\ f (fold_f agg x0 initv) = false).
        {
           rewrite H33 in H0. 
           rewrite filter_distribute in H0.
           apply app_eq_nil in H0.
           destruct H0 as [H01 H02].
           unfold assumption2 in IHlen.
            split.
           apply IHlen in H01.
            exact H01.
            split. rewrite H33 in H. destruct x0. simpl in H32. contradiction.
                          rewrite length_concat in H. simpl in H. rewrite Nat.add_succ_r in H.
                          apply Nat.succ_inj in H. apply plus_equal_to_le in H. exact H.
                   exact H31.
           apply IHlen in H02.
            exact H02.
            split. rewrite H33 in H. destruct x. simpl in H32. contradiction.
                          rewrite length_concat in H. simpl in H. rewrite Nat.add_comm in H.
                          apply Nat.succ_inj in H. apply plus_equal_to_le in H. exact H.
                   exact H32.
        }
      apply <- H1 in Hbreak. rewrite <- H33 in Hbreak. exact Hbreak.
      split.  apply Nat.eq_le_incl in H. rewrite H33 in H. exact H.
      split. exact H31. exact H32. auto.
      }
    }
} 
Qed.

(*
f(agg(U+T))=false -> f(U)=false /\ f(T)=false -> g(T)=nil and g(U)=nil
*)


(*
f (agg (T+U)) = true /\ g (T) = \emptyset
-> agg(T+U)=agg(U)
*)
Definition assumption3 {tuple_T aggr_T : Type} 
  (len : nat) (agg : tuple_T->aggr_T->aggr_T)  (initv : aggr_T) 
  (f : aggr_T -> bool) (g : tuple_T -> bool):= 
  forall (t1 t2 : table_T tuple_T),
    (length (t1 ++ t2) <= len) -> 
    ((f (fold_f agg (t1 ++ t2) initv) = true) /\ 
    (filter g t1 = nil)) ->
      ((fold_f agg (t1 ++ t2) initv) = fold_f agg t2 initv).



Theorem assumption3_small_model : 
forall (tuple_T aggr_T : Type) (len : nat) (agg : tuple_T->aggr_T->aggr_T) (initv : aggr_T)
(f : aggr_T -> bool) (g : tuple_T -> bool), 
(agg_commutative agg initv) /\ (forall (slen : nat), assumption1 slen agg initv f) /\
(agg_assumption 1 agg initv) /\ (forall (slen : nat), assumption2 slen agg initv f g) /\ 
(assumption3 1 agg initv f g) /\ (assumption3 2 agg initv f g)
                             -> assumption3 len agg initv f g.
Proof. intros. destruct H as [Hagg_commute H2]. destruct H2 as [H2 H3].
destruct H3 as [Hagg_fold H4].
destruct H4 as [H3 H4]. destruct H4 as [H4 H5].
destruct len. 
  { unfold assumption3. intros. destruct t1. destruct t2.
    simpl. reflexivity. simpl. reflexivity. destruct H0 as [H0 H6].
    simpl in H0.  apply Nat.nle_succ_0 in H. contradiction. }
destruct len.
exact H4.
induction len.
exact H5.
unfold assumption3.
intros.
apply helper_le_split in H.
destruct H.
  { apply IHlen. exact H. split. destruct H0. exact H0. destruct H0. exact H1. }
destruct H0 as [H0 H6].
destruct t2 as [|t2 table2]. (* U is empty. *)
  { simpl. destruct t1 as [|t1 table1]. 
              simpl. reflexivity.
    rewrite helper_fold_nil in H0. unfold assumption2 in H3. apply <- H3 in H6.
    rewrite H0 in H6. discriminate.
    split. rewrite length_concat in H. simpl in H. rewrite Nat.add_0_r in H. simpl.
    apply Nat.eq_le_incl. exact H. simpl. auto. }
destruct t1 as [|t1 table1].
  { simpl. reflexivity. }
destruct table2 as [|t2' table2]. (* U has one element. *)
  {
    (* |U| = 1: f(agg(T+u)) = true /\ g(T)=\emptyset -> agg(T+u)=agg(u)
          goal: agg(x+T+u)=agg(u)
          f(agg(x+T+u)) = true /\ g(x+T)=\emptyset 
        -> f(agg(x+u+T))=f(agg(x'+T))=true -> agg(x'+T)=agg(x')=agg(x+u)
        -> f(agg(x+u))=true /\ g(x)=\emptyset -> agg(x+u)=agg(u) *)

    assert (Hreorg_list: fold_f agg ((t1 :: table1) ++ t2 :: nil) initv = fold_f agg (t1::(t2::nil)++table1) initv).
      { simpl. rewrite aggr_commutative_table. simpl. reflexivity. auto. }
    assert (Hsmall_table_helper: exists (some_table : table_T tuple_T), length some_table = length (t2::nil) /\
        fold_f agg (t1::(t2::nil)) initv = fold_f agg (some_table) initv).
      { apply agg_assumption_small_model. split. simpl in H.
        simpl. auto. split. exact Hagg_commute. exact Hagg_fold. 
        split. reflexivity. simpl. auto. }
    destruct Hsmall_table_helper as [some_table].
    destruct H1 as [Hlength Hsmall_table_helper].
    unfold assumption3 in IHlen.
    (* agg(x+u+T) = agg(x'+T) *)
    assert (Hsmall_table: fold_f agg (t1::(t2::nil)++table1) initv = fold_f agg (some_table++table1) initv).
       { assert (Htx: (t1::(t2::nil)++table1) = (t1::(t2::nil))++table1). { simpl. reflexivity. }
        rewrite Htx. apply aggr_sub_eq_to_eq. auto. exact Hsmall_table_helper.   }
    (* agg(x+u+T) = agg(x+u) *)
    assert (Htemp: fold_f agg ((t1 :: table1) ++ t2 :: nil) initv = fold_f agg (t1::(t2::nil)) initv).
      {  assert (Hsplit_with_nil: t1::table1 = (t1::nil)++table1).    
          { simpl. reflexivity. }
         rewrite Hsplit_with_nil in H6.
         rewrite filter_distribute in H6. 
         apply app_eq_nil in H6. destruct H6 as [H61 H62].
         rewrite Hsmall_table in Hreorg_list.
         rewrite Hreorg_list in H0.
         rewrite Hsmall_table_helper.
         rewrite Hreorg_list.
         rewrite aggr_commutative_table.
         apply IHlen.
         rewrite length_concat in H. rewrite <- Hlength in H. rewrite length_concat.
         simpl in H. apply Nat.succ_inj in H.
         apply Nat.eq_le_incl. exact H.
         split. rewrite aggr_commutative_table. exact H0. 
         auto. auto. auto.
      }
    (* agg(x+u) = agg(u) *)
    assert (Htemp2: fold_f agg (t1::t2::nil) initv = fold_f agg (t2::nil) initv).
      {
        assert (Hreorg_list2: t1::t2::nil = (t1::nil)++(t2::nil)). { simpl. reflexivity. }
        rewrite Hreorg_list2. apply IHlen.  
        rewrite length_concat. simpl. apply Peano.le_n_S. apply Peano.le_n_S. apply Nat.le_0_l.
        split. rewrite Htemp in H0. simpl in H0. simpl. exact H0.
        assert (Hreorg_list3: t1::table1 = (t1::nil)++table1). { simpl. reflexivity. }
        rewrite Hreorg_list3 in H6. rewrite filter_distribute in H6. apply app_eq_nil in H6. destruct H6. exact H1.
      }
    rewrite Htemp.
    rewrite Htemp2.
    reflexivity.
  }
(* U has more than one element. *)
  {
     (* f(agg(x::T+u::U'))=true /\ g(x::T) = \emptyset -> 
            agg(x::T+Ux)=agg(Ux)=agg(u::U'). *)
     assert (Hsmall_table_helper: exists (some_table : table_T tuple_T), length some_table = (length (t2'::table2)) /\
          fold_f agg (t2::t2'::table2) initv = fold_f agg (some_table) initv).
      { apply agg_assumption_small_model. split.
        simpl. apply Peano.le_n_S. apply Nat.le_0_l.
        split. auto. auto. split. reflexivity. simpl. auto. 
      }
    destruct Hsmall_table_helper as [some_table].
    (* agg(x::T+u::U')=agg(x::T+Ux) *)
    assert (Hsmall_table: fold_f agg ((t1::table1)++some_table) initv = fold_f agg ((t1::table1)++(t2::t2'::table2)) initv).
      { rewrite aggr_commutative_table. rewrite aggr_commutative_table with (table1:=(t1::table1)).
        apply aggr_sub_eq_to_eq. auto. destruct H1. rewrite H7. reflexivity. auto. auto. }
    (* agg(x::T+Ux) = agg(Ux) *)
    assert (Htemp : fold_f agg ((t1::table1)++some_table) initv = fold_f agg (some_table) initv).
      {
        apply IHlen.
        destruct H1.
        rewrite length_concat.
        rewrite H1. simpl. apply Peano.le_n_S. apply Nat.eq_le_incl.
        rewrite length_concat in H. simpl in H. apply Nat.succ_inj in H. 
        rewrite Nat.add_succ_r in H. apply Nat.succ_inj in H. exact H.
        split. rewrite Hsmall_table. exact H0. auto.
      }
    rewrite <- Hsmall_table.
    destruct H1. rewrite H7.
    rewrite Htemp. reflexivity.
  }
Qed.

 

(* length T >= 1 *)
(*
f ( agg T ) = agg ( g(T) )
f ( agg T ) = true -> g(T)=g(T'+U') where g(T')=\emptyset agg(T)=agg(U')=agg(g(T'+U'))
f ( agg T ) = false -> g(T) = \emptyset
*)

(* SMP proof *)
(* pre-conditions are all on a small table of size <=2 *)
(* we prove the correctness holds on all tables. *)

Theorem final_groupby :
forall (tuple_T aggr_T : Type) (agg : tuple_T->aggr_T->aggr_T) (initv : aggr_T)
(f : aggr_T -> bool) (g : tuple_T -> bool) (table : table_T tuple_T),
    (non_empty table /\
    (agg_commutative agg initv) /\ (assumption1 2 agg initv f) /\
    (agg_assumption 1 agg initv) /\ (assumption2 1 agg initv f g) /\ 
    (assumption3 1 agg initv f g) /\ (assumption3 2 agg initv f g))
    -> (((f (fold_f agg (table) initv) = true /\ (exists (t1 t2 : table_T tuple_T), table = t1++t2 /\ filter g table = t1 /\ filter g t2 = nil)
          ) -> (fold_f agg table initv = fold_f agg (filter g table) initv))
        /\
       ((f (fold_f agg (table) initv) = false) -> filter g table = nil)).
Proof. intros.
destruct H as [H1 H].
destruct H as [H2 H].
destruct H as [H3 H].
destruct H as [H4 H].
destruct H as [H6 H].
destruct H as [H7 H].
assert (Hassump1_general: forall slen : nat, assumption1 slen agg initv f).
    { intros. apply assumption1_small_model. split. auto. split. auto. auto. } 
  assert (Hassump2_general : forall slen : nat, assumption2 slen agg initv f g).
    { intros. apply assumption2_small_model. split. auto. auto. }
  assert (Hassump3_general : forall slen : nat, assumption3 slen agg initv f g).
    { intros. apply assumption3_small_model. split. auto. split. auto. split. auto. split. auto. split. auto. auto. }
split.
{
  intros. 
  destruct H0 as [H01 H02]. destruct H02 as [table1 H02]. destruct H02 as [table2 H02].
  destruct H02 as [H02 H03]. destruct H03 as [H03 H04].
  rewrite H02.
  rewrite H02 in H03. rewrite H03. rewrite aggr_commutative_table.
  
  assert (Hhelper: fold_f agg (table2 ++ table1) initv = fold_f agg table1 initv).
    { unfold assumption3 in Hassump3_general. 
      apply Hassump3_general with (slen:=length(table2++table1)).
      auto. split. rewrite aggr_commutative_table. rewrite <- H02. auto. auto. auto. 
    }
  rewrite Hhelper. reflexivity. auto.
}
{
  intros.
  apply Hassump2_general with (slen:=length table). 
  auto. auto.
}
Qed.


