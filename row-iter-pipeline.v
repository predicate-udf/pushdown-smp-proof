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

Lemma length_concat :
forall (X: Type) (t1 t2: table_T X), length (t1 ++ t2) = length t1 + length t2.
Proof.
induction t1. 
  + simpl. reflexivity.
  + intros. simpl. apply f_equal. apply IHt1. 
Qed.

Lemma helper_le_split :
  forall (a b : nat), a <= S b -> (a <= b \/ a = S b).
Admitted.

Lemma filter_distribute : 
forall (tuple_T : Type) (t1 t2 : table_T tuple_T) (g : tuple_T -> bool),
  filter g (t1 ++ t2) = (filter g t1) ++ (filter g t2).
Admitted.

(* INNER JOIN *)
(* for tup1 in table1:
     for tup2 in table2:
        if join_match (tup1 tup2):
          emit (join_f (tup1 tup2)) 
*)
Fixpoint innerjoin_onetup {tuple_T1 tuple_T2 output_T: Type}
(tuple1 : tuple_T1) (t2 : table_T tuple_T2)
(join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
 : table_T output_T :=
  match t2 with 
    | nil => nil
    | h :: t => match join_match tuple1 h with
                  | true => (join_f tuple1 h) :: (innerjoin_onetup tuple1 t join_match join_f )
                  | false => innerjoin_onetup tuple1 t join_match join_f
                end
  end.

Fixpoint innerjoin {tuple_T1 tuple_T2 output_T: Type}
  (t1: table_T tuple_T1) (t2: table_T tuple_T2) 
    (join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
  : table_T output_T :=
  match t1 with
    | nil => nil
    | h :: t => innerjoin_onetup h t2 join_match join_f ++ innerjoin t t2 join_match join_f
  end.

(* LEFT OUTER JOIN *)
(* for tup1 in table1:
     match = False
     for tup2 in table2:
        if join_match (tup1 tup2):
          emit (join_f (tup1 tup2)) 
          match = True
     if match = False:
       emit (join_nomatch (tup1))
*)
Fixpoint outerjoin_onetup {tuple_T1 tuple_T2 output_T: Type}
(tuple1 : tuple_T1) (t2 : table_T tuple_T2)
(join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
(join_nomatch : tuple_T1->output_T)
 : table_T output_T := 
  match t2 with 
     | nil => join_nomatch tuple1::nil
     | h :: t => match join_match tuple1 h with
                  | true => (join_f tuple1 h) :: (innerjoin_onetup tuple1 t join_match join_f)
                  | false => outerjoin_onetup tuple1 t join_match join_f join_nomatch  
                 end  
  end.

Fixpoint outerjoin {tuple_T1 tuple_T2 output_T: Type}
  (t1: table_T tuple_T1) (t2: table_T tuple_T2) 
    (join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
    (join_nomatch : tuple_T1->output_T)
  : table_T output_T :=
    match t1 with
      | nil => nil
      | h :: t => (outerjoin_onetup h t2 join_match join_f join_nomatch) ++
                    (outerjoin t t2 join_match join_f join_nomatch)
    end.

Lemma table_add_nil : 
  forall (tuple_T : Type) (table : table_T tuple_T),
    table++nil = table.
Proof. intros. induction table. simpl. reflexivity. 
simpl. rewrite IHtable. reflexivity.
Qed.

Lemma table_append_eq_split:
  forall (tuple_T : Type) (table : table_T tuple_T) (tuple : tuple_T),
    tuple::table = (tuple::nil) ++ table.
Proof. intros. simpl. reflexivity.
Qed.
  

(*
Lemma outerjoin_equal_maintained_when_switch_order :
  forall (tuple_T1 tuple_T2 output_T: Type) 
(tuple1 : tuple_T1) (tuple2 : tuple_T2) (t21 t22 t23 t24 : table_T tuple_T2)
(join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
(join_nomatch : tuple_T1->output_T),
   (outerjoin_onetup tuple1 (t21++t22) join_match join_f join_nomatch 
      = outerjoin_onetup tuple1 (t23++t24) join_match join_f join_nomatch) ->
   (outerjoin_onetup tuple1 (t22++t21) join_match join_f join_nomatch 
      = outerjoin_onetup tuple1 (t24++t23) join_match join_f join_nomatch).
Proof. intros.
induction t21.
  { rewrite table_add_nil. simpl in H.  }
  { rewrite table_add_nil. rewrite table_add_nil. simpl in H. exact H. }
  { 
*)


Lemma outerjoin_small_table_no_match_head :
  forall (tuple_T1 tuple_T2 output_T: Type) 
(tuple1 : tuple_T1) (tuple2 : tuple_T2) (t2 : table_T tuple_T2)
(join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
(join_nomatch : tuple_T1->output_T),
  join_match tuple1 tuple2 = false ->
      outerjoin_onetup tuple1 (tuple2::t2) join_match join_f join_nomatch
    = outerjoin_onetup tuple1 t2 join_match join_f join_nomatch.
Proof. intros.
simpl. rewrite H. reflexivity.
Qed.

Lemma outerjoin_small_table_no_match_mid :
  forall (tuple_T1 tuple_T2 output_T: Type) 
(tuple1 : tuple_T1) (tuple2 : tuple_T2) (t2 t2': table_T tuple_T2)
(join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
(join_nomatch : tuple_T1->output_T),
  join_match tuple1 tuple2 = false ->
      outerjoin_onetup tuple1 (t2++(tuple2::t2')) join_match join_f join_nomatch
    = outerjoin_onetup tuple1 (t2++t2') join_match join_f join_nomatch.
Admitted.
(*
Proof. intros.
simpl. rewrite H. reflexivity.
Qed.
*)

Lemma innerjoin_distributive : 
  forall (tuple_T1 tuple_T2 output_T: Type) 
(tuple1 : tuple_T1) (tuple2 : tuple_T2) (t2 t2': table_T tuple_T2)
(join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T),
  innerjoin_onetup tuple1 (t2++t2') join_match join_f
  = (innerjoin_onetup tuple1 t2 join_match join_f)++(innerjoin_onetup tuple1 t2' join_match join_f).
Proof. intros.
induction t2. simpl. reflexivity.
simpl. case (join_match tuple1 a). rewrite IHt2. reflexivity.
rewrite IHt2. 
   reflexivity.
Qed.



Lemma filter_add_redundant_head :
  forall (tuple_T2 : Type) (g: tuple_T2 -> bool) (tuple: tuple_T2) (table: table_T tuple_T2),
  (g tuple = false) -> (filter g table = filter g (tuple::table)).
Proof. intros.
simpl. rewrite H. reflexivity.
Qed.

Lemma filter_add_redundant_mid :
  forall (tuple_T2 : Type) (g: tuple_T2 -> bool) (t1 t2: tuple_T2) (table: table_T tuple_T2),
  (g t2 = false) -> (filter g (t1::table) = filter g (t1::(t2::table))).
Proof. intros.
simpl. rewrite H. reflexivity.
Qed.


Definition innerjoin_predicate_pushdown {tuple_T1 tuple_T2 output_T: Type}
    (len:nat) 
    (join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
    (f : output_T->bool) (g2 : tuple_T2->bool) :=
      forall (tuple1: tuple_T1) (table2: table_T tuple_T2),      
       (length table2 <= len) -> 
          (filter f (innerjoin_onetup tuple1 table2 join_match join_f) = 
           innerjoin_onetup tuple1 (filter g2 table2) join_match join_f
          ).

Theorem innerjoin_predicate_pushdown_smallmodel :
  forall (tuple_T1 tuple_T2 output_T : Type) (len: nat) 
    (join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
    (join_nomatch : tuple_T1->output_T)
    (f : output_T->bool) (g2 : tuple_T2->bool),
innerjoin_predicate_pushdown 1 join_match join_f f g2 ->
innerjoin_predicate_pushdown len join_match join_f f g2.
Proof. intros. destruct len.  
  {  unfold innerjoin_predicate_pushdown. intros. 
     destruct table2. simpl. reflexivity. simpl in H0. apply Nat.nle_succ_0 in H0. contradiction. }
  { unfold innerjoin_predicate_pushdown. intros. 
     induction table2. simpl. reflexivity.
     rewrite table_append_eq_split with (tuple := a).
     rewrite filter_distribute.
     rewrite innerjoin_distributive.
     simpl in H0. apply Peano.le_S_n in H0. apply Nat.le_le_succ_r in H0.     
     assert (Htable2_simpl: filter f (innerjoin_onetup tuple1 table2 join_match join_f) =
           innerjoin_onetup tuple1 (filter g2 table2) join_match join_f).
        { apply IHtable2. exact H0. }
     rewrite filter_distribute. rewrite Htable2_simpl.
     rewrite innerjoin_distributive.
     assert (Htable2_initcase: filter f (innerjoin_onetup tuple1 (a :: nil) join_match join_f)
        = innerjoin_onetup tuple1 (filter g2 (a :: nil)) join_match join_f).
        { apply H. simpl. auto. }
     rewrite Htable2_initcase.
     reflexivity.
     auto. auto.
  }
Qed.

(* f(txu) = false -> f(t x ?) = nil *)
Definition assumption1 {tuple_T1 tuple_T2 output_T: Type}
  (len: nat)
  (join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
    (f : output_T->bool) :=
      forall (tuple1: tuple_T1) (tuple2: tuple_T2) (table2: table_T tuple_T2),
        (length table2 <= len /\
         join_match tuple1 tuple2 = true /\ f (join_f tuple1 tuple2) = false) ->
          filter f (innerjoin_onetup tuple1 table2 join_match join_f) = nil.

Theorem assumption1_small_model :
  forall (tuple_T1 tuple_T2 output_T : Type) (len: nat) 
    (join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
    (f : output_T->bool) ,
    assumption1 1 join_match join_f f -> assumption1 len join_match join_f f.
Proof. intros.
destruct len.
 { unfold assumption1. intros. destruct H0. destruct H1.
   destruct table2. simpl. reflexivity. simpl in H0. apply Nat.nle_succ_0 in H0. contradiction. }
induction len. exact H.
  unfold assumption1. intros.
  destruct H0. destruct H1.
  apply helper_le_split in H0.
  destruct H0. unfold assumption1 in H. apply IHlen with (tuple2:=tuple2).
  split. exact H0. split. exact H1. exact H2.
  destruct table2. simpl. reflexivity.
  unfold assumption1 in IHlen. 
  assert (Htemp : filter f (innerjoin_onetup tuple1 table2 join_match join_f) = nil).
   { apply IHlen with (tuple2:=tuple2). split. simpl in H0. apply Nat.succ_inj in H0.
     rewrite H0. auto. split. auto. auto. }
  assert (Htemp2 : filter f (innerjoin_onetup tuple1 (t::nil) join_match join_f) = nil).
    { apply IHlen with (tuple2:=tuple2). simpl. split. apply Peano.le_n_S. apply Nat.le_0_l.
      split. auto. auto. }
  rewrite table_append_eq_split. rewrite innerjoin_distributive. 
  rewrite filter_distribute. rewrite Htemp. rewrite Htemp2. auto. auto.
Qed.
    

(* f(txu) = true -> g2(u) = true *)
Definition assumption2 {tuple_T1 tuple_T2 output_T: Type}
  (join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
    (f : output_T->bool) (g2 : tuple_T2->bool) :=
      forall (tuple1: tuple_T1) (tuple2: tuple_T2) (table2: table_T tuple_T2),
        (join_match tuple1 tuple2 = true /\ f (join_f tuple1 tuple2) = true) ->
          g2 tuple2 = true.

Definition outerjoin_predicate_pushdown {tuple_T1 tuple_T2 output_T: Type}
    (len:nat) 
    (join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
    (join_nomatch : tuple_T1->output_T)
    (f : output_T->bool) (g1 : tuple_T1->bool) (g2 : tuple_T2->bool) :=
      forall (tuple1: tuple_T1) (table2: table_T tuple_T2),      
       (length table2 <= len /\ non_empty table2) -> 
          (filter f (outerjoin_onetup tuple1 table2 join_match join_f join_nomatch) = 
            match g1 tuple1 with 
              | true => outerjoin_onetup tuple1 (filter g2 table2) join_match join_f join_nomatch
              | false => nil
            end
          ).


Theorem outerjoin_remove_assumption1 : 
forall (tuple_T1 tuple_T2 output_T : Type)
  (join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
    (join_nomatch : tuple_T1->output_T)
    (f : output_T->bool) (g1 : tuple_T1->bool) (g2 : tuple_T2->bool),
(outerjoin_predicate_pushdown 1 join_match join_f join_nomatch f g1 g2) ->
assumption1 1 join_match join_f f .
Proof. intros.
unfold outerjoin_predicate_pushdown in H.
unfold assumption1. intros.
destruct H0 as [H0 H1]. destruct H1 as [H1 H2].
destruct table2. simpl. reflexivity.
destruct table2. simpl. (* length table2 = 1 *) 
assert(Hg1t_false : g1 tuple1 = false).
{
  assert(Hrewrite_f : filter f ((join_f tuple1 tuple2)::nil)
  = filter f (outerjoin_onetup tuple1 (tuple2::nil) join_match join_f join_nomatch)).
    { simpl. rewrite H1. rewrite H2. simpl. rewrite H2. reflexivity. }
  assert(Hrewrite_g : filter f (outerjoin_onetup tuple1 (tuple2::nil) join_match join_f join_nomatch)
  = if g1 tuple1 then outerjoin_onetup tuple1 (filter g2 (tuple2::nil)) join_match join_f join_nomatch
      else nil).
    { apply H. split. simpl. auto. simpl. auto. }
  assert(Hg_nil: (if g1 tuple1 then outerjoin_onetup tuple1 (filter g2 (tuple2::nil)) join_match join_f join_nomatch
      else nil) = nil).
    { rewrite <- Hrewrite_g. rewrite <- Hrewrite_f. simpl. rewrite H2. reflexivity. }
  destruct (g1 tuple1) eqn:Hassump.
  simpl in Hg_nil. 
  destruct (g2 tuple2). simpl in Hg_nil. rewrite H1 in Hg_nil. discriminate.
  simpl in Hg_nil. discriminate.
  auto.
}
assert(Htuple2_g_nil : (if g1 tuple1 then outerjoin_onetup tuple1 (filter g2 (t::nil)) join_match join_f join_nomatch
 else nil) = nil).
  { rewrite Hg1t_false. reflexivity. }
assert(Htuple2_outer_nil : filter f (outerjoin_onetup tuple1 (t::nil) join_match join_f join_nomatch)
 = nil).
  { rewrite <- Htuple2_g_nil. apply H. split. simpl. auto. simpl. auto.  }
destruct (join_match tuple1 t) eqn:Ht_match.
unfold outerjoin_onetup in Htuple2_outer_nil. rewrite Ht_match in Htuple2_outer_nil.
simpl in Htuple2_outer_nil. 
destruct (f (join_f tuple1 t)) eqn:Hjoint_pass_filter.
rewrite Htuple2_outer_nil. simpl. reflexivity.
simpl. rewrite Hjoint_pass_filter. reflexivity. simpl. reflexivity.
simpl in H0. apply Peano.le_S_n in H0. apply Nat.nle_succ_0 in H0. contradiction.
Qed.

(* 
  txU
  case tx(u::U):
    if t match U and t match u: 
        tx(u::U)=txu++txU
    if t don't match U and t match u: 
        f(tx(u::U))=f(tx(u::(u1::U'))=tx(g(u)::g(U'))=tx(g(u::U'))=tx(g(u::(u1::U'))
    if t don't match u:
        f(tx(u::U))=f(tx(U))=tx(g(U))=tx(g(u::U'))
*)
Theorem outerjoin_pushdown_small_model :
forall (tuple_T1 tuple_T2 output_T : Type) (len: nat) 
    (join_match : tuple_T1->tuple_T2->bool) (join_f : tuple_T1->tuple_T2->output_T)
    (join_nomatch : tuple_T1->output_T)
    (f : output_T->bool) (g1 : tuple_T1->bool) (g2 : tuple_T2->bool),
(innerjoin_predicate_pushdown 1 join_match join_f f g2 /\ 
assumption2 join_match join_f f g2 /\
outerjoin_predicate_pushdown 1 join_match join_f join_nomatch f g1 g2) ->
outerjoin_predicate_pushdown len join_match join_f join_nomatch f g1 g2.
Proof. intros.
destruct len. 
unfold outerjoin_predicate_pushdown. intros.
  { destruct H0 as [H0 H1]. destruct table2. simpl in H1. contradiction. simpl in H0. apply Nat.nle_succ_0 in H0. contradiction. }
induction len. destruct H as [Hinnerjoin H]. destruct H as [Hassumption2 H]. 
exact H.
unfold outerjoin_predicate_pushdown. intros. 
destruct H0 as [H0 H1].
apply helper_le_split in H0.
destruct H0. 
  { apply IHlen. split. exact H0. exact H1. }
destruct table2 as [|u U]. 
  { simpl in H0. discriminate. }
  { destruct H as [Hinnerjoin H]. destruct H as [Hassumption2 H].
    simpl.
    destruct (join_match tuple1 u) eqn:H4.    
    case (innerjoin_onetup tuple1 U join_match join_f) eqn:H5. 
    { (* t match u and t does not match U *) 
      destruct U as [|u1 U'].       
        { assert (Hrewrite_f : filter f (join_f tuple1 u :: nil)
          = filter f (outerjoin_onetup tuple1 (u::nil) join_match join_f join_nomatch)).
            { simpl. rewrite H4. reflexivity. }
          rewrite Hrewrite_f.
          assert (Hrewrite_g : outerjoin_onetup tuple1 (if g2 u then u :: filter g2 nil else filter g2 nil)
  join_match join_f join_nomatch = outerjoin_onetup tuple1 (filter g2 (u::nil)) join_match join_f join_nomatch).
            { simpl. reflexivity. }
          rewrite Hrewrite_g.
          apply H. split. simpl. auto. simpl. auto.
        }
        {
          assert (Hu1_nomatch : join_match tuple1 u1 = false).
            { simpl in H5.  destruct (join_match tuple1 u1) eqn:H6 in H5. 
              discriminate. auto. 
            }
          assert (Hrewrite_g_1: outerjoin_onetup tuple1
  (if g2 u then u :: filter g2 (u1 :: U') else filter g2 (u1 :: U')) join_match
  join_f join_nomatch = outerjoin_onetup tuple1 (filter g2 ((u::nil)++(u1::U'))) join_match join_f join_nomatch).
            { simpl. reflexivity. }
          rewrite Hrewrite_g_1.
          assert (Hrewrite_g_2 : outerjoin_onetup tuple1 (filter g2 ((u::nil)++(u1::U'))) join_match join_f join_nomatch 
              = outerjoin_onetup tuple1 (filter g2 (u::U')) join_match join_f join_nomatch).
             { rewrite table_append_eq_split with (tuple:=u) (table:=U').
               rewrite filter_distribute. rewrite filter_distribute.  
               simpl. destruct (g2 u1) eqn:H6.                
              apply outerjoin_small_table_no_match_mid. exact Hu1_nomatch. reflexivity. 
             }
          rewrite Hrewrite_g_2.
          assert (Hrewrite_f : filter f (join_f tuple1 u :: nil) = 
              filter f (outerjoin_onetup tuple1 (u::U') join_match join_f join_nomatch)).
             {
              simpl. rewrite H4. simpl. 
              rewrite table_append_eq_split in H5. 
              rewrite innerjoin_distributive in H5.
              apply app_eq_nil in H5. 
              destruct H5 as [H51 H52].
              rewrite H52.
              simpl.  reflexivity. auto.
             }
          rewrite Hrewrite_f.
          apply IHlen.
          split. simpl. apply Peano.le_n_S. simpl in H0. apply Nat.succ_inj in H0. apply Nat.succ_inj in H0.
          rewrite H0. auto. simpl. auto.
        }
    }

    { (* t match u and t match U *)
      rewrite table_append_eq_split with (tuple:=(join_f tuple1 u)) (table:=o::t).
      rewrite filter_distribute.
      destruct (filter f (join_f tuple1 u :: nil)) eqn:Ht_join_u.
        { (* f(txu)=nil -> g1(t)=nil -> f(tx(u::U'))=f(tx(U'))=tx(g(U'))=nil++tx(g(u+U'))=g1(t)x *)
          assert (Htemp1: g1 tuple1 = false).
            { assert (Htemp2 : filter f (join_f tuple1 u :: nil) =
          filter f (outerjoin_onetup tuple1 (u::nil) join_match join_f join_nomatch)).
                { simpl. rewrite H4. simpl. reflexivity. }
              rewrite Ht_join_u in Htemp2.
              assert (Htemp3: filter f (outerjoin_onetup tuple1 (u :: nil) join_match join_f join_nomatch)
               = (match g1 tuple1 with 
              | true => outerjoin_onetup tuple1 (filter g2 (u::nil)) join_match join_f join_nomatch
              | false => nil
            end )).
                { unfold outerjoin_predicate_pushdown in H. apply H. simpl. split. auto. auto. }
               destruct (g1 tuple1) eqn:Hg1_tuple1.
                { rewrite <- Htemp2 in Htemp3. simpl in Htemp3.
                  destruct (g2 u) eqn:Hg2_u. simpl in Htemp3. rewrite H4 in Htemp3. discriminate.
                  simpl in Htemp3. discriminate.
                }
               auto. 
            }
          rewrite <- H5.
          assert (Hassumption1_general : assumption1 (S len) join_match join_f f).
            { assert (Hassumption1: assumption1 1 join_match join_f f). 
                { apply outerjoin_remove_assumption1 with (join_nomatch:=join_nomatch) (g1:=g1) (g2:=g2). exact H. } 
              apply assumption1_small_model. exact Hassumption1. }
          assert (Hfilter_none: filter f (innerjoin_onetup tuple1 U join_match join_f) = nil).
            { unfold assumption1 in Hassumption1_general. 
              apply Hassumption1_general with (tuple2:=u). 
              split. simpl in H0. apply Nat.succ_inj in H0. rewrite H0. auto. 
              split. auto. auto. simpl in Ht_join_u. 
              destruct (f (join_f tuple1 u)) eqn:Htemp. discriminate. auto.
            }
          rewrite Hfilter_none. rewrite Htemp1. simpl. reflexivity.
        }
        { (* f(txu)=true -> g(u) = true*)
          assert (Hg1_true : g1 tuple1 = true).
            { assert (Htemp2 : filter f (join_f tuple1 u :: nil) =
          filter f (outerjoin_onetup tuple1 (u::nil) join_match join_f join_nomatch)).
                { simpl. rewrite H4. simpl. reflexivity. }
              rewrite Ht_join_u in Htemp2.
              assert (Htemp3: filter f (outerjoin_onetup tuple1 (u :: nil) join_match join_f join_nomatch)
               = (match g1 tuple1 with 
              | true => outerjoin_onetup tuple1 (filter g2 (u::nil)) join_match join_f join_nomatch
              | false => nil
            end )).
                { unfold outerjoin_predicate_pushdown in H. apply H. simpl. split. auto. auto. }
              destruct (g1 tuple1) eqn:Hg1_tuple1.
                { auto. } { rewrite <- Htemp2 in Htemp3. discriminate. }
            }
          assert (Hg2_true : g2 u = true). 
            { unfold assumption2 in Hassumption2. apply Hassumption2 with (tuple1:=tuple1).
              auto. split. auto. simpl in Ht_join_u. 
              destruct (f (join_f tuple1 u)) eqn:Htemp. auto. discriminate.
            }
          rewrite Hg1_true. rewrite Hg2_true. rewrite <- H5. rewrite <- Ht_join_u.
          rewrite <- filter_distribute. 
          assert (Hrewrite_f : (join_f tuple1 u :: nil) = innerjoin_onetup tuple1 (u::nil) join_match join_f).
            { simpl. rewrite H4. reflexivity. }
          rewrite Hrewrite_f.
          rewrite <- innerjoin_distributive.
          unfold outerjoin_onetup.
          rewrite H4. 
          assert (Hrewrite_g : join_f tuple1 u :: innerjoin_onetup tuple1 (filter g2 U) join_match join_f = 
              innerjoin_onetup tuple1 (filter g2 ((u::nil) ++ U)) join_match join_f).
            { simpl. rewrite Hg2_true. simpl. rewrite H4. reflexivity. }
          rewrite Hrewrite_g.
          assert (Hinnerjoin_general : innerjoin_predicate_pushdown (S (S len)) join_match join_f f g2).
            {  apply innerjoin_predicate_pushdown_smallmodel. auto. exact Hinnerjoin. }
          apply Hinnerjoin_general. simpl. apply Peano.le_n_S. simpl in H0.  apply Nat.succ_inj in H0. rewrite H0. auto. auto.

        }
    }
    
    { (* t does not match u *)
      destruct (g2 u) eqn: Hg2u_case. 
      simpl. rewrite H4. apply IHlen. split. simpl in H0. apply Nat.succ_inj in H0.
      rewrite H0. auto. destruct U. simpl in H0. apply Nat.succ_inj in H0. discriminate.
      simpl. auto. apply IHlen. split. simpl in H0. apply Nat.succ_inj in H0. rewrite H0.
      auto. destruct U. simpl in H0. apply Nat.succ_inj in H0. discriminate. simpl. auto.
    }
} 
Qed.


(* Extended join pattern 1 *)
(* for tup1 in table1:
      Op(table2, tup1) [Op: tuple_T1->table_T(tuple_T2)->output_T
*)



Fixpoint nested_loop_1 {tuple_T1 tuple_T2 output_T: Type}
  (t1: table_T tuple_T1) (t2: table_T tuple_T2) 
    (Op: tuple_T1->(table_T tuple_T2)->output_T)
  : table_T output_T :=
    match t1 with
      | nil => nil
      | h :: t => (Op h t2) :: (nested_loop_1 t t2 Op)
    end.

Definition nested_loop_1_pred_pushdown {tuple_T1 tuple_T2 output_T: Type}
  (len: nat) (Op: tuple_T1->(table_T tuple_T2)->output_T)
  (f: output_T->bool) (g1: tuple_T1->bool) (g2: tuple_T2->bool) :=
  forall (t1: table_T tuple_T1) (t2: table_T tuple_T2),
    (length t1 <= len /\ length t2 <= len) -> 
      (filter f (nested_loop_1 t1 t2 Op)) = 
      (nested_loop_1 (filter g1 t1) (filter g2 t2) Op).

Definition nested_loop_1_pred_pushdown_sub {tuple_T1 tuple_T2 output_T: Type}
  (len: nat) (Op: tuple_T1->(table_T tuple_T2)->output_T)
  (f: output_T->bool) (g1: tuple_T1->bool) (g2: tuple_T2->bool) :=
  forall (tup1: tuple_T1) (t2: table_T tuple_T2),
    (length t2 <= len) -> 
      (filter f (nested_loop_1 (tup1::nil) t2 Op)) = 
      (nested_loop_1 (filter g1 (tup1::nil)) (filter g2 t2) Op).


Definition Op_assumption_true {tuple_T1 tuple_T2 output_T: Type}
(Op: tuple_T1->(table_T tuple_T2)->output_T)
  (f: output_T->bool) (g1: tuple_T1->bool) (g2: tuple_T2->bool) :=
  forall (tup1: tuple_T1) (t2: table_T tuple_T2),
    (g1 tup1 = true) -> (match (f (Op tup1 t2)) with 
                           | true => (Op tup1 t2)::nil
                           | false => nil
                         end) = (Op tup1 (filter g2 t2))::nil.

Definition Op_assumption_false {tuple_T1 tuple_T2 output_T: Type}
(Op: tuple_T1->(table_T tuple_T2)->output_T)
  (f: output_T->bool) (g1: tuple_T1->bool) (g2: tuple_T2->bool) :=
  forall (tup1: tuple_T1) (t2: table_T tuple_T2),
    (g1 tup1 = false) -> f (Op tup1 t2) = false.

Theorem nested_loop_1_pred_pushdown_sub_small_model : 
forall (tuple_T1 tuple_T2 output_T: Type) (len: nat) 
(Op: tuple_T1->(table_T tuple_T2)->output_T)
  (f: output_T->bool) (g1: tuple_T1->bool) (g2: tuple_T2->bool),
(Op_assumption_true Op f g1 g2 /\ Op_assumption_false Op f g1 g2 /\
nested_loop_1_pred_pushdown_sub 1 Op f g1 g2)
-> nested_loop_1_pred_pushdown_sub len Op f g1 g2.
Proof. intros.
destruct len. 
  { unfold nested_loop_1_pred_pushdown_sub. intros.
  apply H. destruct t2. simpl. auto. simpl in H0. apply Nat.nle_succ_0 in H0. contradiction.
  }
induction len.
destruct H as [Hassump_true H].
destruct H as [Hassump_false H]. exact H.
destruct H as [Hassump_true H].
destruct H as [Hassump_false H].
unfold nested_loop_1_pred_pushdown_sub. intros.
simpl.
apply helper_le_split in H0. 
destruct H0. apply IHlen. exact H0.
unfold nested_loop_1. 
destruct (g1 tup1) eqn:Hg1. simpl. 
unfold Op_assumption_true in Hassump_true. apply Hassump_true. exact Hg1.
unfold Op_assumption_false in Hassump_false. 
assert (f (Op tup1 t2) = false). {  apply Hassump_false. exact Hg1. }
rewrite H1. reflexivity.
Qed.


(* size=1 correct; Op true for any tup1 and t2 *)
 
(* subset :  *)

(* Generalized OUTER JOIN *)
(*
    for tup1 in table1:
      state = init(tup1)
      for tup2 in table2:
         state = fold (state tup1 tup2)
         if output_b (state tup1 tup2):
            emit (join_f (state tup1 tup2)
      if output_state_b (state)
        emit (ouptut_state_f (state))
        
*)

Fixpoint outerjoin_onetup {tuple_T1 tuple_T2 state_T output_T: Type}
(state_init : tuple_T1->state_T)
(fold: state_T->tuple_T1->tuple_T2->state_T)
(output_b: state_T->tuple_T1->tuple_T2->bool)
(join_f: state_T->tuple_T1->tuple_T2->output_T)
(output_state_b: state_T->bool)
(output_state_f: state_T->output_T)
(tuple1 : tuple_T1) (t2 : table_T tuple_T2) : table_T state_T*output_T
  match t2 with 
    | nil => state_init tuple1
    | h :: t => match 
  end.  


Fixpoint outerjoin {tuple_T1 tuple_T2 output_T: Type}

    (t1: table_T tuple_T1) (t2: table_T tuple_T2) : table_T output_T :=
  match t1 with
    | nil => nil
    | h :: t => 
