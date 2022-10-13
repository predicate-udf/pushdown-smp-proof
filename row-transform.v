Require Import Bool Arith List.
Set Implicit Arguments.
Set Asymmetric Patterns.

Definition table_T (tuple_T: Type) := list tuple_T.
Definition non_empty {tuple_T: Type} (l: table_T tuple_T) :=
  match l with
   | nil => False
   | h :: t => True
  end.

Fixpoint row_transform {tuple_T1 tuple_T2: Type} 
(op : tuple_T1 -> tuple_T2) (l : table_T tuple_T1) : table_T tuple_T2:=
  match l with
  | nil => nil
  | h :: t => (op h) :: (row_transform op t)
  end.

Fixpoint filter {tuple_T: Type} 
(f : tuple_T -> bool) (l : table_T tuple_T) : table_T tuple_T:=
  match l with
  | nil => nil
  | h :: t => if f h then h :: (filter f t) else (filter f t)
  end.

Definition row_transform_sz {tuple_T1 tuple_T2: Type} 
(op : tuple_T1 -> tuple_T2) (f : tuple_T2 -> bool) (g : tuple_T1 -> bool) 
(len : nat) :=
forall (t : table_T tuple_T1), 
(length t <= len) -> (filter f (row_transform op t) = row_transform op (filter g t)).


Lemma filter_split {tuple_T: Type} : 
forall (t : table_T tuple_T) (tup : tuple_T) (f: tuple_T -> bool),
filter f (tup::t) = ((filter f (tup::nil)) ++ filter f t).
Proof.
intros.
simpl. destruct (f tup). simpl. reflexivity.
simpl. reflexivity.
Qed.

Lemma filter_split2 {tuple_T: Type} : 
forall (t1 t2: table_T tuple_T) (f: tuple_T -> bool),
filter f (t1++t2) = (filter f t1) ++ (filter f t2).
Proof.
intros.
induction t1. 
+ simpl. reflexivity.
+ rewrite filter_split. simpl.
  destruct (f a). simpl. rewrite IHt1. reflexivity.
  rewrite IHt1. simpl. reflexivity.
Qed.

Lemma transform_split {tuple_T1 tuple_T2: Type} : 
forall (t : table_T tuple_T1) (tup : tuple_T1) (op: tuple_T1 -> tuple_T2),
row_transform op (tup::t) = (row_transform op (tup::nil)) ++ (row_transform op t).
Proof.
intros.
simpl. reflexivity.
Qed.

Lemma transform_split2 {tuple_T1 tuple_T2: Type} :
forall (t1 t2 : table_T tuple_T1) (op: tuple_T1 -> tuple_T2),
row_transform op (t1++t2) = (row_transform op t1) ++ (row_transform op t2).
Proof.
intros. induction t1. 
 + simpl.  reflexivity.
 + rewrite transform_split. simpl. rewrite IHt1. reflexivity.
Qed.



(* SMP proof *)
Theorem row_transform_smp : 
forall (tuple_T1 tuple_T2 : Type)
(op : tuple_T1 -> tuple_T2) (f : tuple_T2 -> bool) (g : tuple_T1 -> bool)
(len : nat),
(row_transform_sz op f g 1) -> (row_transform_sz op f g len).
Proof.
intros.
induction len.
(* empty table *)
{ unfold row_transform_sz. intros. induction t. simpl. reflexivity. 
  simpl in H0. apply Nat.nle_succ_0 in H0. contradiction. }
induction len.
apply H.
{ unfold row_transform_sz. intros.
  induction t. simpl. reflexivity.
  rewrite transform_split. rewrite filter_split. 
  rewrite transform_split2. rewrite filter_split2.
  simpl in H0. apply le_S_n in H0. 
  assert (Hlen: length t <= S (S len)). 
    { rewrite Nat.le_succ_diag_r. apply le_n_S. apply H0. }
  assert (part1: filter f (row_transform op t) = row_transform op (filter g t)).
    { apply IHt. apply Hlen. }
  assert (part2: filter f (row_transform op (a :: nil)) = row_transform op (filter g (a :: nil))).
    { unfold row_transform_sz in H. apply H. simpl. reflexivity. }
  rewrite part1. rewrite part2. reflexivity.
}
Qed.
  
 


