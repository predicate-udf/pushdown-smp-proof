Require Import Bool Arith List.
Set Implicit Arguments.
Set Asymmetric Patterns.

Definition table_T (tuple_T: Type) := list tuple_T.
Definition non_empty {tuple_T: Type} (l: table_T tuple_T) :=
  match l with
   | nil => False
   | h :: t => True
  end.

Fixpoint sorted {tuple_T: Type} 
(cmp: tuple_T->tuple_T-> bool) (t: table_T tuple_T) :=
  match t with 
    | nil => True
    | h :: t => (match t with 
        | nil => True
        | h1 :: t1 => if cmp h h1 then (sorted cmp t) else False
        end )
  end.

Lemma sorted_helper {tuple_T: Type} :
forall (cmp: tuple_T->tuple_T-> bool) (t: table_T tuple_T) (a: tuple_T),
sorted cmp (a::t) -> sorted cmp t.
Proof.
Admitted.

Fixpoint filter {tuple_T: Type} 
(f : tuple_T -> bool) (l : table_T tuple_T) : table_T tuple_T:=
  match l with
  | nil => nil
  | h :: t => if f h then h :: (filter f t) else (filter f t)
  end.

Fixpoint last_in_sorted {tuple_T: Type}
(cmp: tuple_T->tuple_T-> bool) (default: tuple_T) (t: table_T tuple_T) : tuple_T :=
  match t with 
    | nil => default
    | h :: t1 => if cmp h (last_in_sorted cmp default t1) 
                then (last_in_sorted cmp default t1) else h
  end.

Definition last_in_sorted2 {tuple_T: Type}
(cmp: tuple_T->tuple_T-> bool) (default: tuple_T) (t: table_T tuple_T) : tuple_T :=
  match t with
    | nil => default
    | h :: t1 => h
  end.

(* Fixpoint topK {tuple_T: Type}
  (t: table_T tuple_T) (K: nat) : table_T tuple_T :=
  match t with
    | nil => nil
    | h :: t1 => match K with
      | O => nil
      | S k1 => h:: (topK t1 k1)
      end
  end.
*)

Definition cmp_transitive {tuple_T: Type} (cmp: tuple_T->tuple_T->bool) :=
forall (a b c: tuple_T) ,
  cmp a b = true /\ cmp b c = true -> cmp a c = true.


Fixpoint lt_nat (n m : nat) : bool :=
  match n with
  | O => match m with 
      | O => false
      | S m' => true
      end
  | S n' =>
      match m with
      | O => false
      | S m' => lt_nat n' m'
      end
  end.

Fixpoint gt_nat (n m : nat) : bool :=
  match n with
  | O => false
  | S n' =>
      match m with
      | O => true
      | S m' => gt_nat n' m'
      end
  end.

Notation "x <? y" := (lt_nat x y).
Notation "x >? y" := (gt_nat x y) (at level 70).
Lemma lt_rewrite_true :
forall (n m : nat), n <? m = true <-> n < m.
Proof.
Admitted.

Lemma lt_rewrite_false :
forall (n m : nat), n <? m = false <-> n >= m.
Proof.
Admitted.

Lemma gt_rewrite_true :
forall (n m : nat), n >? m = true <-> n > m.
Proof.
Admitted.

Lemma gt_rewrite_false :
forall (n m : nat), n >? m = false <-> n <= m.
Proof.
Admitted.



Fixpoint topK {tuple_T: Type}
  (t: table_T tuple_T) (K: nat) : table_T tuple_T :=
  match t with
    | nil => nil
    | h :: t1 => if ((length t1) <? K) then h::t1 else topK t1 K
  end.


Lemma topK_remove_element {tuple_T: Type}:
forall (a: tuple_T) (t: table_T tuple_T) (K: nat),
  length t >= K -> topK t K = topK (a::t) K.
Proof. 
Admitted.


Lemma topK_length_cap {tuple_T: Type}:
forall (t: table_T tuple_T) (K: nat),
  length (topK t K) <= K.
Proof.
intros. induction t. simpl. apply Nat.le_0_l.
simpl. case (length t <? K) eqn:Hx.
apply lt_rewrite_true in Hx. simpl. apply lt_le_S. auto.
auto.
Qed.

Lemma topK_sorted {tuple_T: Type}:
forall (t: table_T tuple_T) (K: nat) (cmp: tuple_T->tuple_T->bool),
  sorted cmp t -> sorted cmp (topK t K).
Proof.
intros. induction t. auto.
simpl. case (length t <? K) eqn:Hx.
apply lt_rewrite_true in Hx. auto.
apply IHt. apply sorted_helper in H. auto.
Qed.

Lemma topK_reapply {tuple_T: Type}:
  forall (t: table_T tuple_T) (K: nat),
  topK t K = topK (topK t K) K.
Proof.
intros. induction t. auto. 
simpl. case (length t <? K) eqn:Hx.
simpl. rewrite Hx. auto.
apply IHt.
Qed.


(* the first (cmp r default = true) can be ignored as the default value
  is only used when the table is empty *)
Lemma topK_sorted_cmp {tuple_T: Type}:
  forall (K: nat) (cmp: tuple_T->tuple_T->bool) (t: table_T tuple_T) (r default: tuple_T),
  (cmp r default = true) /\ (cmp_transitive cmp) /\ 
  (sorted cmp t) /\ (cmp r (last_in_sorted2 cmp default t) = true) ->
    cmp r (last_in_sorted2 cmp default (topK t K)) = true.
Proof.
intros.
destruct H as [H0 H1].
destruct H1 as [H1 H2].
destruct H2 as [H2 H3].
unfold last_in_sorted2.
induction t. auto. 
simpl.
case (length t <? K) eqn:Hx.
{ (* (length t <? K) = true *)
  auto. }
{ (* (length t <? K) = false *) 
  destruct t as [|e t2] . simpl. auto.
  apply IHt. apply sorted_helper with (a). auto.
  simpl.
  simpl in H3. 
  assert (cmp_helper: cmp a e = true).
  { unfold sorted in H2. case (cmp a e) eqn:contra.
    auto. auto. }
  unfold cmp_transitive in H1.
  apply H1 with (a). auto.
}
Qed.


Definition max_default {tuple_T: Type} (cmp: tuple_T->tuple_T->bool) (default: tuple_T) :=
  forall (r: tuple_T), cmp r default = true.

(* pre-condition 1 *)
(* |F(topK (T))| < K -> (forall r, r <= min(T) -> G(r) = empty). *)
Definition topK_precond {tuple_T: Type} (K: nat) (f g: tuple_T->bool)
(cmp: tuple_T->tuple_T-> bool):=
forall (default: tuple_T) (t: table_T tuple_T),
(max_default cmp default /\ sorted cmp t /\ length (filter f (topK t K)) < K ) -> 
  (forall (r: tuple_T), cmp r (last_in_sorted2 cmp default t) = true -> (g r = false)).

Definition topK_precond_with_length {tuple_T: Type} (len K: nat) (f g: tuple_T->bool)
(cmp: tuple_T->tuple_T-> bool):=
forall (default: tuple_T) (t: table_T tuple_T),
(length t <= len /\ max_default cmp default /\ sorted cmp t /\ length (filter f (topK t K)) < K ) -> 
  (forall (r: tuple_T), cmp r (last_in_sorted2 cmp default t) = true -> (g r = false)).

Theorem topK_precond_smp :
forall (tuple_T: Type) (K: nat) (cmp: tuple_T->tuple_T-> bool) (f g: tuple_T->bool),
  (cmp_transitive cmp) /\
  (topK_precond_with_length (S K) K f g cmp) ->
  topK_precond K f g cmp.
Proof.
intros.
unfold topK_precond.
intros.
destruct H as [H4 H5].
destruct H0 as [H0 H2].
destruct H2 as [H2 H3].
case (length t >? S K) eqn:Hx.
(* (length t >? S K) = true *)
{ 
  unfold topK_precond_with_length in H5.
  apply H5 with (default) (topK t K).
  split. rewrite topK_length_cap. auto.
  split. auto.
  split. apply topK_sorted. auto.
  rewrite <- topK_reapply. auto.
  apply topK_sorted_cmp.
  split. auto.
  split. auto.
  split.  auto. auto.
}
(* (length t >? S K) = false *)
{
  unfold topK_precond_with_length in H5.
  apply H5 with (default) (t).
  split. apply gt_rewrite_false in Hx. auto.
  split. auto.
  split. auto. auto.
  auto.
}
Qed.


Theorem topK_smp : 
forall (tuple_T: Type) (K: nat) (cmp: tuple_T->tuple_T-> bool) (f g: tuple_T->bool) (default: tuple_T),
(
  (topK_precond K f g cmp) /\ (max_default cmp default) /\
  (forall (t: table_T tuple_T),
    ((length t)<= S K /\ (sorted cmp t)) -> filter f (topK t K) = topK (filter g t) K) 
->(forall (t: table_T tuple_T),
    ((length t)> S K /\ (sorted cmp t)) -> filter f (topK t K) = topK (filter g t) K) 
).
Proof.
intros.
destruct H0 as [H0 H1].
destruct H as [H H2].
destruct H2 as [H2 H3]. 
induction t. simpl. reflexivity.
simpl. 
assert (length_t1: length t <? K = false).
  { apply lt_rewrite_false. simpl in H0. apply gt_S_n in H0. }
rewrite length_t1. 
case (length (filter f (topK t K)) <? K) eqn:topK_len. 
(* |F(topK(t))| < K *)
{
  assert (g a = false).
    { unfold topK_precond in H. apply H with default t.
      split. auto.
      split. apply sorted_helper in H1. auto.
      rewrite lt_rewrite_true in topK_len. auto.
      destruct t. simpl. auto. 
      simpl. simpl in H1. 
      case (cmp a t) eqn:cmp_a_t.
      auto. auto.
    }
  rewrite H4.
  case (length t >? S K) eqn:length_split.
  { apply IHt. rewrite gt_rewrite_true in length_split. auto. 
    apply sorted_helper with (a). auto.
  }
  { apply H3. split. rewrite gt_rewrite_false in length_split. auto.
    apply sorted_helper with (a). auto.
  }
}
(* |F(topK(t))| = K *)
{
  rewrite lt_rewrite_false in topK_len.
  rewrite lt_rewrite_false in length_t1.
  assert (filter f (topK t K) = topK (filter g t) K).
    { case (length t >? S K) eqn:topK_fit.
      (* (length t >? S K) = true *)
       { apply gt_rewrite_true in topK_fit.
         apply IHt. auto. auto. apply sorted_helper with (a). auto. }
      (* (length t >? S K) = false *)
       { apply gt_rewrite_false in topK_fit.
         apply H3. split. auto. auto. apply sorted_helper with (a). auto. }
    }
  assert (length (filter g t) >= K).
    { rewrite H4 in topK_len.  }
  rewrite H4.
  case (g a) eqn:g_a.
    { (* g a = true *) 
      assert (a :: filter g t = filter g (a::t)).
        { simpl. rewrite g_a. auto. }
      apply topK_remove_element. auto.
    }
    { (* g a = false *) auto. }
}
Qed.




