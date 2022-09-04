From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import FunInd FMapInterface.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.FSets.FMapInterface.
Require Import Lia.

(* Definition of Pure Lambda Calculus *)

Inductive tm : Type :=
| tm_var   : nat -> tm
| tm_app   : tm -> tm -> tm
| tm_abs   : tm -> tm.

Inductive value : tm -> Prop :=
| v_abs : forall t,
    value (tm_abs t)
| v_var : forall x,
    value (tm_var x).

Inductive nonvalue : tm -> Prop :=
| nv_app : forall t1 t2,
    nonvalue (tm_app t1 t2).

Fixpoint isvalue (p:tm) : bool :=
  match p with
  | tm_abs _ => true
  | tm_var _ => true
  | tm_app _ _ => false
  end.

(* De Brujin index *)

Fixpoint liftX  (n : nat) (t : tm) : tm :=
  match t with 
  | tm_var ix =>
    if lt_dec ix n then t else tm_var (S ix)
  | tm_abs x1 => tm_abs (liftX (S n) x1)
  | tm_app x1 x2 => tm_app (liftX n x1) (liftX n x2)
  end.

Fixpoint substX (n:  nat) (u:  tm) (t: tm) : tm :=
  match t with
  | tm_var ix =>
    if lt_dec ix n
    then tm_var ix
    else if lt_dec n ix
         then tm_var (ix - 1)
         else u
  | tm_abs x2
    => tm_abs (substX (S n) (liftX 0 u) x2)
  | tm_app x1 x2 
    => tm_app (substX n u x1) (substX n u x2)
  end.

Ltac kill_lift :=
  match goal with 
  | [ |- context [lt_dec ?n ?n'] ]
    => case (lt_dec n n'); intros
  | [H: context [lt_dec ?n ?n'] |- _]
    => destruct (lt_dec n n'); intros
  end.

Ltac solve_lift :=
  lia || kill_lift || auto using Nat.sub_0_r || simpl.

Lemma liftX_liftX: forall t1 n n',
    liftX n (liftX (n + n') t1) 
    = liftX (1 + (n + n')) (liftX n t1).
Proof with eauto.
  induction t1; intros; simpl in *...
  - repeat solve_lift.
  - rewrite IHt1_1. rewrite IHt1_2...
  - specialize IHt1 with (S n) n'.
    assert (S (n + n') = S n + n') by lia.
    rewrite H.
    rewrite IHt1...
Qed.
    
Lemma substX_liftX: forall t1 t2 n,
    substX n t2 (liftX n t1) = t1.
Proof with eauto.
  induction t1; intros; simpl...
  - repeat solve_lift...
  - rewrite IHt1_1. rewrite IHt1_2. reflexivity.
  - rewrite IHt1...
Qed.

Lemma liftX_substX: forall t1 t2 n n',
    liftX n (substX (n + n') t2 t1)
    = substX (1 + n + n') (liftX n t2) (liftX n t1).
Proof with eauto.
  induction t1; intros; simpl in *...
  - repeat solve_lift.
    assert (S (n - 1) = n - 0) by lia.
    rewrite H...
  - rewrite <- IHt1_1. rewrite IHt1_2. reflexivity.
  - specialize IHt1 with (liftX 0 t2) (S n) n'.
    assert (S (n + n') = S n + n') by lia.
    rewrite H. rewrite IHt1. simpl.
    assert (liftX 0 (liftX n t2) = liftX (S n) (liftX 0 t2)). {
      assert (n = 0 + n) by lia.
      rewrite H0.
      rewrite liftX_liftX with t2 0 n.
      auto.
    }
    rewrite H0...
Qed.

Lemma liftX_substX': forall t1 t2 n n',
    liftX (n + n') (substX n t2 t1)
    = substX n (liftX (n + n') t2) (liftX (1 + n + n') t1).
Proof with eauto.
  induction t1; intros; simpl in *...
  - repeat solve_lift.
    assert (S (n - 1) = n - 0) by lia.
    rewrite H...
  - rewrite <- IHt1_1. rewrite IHt1_2...
  - specialize IHt1 with (liftX 0 t2) (S n) n'.
    assert (S (n + n') = S n + n') by lia.
    rewrite H. rewrite IHt1. simpl.
    assert (liftX (S (n + n')) (liftX 0 t2) = liftX 0 (liftX (n + n') t2)). {
      assert (n + n' = 0 + (n + n')) by lia.
      rewrite H0.
      rewrite liftX_liftX.
      auto.
    }
    rewrite <- H0...
Qed.

Lemma substX_substX: forall t1 t2 t3 n m,
    substX (n + m) t3 (substX n t2 t1)
    = substX n (substX (n + m) t3 t2)
             (substX (1 + n + m) (liftX n t3) t1).
Proof with eauto.
  induction t1; intros; simpl in *...
  - repeat solve_lift. rewrite substX_liftX...
  - rewrite IHt1_1. rewrite IHt1_2...
  - specialize IHt1 with (liftX 0 t2) (liftX 0 t3) (S n) m.
    assert (S (n + m) = S n + m) by lia.
    rewrite H. rewrite IHt1. simpl.
    assert (liftX (S n) (liftX 0 t3) = liftX 0 (liftX n t3)). {
      assert (S n = 1 + (0 + n)) by lia. rewrite H0.
      rewrite <- liftX_liftX...
    }
    rewrite H0.
    assert (substX (S (n + m)) (liftX 0 t3) (liftX 0 t2) = liftX 0 (substX (n + m) t3 t2)). {
      assert (S (n + m) = 1 + 0 + (n + m)) by lia.
      rewrite H1. rewrite <- liftX_substX...
    }
    rewrite H1...
Qed.

(* Evaluation *)

(* Weak Head reduction *)
Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall t1 v2,
    value v2 ->
    step (tm_app (tm_abs t1) v2) (substX 0 v2 t1)
| ST_App1 : forall t1 t1' t2,
    step t1 t1' ->
     step (tm_app t1 t2) (tm_app t1' t2)
| ST_App2 : forall v1 t2 t2',
    value v1 ->
    step t2 t2' ->
    step (tm_app v1 t2) (tm_app v1 t2').

(* Beta reduction *)
Inductive reduce : tm -> tm -> Prop :=
| Red_Self : forall t, reduce t t
| Red_Body : forall t1 t2,
    reduce t1 t2 ->
    reduce (tm_abs t1) (tm_abs t2)
| Red_App1 : forall t1 t1' t2 t2',
    reduce t1 t1' ->
    reduce t2 t2' ->
    reduce (tm_app t1 t2) (tm_app t1' t2')
| Red_App2 : forall t1 t1' v2 v2',
    value v2 ->
    reduce t1 t1' ->
    reduce v2 v2' ->
    reduce (tm_app (tm_abs t1) v2) (substX 0 v2' t1').

(* Non-head reduction *)
Inductive ireduce : tm -> tm -> Prop :=
| Int_Self : forall t, ireduce t t
| Int_Body : forall t1 t2,
    reduce t1 t2 ->
    ireduce (tm_abs t1) (tm_abs t2)
| Int_App1 : forall t1 t1' t2 t2',
    nonvalue t1 ->
    ireduce t1 t1' ->
    reduce t2 t2' ->
    ireduce (tm_app t1 t2) (tm_app t1' t2')
| Int_App2 : forall t1 t1' t2 t2',
    ireduce t1 t1' ->
    ireduce t2 t2' ->
    ireduce (tm_app t1 t2) (tm_app t1' t2').

Hint Constructors value : core.
Hint Constructors nonvalue : core.
Hint Constructors step :  core.
Hint Constructors reduce : core.
Hint Constructors ireduce : core.

Inductive multi {X : Type} (R : relation X) : relation X :=
| multi_refl : forall (x : X), multi R x x
| multi_step : forall (x y z : X),
    R x y ->
    multi R y z ->
    multi R x z.

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - assumption.
    - apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.

Notation mstep := (multi step).
Notation mreduce := (multi reduce).
Notation mireduce := (multi ireduce).

(* Example *)

Example e1: mstep (tm_app (tm_abs (tm_var 1000)) (tm_var 100)) (tm_var 999).
Proof.
  apply multi_R.
  constructor. constructor.
Qed.

Inductive halt : tm -> Prop :=
| Halt : forall t1 t2, mstep t1 t2 -> value t2 -> halt t1.

Hint Constructors halt:Core.

Inductive val_or_not : tm -> Prop :=
| Is_Val : forall t, value t -> val_or_not t
| Not_Val : forall t, nonvalue t -> val_or_not t.

Hint Constructors val_or_not:Core.

Lemma decide_val : forall t,
    val_or_not t.
Proof with eauto.
  destruct t.
  - apply Is_Val...
  - apply Not_Val...
  - apply Is_Val...
Qed.

Lemma step_nvalue : forall t1 t2,
    step t1 t2 -> nonvalue t1.
Proof with eauto.
  intros. induction H... Qed.

(* Reduction *)

Lemma step_implies_reduce : forall t1 t2,
    step t1 t2 -> reduce t1 t2.
Proof with eauto.
  intros. induction H... Qed.

Lemma mstep_implies_mreduce : forall t1 t2,
    mstep t1 t2 -> mreduce t1 t2.
Proof with eauto.
  intros.
  induction H;
    eauto using step_implies_reduce, multi_trans, multi_R.
Qed.

Lemma reduce_val : forall t1 t2,
    reduce t1 t2 -> value t1 -> value t2.
Proof with eauto.
  intros. destruct H0; inversion H; subst; constructor.
Qed.

Lemma reduce_compact : forall t1 t2 t2',
    reduce t2 t2' -> reduce (tm_app t1 t2) (tm_app t1 t2).
Proof with eauto.
  intros. induction H... Qed.

Lemma lift_inv_val : forall t1 n,
    value t1 <-> value (liftX n t1).
Proof with eauto.
  intros. split; intros.
  - induction n; destruct H; simpl;     
      solve [repeat constructor ||
                    match goal with
                    | [|- context[if ?a then _ else ?c]] => destruct a
                    end].
  - induction t1... simpl in *. inversion H.
Qed.

Lemma lift_inv_nonval : forall t1 n,
    nonvalue t1 <-> nonvalue (liftX n t1).
Proof with eauto.
  intros. split; intros.
  - induction n; destruct H; simpl;
      try solve [constructor].
  - induction t1; simpl in H...
    destruct (lt_dec n0 n); inversion H.
    inversion H.
Qed.

Lemma subst_inv_val : forall t1 t2 n,
    value t2 ->
    value t1 <-> value (substX n t2 t1).
Proof with eauto.
  intros. split; intros.
  - induction t1; destruct H; simpl;
      try repeat solve_lift; inversion H0.
  - induction t1; destruct H; simpl; inversion H0...
Qed.

Lemma subst_inv_nval : forall t1 t2 n,
    value t2 ->
    nonvalue t1 <-> nonvalue (substX n t2 t1).
Proof with eauto.
  intros. split; intros.
  - induction t1; destruct H; simpl;
      try repeat solve_lift; inversion H0.
  - induction t1; simpl in *...
    destruct (lt_dec n0 n) eqn:Eb...
    destruct (lt_dec n n0) eqn:Eb'...
    inversion H0.
    destruct H0. inversion H.
    inversion H0.
Qed.

Lemma step_subst : forall t1 t2 t2' n,
    step t2 t2' -> value t1 ->
    step (substX n t1 t2) (substX n t1 t2').
Proof with eauto.
  intros.
  generalize dependent t1.
  generalize dependent n.
  induction H; intros; simpl in *...
  + assert (n = 0 + n) by lia.
    rewrite H1. rewrite substX_substX.
    constructor. rewrite <- subst_inv_val...
  + constructor... rewrite <- subst_inv_val...
Qed.

Lemma reduce_lift : forall t1 t1' n,
    reduce t1 t1' ->
    reduce (liftX n t1) (liftX n t1').
Proof with eauto.
  intros. generalize dependent n.
  induction H; intros; simpl in *...
  - assert (n = 0 + n) by lia.
    rewrite H2.
    rewrite liftX_substX'.
    simpl.
    constructor...
    apply lift_inv_val...
Qed.

Lemma reduce_subst : forall t1 t1' t2 t2' n, 
    reduce t1 t1' -> reduce t2 t2' -> value t2 ->
    reduce (substX n t2 t1) (substX n t2' t1').
Proof with eauto using reduce_lift.
  intros. generalize dependent n.
  generalize dependent t2. generalize dependent t2'.
  induction H; simpl in *...
  - induction t; intros; simpl in *...
    + repeat solve_lift.
    + constructor... apply IHt... rewrite <- lift_inv_val...
  - intros. constructor. apply IHreduce... rewrite <- lift_inv_val...
  - intros. assert (n = 0 + n) by lia. rewrite H4.
    rewrite substX_substX. simpl.
    constructor... rewrite <- subst_inv_val...
    apply IHreduce1... rewrite <- lift_inv_val...
Qed.

Lemma ireduce_subst : forall t1 t1' t2 t2' n, 
    ireduce t1 t1' -> reduce t2 t2' -> value t2 ->
    ireduce (substX n t2 t1) (substX n t2' t1').
Proof with eauto using reduce_subst, reduce_lift.
  intros. generalize dependent n.
  generalize dependent t2. generalize dependent t2'.
  induction H; simpl in *...
  - induction t; intros; simpl in *...
    repeat solve_lift.
    destruct H1. inversion H0...
    inversion H0; subst...
    constructor. apply reduce_subst...
    rewrite <- lift_inv_val...
  - intros. constructor. apply reduce_subst...
    rewrite <- lift_inv_val...
  - intros. constructor. rewrite <- subst_inv_nval...
    apply IHireduce...
    apply reduce_subst...
Qed.
  
Lemma ireduce_nval : forall t1 t2,
    ireduce t1 t2 -> nonvalue t1 -> nonvalue t2.
Proof with eauto.
  intros. induction H... inversion H0. Qed.

Lemma ireduce_inv_val : forall t1 t2,
    ireduce t1 t2 -> value t2 -> value t1.
Proof with eauto.
  intros. induction H; try solve [inversion H0]... Qed.

Lemma ireduce_inv_nval : forall t1 t2,
    ireduce t1 t2 -> nonvalue t2 -> nonvalue t1.
Proof with eauto.
  intros. induction H; try solve [inversion H0]... Qed.

Lemma mireduce_inv_val : forall t1 t2,
    mireduce t1 t2 -> value t2 -> value t1.
Proof with eauto.
  intros. induction H; eauto using ireduce_inv_val.
Qed.

Lemma mireduce_inv_nval : forall t1 t2,
    mireduce t1 t2 -> nonvalue t2 -> nonvalue t1.
Proof with eauto.
  intros. induction H; eauto using ireduce_inv_nval...
Qed.

Lemma ireduce_implies_reduce: forall t1 t2,
    ireduce t1 t2 -> reduce t1 t2.
Proof with eauto.
  intros. induction H... Qed.

Inductive sreduce : tm -> tm -> Prop :=
| SRed__z : forall t1 t2,
    ireduce t1 t2 -> sreduce t1 t2
| SRed__s : forall t1 t2 t3,
    reduce t1 t3 -> step t1 t2 -> sreduce t2 t3 -> sreduce t1 t3.

Hint Constructors sreduce : Core.

Lemma sreduce_implies_reduce : forall t1 t2,
    sreduce t1 t2 -> reduce t1 t2.
Proof with eauto.
  intros. induction H... induction H... Qed.

(* Lemma 2 *)
Lemma sreduce_app_nval : forall t1 t1' t2 t2',
    sreduce t1 t1' -> reduce t2 t2' -> nonvalue t1' ->
    sreduce (tm_app t1 t2) (tm_app t1' t2').
Proof with eauto.
  intros. generalize dependent t2. generalize dependent t2'.
  induction H.
  - constructor... constructor... eapply ireduce_inv_nval...
  - intros. eapply IHsreduce in H1. eapply SRed__s in H1... assumption.
Qed.

Lemma sreduce_app_val : forall t1 t1' t2 t2',
    sreduce t1 t1' -> sreduce t2 t2' -> value t1' ->
    sreduce (tm_app t1 t2) (tm_app t1' t2').
Proof with eauto.
  intros.
  generalize dependent t2. generalize dependent t2'.
  induction H; intros; induction H0; simpl in *;
    try solve
        [eapply SRed__s; eauto; constructor; eauto;
         apply sreduce_implies_reduce; eauto]...
  - constructor. apply Int_App2...
  - eapply SRed__s... constructor...
    apply ireduce_implies_reduce...
    constructor... eapply ireduce_inv_val in H1...
Qed.

(* Lemma 3 *)
Lemma sreduce_app: forall t1 t1' t2 t2',
    sreduce t1 t1' -> sreduce t2 t2' ->
    sreduce (tm_app t1 t2) (tm_app t1' t2').
Proof with eauto.
  intros. assert (val_or_not t1') by auto using decide_val.
  inversion H1; subst.
  - apply sreduce_app_val...
  - apply sreduce_app_nval...
    apply sreduce_implies_reduce...
Qed.

Lemma sreduce_compact: forall t1 t2 t2' n,
    sreduce t2 t2' -> value t2 ->
    sreduce (substX n t2 t1 ) (substX n t2' t1).
Proof with eauto.
  induction t1; simpl; intros; try repeat solve_lift...
  - repeat constructor.
  - repeat constructor.
  - apply sreduce_app.
    apply IHt1_1... apply IHt1_2...
  - constructor. constructor.
    apply reduce_subst...
    apply reduce_lift... apply sreduce_implies_reduce...
    rewrite <- lift_inv_val...
Qed.

(* Lemma 4 *)
Lemma ireduce_sreduce_subst: forall t1 t1' t2 t2' n,
    ireduce t1 t1' -> sreduce t2 t2' -> value t2 ->
    sreduce (substX n t2 t1) (substX n t2' t1').
Proof with eauto.
  intros.
  generalize dependent t2. generalize dependent t2'.
  generalize dependent n.
  induction H; simpl in *...
  - intros. apply sreduce_compact...
  - intros. constructor. constructor.
    apply reduce_subst... apply reduce_lift...
    apply sreduce_implies_reduce...
    rewrite <- lift_inv_val...
  - intros. repeat constructor.
    rewrite <- subst_inv_nval...
    apply ireduce_subst...
    apply sreduce_implies_reduce...
    apply reduce_subst...
    apply sreduce_implies_reduce in H2...
  - intros. constructor. apply sreduce_implies_reduce in H1.
    apply Int_App2; apply ireduce_subst...
Qed.

(* Lemma 5 *)
Lemma sreduce_subst: forall t1 t1' t2 t2' n,
    sreduce t1 t1' ->
    sreduce t2 t2' -> value t2 ->
    sreduce (substX n t2 t1) (substX n t2' t1').
Proof with eauto.
  intros.
  generalize dependent t2. generalize dependent t2'.
  generalize dependent n.
  induction H; intros.
  - apply ireduce_sreduce_subst...
  - eapply SRed__s.
    + apply reduce_subst...
      apply sreduce_implies_reduce...
    + apply step_subst...
    + apply IHsreduce...
Qed.

Lemma reduce_implies_sreduce: forall t1 t2,
    reduce t1 t2 -> sreduce t1 t2.
Proof with eauto.
  intros. induction H.
  - repeat constructor.
  - repeat constructor...
  - apply sreduce_app...
  - eapply SRed__s.
    constructor...
    constructor...
    apply sreduce_subst...
Qed.

Lemma sreduce_implies_mstep_ireduce: forall t1 t3,
    sreduce t1 t3 -> exists t2, mstep t1 t2 /\ ireduce t2 t3.
Proof with eauto using multi_R, multi_trans.
  intros.
  induction H...
  - eexists. split... constructor.
  - destruct IHsreduce. destruct H2.
    exists x. split...
Qed.

(* Lemma 6: main lemma*)
Lemma reduce_implies_mstep_ireduce: forall t1 t3,
    reduce t1 t3 -> exists t2, mstep t1 t2 /\ ireduce t2 t3.
Proof.
  eauto using sreduce_implies_mstep_ireduce, reduce_implies_sreduce. Qed.
 
Ltac kill_step :=
  match goal with
    | [H: step _ _ |- _] => inversion H 
    | [H: step _ _ |- _] => inversion H
    | [H: value (tm_app ?a ?b) |- _] => inversion H
    | [H: value ?a, G: step ?a _ |- _] => destruct H; inversion G
  end.

Ltac solve_step :=
  kill_step || auto || simpl in *.

(* Postponement *)

(* Lemma 7: Postponement *)
Lemma ireduce_step_implies_step_reduce: forall t1 t2 t3,
    ireduce t1 t2 -> step t2 t3 ->
    exists t2', step t1 t2' /\ reduce t2' t3.
Proof with eauto.
  (* 
    Note: the paper said induction on t1
    But in fact you will lost information by that
    So we induct by hypothesis on Coq
  *)
  intros. generalize dependent t3.
  induction H; intros.
  - eexists...
  - inversion H0.
  - apply ireduce_nval in H0 as H'...
    destruct H'. destruct H.
    inversion H2; subst...
    eapply IHireduce in H5...
    destruct H5. destruct H. eexists. split...
    inversion H4.
  - apply ireduce_implies_reduce in H as I.
    apply ireduce_implies_reduce in H0 as I0.
    inversion H1; subst... 
    + apply ireduce_inv_val in H as H'...
      apply ireduce_inv_val in H0 as H''...
      destruct H'; try solve [inversion H].
      eexists. split. constructor...
      inversion H; subst; apply reduce_subst...
    + apply step_nvalue in H5 as H'.
      apply ireduce_inv_nval in H...
      destruct H. destruct H'.
      apply IHireduce1 in H5.
      destruct H5. destruct H.
      eexists. split...
    + apply IHireduce2 in H6. destruct H6. destruct H2.
      eexists (tm_app t1 x). split... constructor...
      apply ireduce_inv_val in H...
Qed.

(* Collary 8 *)
Lemma ireduce_step_implies_mstep_ireduce: forall t1 t2 t3,
    ireduce t1 t2 -> step t2 t3 ->
    exists t2', mstep t1 t2' /\ ireduce t2' t3.
Proof with eauto.
  intros.
  eapply ireduce_step_implies_step_reduce in H...
  destruct H. destruct H.
  apply reduce_implies_mstep_ireduce in H1.
  destruct H1. destruct H1.
  eexists. split...
  eapply multi_trans...
  eapply multi_R...
Qed.
  
Lemma ireduce_mstep_implies_mstep_ireduce: forall t1 t2 t3,
    ireduce t1 t2 -> mstep t2 t3 ->
    exists t2', mstep t1 t2' /\ ireduce t2' t3.
Proof with eauto.
  intros. revert dependent t1.
  induction H0; intros.
  - eexists. split... constructor.
  - eapply ireduce_step_implies_mstep_ireduce with t1 x y in H1...
    destruct H1 as [? [?]].
    apply IHmulti in H2.
    destruct H2 as [? [?]].
    eapply multi_trans in H2...
Qed.

(* Evaluation *)

Lemma reduce_mstep_implies_mstep_ireduce: forall t1 t2 t3,
    reduce t1 t2 -> mstep t2 t3 ->
    exists t2', mstep t1 t2' /\ ireduce t2' t3.
Proof with eauto.
  intros. 
  apply reduce_implies_mstep_ireduce in H.
  destruct H as [? [?]].
  eapply ireduce_mstep_implies_mstep_ireduce in H1...
  destruct H1 as [? [?]].
  eapply multi_trans in H1...
Qed.

(* Lemma 9: Bifurcation *)
Lemma mreduce_implies_mstep_mireduce: forall t1 t3,
    mreduce t1 t3 ->
    exists t2, mstep t1 t2 /\ mireduce t2 t3.
Proof with eauto.
  intros. induction H...
  - eexists. split; constructor.
  - destruct IHmulti as [? [?]].
    eapply reduce_mstep_implies_mstep_ireduce with x y x0 in H...
    destruct H as [? [?]].
    eexists. split...
    econstructor...  
Qed.

(* Confluence *)

Lemma diamond: forall t1 t2 t2',
    reduce t1 t2 -> reduce t1 t2' ->
    exists t3, reduce t2 t3 /\ reduce t2' t3.
Proof with eauto using reduce_val, reduce_subst.
  intros. generalize dependent t2'.
  induction H; intros...
  - inversion H0; subst...
    apply IHreduce in H2...
    destruct H2. destruct H1.
    exists (tm_abs x). split...
  - inversion H1; subst...
    + apply IHreduce1 in H4. apply IHreduce2 in H6.
      destruct H4 as [? [?]]. destruct H6 as [? [?]].
      exists (tm_app x x0). split...
    + assert (reduce (tm_abs t0) (tm_abs t1'0)) by auto.
      apply IHreduce1 in H2. destruct H2 as [? [?]].
      apply reduce_val in H7 as H7'...
      apply IHreduce2 in H7. destruct H7 as [? [?]].
      (* a lot of inversions... *)
      inversion H; subst; inversion H2; subst; inversion H3; subst;
        try solve [exists (substX 0 x0 t0); split; eauto using reduce_val, reduce_subst];
        try solve [exists (substX 0 x0 t3); split; eauto using reduce_val, reduce_subst];
        try solve [exists (substX 0 x0 t4); split; eauto using reduce_val, reduce_subst].
  - inversion H2; subst...
    + apply reduce_val in H7 as H7'...
      apply IHreduce2 in H7. destruct H7 as [? [?]].
      inversion H5; subst.
      * exists (substX 0 x t1'). split...
      * apply IHreduce1 in H7. destruct H7 as [? [?]].
        exists (substX 0 x x0). split...
    + apply IHreduce1 in H6 as H6'. destruct H6' as [? [?]].
      apply IHreduce2 in H8 as H8'. destruct H8' as [? [?]].
      exists (substX 0 x0 x). split...
Qed.

Lemma strip: forall t1 t2 t2',
    reduce t1 t2 -> mreduce t1 t2' ->
    exists t3, mreduce t2 t3 /\ reduce t2' t3.
Proof with eauto using multi_R.
  intros. revert dependent t2. induction H0; intros...
  apply diamond with x y t2 in H as H'... destruct H' as [? [?]].
  apply IHmulti in H2. destruct H2 as [? [?]].
  eapply multi_step in H2...
Qed.

Lemma confluence: forall t1 t2 t2',
    mreduce t1 t2 -> mreduce t1 t2' ->
    exists t3, mreduce t2 t3 /\ mreduce t2' t3.
Proof with eauto using multi_R.
  intros. revert dependent t2'. induction H; intros...
  apply strip with x y t2' in H as H'... destruct H' as [? [?]].
  apply IHmulti in H2. destruct H2 as [? [?]].
  eapply multi_step in H3...
Qed.

(* Termincation *)

Lemma rhalt_implies_halt : forall t1 t2,
    mreduce t1 t2 -> value t2 -> halt t1.
Proof with eauto.
  intros.
  apply mreduce_implies_mstep_mireduce in H.
  destruct H as [? [?]].
  apply mireduce_inv_val in H1...
  econstructor...
Qed.

Lemma reduce_inv_preserves_halt: forall t1 t2,
    mreduce t1 t2 -> halt t2 -> halt t1.
Proof with eauto.
  intros. destruct H0.
  apply mstep_implies_mreduce in H0.
  eapply multi_trans in H0...
  eapply rhalt_implies_halt...
Qed.

(* Theorem 10: Adequacy of Reduction *)
Lemma reduce_preserves_halt: forall t1 t2,
    reduce t1 t2 -> halt t1 -> halt t2.
Proof with eauto.
  intros. destruct H0.
  apply mstep_implies_mreduce in H0.
  eapply strip in H...
  destruct H as [? [?]].
  apply reduce_val in H2...
  eapply rhalt_implies_halt...
Qed.

(* Standardization *)

(* Definition 11 *)
Inductive treduce : tm -> tm -> Prop :=
| TRed__z : forall t, treduce t t
| TRed__s : forall t1 t2 t3,
    step t1 t2 ->
    treduce t2 t3 ->
    treduce t1 t3
| TRed__lam : forall t1 t2,
    treduce t1 t2 ->
    treduce (tm_abs t1) (tm_abs t2)
 | TRed__App : forall t1 t1' t2 t2',
    treduce t1 t1' ->
    treduce t2 t2' ->
    treduce (tm_app t1 t2) (tm_app t1' t2').

Hint Constructors treduce.

Lemma mstep_treduce_trans : forall t1 t2 t3,
    mstep t1 t2 -> treduce t2 t3 -> treduce t1 t3.
Proof with eauto.
  intros. induction H... Qed.

Lemma mstep_implies_treduce : forall t1 t2,
    mstep t1 t2 -> treduce t1 t2.
Proof with eauto.
  intros. eapply mstep_treduce_trans... Qed.

Inductive wmireduce : tm -> tm -> Prop :=
| WMIRed__ident : forall t, wmireduce t t
| WMIRed__lam : forall t1 t2,
    mreduce t1 t2 ->
    wmireduce (tm_abs t1) (tm_abs t2)
| WMIRed__App : forall t1 t1' t2 t2',
    mreduce t1 t1' ->
    mreduce t2 t2' ->
    wmireduce (tm_app t1 t2) (tm_app t1' t2').

Hint Constructors wmireduce.

Ltac kill_multi :=
  match goal with
  | [H: context[reduce ?t1 ?t2], I: context[mreduce ?t2 ?t3] |- mreduce ?t1 ?t3 ] => 
    eapply multi_trans; eauto; eapply multi_R; eauto
  end.

Lemma ireduce_wmireduce_trans : forall t1 t2 t3,
    ireduce t1 t2 -> wmireduce t2 t3 -> wmireduce t1 t3.
Proof with eauto.
  intros. generalize dependent t3. 
  induction H; intros; eauto using multi_R.
  - inversion H0; subst; constructor;
      eauto using ireduce_implies_reduce, multi_R.
    kill_multi.
  - inversion H2; subst; constructor;
      eauto using ireduce_implies_reduce, multi_R;
      apply ireduce_implies_reduce in H0; kill_multi.
  - inversion H1; subst; constructor;
      eauto using ireduce_implies_reduce, multi_R;
      apply ireduce_implies_reduce in H, H0; kill_multi.                                        
Qed.

Lemma mireduce_implies_wmireduce : forall t1 t2,
    mireduce t1 t2 -> wmireduce t1 t2.
Proof with eauto using ireduce_wmireduce_trans.
  intros. induction H... Qed.

(* Theorem 12 *)
(* Note: the original twelf method does not work here *)
(* I followed the idea from paper *)
Lemma mreduce_implies_treduce : forall t1 t2,
    mreduce t1 t2 -> treduce t1 t2.
Proof with eauto using mstep_implies_treduce.
  intros. revert dependent t1.
  induction t2; intros;
    apply mreduce_implies_mstep_mireduce in H as I;
    destruct I as [? [?]].
  - eapply mstep_treduce_trans with x...
    clear H. clear H0. clear t1.
    apply mireduce_inv_val in H1 as H1'...
    destruct H1'.
    + exfalso.
      remember (tm_abs t). remember (tm_var n).
      revert dependent t.
      induction H1; intros; subst...
      discriminate Heqt0.
      inversion H; subst...
    + remember (tm_var x). remember (tm_var n).
      revert dependent x. revert dependent n.
      induction H1; intros; subst...
      inversion H; subst...
  - apply mireduce_inv_nval in H1 as H1'... destruct H1'.
    eapply mstep_treduce_trans with (tm_app t0 t2)... clear H0.
    apply mireduce_implies_wmireduce in H1.
    remember (tm_app t2_1 t2_2). remember (tm_app t0 t2).
    induction H1; intros; subst...
    + inversion Heqt.
    + inversion Heqt; inversion Heqt3; subst.
      clear Heqt. clear Heqt3.
      constructor...
  - eapply mstep_treduce_trans with x...
    clear H. clear H0. clear t1.
    apply mireduce_inv_val in H1 as H1'...
    destruct H1'.
    + constructor...
      apply mireduce_implies_wmireduce in H1.
      remember (tm_abs t). remember (tm_abs t2).
      revert dependent t. revert dependent t2.
      induction H1; intros; subst...
      inversion Heqt0...
      inversion Heqt0. inversion Heqt1. subst...
      inversion Heqt0.
    + exfalso.
      remember (tm_abs t2). remember (tm_var x).
      revert dependent t2.
      induction H1; intros; subst...
      discriminate Heqt.
      inversion H; subst...
Qed.
    
Lemma wmireduce_implies_treduce : forall t1 t2,
    wmireduce t1 t2 -> treduce t1 t2.
Proof with eauto using mreduce_implies_treduce.
  intros. induction H... Qed.

Inductive ctx : Type :=
| ctxHole: ctx
| ctxLam: ctx -> ctx
| ctxApp1: tm -> ctx -> ctx
| ctxApp2: ctx -> tm -> ctx.

Fixpoint fill_context C t :=
  match C with
  | ctxHole => t
  | ctxLam C' => tm_abs (fill_context C' t)
  | ctxApp1 t1 C' => tm_app t1 (fill_context C' t)
  | ctxApp2 C' t2 => tm_app (fill_context C' t) t2
  end.  

Lemma mreduce_app2: forall t1 t2 t2',
    mreduce t2 t2' -> mreduce (tm_app t1 t2) (tm_app t1 t2').
Proof with eauto.
  intros. induction H...
  - apply multi_R. econstructor.
  - eapply multi_trans. apply multi_R.
    apply Red_App1... assumption.
Qed.

Lemma mreduce_app1: forall t1 t1' t2,
    mreduce t1 t1' -> mreduce (tm_app t1 t2) (tm_app t1' t2).
Proof with eauto.
  intros. induction H...
  - apply multi_R. econstructor.
  - eapply multi_trans. apply multi_R.
    apply Red_App1... assumption.
Qed.

Lemma mreduce_abs: forall t1 t1',
    mreduce t1 t1' -> mreduce (tm_abs t1) (tm_abs t1').
Proof with eauto.
  intros. induction H...
  - apply multi_R. econstructor.
  - eapply multi_trans. apply multi_R.
    apply Red_Body... assumption.
Qed.

Lemma context_mreduce: forall C t1 t2,
    mreduce t1 t2 -> mreduce (fill_context C t1) (fill_context C t2).
Proof with eauto.
  induction C; intros; simpl in *;
    eauto using mreduce_abs, mreduce_app2, mreduce_app1. 
Qed.

Lemma contextual_equivalence: forall C t1 t2,
    mstep t1 t2 -> halt (fill_context C t1) <-> halt (fill_context C t2).
Proof with eauto using
           value_halt, mreduce_preserves_halt, mreduce_inv_preserves_halt.
  induction C; split; simpl in *;
    apply mstep_implies_mreduce in H as H';
    intros...
  - inversion H0; subst.
    eapply mreduce_preserves_halt...
    apply mreduce_app2.
    apply context_mreduce...
  - inversion H0; subst.
    eapply mreduce_inv_preserves_halt...
    apply mreduce_app2.
    apply context_mreduce...
  - inversion H0; subst.
    eapply mreduce_preserves_halt...
    apply mreduce_app1.
    apply context_mreduce...
  - inversion H0; subst.
    eapply mreduce_inv_preserves_halt...
    apply mreduce_app1.
    apply context_mreduce...
Qed.
