From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import FunInd FMapInterface.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.FSets.FMapInterface.
Require Import Lia.
Require Import Setoid.
Require Import Relations.
Require Import Relation_Definitions.
Require Import Equivalence.
Require Import Coq.Classes.RelationClasses.

(** Definitions *)

(* maybe more terms? *)
Inductive value :=
(* value *)
| tm_thunk : comp -> value
| tm_var : nat -> value
with comp :=
(* computations *)
| tm_to : comp -> comp -> comp
| tm_abs : comp -> comp
| tm_app : comp -> value -> comp
| tm_produce : value -> comp
| tm_force : value -> comp.

(** De Brujin Index *)

Fixpoint vlift (n : nat) (t : value) : value :=
  match t with 
  | tm_var ix =>
      if lt_dec ix n then t else tm_var (S ix)
  | tm_thunk x => tm_thunk (clift n x)
  end with
clift (n : nat) (t : comp) : comp :=
  match t with
  | tm_abs c => tm_abs (clift (S n) c)
  | tm_to c c' => tm_to (clift n c) (clift (S n) c') 
  | tm_app c v => tm_app (clift n c) (vlift n v)
  | tm_produce v => tm_produce (vlift n v)
  | tm_force v => tm_force (vlift n v)
  end. 

Fixpoint vsubst (n: nat) (u: value) (t: value) : value :=
  match t with
  | tm_var ix =>
    if lt_dec ix n
    then tm_var ix
    else if lt_dec n ix
         then tm_var (ix - 1)
         else u
  | tm_thunk c =>
      tm_thunk (csubst n u c)
  end with
csubst (n: nat) (u: value) (t: comp) : comp :=
  match t with
  | tm_abs c => tm_abs (csubst (S n) (vlift 0 u) c)
  | tm_to c c' => tm_to (csubst n u c) (csubst (S n) (vlift 0 u) c')
  | tm_app c v => tm_app (csubst n u c) (vsubst n u v)
  | tm_produce v => tm_produce (vsubst n u v)
  | tm_force v => tm_force (vsubst n u v)
  end.

Check value_rec. Check comp_rec.

Scheme value_mut := Induction for value Sort Set
with comp_mut := Induction for comp Sort Set.

Check value_mut.
Check comp_mut.

Ltac kill_lift :=
  match goal with 
  | [ |- context [lt_dec ?n ?n'] ]
    => case (lt_dec n n'); intros
  | [H: context [lt_dec ?n ?n'] |- _]
    => destruct (lt_dec n n') eqn:?H; intros
  | [ |- context [S (?n - 1)]] => try replace (S (n - 1)) with (n - 0) by lia
  end.

Ltac simplify := intros; simpl in *.

Ltac solve_lift :=
  simplify || lia || auto using Nat.sub_0_r, Nat.add_succ_l || congruence || kill_lift.

Definition v_lift_lift__hyp :=
  fun v => forall n n', vlift n (vlift (n + n') v) 
                 = vlift (1 + (n + n')) (vlift n v).
Definition c_lift_lift__hyp :=
  fun c => forall n n', clift n (clift (n + n') c) 
                 = clift (1 + (n + n')) (clift n c). 

Ltac unfold_lift_lift := unfold v_lift_lift__hyp, c_lift_lift__hyp in *.

Lemma vlift_vlift: forall v n n',
    vlift n (vlift (n + n') v) 
    = vlift (1 + (n + n')) (vlift n v).
Proof with eauto.
  apply (value_mut v_lift_lift__hyp c_lift_lift__hyp).
  all: unfold_lift_lift; try repeat solve_lift.
  all: replace (S (n + n')) with (S n + n') by lia;
    rewrite H; try rewrite H0; repeat solve_lift.
Qed.

Lemma clift_clift: forall c n n',
    clift n (clift (n + n') c) 
    = clift (1 + (n + n')) (clift n c).
Proof with eauto.
  apply (comp_mut v_lift_lift__hyp c_lift_lift__hyp).
  all: unfold_lift_lift; try repeat solve_lift.
  all: replace (S (n + n')) with (S n + n') by lia;
    rewrite H; try rewrite H0; repeat solve_lift.
Qed.

Definition v_subst_lift__hyp := fun v => forall t n, vsubst n t (vlift n v) = v.
Definition c_subst_lift__hyp := fun c => forall t n, csubst n t (clift n c) = c.

Ltac unfold_subst_lift := unfold v_subst_lift__hyp, c_subst_lift__hyp in *.

Lemma vsubst_vlift: forall v t n,
    vsubst n t (vlift n v) = v.
Proof with eauto.
  apply (value_mut v_subst_lift__hyp c_subst_lift__hyp).
  all: unfold_subst_lift; try repeat solve_lift.
Qed.

Lemma csubst_clift: forall c t n,
    csubst n t (clift n c) = c.
Proof with eauto.
  apply (comp_mut v_subst_lift__hyp c_subst_lift__hyp).
  all: unfold_subst_lift; try repeat solve_lift.
Qed.

Definition v_lift_subst__hyp :=
  fun v => forall t n n', vlift n (vsubst (n + n') t v)
               = vsubst (1 + n + n') (vlift n t) (vlift n v).
Definition c_lift_subst__hyp :=
  fun c => forall t n n', clift n (csubst (n + n') t c)
    = csubst (1 + n + n') (vlift n t) (clift n c).

Ltac unfold_lift_subst := unfold v_lift_subst__hyp, c_lift_subst__hyp in *.

Lemma vlift_0: forall n t,
    vlift 0 (vlift n t) = vlift (S n) (vlift 0 t).
Proof.
  intros. replace n with (0 + n);
    try rewrite vlift_vlift with t 0 n; auto.
Qed.
  
Lemma vlift_vsubst: forall v t n n',
    vlift n (vsubst (n + n') t v)
    = vsubst (1 + n + n') (vlift n t) (vlift n v).
Proof with auto using vlift_0.
  apply (value_mut v_lift_subst__hyp c_lift_subst__hyp).
  all: unfold_lift_subst; try repeat solve_lift.
  all: assert (S (n + n') = S n + n') by lia;
    rewrite vlift_0; congruence.
Qed.

Lemma clift_csubst: forall c t n n',
    clift n (csubst (n + n') t c)
    = csubst (1 + n + n') (vlift n t) (clift n c).
Proof with eauto.
  apply (comp_mut v_lift_subst__hyp c_lift_subst__hyp).
  all: unfold_lift_subst; try repeat solve_lift.
  all: assert (S (n + n') = S n + n') by lia;
    rewrite vlift_0; congruence.
Qed.

Definition v_lift_subst'__hyp :=
  fun v => forall t n n', vlift (n + n') (vsubst n t v)
                  = vsubst n (vlift (n + n') t) (vlift (1 + n + n') v).
Definition c_lift_subst'__hyp :=
  fun c => forall t n n', clift (n + n') (csubst n t c)
                  = csubst n (vlift (n + n') t) (clift (1 + n + n') c).

Ltac unfold_lift_subst' := unfold v_lift_subst'__hyp, c_lift_subst'__hyp in *.

Corollary vlift_vsubst': forall v t n n',
    vlift (n + n') (vsubst n t v)
    = vsubst n (vlift (n + n') t) (vlift (1 + n + n') v).
Proof with eauto.
  apply (value_mut v_lift_subst'__hyp c_lift_subst'__hyp).
  all: unfold_lift_subst'; repeat solve_lift. 
  all: assert (S (n + n') = S n + n') by lia;
    rewrite vlift_0; congruence.
Qed.

Corollary clift_csubst': forall c t n n',
    clift (n + n') (csubst n t c)
    = csubst n (vlift (n + n') t) (clift (1 + n + n') c).
Proof with eauto.
  apply (comp_mut v_lift_subst'__hyp c_lift_subst'__hyp).
  all: unfold_lift_subst'; repeat solve_lift.
  all: assert (S (n + n') = S n + n') by lia;
    rewrite vlift_0; congruence.
Qed.

Definition v_subst_subst__hyp :=
  fun v => forall t1 t2 n m, vsubst (n + m) t2 (vsubst n t1 v)
                  = vsubst n (vsubst (n + m) t2 t1)
                           (vsubst (1 + n + m) (vlift n t2) v).
Definition c_subst_subst__hyp :=
  fun c => forall t1 t2 n m, csubst (n + m) t2 (csubst n t1 c)
                     = csubst n (vsubst (n + m) t2 t1)
                              (csubst (1 + n + m) (vlift n t2) c).

Ltac unfold_subst_subst := unfold v_subst_subst__hyp, c_subst_subst__hyp in *.

Lemma vsubst_vsubst: forall v t1 t2 n m,
    vsubst (n + m) t2 (vsubst n t1 v)
    = vsubst n (vsubst (n + m) t2 t1) (vsubst (1 + n + m) (vlift n t2) v).
Proof with auto using vsubst_vlift.
  apply (value_mut v_subst_subst__hyp c_subst_subst__hyp).
  all: unfold_subst_subst; try repeat solve_lift...
  all: rewrite vlift_vsubst with _ _ 0 (n + m);
    simpl; try rewrite H; 
    replace (S (n + m)) with (S n + m) by lia;
    rewrite vlift_0; try (rewrite H0 || rewrite H);
    repeat solve_lift.
Qed.

Lemma csubst_csubst: forall c t1 t2 n m,
    csubst (n + m) t2 (csubst n t1 c)
    = csubst n (vsubst (n + m) t2 t1) (csubst (1 + n + m) (vlift n t2) c).
Proof with auto using vsubst_vlift.
  apply (comp_mut v_subst_subst__hyp c_subst_subst__hyp).
  all: unfold_subst_subst; try repeat solve_lift...
  all: replace (n + m) with (0 + (n + m)) by lia;
    rewrite vlift_vsubst; simpl; try rewrite H; 
    replace (S (n + m)) with (S n + m) by lia;
    rewrite vlift_0; try (rewrite H0 || rewrite H);
    repeat solve_lift.
Qed.

Hint Rewrite vlift_vsubst'.
Hint Rewrite clift_csubst'.
Hint Rewrite vsubst_vsubst.
Hint Rewrite csubst_csubst.

(** Reduction Strategy *)

(* seems...not too many steppings? *)
Inductive cstep : comp -> comp -> Prop :=
| ST_App1 : forall c v,
    cstep (tm_app (tm_abs c) v) (csubst 0 v c)
| ST_App2 : forall c c' v,
    cstep c c' -> cstep (tm_app c v) (tm_app c' v)
| ST_Force : forall c,
    cstep (tm_force (tm_thunk c)) c
| ST_To1 : forall v c',
    cstep (tm_to (tm_produce v) c') (csubst 0 v c')
| ST_To2 : forall c1 c1' c2,
    cstep c1 c1' -> cstep (tm_to c1 c2) (tm_to c1' c2).

Inductive vreduce : value -> value -> Prop :=
| VRed_Self : forall v, vreduce v v
| VRed_thunk : forall c c', creduce c c' -> vreduce (tm_thunk c) (tm_thunk c')
with creduce : comp -> comp -> Prop :=
| CRed_Self : forall c, creduce c c
| CRed_Abs : forall c c', creduce c c' -> creduce (tm_abs c) (tm_abs c')
| CRed_Prod : forall v v', vreduce v v' -> creduce (tm_produce v) (tm_produce v')
| CRed_App1 : forall c c' v v',
    creduce c c' ->
    vreduce v v' ->
    creduce (tm_app (tm_abs c) v) (csubst 0 v' c')
| CRed_App2 : forall c c' v v',
    creduce c c' ->
    vreduce v v' ->
    creduce (tm_app c v) (tm_app c' v')
| CRed_Force1 : forall c c',
    creduce c c' -> creduce (tm_force (tm_thunk c)) c'
| CRed_Force2 : forall v v',
    vreduce v v' -> creduce (tm_force v) (tm_force v')
| CRed_To1 : forall v v' c c',
    creduce c c' ->
    vreduce v v' ->
    creduce (tm_to (tm_produce v) c) (csubst 0 v' c')
| CRed_To2 : forall c1 c1' c2 c2',
    creduce c1 c1' ->
    creduce c2 c2' ->
    creduce (tm_to c1 c2) (tm_to c1' c2').

(* nonvalue is not defined, since the value in CBPV is quiite different from CBV *)
Inductive ivreduce : value -> value -> Prop :=
| VInt_Self : forall v, ivreduce v v
| VInt_Thunk: forall c c', creduce c c' -> ivreduce (tm_thunk c) (tm_thunk c')
with icreduce : comp -> comp -> Prop :=
| CInt_Self : forall c, icreduce c c
| CInt_Body : forall c c', creduce c c' -> icreduce (tm_abs c) (tm_abs c')
| CInt_Prod : forall v v', vreduce v v' -> icreduce (tm_produce v) (tm_produce v')
| CInt_App1 : forall c c' v v',
    icreduce c c' ->
    vreduce v v' ->
    icreduce (tm_app c v) (tm_app c' v')
| CInt_Force : forall v v',
    vreduce v v' -> icreduce (tm_force v) (tm_force v')
| CInt_To1 : forall c1 c1' c2 c2',
    icreduce c1 c1' ->
    creduce c2 c2' -> 
    icreduce (tm_to c1 c2) (tm_to c1' c2').

Hint Constructors cstep : core.
Hint Constructors vreduce : core.
Hint Constructors creduce : core.
Hint Constructors ivreduce : core.
Hint Constructors icreduce : core.

Notation mcstep := (clos_refl_trans comp cstep).
Notation mcreduce := (clos_refl_trans comp creduce).
Notation micreduce := (clos_refl_trans comp icreduce).

Hint Resolve rt_refl.
Hint Resolve rt_step.
Hint Resolve rt_trans.
  
Lemma cstep_implies_creduce : forall t1 t2,
    cstep t1 t2 -> creduce t1 t2.
Proof with eauto.
  intros. induction H... Qed.

Lemma mstep_implies_mcreduce : forall c c',
    mcstep c c' -> mcreduce c c'.
Proof with eauto using cstep_implies_creduce.
  intros. induction H... Qed.

Hint Resolve cstep_implies_creduce.
Hint Resolve mstep_implies_mcreduce.

Ltac simp_proper :=
  unfold Proper; unfold respectful; unfold equiv;
  unfold pointwise_relation; intros; simpl; subst.

(* vreduce v v' -> creduce (tm_app c v) (tm_app c v) *)
Instance creduce_app : Proper (eq ++> vreduce ++> creduce) tm_app.
Proof.
  simp_proper; induction H0; eauto. Qed.

Lemma step_subst : forall c c' v n,
    cstep c c' ->
    cstep (csubst n v c) (csubst n v c').
Proof with eauto.
  intros.
  revert dependent v.
  revert dependent n.
  induction H; intros; simpl in *...
  all: rewrite csubst_csubst with _ _ _ 0 n...
Qed.

Lemma mstep_subst : forall c c' v n,
    mcstep c c' ->
    mcstep (csubst n v c) (csubst n v c').
Proof with eauto using step_subst.
  intros. induction H... Qed.

Lemma step_app : forall c c' v,
    cstep c c' ->
    cstep (tm_app c v) (tm_app c' v).
Proof with eauto.
  intros. induction H... Qed.

Lemma mstep_app : forall c c' v,
    mcstep c c' ->
    mcstep (tm_app c v) (tm_app c' v).
Proof with eauto using step_app.
  intros. induction H... Qed.

Lemma step_to : forall c c' c'',
    cstep c c' ->
    cstep (tm_to c c'') (tm_to c' c'').
Proof with eauto.
  intros. induction H... Qed.

Lemma mstep_to : forall c c' c'',
    mcstep c c' ->
    mcstep (tm_to c c'') (tm_to c' c'').
Proof with eauto.
  intros. induction H... Qed.

Hint Resolve mstep_subst.
Hint Resolve mstep_app.
Hint Resolve mstep_to.

Ltac inversion_reduce :=
  match goal with
  | [H: creduce (?a _) _ |- _] => solve [inversion H; subst; simpl in *; eauto]
  | [H: vreduce (?a _) _ |- _] => solve [inversion H; subst; simpl in *; eauto]
  | [H: icreduce (?a _) _ |- _] => solve [inversion H; subst; simpl in *; eauto]
  | [H: ivreduce (?a _) _ |- _] => solve [inversion H; subst; simpl in *; eauto]
  | [H: cstep (?a _) _ |- _] => solve [inversion H; subst; simpl in *; eauto]
  end || intros || simpl in *.

Definition c_reduce_lift__hyp :=
  fun c => forall c' n, creduce c c' -> creduce (clift n c) (clift n c').
Definition v_reduce_lift__hyp :=
  fun v => forall v' n, vreduce v v' -> vreduce (vlift n v) (vlift n v').

Ltac unfold_reduce_lift :=
  unfold c_reduce_lift__hyp, v_reduce_lift__hyp in *.

Lemma vreduce_lift : forall c c' n,
    vreduce c c' ->
    vreduce (vlift n c) (vlift n c').
Proof with eauto using Nat.add_0_l.
  apply (value_mut v_reduce_lift__hyp c_reduce_lift__hyp);
    unfold_reduce_lift; try repeat inversion_reduce.
  - inversion H1; subst; simpl in *...
    rewrite clift_csubst' with _ _ 0 n.
    constructor; simpl in *...
    assert (I': creduce (tm_produce v) (tm_produce v')) by auto.
    eapply (H _ n) in I'. inversion I'...
  - inversion H1; subst; simpl in *...
    rewrite clift_csubst' with _ _ 0 n.
    constructor; simpl in *... 
    assert (I': creduce (tm_abs c0) (tm_abs c'0)) by auto.
    eapply (H _ n) in I'. inversion I'...
  - inversion H0; subst; simpl in *... constructor.
    assert (I': vreduce (tm_thunk c) (tm_thunk c')) by auto.
    eapply (H _ n) in I'. inversion I'...
Qed.

Lemma creduce_lift : forall c c' n,
    creduce c c' ->
    creduce (clift n c) (clift n c').
Proof with eauto.
  apply (comp_mut v_reduce_lift__hyp c_reduce_lift__hyp);
    unfold_reduce_lift; try repeat inversion_reduce.
  - inversion H1; subst; simpl in *...
    rewrite clift_csubst' with _ _ 0 n.
    constructor; simpl in *...
    assert (I': creduce (tm_produce v) (tm_produce v')) by auto.
    eapply (H _ n) in I'. inversion I'...
  - inversion H1; subst; simpl in *...
    rewrite clift_csubst' with _ _ 0 n.
    constructor; simpl in *... 
    assert (I': creduce (tm_abs c0) (tm_abs c'0)) by auto.
    eapply (H _ n) in I'. inversion I'...
  - inversion H0; subst; simpl in *... constructor.
    assert (I': vreduce (tm_thunk c) (tm_thunk c')) by auto.
    eapply (H _ n) in I'. inversion I'...
Qed.

Hint Resolve vreduce_lift.
Hint Resolve creduce_lift.

Definition c_reduce_subst__hyp :=
  fun c => forall c' v v' n,
      creduce c c' -> vreduce v v' -> creduce (csubst n v c) (csubst n v' c').
Definition v_reduce_subst__hyp :=
  fun v1 => forall v1' v2 v2' n,
      vreduce v1 v1' -> vreduce v2 v2' -> vreduce (vsubst n v2 v1) (vsubst n v2' v1').

Ltac unfold_reduce_subst :=
  unfold c_reduce_subst__hyp, v_reduce_subst__hyp in *.

Lemma creduce_subst : forall c c' v v' n,
    creduce c c' -> vreduce v v' ->
    creduce (csubst n v c) (csubst n v' c').
Proof with eauto using vreduce_lift, creduce_lift.
  apply (comp_mut v_reduce_subst__hyp c_reduce_subst__hyp);
    unfold_reduce_subst; try repeat inversion_reduce.
  - repeat solve_lift; inversion H; repeat solve_lift.
  - inversion H1; subst; simpl in *... repeat constructor...
    rewrite csubst_csubst with _ _ _ 0 n. constructor...
    assert (I: creduce (tm_produce v0) (tm_produce v'0)) by auto.
    eapply (H _ v v' n) in I...
    inversion I; subst...
    rewrite H6...
  - inversion H1; subst; simpl in *...
    rewrite csubst_csubst with _ _ _ 0 n. constructor...
    simpl in *.
    assert (I: creduce (tm_abs c0) (tm_abs c'0)) by auto.
    eapply (H _ v0 v' n) in I...
    inversion I; subst...
  - inversion H0; subst; simpl in *... constructor.
    assert (I:  vreduce (tm_thunk c) (tm_thunk c')) by auto.
    eapply (H _ v0 v' n) in I...
    inversion I; subst...
Qed.

Lemma vreduce_subst : forall v1 v1' v2 v2' n,
    vreduce v1 v1' -> vreduce v2 v2' ->
    vreduce (vsubst n v2 v1) (vsubst n v2' v1').
Proof with eauto using vreduce_lift, creduce_lift.
  apply (value_mut v_reduce_subst__hyp c_reduce_subst__hyp);
    unfold_reduce_subst; try repeat inversion_reduce.
  - repeat solve_lift; inversion H; repeat solve_lift. 
  - inversion H1; subst; simpl in *... repeat constructor...
    rewrite csubst_csubst with _ _ _ 0 n. constructor...
    assert (I: creduce (tm_produce v0) (tm_produce v'0)) by auto.
    eapply (H _ v v' n) in I...
    inversion I; subst...
    rewrite H6...
  - inversion H1; subst; simpl in *...
    rewrite csubst_csubst with _ _ _ 0 n. constructor...
    simpl in *.
    assert (I: creduce (tm_abs c0) (tm_abs c'0)) by auto.
    eapply (H _ v0 v' n) in I...
    inversion I; subst...
  - inversion H0; subst; simpl in *... constructor.
    assert (I:  vreduce (tm_thunk c) (tm_thunk c')) by auto.
    eapply (H _ v0 v' n) in I...
    inversion I; subst...
Qed.

Hint Resolve creduce_app.
Hint Resolve vreduce_subst.
Hint Resolve creduce_subst.

Definition c_ireduce_imp_reduce__hyp :=
  fun c => forall c', icreduce c c' -> creduce c c'.
Definition v_ireduce_imp_reduce__hyp :=
  fun v => forall v', ivreduce v v' -> vreduce v v'.

Ltac unfold_ireduce_imp_reduce :=
  unfold v_ireduce_imp_reduce__hyp, c_ireduce_imp_reduce__hyp in *.

Lemma icreduce_implies_creduce: forall c c',
    icreduce c c' -> creduce c c'.
Proof with eauto.
  apply (comp_mut v_ireduce_imp_reduce__hyp c_ireduce_imp_reduce__hyp).
  all: unfold_ireduce_imp_reduce; intros; try inversion H0; subst; auto.
  try inversion H.
  all: try inversion H1; subst; auto.
Qed.

Lemma ivreduce_implies_vreduce: forall c c',
    ivreduce c c' -> vreduce c c'.
Proof with eauto.
  apply (value_mut v_ireduce_imp_reduce__hyp c_ireduce_imp_reduce__hyp).
  all: unfold_ireduce_imp_reduce; intros; try inversion H0; subst; auto.
  try inversion H.
  all: try inversion H1; subst; auto.
Qed.

Hint Resolve icreduce_implies_creduce.
Hint Resolve ivreduce_implies_vreduce.

Lemma micreduce_implies_mcreduce: forall c c',
    micreduce c c' -> mcreduce c c'.
Proof with eauto.
  intros. induction H... Qed.

Definition c_ireduce_lift__hyp :=
  fun c => forall c' n, icreduce c c' -> icreduce (clift n c) (clift n c').
Definition v_ireduce_lift__hyp :=
  fun v => forall v' n, ivreduce v v' -> ivreduce (vlift n v) (vlift n v').

Ltac unfold_ireduce_lift :=
  unfold c_ireduce_lift__hyp, v_ireduce_lift__hyp in *.

Lemma ivreduce_lift : forall c c' n,
    ivreduce c c' ->
    ivreduce (vlift n c) (vlift n c').
Proof with eauto using Nat.add_0_l.
  apply (value_mut v_ireduce_lift__hyp c_ireduce_lift__hyp);
    unfold_ireduce_lift; try repeat inversion_reduce.
Qed.

Lemma icreduce_lift : forall c c' n,
    icreduce c c' ->
    icreduce (clift n c) (clift n c').
Proof with eauto.
  apply (comp_mut v_ireduce_lift__hyp c_ireduce_lift__hyp);
    unfold_ireduce_lift; try repeat inversion_reduce.
Qed.

Hint Resolve ivreduce_lift.
Hint Resolve icreduce_lift.

Definition c_ireduce_subst__hyp :=
  fun c => forall c' v v' n,
      icreduce c c' -> vreduce v v' -> icreduce (csubst n v c) (csubst n v' c').
Definition v_ireduce_subst__hyp :=
  fun v1 => forall v1' v2 v2' n,
      ivreduce v1 v1' -> vreduce v2 v2' -> ivreduce (vsubst n v2 v1) (vsubst n v2' v1').

Ltac unfold_ireduce_subst :=
  unfold c_ireduce_subst__hyp, v_ireduce_subst__hyp in *.

Lemma icreduce_subst : forall c c' v v' n,
    icreduce c c' -> vreduce v v' ->
    icreduce (csubst n v c) (csubst n v' c').
Proof with eauto using ivreduce_lift, icreduce_lift.
  apply (comp_mut v_ireduce_subst__hyp c_ireduce_subst__hyp);
    unfold_ireduce_subst; try repeat inversion_reduce.
  - repeat solve_lift; inversion H; repeat solve_lift. 
    inversion H0; subst...
Qed.   

Lemma ivreduce_subst :  forall v1 v1' v2 v2' n,
    ivreduce v1 v1' -> vreduce v2 v2' ->
    ivreduce (vsubst n v2 v1) (vsubst n v2' v1').
Proof with eauto using ivreduce_lift, icreduce_lift.
  apply (value_mut v_ireduce_subst__hyp c_ireduce_subst__hyp);
    unfold_ireduce_subst; try repeat inversion_reduce.
  - repeat solve_lift; inversion H; repeat solve_lift. 
    inversion H0; subst...
Qed.

Hint Resolve icreduce_subst.
Hint Resolve ivreduce_subst.

(* Lemma 6: main lemma *)
Lemma reduce_implies_mstep_ireduce: forall c c'',
    creduce c c'' -> exists c', mcstep c c' /\ icreduce c' c''.
Proof with eauto.
  intros. induction H; try destruct IHcreduce as [? [?]]; try inversion_reduce...
  all: try (eexists (csubst 0 v x); split; eauto).
  destruct IHcreduce1 as [? [?]]. destruct IHcreduce2 as [? [?]].
  exists (tm_to x c2); split...
Qed.

Hint Resolve reduce_implies_mstep_ireduce.

(* Lemma 7: Postponement *)
Lemma ireduce_step_implies_step_reduce: forall c1 c2 c3,
    icreduce c1 c2 -> cstep c2 c3 ->
    exists c2', cstep c1 c2' /\ creduce c2' c3.
Proof with eauto.
  intros. revert dependent c3.
  induction H; try destruct IHcreduce as [? [?]]; try repeat inversion_reduce...
  - inversion H1; subst...
    + inversion H...
    + apply IHicreduce in H5 as [? [?]]...
  - inversion H0; subst.
    inversion H...
  - inversion H1; subst...
    + inversion H...
    + apply IHicreduce in H5 as [? [?]]...
Qed.

Hint Resolve ireduce_step_implies_step_reduce.

(* Collary 8 *)
Lemma ireduce_step_implies_mstep_ireduce: forall c1 c2 c3,
    icreduce c1 c2 -> cstep c2 c3 ->
    exists c2', mcstep c1 c2' /\ icreduce c2' c3.
Proof with eauto.
  intros.
  eapply ireduce_step_implies_step_reduce in H as [? [?]]...
  apply reduce_implies_mstep_ireduce in H1 as [? [?]]...
Qed.

Hint Resolve ireduce_step_implies_mstep_ireduce.

Lemma ireduce_mstep_implies_mstep_ireduce: forall c1 c2 c3,
    icreduce c1 c2 -> mcstep c2 c3 ->
    exists c2', mcstep c1 c2' /\ icreduce c2' c3.
Proof with eauto.
  intros. revert dependent c1.
  induction H0; intros...
  - apply IHclos_refl_trans1 in H as [? [?]].
    apply IHclos_refl_trans2 in H0 as [? [?]]... 
Qed.

Hint Resolve ireduce_mstep_implies_mstep_ireduce.

(** Evaluation *)

Lemma reduce_mstep_implies_mstep_ireduce: forall c1 c2 c3,
    creduce c1 c2 -> mcstep c2 c3 ->
    exists c2', mcstep c1 c2' /\ icreduce c2' c3.
Proof with eauto.
  intros. 
  apply reduce_implies_mstep_ireduce in H as [? [?]].
  eapply ireduce_mstep_implies_mstep_ireduce in H1 as [? [?]]...
Qed.

Hint Resolve reduce_mstep_implies_mstep_ireduce.

Lemma mreduce_mstep_implies_mstep_mireduce: forall c1 c2 c3,
    mcreduce c1 c2 -> mcstep c2 c3 ->
    exists c2', mcstep c1 c2' /\ micreduce c2' c3.
Proof with eauto.
  intros. revert dependent c3. induction H; intros...
  - eapply reduce_mstep_implies_mstep_ireduce in H as [? [?]]...
  - apply IHclos_refl_trans2 in H1 as [? [?]].
    apply IHclos_refl_trans1 in H1 as [? [?]]...
Qed.

(* Lemma 9: Bifurcation *)
Lemma mreduce_implies_mstep_mireduce: forall c c'',
    mcreduce c c'' ->
    exists c', mcstep c c' /\ micreduce c' c''.
Proof with eauto.
  intros. induction H...
  - apply reduce_implies_mstep_ireduce in H as [? [?]]...
  - destruct IHclos_refl_trans1 as [? [?]].
    destruct IHclos_refl_trans2 as [? [?]].
    apply (mreduce_mstep_implies_mstep_mireduce _ _ x1) in H as [? [?]]...
Qed.

(** Confluence *)

Definition c_diamond :=
  fun c1 => forall c2 c2',
      creduce c1 c2 -> creduce c1 c2' -> exists c3, creduce c2 c3 /\ creduce c2' c3.
Definition v_diamond :=
  fun v1 => forall v2 v2',
      vreduce v1 v2 -> vreduce v1 v2' -> exists v3, vreduce v2 v3 /\ vreduce v2' v3.

Ltac unfold_diamond := unfold c_diamond, v_diamond in *.

Ltac solve_eq := match goal with
                 | [H: (?a _) = (?a _) |- _] => inversion H; subst; eauto
                 end.

Lemma diamond: forall c1 c2 c2',
    creduce c1 c2 -> creduce c1 c2' ->
    exists c3, creduce c2 c3 /\ creduce c2' c3.
Proof with eauto.
  apply (comp_mut v_diamond c_diamond);
    unfold_diamond; try repeat inversion_reduce...
  1,3,5: inversion H0; inversion H1; subst; eauto; eapply H in H3 as [? [?]]...
  - inversion H1; inversion H2; subst...
    + inversion H8; subst...
      assert (I: creduce (tm_produce v) (tm_produce v')) by auto.
      assert (I': creduce (tm_produce v) (tm_produce v'0)) by auto.
      apply (H _ (tm_produce v'0)) in I as [? [?]]...
      apply (H0 _ c'0) in H5 as [? [?]]...
      inversion H3; inversion H4; subst; solve_eq.
    + assert (I: creduce (tm_produce v) (tm_produce v')) by auto.
      apply (H _ c1') in I as [? [?]]...
      apply (H0 _ c2'0) in H5 as [? [?]]...
      inversion H10; subst...
      inversion H4; subst; inversion H3; subst...
    + assert (I: creduce (tm_produce v) (tm_produce v')) by auto.
      apply (H _ c1') in I as [? [?]]...
      apply (H0 _ c') in H7 as [? [?]]...
      inversion H5; subst...
      inversion H4; subst; inversion H3; subst...
    + apply (H _ c1'0) in H5 as [? [?]]...
      apply (H0 _ c2'0) in H12 as [? [?]]...
  - inversion H1; inversion H2; subst...
    + inversion H8; subst...
      assert (I: creduce (tm_abs c0) (tm_abs c')) by auto.
      assert (I': creduce (tm_abs c0) (tm_abs c'0)) by auto.
      apply (H _ (tm_abs c'0)) in I as [? [?]]...
      apply (H0 _ v'0) in H7 as [? [?]]...
      inversion H3; inversion H4; subst; solve_eq.
    + assert (I: creduce (tm_abs c0) (tm_abs c')) by auto.
      apply (H _ c'0) in I as [? [?]]...
      apply (H0 _ v'0) in H7 as [? [?]]...
      inversion H10; subst...
      inversion H4; subst; inversion H3; subst...
    + assert (I: creduce (tm_abs c1) (tm_abs c'0)) by auto.
      apply (H _ c') in I as [? [?]]...
      apply (H0 _ v'0) in H7 as [? [?]]...
      inversion H5; subst...
      inversion H4; subst; inversion H3; subst...
    + apply (H _ c'0) in H5 as [? [?]]...
      apply (H0 _ v'0) in H7 as [? [?]]...
  - inversion H0; inversion H1; subst...
    + inversion H5; subst.
      assert (I: vreduce (tm_thunk c) (tm_thunk c2)) by auto.
      assert (I': vreduce (tm_thunk c) (tm_thunk c2')) by auto.
      eapply (H _ (tm_thunk c2')) in I as [? [?]]...
      inversion H2; inversion H4; subst; solve_eq.
    + assert (I: vreduce (tm_thunk c) (tm_thunk c2)) by auto.
      eapply (H _ (tm_thunk c2)) in H6 as [? [?]]...
      inversion H4; inversion H2; subst; try solve_eq...
    + assert (I: vreduce (tm_thunk c) (tm_thunk c2')) by auto.
      eapply (H _ (tm_thunk c2')) in H3 as [? [?]]...
      inversion H3; inversion H2; subst; try solve_eq...
    + eapply (H _ _) in H3 as [? [?]]...
Qed.

Lemma strip: forall c1 c2 c2',
    creduce c1 c2 -> mcreduce c1 c2' ->
    exists c3, mcreduce c2 c3 /\ creduce c2' c3.
Proof with eauto using diamond.
  intros. revert dependent c2.
  induction H0; intros...
  - eapply diamond in H as [? [?]]...
  - apply IHclos_refl_trans1 in H as [? [?]].
    apply IHclos_refl_trans2 in H0 as [? [?]]...
Qed.

Lemma confluence: forall c1 c2 c2',
    mcreduce c1 c2 -> mcreduce c1 c2' ->
    exists c3, mcreduce c2 c3 /\ mcreduce c2' c3.
Proof with eauto using strip.
  intros. revert dependent c2'.
  induction H; intros...
  - eapply strip in H as [? [?]]... 
  - apply IHclos_refl_trans1 in H1 as [? [?]].
    apply IHclos_refl_trans2 in H1 as [? [?]]...
Qed.

(** Termination *)

Inductive nf : comp -> Prop :=
| Nf_Abs : forall c,
    nf (tm_abs c)
| Nf_Produce : forall c,
    nf (tm_produce c).

Inductive halt : comp -> Prop :=
| Halt : forall c c', mcstep c c' -> nf c' -> halt c.

Hint Constructors nf : core.
Hint Constructors halt : core.

Lemma creduce_val : forall c c',
    creduce c c' -> nf c -> nf c'.
Proof with eauto.
  intros. destruct H0; inversion H... Qed.

Lemma icreduce_inv_nf : forall c c',
    icreduce c c' -> nf c' -> nf c.
Proof with eauto.
  intros. induction H; try solve [inversion H0]... Qed.

Lemma micreduce_inv_nf : forall c c',
    micreduce c c' -> nf c' -> nf c.
Proof with eauto using icreduce_inv_nf.
  intros. induction H... Qed.

Lemma rhalt_implies_halt : forall c c',
    mcreduce c c' -> nf c' -> halt c.
Proof with eauto using micreduce_inv_nf.
  intros. apply mreduce_implies_mstep_mireduce in H as [? [?]]... Qed.

Lemma mreduce_inv_preserves_halt: forall c c',
    mcreduce c c' -> halt c' -> halt c.
Proof with eauto using rhalt_implies_halt.
  intros. destruct H0... Qed.

(* Theorem 10: Adequacy of Reduction *)
Lemma reduce_preserves_halt: forall t1 t2,
    creduce t1 t2 -> halt t1 -> halt t2.
Proof with eauto using rhalt_implies_halt, creduce_val.
  intros. destruct H0.
  apply mstep_implies_mcreduce in H0...
  eapply strip in H as [? [?]]... Qed.

Hint Resolve reduce_preserves_halt.

