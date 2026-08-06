(*
  定理：R 的子集 E 是连通的 ↔ E 满足区间性质

  区间性质：∀ x, y ∈ E, ∀ z, x < z < y → z ∈ E

  连通性定义（拓扑）：不存在两个不相交开集 U, V 使得
  E ⊆ U ∪ V 且 E ∩ U ≠ ∅ 且 E ∩ V ≠ ∅
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Rtopology.
From Stdlib Require Import Lra.
From Stdlib Require Import RIneq.
From Stdlib Require Import Raxioms.
From Stdlib Require Import Classical.

Open Scope R_scope.

(*****************************************************************************)
(* 定义                                                                       *)
(*****************************************************************************)

(* 连通性：不存在两个不相交开集使其分割 E *)
Definition connected_subset (E : R -> Prop) : Prop :=
  forall U V : R -> Prop,
    open_set U -> open_set V ->
    included E (fun x => U x \/ V x) ->
    (exists x, E x /\ U x) ->
    (exists x, E x /\ V x) ->
    exists x, E x /\ U x /\ V x.

(* 区间性质（凸性） *)
Definition interval_property (E : R -> Prop) : Prop :=
  forall x y z : R,
    E x -> E y -> Rlt x z -> Rlt z y ->
    E z.

(*****************************************************************************)
(* 辅助引理                                                                   *)
(*****************************************************************************)

Lemma Rabs_lt_between :
  forall x y : R,
    Rabs x < y -> - y < x /\ x < y.
Proof.
  intros x y H.
  unfold Rabs in H.
  destruct (Rcase_abs x).
  - split; nra.
  - split; nra.
Qed.

Lemma open_set_lt :
  forall c : R, open_set (fun x => x < c).
Proof.
  intros c x Hx.
  assert (Hpos: c - x > 0) by lra.
  exists (mkposreal (c - x) Hpos).
  intros y Hy.
  unfold disc in Hy.
  simpl in Hy.
  apply Rabs_lt_between in Hy.
  destruct Hy as [H1 H2].
  nra.
Qed.

Lemma open_set_gt :
  forall c : R, open_set (fun x => x > c).
Proof.
  intros c x Hx.
  assert (Hpos: x - c > 0) by lra.
  exists (mkposreal (x - c) Hpos).
  intros y Hy.
  unfold disc in Hy.
  simpl in Hy.
  apply Rabs_lt_between in Hy.
  destruct Hy as [H1 H2].
  nra.
Qed.

Lemma interval_contains_closed_interval :
  forall E : R -> Prop,
    interval_property E ->
    forall a b : R,
      E a -> E b -> a <= b ->
      forall x, a <= x -> x <= b -> E x.
Proof.
  intros E HE a b Ha Hb Hab x Hax Hxb.
  destruct (Req_dec a b) as [Heq | Hneq].
  - assert (Hx: x = b) by lra.
    rewrite Hx. assumption.
  - destruct Hax as [Hax_lt | Hax_eq].
    + destruct Hxb as [Hxb_lt | Hxb_eq].
      * eapply HE; [exact Ha | exact Hb | exact Hax_lt | exact Hxb_lt].
      * subst x. assumption.
    + subst x. assumption.
Qed.

Lemma Rmin_pos_R :
  forall a b : R,
    a > 0 -> b > 0 -> Rmin a b > 0.
Proof.
  intros a b Ha Hb.
  unfold Rmin.
  destruct (Rle_dec a b).
  - assumption.
  - assumption.
Qed.

(*****************************************************************************)
(* 辅助引理：区间性质 + 分割假设 → 存在一点同时在两个开集中                 *)
(*****************************************************************************)

Lemma interval_open_sets_intersection :
  forall (E : R -> Prop),
    interval_property E ->
    forall (U V : R -> Prop),
      open_set U -> open_set V ->
      included E (fun x => U x \/ V x) ->
      forall a b : R,
        E a -> U a ->
        E b -> V b ->
        a <= b ->
        exists x, E x /\ U x /\ V x.
Proof.
  intros E HE U V OU OV ECov a b HEa HUa HEb HVb Hab.

  destruct (Req_dec a b) as [Heq | Hneq].
  { rewrite Heq in *. exists b. tauto. }

  assert (Hab': a < b) by nra.

  set (S := fun x => E x /\ U x /\ x < b).

  assert (Hnonempty: exists x, S x).
  { exists a. unfold S.
    split. exact HEa.
    split. exact HUa.
    exact Hab'. }

  assert (Hbounded: bound S).
  { unfold bound. exists b. unfold is_upper_bound.
    intros x [HE' [_ Hx]]. lra. }

  generalize (completeness S Hbounded Hnonempty).
  intros Hcomp. destruct Hcomp as [s Hlub].
  destruct Hlub as [HUB Hleast].

  assert (Hsb: s <= b).
  { apply Hleast. intros x [_ [_ Hx]]. lra. }

  assert (Has: a <= s).
  { specialize (HUB a). unfold S in HUB. tauto. }

  assert (HEs: E s).
  { eapply interval_contains_closed_interval with (a := a) (b := b);
      [exact HE | exact HEa | exact HEb | exact Hab | exact Has | exact Hsb]. }

  specialize (ECov s HEs).
  destruct ECov as [HsU | HsV].

  (* Case: s ∈ U *)
  + destruct (OU s HsU) as [eps HUeps].
    destruct (Req_dec s b) as [Heq_s | Hneq_s].
    - rewrite Heq_s in *. exists b. tauto.
    - assert (Hsb': s < b) by nra.
      set (epsR := pos eps).
      assert (HepsR: epsR > 0) by (exact (cond_pos eps)).
      set (delta := Rmin (epsR / 2) ((b - s) / 2)).
      assert (Hdelta_pos: delta > 0).
      { unfold delta. unfold Rmin.
        destruct (Rle_dec (epsR / 2) ((b - s) / 2)); nra. }
      set (t := s + delta).
    assert (HtU: U t).
    { apply HUeps. unfold disc. simpl.
      unfold t.
      assert (Hdelta_nonneg: delta >= 0).
      { unfold delta. unfold Rmin.
        destruct (Rle_dec (epsR / 2) ((b - s) / 2)); lra. }
      assert (Hrewrite: s + delta - s = delta).
      { unfold Rminus.
        rewrite (Rplus_comm s delta).
        rewrite Rplus_assoc.
        rewrite Rplus_opp_r.
        rewrite Rplus_0_r.
        reflexivity. }
      rewrite Hrewrite.
      rewrite (Rabs_right delta Hdelta_nonneg).
      unfold delta. unfold Rmin.
      assert (Hhalf: epsR / 2 < epsR) by lra.
      destruct (Rle_dec (epsR / 2) ((b - s) / 2)).
      * exact Hhalf.
      * assert (Htmp: (b - s) / 2 < epsR) by nra. exact Htmp. }
    assert (HtE: E t).
    { assert (Htleb: t <= b).
      { unfold t. unfold delta. unfold Rmin.
        destruct (Rle_dec (epsR / 2) ((b - s) / 2)); lra. }
      eapply interval_contains_closed_interval with (a := a) (b := b);
        [exact HE | exact HEa | exact HEb | exact Hab | unfold t; lra | exact Htleb]. }
    assert (Htb: t < b).
    { unfold t. unfold delta. unfold Rmin.
      destruct (Rle_dec (epsR / 2) ((b - s) / 2)).
      - assert (H1': epsR / 2 * 2 <= (b - s) / 2 * 2) by lra.
        assert (H2: epsR / 2 * 2 = epsR). { field. }
        rewrite H2 in H1'.
        assert (H3: (b - s) / 2 * 2 = b - s). { field. }
        rewrite H3 in H1'.
        assert (H4: s + epsR / 2 < s + epsR) by lra.
        assert (H5: s + epsR <= b) by lra.
        lra.
      - lra. }
    specialize (HUB t). unfold S in HUB.
    assert (HtS: E t /\ U t /\ t < b) by tauto.
    apply HUB in HtS.
    assert (Hcontr: t > s).
    { unfold t. lra. }
    exfalso. lra.

  (* Case: s ∈ V *)
  + destruct (OV s HsV) as [eps HVeps].
    set (epsR := pos eps).
    assert (HepsR: epsR > 0) by (exact (cond_pos eps)).
    assert (Hexists: exists x, S x /\ s - epsR / 2 < x).
    { assert (Hcontr: ~ is_upper_bound S (s - epsR / 2)).
      { intro HUB'. apply Hleast in HUB'. exfalso. lra. }
      unfold is_upper_bound in Hcontr.
      apply not_all_ex_not in Hcontr.
      destruct Hcontr as [x Hx].
      exists x. split.
      - apply not_imply_elim in Hx. assumption.
      - apply not_imply_elim2 in Hx. lra. }
    destruct Hexists as [x [HSx Hx_close]].
    assert (Hx_le_s: x <= s).
    { unfold S in HSx. apply HUB. exact HSx. }
    unfold S in HSx.
    destruct HSx as [HE_x [HU_x Hxb]].
    assert (Hx_in_V: V x).
    { apply HVeps. unfold disc. simpl.
      assert (Hle: Rabs (x - s) = s - x).
      { assert (Hdiff: x - s <= 0) by lra.
        rewrite (Rabs_left1 _ Hdiff).
        lra. }
      rewrite Hle.
      assert (Hhalf: s - x < epsR / 2) by lra.
      assert (Heps: epsR / 2 < epsR) by lra.
      change (Rabs (x - s) < eps) with (Rabs (x - s) < epsR).
      assert (Htrans: s - x < epsR) by lra.
      exact Htrans. }
    exists x. tauto.
Qed.

(*****************************************************************************)
(* 主要定理                                                                   *)
(*****************************************************************************)

(* 定理 1：连通 → 区间性质 *)
Theorem connected_impl_interval :
  forall E : R -> Prop,
    connected_subset E ->
    interval_property E.
Proof.
  intros E Hconn x y z Hx Hy Hxz Hzy.
  destruct (classic (E z)).
  { assumption. }
  set (U := fun t => t < z).
  set (V := fun t => t > z).
  assert (HOU: open_set U) by (unfold U; apply open_set_lt).
  assert (HOV: open_set V) by (unfold V; apply open_set_gt).
  assert (ECov: included E (fun t => U t \/ V t)).
  { unfold included, U, V. intros t Ht.
    destruct (Rtotal_order t z) as [Hlt | [Heq | Hgt]].
    - left. assumption.
    - rewrite Heq in *. contradiction.
    - right. assumption. }
  assert (EU: exists t, E t /\ U t).
  { exists x. split; [assumption | exact Hxz]. }
  assert (EV: exists t, E t /\ V t).
  { exists y. split; [assumption | exact Hzy]. }
  specialize (Hconn U V HOU HOV ECov EU EV).
  destruct Hconn as [c [HEc [HUc HVc]]].
  unfold U, V in HUc, HVc.
  exfalso. nra.
Qed.

(* 定理 2：区间性质 → 连通 *)
Theorem interval_impl_connected :
  forall E : R -> Prop,
    interval_property E ->
    connected_subset E.
Proof.
  intros E HE U V OU OV ECov EU EV.
  destruct EU as [a [HEa HUa]].
  destruct EV as [b [HEb HVb]].
  destruct (Rle_dec a b).
  - apply interval_open_sets_intersection with (a := a) (b := b).
    exact HE.
    exact OU.
    exact OV.
    exact ECov.
    exact HEa.
    exact HUa.
    exact HEb.
    exact HVb.
    assumption.
  - assert (ECov': included E (fun x => V x \/ U x)).
    { unfold included in ECov. unfold included. intros x Hx. specialize (ECov x Hx). tauto. }
    assert (Hba: b <= a) by lra.
    specialize (interval_open_sets_intersection E HE V U OV OU ECov' b a HEb HVb HEa HUa) as H.
    specialize (H Hba).
    destruct H as [x [H1 [H2 H3]]].
    exists x. tauto.
Qed.

(*****************************************************************************)
(* 等价定理                                                                   *)
(*****************************************************************************)

Theorem connected_subset_interval_equiv :
  forall E : R -> Prop,
    connected_subset E <-> interval_property E.
Proof.
  intros E. split.
  - apply connected_impl_interval.
  - apply interval_impl_connected.
Qed.
