(*
 * Remove Unused — SSA infrastructure proofs.
 *
 * Key theorem: nop_output_not_used_as_operand
 *   Under wf_ssa + ssa_form, NOP'd variables are never used
 *   as operands. This discharges the extern in
 *   remove_unused_single_pass_correct_proof.
 *
 * Strategy:
 *   Same block: live_vars_at_uses + live_vars_at_propagate_range gives
 *     v live at def+1, contradicting NOP condition.
 *   Cross block: v live at use block, not killed on path to def block
 *     (SSA single def), so v live at def block exit, contradicting
 *     nop_output_not_live_at_exit.
 *)

Theory removeUnusedSsaProofs
Ancestors
  removeUnusedProofs removeUnusedDefs
  passSimulationDefs passSimulationProps analysisSimProps
  livenessProofs livenessDefs
  dfAnalyzeProofs dfAnalyzeDefs dfAnalyzeProps dfHelperProofs
  venomInstProps venomWf venomExecProps
  stateEquiv stateEquivProps stateEquivProofs
  execEquivProps cfgTransformProps cfgDefs
  passSharedDefs passSharedProps
  venomInst venomState venomExecSemantics
  indexedLists cfgAnalysisProps pointerConfinedDefs
  worklistDefs list rich_list combin

(* ===== Fixpoint bridge: edge_transfer ⊆ live_exit ===== *)

(* FOLDL list_union preserves accumulator membership *)
Theorem foldl_list_union_acc[local]:
  !l v acc. MEM v acc ==> MEM v (FOLDL list_union acc l)
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[list_union_mem_proof]
QED

(* Element in a component list is in FOLDL list_union *)
Theorem mem_foldl_list_union[local]:
  !l v xs acc. MEM xs l /\ MEM v xs ==>
               MEM v (FOLDL list_union acc l)
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >> gvs[]
  >- (irule foldl_list_union_acc >> simp[list_union_mem_proof])
  >- (first_x_assum irule >> metis_tac[])
QED

(* Membership in df_joined_val for Backward with NONE entry_val *)
Theorem mem_df_joined_val_backward[local]:
  !join edge_transfer ctx cfg result lbl succ_lbl v.
    MEM succ_lbl (cfg_succs_of cfg lbl) /\
    MEM v (edge_transfer ctx succ_lbl lbl
             (df_boundary [] result succ_lbl)) ==>
    MEM v (df_joined_val Backward [] list_union edge_transfer ctx NONE
             cfg result lbl)
Proof
  rpt strip_tac >> simp[df_joined_val_def, LET_THM] >>
  Cases_on `MAP (\nbr. edge_transfer ctx nbr lbl
    (df_boundary [] result nbr)) (cfg_succs_of cfg lbl)` >- (
    fs[listTheory.MAP_EQ_NIL] >> fs[]) >>
  REWRITE_TAC [listTheory.list_case_def] >>
  irule mem_foldl_list_union >>
  qexists_tac `edge_transfer ctx succ_lbl lbl
    (df_boundary [] result succ_lbl)` >>
  qpat_x_assum `MAP _ _ = _` (SUBST1_TAC o SYM) >>
  simp[listTheory.MEM_MAP] >> qexists_tac `succ_lbl` >> simp[]
QED

val df_at_inter_liveness = let
  val th0 = INST_TYPE [alpha |-> ``:string list``,
                       beta |-> ``:basic_block list``] df_at_inter_transfer
  val th1 = CONV_RULE (SIMP_CONV (srw_ss()) [LET_THM]) th0
  val th2 = SPEC_ALL th1
  val th3 = GENL [``lbl:string``, ``bb:basic_block``] th2
  in CONV_RULE (STRIP_QUANT_CONV (REWR_CONV (GSYM AND_IMP_INTRO))) th3
  end;

Theorem edge_transfer_subset_live_exit[local]:
  !fn pred_lbl pred_bb succ_lbl v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
      MEM pred_lbl cfg.cfg_dfs_pre /\
      lookup_block pred_lbl fn.fn_blocks = SOME pred_bb /\
      MEM succ_lbl (cfg_succs_of cfg pred_lbl) /\
      MEM v (liveness_edge_transfer fn.fn_blocks succ_lbl pred_lbl
               (df_boundary [] lr succ_lbl)) ==>
      MEM v (live_vars_at lr pred_lbl (LENGTH pred_bb.bb_instructions))
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >>
  strip_tac >> strip_tac >>
  simp[live_vars_at_def, liveness_analyze_def] >>
  mp_tac (Q.SPEC `fn` liveness_convergence) >>
  simp[LET_THM, liveness_analyze_def] >> strip_tac >>
  first_x_assum (mp_tac o MATCH_MP df_at_inter_liveness) >>
  disch_then (qspecl_then [`pred_lbl`, `pred_bb`] mp_tac) >>
  simp[] >> strip_tac >>
  irule mem_df_joined_val_backward >>
  qexists_tac `succ_lbl` >> fs[liveness_analyze_def]
QED

(* ===== NOP output liveness helpers ===== *)

Theorem remove_unused_inst_nop_outputs_not_live[local]:
  !live fence inst. remove_unused_inst live fence inst = mk_nop_inst inst ==>
    EVERY (\v. ~MEM v live) inst.inst_outputs
Proof
  rpt gen_tac >> simp[remove_unused_inst_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  simp[mk_nop_inst_def, instruction_component_equality] >>
  rpt strip_tac >> gvs[]
QED

Theorem nop_output_not_live_at_exit:
  !fn lr cfg lbl bb idx inst v fence.
    wf_function fn /\ ssa_form fn /\
    lr = liveness_analyze fn /\
    cfg = cfg_analyze fn /\
    MEM lbl cfg.cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = inst /\
    remove_unused_inst
      (live_after_at lr lbl idx (LENGTH bb.bb_instructions))
      (fence idx) inst = mk_nop_inst inst /\
    MEM v inst.inst_outputs ==>
    ~MEM v (live_vars_at lr lbl (LENGTH bb.bb_instructions))
Proof
  rpt strip_tac >>
  drule remove_unused_inst_nop_outputs_not_live >> strip_tac >>
  gvs[listTheory.EVERY_MEM] >>
  gvs[live_after_at_def] >>
  Cases_on `idx + 1 < LENGTH bb.bb_instructions` >> gvs[] >>
  mp_tac not_live_forward_in_block >>
  disch_then (qspecl_then [`fn`, `lbl`, `bb`, `idx + 1`,
                           `LENGTH bb.bb_instructions`, `v`] mp_tac) >>
  simp[LET_THM] >>
  rpt gen_tac >> simp[inst_defs_def] >>
  spose_not_then strip_assume_tac >> gvs[] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `idx < LENGTH bb.bb_instructions` by simp[] >>
  `k = idx` by metis_tac[ssa_form_no_dup_in_block] >>
  gvs[]
QED

(* v not live at idx+1 (directly from NOP condition) *)
Theorem nop_output_not_live_after_def[local]:
  !fn lr cfg lbl bb idx inst v fence.
    wf_function fn /\ ssa_form fn /\
    lr = liveness_analyze fn /\
    cfg = cfg_analyze fn /\
    MEM lbl cfg.cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = inst /\
    remove_unused_inst
      (live_after_at lr lbl idx (LENGTH bb.bb_instructions))
      (fence idx) inst = mk_nop_inst inst /\
    MEM v inst.inst_outputs ==>
    ~MEM v (live_vars_at lr lbl (SUC idx))
Proof
  rpt strip_tac >>
  drule remove_unused_inst_nop_outputs_not_live >> strip_tac >>
  gvs[listTheory.EVERY_MEM, live_after_at_suc]
QED

(* ===== Main theorem: NOP'd variables not used as operands ===== *)

(* Helper: operand var in inst_uses *)
Theorem mem_var_operand_vars[local]:
  !ops v. MEM (Var v) ops ==> MEM v (operand_vars ops)
Proof
  Induct >> simp[operand_vars_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `operand_var h` >> simp[] >>
  Cases_on `h` >> gvs[operand_var_def]
QED

Theorem operand_var_in_inst_uses[local]:
  !inst v. MEM (Var v) inst.inst_operands ==>
           MEM v (inst_uses inst)
Proof
  simp[inst_uses_def] >> metis_tac[mem_var_operand_vars]
QED

(* fn_insts_blocks = FLAT (MAP bb_instructions ...) *)
Theorem fn_insts_blocks_flat:
  !bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* ALL_DISTINCT (FLAT (MAP f l)) + v in two different elements => F *)
Theorem all_distinct_flat_map_cross[local]:
  !f l (x:'a) y (v:'b).
    ALL_DISTINCT (FLAT (MAP f l)) /\
    MEM x l /\ MEM y l /\ x <> y /\
    MEM v (f x) /\ MEM v (f y) ==> F
Proof
  Induct_on `l` >> rw[MEM_FLAT, MEM_MAP, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* ALL_DISTINCT (FLAT (MAP f l)) + MEM x l => ALL_DISTINCT (f x) *)
Theorem all_distinct_flat_map_member:
  !(f:'a -> 'b list) l x.
    ALL_DISTINCT (FLAT (MAP f l)) /\ MEM x l ==> ALL_DISTINCT (f x)
Proof
  Induct_on `l` >> rw[ALL_DISTINCT_APPEND] >> metis_tac[]
QED


(* Strongest SSA uniqueness: same output var ⇒ same instruction AND same block *)
Theorem ssa_unique_output_block[local]:
  !fn bb1 inst1 bb2 inst2 v.
    ssa_form fn /\
    MEM bb1 fn.fn_blocks /\ MEM inst1 bb1.bb_instructions /\
    MEM v inst1.inst_outputs /\
    MEM bb2 fn.fn_blocks /\ MEM inst2 bb2.bb_instructions /\
    MEM v inst2.inst_outputs ==> bb1 = bb2 /\ inst1 = inst2
Proof
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  rename1 `ssa_form func` >>
  gvs[ssa_form_def, fn_insts_def, fn_insts_blocks_flat] >>
  (* The key: rewrite the flat-inst ALL_DISTINCT to block-level form *)
  `!bbs. FLAT (MAP (\i:instruction. i.inst_outputs)
              (FLAT (MAP (\bb:basic_block. bb.bb_instructions) bbs))) =
         FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
              bbs)` by
    rw[MAP_FLAT, FLAT_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  fs[] >>
  (* Specialize the cross lemma for blocks *)
  qabbrev_tac `bouts = \bb:basic_block.
    FLAT (MAP (\i:instruction. i.inst_outputs) bb.bb_instructions)` >>
  `MEM v (bouts bb1) /\ MEM v (bouts bb2)` by
    (simp[Abbr `bouts`, MEM_FLAT, MEM_MAP] >> metis_tac[])
  >- (
    (* bb1 ≠ bb2: block-level *)
    metis_tac[all_distinct_flat_map_cross])
  >- (
    (* inst1 ≠ inst2: within-block *)
    Cases_on `bb1 = bb2`
    >- (
      gvs[] >>
      drule_all all_distinct_flat_map_member >> strip_tac >>
      gvs[Abbr `bouts`] >>
      metis_tac[all_distinct_flat_map_cross])
    >- metis_tac[all_distinct_flat_map_cross])
QED

(* ===== Boilerplate: reachability / lookup helpers ===== *)

(* is_fn_path → RTC fn_cfg_edge *)
Theorem is_fn_path_rtc[local]:
  !fn path. is_fn_path fn path /\ path <> [] ==>
    (fn_cfg_edge fn)^* (HD path) (LAST path)
Proof
  Induct_on `path` >> simp[is_fn_path_def] >>
  rpt strip_tac >> Cases_on `path` >> gvs[is_fn_path_def] >>
  irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >>
  qexists_tac `h'` >> simp[]
QED

(* RTC fn_cfg_edge → is_fn_path *)
Theorem rtc_to_fn_path[local]:
  !fn x y. (fn_cfg_edge fn)^* x y ==>
    ?path. is_fn_path fn path /\ path <> [] /\ HD path = x /\ LAST path = y
Proof
  gen_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[]
  >- (qexists_tac `[x]` >> simp[is_fn_path_def])
  >- (qexists_tac `x::path` >> Cases_on `path` >> gvs[is_fn_path_def])
QED

(* is_fn_path prefix: if d ∈ path, take prefix up to d *)
Theorem is_fn_path_prefix[local]:
  !fn path d. is_fn_path fn path /\ MEM d path ==>
    ?pre. is_fn_path fn (pre ++ [d]) /\ HD (pre ++ [d]) = HD path
Proof
  Induct_on `path` >> simp[] >> rpt strip_tac >> gvs[]
  >- (qexists_tac `[]` >> simp[is_fn_path_def])
  >- (Cases_on `path` >> gvs[is_fn_path_def]
      >- (qexists_tac `[h]` >> simp[is_fn_path_def])
      >- (first_x_assum (qspecl_then [`fn`, `d`] mp_tac) >> simp[] >>
          strip_tac >> qexists_tac `h::pre` >>
          Cases_on `pre` >> gvs[is_fn_path_def]))
QED

(* fn_dominates → dominator is reachable *)
Theorem fn_dominates_dom_reachable[local]:
  !fn d n. fn_dominates fn d n ==> fn_reachable fn d
Proof
  rw[fn_dominates_def, fn_reachable_def] >>
  qexists_tac `entry` >> simp[] >>
  drule rtc_to_fn_path >> strip_tac >>
  `MEM d path` by (first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule_all is_fn_path_prefix >> strip_tac >>
  drule is_fn_path_rtc >>
  simp[listTheory.APPEND_eq_NIL]
QED

Theorem fn_reachable_in_cfg_dfs_pre[local]:
  !fn lbl. wf_function fn /\ fn_reachable fn lbl ==>
    MEM lbl (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  gvs[fn_reachable_def, fn_entry_label_def, entry_block_def] >>
  Cases_on `NULL fn.fn_blocks` >> gvs[] >>
  (* Goal: MEM lbl cfg_dfs_pre. Strategy: show cfg_reachable_of *)
  `cfg_reachable_of (cfg_analyze fn) lbl` suffices_by (
    strip_tac >>
    `wf_function fn` by simp[] >>
    drule cfg_analyze_reachable_sets >> strip_tac >>
    fs[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  (* cfg_reachable_of ⟺ cfg_path from entry *)
  drule_at Any cfg_analyze_semantic_reachability >>
  disch_then (qspecl_then [`HD fn.fn_blocks`, `lbl`] mp_tac) >>
  simp[entry_block_def] >> strip_tac >>
  (* cfg_path from RTC fn_cfg_edge via RTC_MONOTONE *)
  pop_assum kall_tac >>
  simp[cfg_path_def] >>
  irule relationTheory.RTC_MONOTONE >>
  qexists_tac `fn_cfg_edge fn` >> simp[] >>
  rw[fn_cfg_edge_def] >>
  irule bb_succs_in_cfg_succs >> gvs[wf_function_def]
QED

Theorem wf_lookup_block[local]:
  !fn bb. wf_function fn /\ MEM bb fn.fn_blocks ==>
    lookup_block bb.bb_label fn.fn_blocks = SOME bb
Proof
  rpt strip_tac >>
  irule MEM_lookup_block >> simp[] >>
  gvs[wf_function_def, fn_labels_def]
QED

(* lookup_block returns a block with matching label *)
Theorem lookup_block_label[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  rw[lookup_block_def] >>
  pop_assum mp_tac >> Induct_on `bbs` >> simp[listTheory.FIND_thm] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >> gvs[]
QED

(* is_fn_path can be extended by one edge *)
Theorem is_fn_path_snoc[local]:
  !fn path lbl. is_fn_path fn path /\ path <> [] /\
    fn_cfg_edge fn (LAST path) lbl ==>
    is_fn_path fn (path ++ [lbl])
Proof
  Induct_on `path` >> simp[is_fn_path_def] >>
  rpt strip_tac >> Cases_on `path` >> gvs[is_fn_path_def]
QED

(* fn_dominates predecessor: if d dominates n, d ≠ n, and p → n is CFG edge,
   and p is reachable, then d dominates p *)
Theorem fn_dominates_predecessor[local]:
  !fn d n p.
    fn_dominates fn d n /\ d <> n /\
    fn_cfg_edge fn p n /\ fn_reachable fn p ==>
    fn_dominates fn d p
Proof
  rw[fn_dominates_def] >> rpt strip_tac >>
  (* path goes from entry to p; extend by edge p → n to get path to n *)
  `is_fn_path fn (path ++ [n])` by (
    irule is_fn_path_snoc >> simp[]) >>
  `MEM d (path ++ [n])` by (
    first_x_assum (qspec_then `path ++ [n]` mp_tac) >>
    impl_tac >- (
      simp[listTheory.LAST_APPEND_CONS] >>
      Cases_on `path` >> gvs[]
    ) >>
    simp[]
  ) >>
  gvs[listTheory.MEM_APPEND]
QED

(* phi_pairs produces only vars present in the operand list *)
Theorem phi_pairs_mem_var[local]:
  !ops l v. MEM (l, v) (phi_pairs ops) ==> MEM (Var v) ops
Proof
  ho_match_mp_tac phi_pairs_ind >> rw[phi_pairs_def] >> gvs[] >> metis_tac[]
QED

(* fn_cfg_edge → cfg_succs_of (bridge from path-level to analysis-level) *)
Theorem fn_cfg_edge_succs[local]:
  !fn a b. wf_function fn /\ fn_cfg_edge fn a b ==>
    MEM b (cfg_succs_of (cfg_analyze fn) a)
Proof
  rw[fn_cfg_edge_def] >>
  irule bb_succs_in_cfg_succs >> gvs[wf_function_def]
QED


(* Helper: fn_cfg_edge target has a block *)
Theorem fn_cfg_edge_target_block[local]:
  !fn a b. wf_function fn /\ fn_cfg_edge fn a b ==>
    ?bb. lookup_block b fn.fn_blocks = SOME bb
Proof
  rw[fn_cfg_edge_def, wf_function_def] >> rpt strip_tac >>
  `MEM b (fn_labels fn)` by metis_tac[fn_succs_closed_def] >>
  gvs[fn_labels_def, MEM_MAP] >>
  metis_tac[MEM_lookup_block]
QED

(* Helper: is_fn_path init (drop last element) *)
Theorem is_fn_path_init[local]:
  !fn path x. is_fn_path fn (SNOC x path) ==> is_fn_path fn path
Proof
  Induct_on `path` >> simp[is_fn_path_def, SNOC] >> rpt strip_tac >>
  Cases_on `path` >> gvs[SNOC, is_fn_path_def] >>
  metis_tac[]
QED

(* Helper: is_fn_path last edge *)
Theorem is_fn_path_last_edge[local]:
  !fn path x. is_fn_path fn (SNOC x path) /\ path <> [] ==>
    fn_cfg_edge fn (LAST path) x
Proof
  Induct_on `path` >> simp[SNOC] >> rpt strip_tac >>
  Cases_on `path` >> gvs[SNOC, is_fn_path_def, listTheory.LAST_DEF]
QED

(* Helper: is_fn_path suffix — if d ∈ path, take suffix from d *)
Theorem is_fn_path_suffix[local]:
  !fn path d. is_fn_path fn path /\ MEM d path ==>
    ?suffix. is_fn_path fn (d :: suffix) /\
             LAST (d :: suffix) = LAST path
Proof
  Induct_on `path` >> simp[] >> rpt strip_tac >> gvs[]
  >- (qexists_tac `path` >> Cases_on `path` >> gvs[is_fn_path_def])
  >- (Cases_on `path` >> gvs[is_fn_path_def] >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `suffix` >> simp[] >>
      Cases_on `suffix` >> gvs[listTheory.LAST_DEF])
QED

(* Helper: reachability extends by one cfg edge *)
Theorem fn_reachable_step[local]:
  !fn a b. fn_reachable fn a /\ fn_cfg_edge fn a b ==> fn_reachable fn b
Proof
  rw[fn_reachable_def] >> qexists_tac `entry` >> simp[] >>
  metis_tac[relationTheory.RTC_RTC, relationTheory.RTC_SINGLE]
QED

(* Helper: reachable node along path from reachable start *)
Theorem is_fn_path_all_reachable[local]:
  !fn path lbl. is_fn_path fn path /\ path <> [] /\
    fn_reachable fn (HD path) /\ MEM lbl path ==>
    fn_reachable fn lbl
Proof
  Induct_on `path` >> simp[] >> rpt strip_tac >> gvs[] >>
  Cases_on `path` >> gvs[is_fn_path_def, listTheory.MEM]
  >- metis_tac[fn_reachable_step]
  >- (first_x_assum irule >> simp[] >> metis_tac[fn_reachable_step])
QED

(* Helper: reachable implies has a block (via wf_function) *)
Theorem fn_reachable_has_block[local]:
  !fn lbl. wf_function fn /\ fn_reachable fn lbl ==>
    ?bb. lookup_block lbl fn.fn_blocks = SOME bb
Proof
  rpt strip_tac >> gvs[fn_reachable_def] >>
  gvs[Once relationTheory.RTC_CASES2]
  >- (
    (* lbl = entry: entry block exists *)
    gvs[fn_entry_label_def, entry_block_def] >>
    Cases_on `fn.fn_blocks` >> gvs[] >>
    rename1 `hd :: tl` >>
    qexists_tac `hd` >>
    irule MEM_lookup_block >>
    gvs[wf_function_def, fn_labels_def])
  >- metis_tac[fn_cfg_edge_target_block]
QED

(* If v is live at block p's exit, v is only defined at d_bb, and p <> d,
   then v is live at p's entry (backward propagation through non-defining block) *)
Theorem live_backward_step[local]:
  !fn v d d_bb p p_bb.
    wf_function fn /\ ssa_form fn /\
    p <> d /\
    lookup_block p fn.fn_blocks = SOME p_bb /\
    fn_reachable fn p /\
    MEM v (live_vars_at (liveness_analyze fn) p
             (LENGTH p_bb.bb_instructions)) /\
    lookup_block d fn.fn_blocks = SOME d_bb /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
              MEM v inst.inst_outputs ==> bb = d_bb) ==>
    MEM v (live_vars_at (liveness_analyze fn) p 0)
Proof
  rpt strip_tac >>
  `MEM p_bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `!k. k < LENGTH p_bb.bb_instructions ==>
       ~MEM v (inst_defs (EL k p_bb.bb_instructions))` by (
    rpt strip_tac >> gvs[inst_defs_def] >>
    `MEM (EL k p_bb.bb_instructions) p_bb.bb_instructions`
      by metis_tac[MEM_EL] >>
    `p_bb = d_bb` by metis_tac[] >>
    `p = d` by metis_tac[lookup_block_label] >>
    gvs[]) >>
  `MEM p (cfg_analyze fn).cfg_dfs_pre` by
    (irule fn_reachable_in_cfg_dfs_pre >> simp[]) >>
  Cases_on `LENGTH p_bb.bb_instructions = 0` >- gvs[] >>
  drule (SIMP_RULE std_ss [LET_THM] live_vars_at_propagate_range) >>
  disch_then (qspecl_then [`p`, `p_bb`, `0`,
                           `LENGTH p_bb.bb_instructions`, `v`] mp_tac) >>
  simp[]
QED

(* Liveness propagates backward along a CFG path from d to n:
   if v is live at entry of LAST(path), v is only defined at d_bb,
   and LAST(path) <> d, then v is live at d's exit.

   SNOC induction: peel off the last node and work backward. *)
Theorem live_backward_along_path[local]:
  !path fn v d d_bb.
    wf_function fn /\ ssa_form fn /\
    is_fn_path fn (d :: path) /\ path <> [] /\
    LAST path <> d /\
    fn_reachable fn d /\
    lookup_block d fn.fn_blocks = SOME d_bb /\
    MEM v (live_vars_at (liveness_analyze fn) (LAST path) 0) /\
    (* v only defined at d_bb *)
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
              MEM v inst.inst_outputs ==> bb = d_bb) ==>
    MEM v (live_vars_at (liveness_analyze fn) d
             (LENGTH d_bb.bb_instructions))
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[] >> rpt strip_tac >>
  gvs[SNOC_APPEND, listTheory.LAST_APPEND_CONS] >>
  (* After SNOC induction: path was SNOC x path', now x is last node *)
  (* Assumptions have path ++ [x] form; LAST simplified to x *)
  `is_fn_path fn (SNOC x (d :: path))` by simp[SNOC_APPEND] >>
  `fn_cfg_edge fn (LAST (d :: path)) x` by
    metis_tac[is_fn_path_last_edge, listTheory.NOT_NIL_CONS] >>
  `is_fn_path fn (d :: path)` by metis_tac[is_fn_path_init] >>
  qabbrev_tac `p = LAST (d :: path)` >>
  `MEM p (d :: path)` by simp[Abbr `p`, rich_listTheory.MEM_LAST] >>
  `fn_reachable fn p` by
    metis_tac[is_fn_path_all_reachable, HD, listTheory.NOT_NIL_CONS] >>
  `fn_reachable fn x` by metis_tac[fn_reachable_step] >>
  `?x_bb. lookup_block x fn.fn_blocks = SOME x_bb` by
    (irule fn_cfg_edge_target_block >> metis_tac[]) >>
  `?p_bb. lookup_block p fn.fn_blocks = SOME p_bb` by
    (irule fn_reachable_has_block >> simp[]) >>
  (* v not PHI output at x_bb (v only defined at d_bb, x <> d) *)
  `!inst. MEM inst (collect_phis x_bb.bb_instructions) ==>
          ~MEM v inst.inst_outputs` by (
    rpt strip_tac >>
    `x_bb = d_bb` by metis_tac[collect_phis_mem, lookup_block_MEM] >>
    metis_tac[lookup_block_label]) >>
  (* Set up cfg membership *)
  `MEM x (cfg_analyze fn).cfg_dfs_pre` by
    (irule fn_reachable_in_cfg_dfs_pre >> simp[]) >>
  `MEM p (cfg_analyze fn).cfg_dfs_pre` by
    (irule fn_reachable_in_cfg_dfs_pre >> simp[]) >>
  `MEM x (cfg_succs_of (cfg_analyze fn) p)` by
    (irule fn_cfg_edge_succs >> simp[]) >>
  (* v live at x entry → v live at p exit (cross-block) *)
  `MEM v (live_vars_at (liveness_analyze fn) p
                       (LENGTH p_bb.bb_instructions))` by (
    drule (SIMP_RULE std_ss [LET_THM] live_vars_at_cross_block) >>
    disch_then (qspecl_then [`p`, `p_bb`, `x`, `x_bb`, `v`] mp_tac) >>
    simp[]) >>
  Cases_on `p = d`
  >- (
    `p_bb = d_bb` by
      (`lookup_block d fn.fn_blocks = SOME p_bb` by gvs[] >> gvs[]) >>
    gvs[])
  >- (
    `MEM v (live_vars_at (liveness_analyze fn) p 0)` by
      (irule live_backward_step >> simp[] >>
       metis_tac[]) >>
    `path <> []` by (strip_tac >> gvs[Abbr `p`]) >>
    gvs[Abbr `p`, listTheory.LAST_DEF] >>
    first_x_assum irule >> simp[] >> metis_tac[])
QED

(* Dominator version: d dominates n, d <> n, v live at n entry *)
Theorem live_at_entry_backward_to_dominator[local]:
  !fn v d d_bb n.
    wf_function fn /\ ssa_form fn /\
    fn_dominates fn d n /\ d <> n /\
    lookup_block d fn.fn_blocks = SOME d_bb /\
    MEM v (live_vars_at (liveness_analyze fn) n 0) /\
    (* v only defined at d_bb *)
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
              MEM v inst.inst_outputs ==> bb = d_bb) ==>
    MEM v (live_vars_at (liveness_analyze fn) d
             (LENGTH d_bb.bb_instructions))
Proof
  rpt strip_tac >>
  `fn_reachable fn n` by gvs[fn_dominates_def] >>
  gvs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  rename1 `is_fn_path fn path_to_n` >>
  `LAST path_to_n = n` by simp[] >>
  `MEM d path_to_n` by (
    gvs[fn_dominates_def] >>
    first_x_assum (qspec_then `path_to_n` mp_tac) >> simp[]) >>
  drule_all is_fn_path_suffix >> strip_tac >>
  rename1 `is_fn_path fn (d :: suffix)` >>
  `LAST (d :: suffix) = n` by simp[] >>
  Cases_on `suffix` >- gvs[] >>
  `fn_reachable fn d` by (irule fn_dominates_dom_reachable >> metis_tac[]) >>
  irule live_backward_along_path >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `h :: t` >> simp[] >>
  gvs[listTheory.LAST_DEF]
QED

Theorem nop_output_not_used_as_operand:
  !fn v bb inst.
    wf_ssa fn /\ ssa_form fn /\ wf_function fn /\
    v IN single_pass_nop_outputs fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM (Var v) inst.inst_operands ==> F
Proof
  rpt strip_tac >>
  rename1 `wf_ssa func` >>
  (* v is NOP'd at some block B at index idx_b *)
  gvs[single_pass_nop_outputs_def, LET_THM,
      pred_setTheory.IN_BIGUNION, PULL_EXISTS,
      listTheory.MEM_MAP] >>
  rename1 `v IN block_nop_outputs _ _ def_bb` >>
  gvs[block_nop_outputs_def, LET_THM,
      listTheory.MEM_FLAT, MEM_MAPi, PULL_EXISTS] >>
  rename1 `idx_b < LENGTH def_bb.bb_instructions` >>
  `MEM v (EL idx_b def_bb.bb_instructions).inst_outputs /\
   is_removable (EL idx_b def_bb.bb_instructions) /\
   EVERY (\v. ~MEM v (live_after_at (liveness_analyze func)
     def_bb.bb_label idx_b (LENGTH def_bb.bb_instructions)))
     (EL idx_b def_bb.bb_instructions).inst_outputs` by (
    qpat_x_assum `MEM v (if _ then _ else _)` mp_tac >>
    simp[COND_RAND, COND_RATOR]) >>
  qabbrev_tac `def_inst = EL idx_b def_bb.bb_instructions` >>
  qabbrev_tac `lr = liveness_analyze func` >>
  qabbrev_tac `cfg = cfg_analyze func` >>
  qabbrev_tac `fence = \idx. msize_fence lr cfg func def_bb.bb_label idx
                                        def_bb.bb_instructions` >>
  (* lookup_block for both blocks *)
  `lookup_block def_bb.bb_label func.fn_blocks = SOME def_bb` by (
    irule wf_lookup_block >> simp[]) >>
  `lookup_block bb.bb_label func.fn_blocks = SOME bb` by (
    irule wf_lookup_block >> simp[]) >>
  (* v used at (bb, some index) *)
  `MEM v (inst_uses inst)` by (irule operand_var_in_inst_uses >> simp[]) >>
  (* By def_dominates_uses: get dominance of defining block over use block *)
  `?def_bb' def_inst'.
     MEM def_bb' func.fn_blocks /\ MEM def_inst' def_bb'.bb_instructions /\
     MEM v def_inst'.inst_outputs /\
     fn_dominates func def_bb'.bb_label bb.bb_label /\
     (def_bb' = bb ==>
       ?i j. i < j /\ j < LENGTH bb.bb_instructions /\
             EL i bb.bb_instructions = def_inst' /\
             EL j bb.bb_instructions = inst)` by (
    `def_dominates_uses func` by gvs[wf_ssa_def] >>
    fs[def_dominates_uses_def] >>
    first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
    simp[] >> metis_tac[]) >>
  (* The defining block must be def_bb by ssa_form *)
  rename1 `MEM def_bb2 func.fn_blocks` >>
  rename1 `MEM def_inst2 def_bb2.bb_instructions` >>
  `def_bb2 = def_bb /\ def_inst2 = def_inst` by
    metis_tac[ssa_unique_output_block, MEM_EL] >>
  gvs[] >>
  (* Now: fn_dominates fn def_bb.bb_label bb.bb_label *)
  (* Derive reachability: fn_dominates gives fn_reachable bb, and
     since def_bb is on every path to bb, def_bb is also reachable *)
  `fn_reachable func bb.bb_label` by gvs[fn_dominates_def] >>
  `MEM bb.bb_label cfg.cfg_dfs_pre` by (
    simp[Abbr `cfg`] >>
    irule fn_reachable_in_cfg_dfs_pre >> simp[]) >>
  (* def_bb reachable: dominance → dominator reachable *)
  `fn_reachable func def_bb.bb_label` by (
    irule fn_dominates_dom_reachable >> metis_tac[]) >>
  `MEM def_bb.bb_label cfg.cfg_dfs_pre` by (
    simp[Abbr `cfg`] >>
    irule fn_reachable_in_cfg_dfs_pre >> simp[]) >>
  (* v is not live at SUC idx_b *)
  `~MEM v (live_vars_at lr def_bb.bb_label (SUC idx_b))` by (
    `live_after_at lr def_bb.bb_label idx_b
       (LENGTH def_bb.bb_instructions) =
     live_vars_at lr def_bb.bb_label (SUC idx_b)` by
      simp[live_after_at_suc] >>
    gvs[listTheory.EVERY_MEM]) >>
  (* Case split: same block or different block *)
  Cases_on `def_bb = bb`
  >- (
    (* Same block *)
    fs[] >>
    `i = idx_b` by (
      `i < LENGTH bb.bb_instructions` by simp[] >>
      qspecl_then [`func`, `bb`, `v`, `i`, `idx_b`]
        mp_tac ssa_form_no_dup_in_block >>
      simp[markerTheory.Abbrev_def]) >>
    fs[] >>
    gvs[markerTheory.Abbrev_def] >>
    `MEM v (live_vars_at (liveness_analyze func) bb.bb_label j)` by (
      drule live_vars_at_uses >>
      disch_then (qspecl_then [`bb.bb_label`, `bb`, `j`, `v`] mp_tac) >>
      simp_tac std_ss [LET_THM] >> simp[]) >>
    `MEM v (live_vars_at (liveness_analyze func) bb.bb_label (SUC i))` by (
      drule live_vars_at_propagate_range >>
      disch_then (qspecl_then [`bb.bb_label`, `bb`, `SUC i`,
                               `j`, `v`] mp_tac) >>
      simp_tac std_ss [LET_THM] >>
      disch_then match_mp_tac >>
      simp[] >> rpt strip_tac >>
      CCONTR_TAC >> gvs[inst_defs_def] >>
      `k < LENGTH bb.bb_instructions` by simp[] >>
      qspecl_then [`func`, `bb`, `v`, `i`, `k`]
        mp_tac ssa_form_no_dup_in_block >>
      simp[]) >>
    metis_tac[])
  >- (
    (* Cross block: def_bb dominates bb, v live at bb.
       Unfold abbreviations first (safe: last branch, no leak risk) *)
    gvs[markerTheory.Abbrev_def] >>
    (* Derive: pass NOP'd this instruction *)
    `remove_unused_inst
       (live_after_at (liveness_analyze func) def_bb.bb_label idx_b
          (LENGTH def_bb.bb_instructions))
       (msize_fence (liveness_analyze func) (cfg_analyze func) func
          def_bb.bb_label idx_b def_bb.bb_instructions)
       def_bb.bb_instructions❲idx_b❳ =
     mk_nop_inst def_bb.bb_instructions❲idx_b❳` by (
      simp[remove_unused_inst_def] >>
      rpt (IF_CASES_TAC >> gvs[])) >>
    (* v not live at block exit *)
    `~MEM v (live_vars_at (liveness_analyze func) def_bb.bb_label
               (LENGTH def_bb.bb_instructions))` by (
      qspecl_then [`func`, `liveness_analyze func`, `cfg_analyze func`,
        `def_bb.bb_label`, `def_bb`, `idx_b`,
        `def_bb.bb_instructions❲idx_b❳`, `v`,
        `\idx. msize_fence (liveness_analyze func) (cfg_analyze func)
                 func def_bb.bb_label idx def_bb.bb_instructions`]
        mp_tac nop_output_not_live_at_exit >>
      simp[]) >>
    (* v is live at use block entry *)
    `?idx_s. idx_s < LENGTH bb.bb_instructions /\
             EL idx_s bb.bb_instructions = inst` by metis_tac[MEM_EL] >>
    `MEM v (live_vars_at (liveness_analyze func) bb.bb_label idx_s)` by (
      drule live_vars_at_uses >>
      disch_then (qspecl_then [`bb.bb_label`, `bb`, `idx_s`, `v`] mp_tac) >>
      simp_tac std_ss [LET_THM] >> simp[]) >>
    (* Propagate to block entry *)
    `MEM v (live_vars_at (liveness_analyze func) bb.bb_label 0)` by (
      Cases_on `idx_s = 0` >- gvs[] >>
      drule live_vars_at_propagate_range >>
      disch_then (qspecl_then [`bb.bb_label`, `bb`, `0`,
                               `idx_s`, `v`] mp_tac) >>
      simp_tac std_ss [LET_THM] >>
      disch_then match_mp_tac >> simp[] >>
      rpt strip_tac >> CCONTR_TAC >>
      gvs[inst_defs_def] >>
      `k < LENGTH bb.bb_instructions` by simp[] >>
      metis_tac[ssa_unique_output_block, MEM_EL]) >>
    (* v live at use block entry, def_bb dominates use block,
       v only defined at def_bb → v live at def_bb exit — contradiction *)
    `def_bb.bb_label <> bb.bb_label` by (
      strip_tac >> gvs[] >>
      `def_bb = bb` by metis_tac[wf_lookup_block] >> gvs[]) >>
    `MEM v (live_vars_at (liveness_analyze func) def_bb.bb_label
              (LENGTH def_bb.bb_instructions))` by (
      irule live_at_entry_backward_to_dominator >>
      simp[] >>
      conj_tac >- metis_tac[ssa_unique_output_block] >>
      qexists_tac `bb.bb_label` >> simp[]) >>
    metis_tac[])
QED

(* ===== Compose with existing single-pass proof ===== *)

Theorem remove_unused_single_pass_correct_ssa:
  !fuel ctx fn s.
    venom_wf ctx /\ wf_function fn /\ fn_inst_wf fn /\
    wf_ssa fn /\ ssa_form fn /\
    alloca_pointer_confined fn /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb ==>
    let elim = single_pass_nop_outputs fn in
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim)
      (run_function fuel ctx fn s)
      (run_function fuel ctx (remove_unused_single_pass fn) s)
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >>
  irule (SIMP_RULE std_ss [LET_THM] remove_unused_single_pass_correct_proof) >>
  simp[] >> rpt strip_tac >>
  CCONTR_TAC >> fs[] >>
  metis_tac[nop_output_not_used_as_operand]
QED

