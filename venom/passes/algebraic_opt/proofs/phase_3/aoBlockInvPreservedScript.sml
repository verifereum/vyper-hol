(* Phase 3 — block_inv preservation through exec_block.
 *
 * Combines the per-component preservation obligations:
 *   ao_dc_exec_block               (ao_dfg_inv, ao_chain_defined_prefix)
 *   strict_dom_iszero_inv_preserved (strict_dom_iszero_inv)
 *   range_successor_obligation     (range_sound, cfg membership,
 *                                   dfg_sound, ops-defined)
 *   fn_reachable_step              (fn_reachable)
 *
 * TOP-LEVEL: ao_block_inv_preserved
 *)

Theory aoBlockInvPreserved
Ancestors
  algebraicOptDefs aoStepInvObligation aoStrictDomObligation
  assertElimProofs dfgSoundStep rangeAnalysisProofs
  allocaRemapSSA dfgAnalysisProps
  venomExecSemantics venomExecProofs
  venomWf venomState venomInst
Libs
  pairLib BasicProvers

Theorem ao_block_inv_preserved:
  !fn0 dfg ra targets bb fuel ctx s v.
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    wf_function fn0 /\ wf_ssa fn0 /\
    fn_inst_wf fn0 /\
    dfg_block_local fn0 /\
    MEM bb fn0.fn_blocks /\
    s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
    exec_block fuel ctx bb s = OK v /\
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    strict_dom_iszero_inv fn0 dfg s /\
    ao_chain_defined_prefix targets s /\
    range_sound (df_widen_at NONE ra s.vs_current_bb 0) s /\
    MEM s.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre /\
    dfg_sound dfg s.vs_vars /\
    (!vv dinst u. dfg_get_def dfg vv = SOME dinst /\
       vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==> u IN FDOM s.vs_vars) /\
    fn_reachable fn0 s.vs_current_bb ==>
    ao_dfg_inv dfg (v with vs_inst_idx := 0) /\
    strict_dom_iszero_inv fn0 dfg v /\
    ao_chain_defined_prefix targets v /\
    range_sound (df_widen_at NONE ra v.vs_current_bb 0) v /\
    MEM v.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre /\
    dfg_sound dfg v.vs_vars /\
    (!vv dinst u. dfg_get_def dfg vv = SOME dinst /\
       vv IN FDOM v.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==> u IN FDOM v.vs_vars) /\
    fn_reachable fn0 v.vs_current_bb
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `ssa_form fn0` by fs[wf_ssa_def] >>
  `EVERY inst_wf bb.bb_instructions` by metis_tac[fn_inst_wf_every_bb] >>
  `~v.vs_halted` by metis_tac[exec_block_OK_not_halted] >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by
    (rpt strip_tac >> CCONTR_TAC >> fs[bb_well_formed_def] >>
     `i < LENGTH bb.bb_instructions` by DECIDE_TAC >>
     res_tac >> DECIDE_TAC) >>
  (* successor + reachability *)
  `MEM v.vs_current_bb (bb_succs bb)` by
    (qspecl_then [`fuel`, `ctx`, `bb`, `s`, `v`] mp_tac
       exec_block_current_bb_in_succs >>
     impl_tac >- (simp[] >> fs[bb_well_formed_def]) >> simp[]) >>
  `fn_cfg_edge fn0 bb.bb_label v.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> qexists_tac `bb` >> simp[]) >>
  `fn_reachable fn0 v.vs_current_bb` by metis_tac[fn_reachable_step] >>
  (* ao_dfg_inv + ao_chain_defined_prefix via ao_dc_exec_block *)
  `ao_dfg_inv (dfg_build_function fn0) s` by
    (qpat_x_assum `ao_dfg_inv _ _` mp_tac >>
     simp[ao_dfg_inv_def, lookup_var_def]) >>
  `ao_dfg_inv (dfg_build_function fn0) v /\
   ao_chain_defined_prefix (ao_compute_fn_iszero_targets fn0) v` by
    (qspecl_then [`fn0`, `dfg_build_function fn0`,
                  `ao_compute_fn_iszero_targets fn0`, `bb`, `fuel`, `ctx`,
                  `s`, `v`] mp_tac ao_dc_exec_block >>
     impl_tac >- simp[] >> simp[]) >>
  (* strict_dom_iszero_inv via strict_dom_iszero_inv_preserved *)
  `strict_dom_iszero_inv fn0 (dfg_build_function fn0) v` by
    (qspecl_then [`fn0`, `dfg_build_function fn0`, `bb`, `fuel`, `ctx`,
                  `s`, `v`] mp_tac strict_dom_iszero_inv_preserved >>
     impl_tac >- simp[] >> simp[]) >>
  (* range_sound + cfg membership + dfg_sound + ops-defined *)
  `ALL_DISTINCT (fn_labels fn0)` by fs[wf_function_def] >>
  `!iv i1 i2. MEM i1 (fn_insts fn0) /\ MEM i2 (fn_insts fn0) /\
     MEM iv i1.inst_outputs /\ MEM iv i2.inst_outputs ==> i1 = i2` by
    metis_tac[ssa_unique_output] >>
  `!tbb. MEM tbb fn0.fn_blocks ==>
     !ti. ti < LENGTH tbb.bb_instructions - 1 ==>
       ~is_terminator (EL ti tbb.bb_instructions).inst_opcode` by
    (rpt strip_tac >> `bb_well_formed tbb` by fs[wf_function_def] >>
     CCONTR_TAC >> fs[bb_well_formed_def] >>
     `ti < LENGTH tbb.bb_instructions` by DECIDE_TAC >>
     res_tac >> DECIDE_TAC) >>
  `MEM v.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre /\
   range_sound (df_widen_at NONE (range_analyze fn0) v.vs_current_bb 0) v /\
   dfg_sound (dfg_build_function fn0) v.vs_vars /\
   (!vv dinst u. dfg_get_def (dfg_build_function fn0) vv = SOME dinst /\
      vv IN FDOM v.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
      MEM (Var u) dinst.inst_operands ==> u IN FDOM v.vs_vars)` by
    (mp_tac (Q.INST [`fn` |-> `fn0`] range_successor_obligation) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (qspecl_then [`bb`, `fuel`, `ctx`, `s`, `v`] mp_tac) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[]) >>
     disch_then ACCEPT_TAC) >>
  (* assemble *)
  conj_tac
  >- (qpat_x_assum `ao_dfg_inv _ v` mp_tac >>
      simp[ao_dfg_inv_def, lookup_var_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

val _ = export_theory();
