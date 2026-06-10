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
  aoChainStruct aoResolveObligation
  assertElimProofs dfgSoundStep rangeAnalysisProofs
  allocaRemapSSA dfgAnalysisProps
  venomExecSemantics venomExecProofs venomExecProps instIdxIndep
  venomWf venomState venomInst
  finite_map pred_set
Libs
  pairLib BasicProvers

(* ===== vs_inst_idx irrelevance of run_block (re-derived locally) ===== *)

Triviality eval_one_phi_inst_idx:
  !inst s n. eval_one_phi (s with vs_inst_idx := n) inst = eval_one_phi s inst
Proof
  simp[eval_one_phi_def, eval_op_inst_idx]
QED

Triviality eval_phis_inst_idx:
  !insts s n.
    eval_phis (s with vs_inst_idx := n) insts =
    exec_result_map (\s'. s' with vs_inst_idx := n) (eval_phis s insts)
Proof
  Induct >> simp[eval_phis_def, exec_result_map_def, eval_one_phi_inst_idx] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `eval_one_phi s h` >> gvs[eval_one_phi_inst_idx]
  >- simp[exec_result_map_def] >>
  Q.SPEC_THEN `x` STRIP_ASSUME_TAC pairTheory.pair_CASES >>
  Cases_on `eval_phis s insts` >>
  gvs[exec_result_map_def, update_var_def]
QED

Triviality run_block_inst_idx_irrel:
  !fuel ctx bb s.
    run_block fuel ctx bb s =
    run_block fuel ctx bb (s with vs_inst_idx := 0)
Proof
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[eval_phis_inst_idx] >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[exec_result_map_def]
QED

(* ===== eval_phis preserves the ao invariants ===== *)

(* eval_phis preserves ao_dfg_inv: PHI-defined vars hit the vacuous clauses,
   non-PHI-defined vars keep their values and the call ctx is unchanged. *)
Theorem eval_phis_ao_dfg_inv:
  !fn0 bb s s'.
    ssa_form fn0 /\ MEM bb fn0.fn_blocks /\
    eval_phis s bb.bb_instructions = OK s' /\
    ao_dfg_inv (dfg_build_function fn0) s ==>
    ao_dfg_inv (dfg_build_function fn0) s'
Proof
  rpt strip_tac >>
  `s'.vs_call_ctx = s.vs_call_ctx` by
    (`s' = s with vs_vars := s'.vs_vars` by metis_tac[eval_phis_only_updates_vs_vars] >>
     pop_assum (fn th => simp[Once th])) >>
  simp[ao_dfg_inv_def] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  `inst.inst_opcode <> PHI` by (strip_tac >> gvs[]) >>
  `lookup_var x s' = lookup_var x s` by
    (irule eval_phis_lookup_not_bb_phi >> qexists_tac `bb` >> simp[] >>
     metis_tac[dfg_def_not_bb_phi]) >>
  qpat_x_assum `ao_dfg_inv _ s` mp_tac >> simp[ao_dfg_inv_def] >>
  disch_then (qspecl_then [`x`, `inst`, `val`] mp_tac) >> gvs[]
QED

(* eval_phis preserves definedness of operands (FDOM only grows). *)
Theorem eval_phis_eval_operand_defined_mono:
  !s insts s' op w.
    eval_phis s insts = OK s' /\ eval_operand op s = SOME w ==>
    ?w'. eval_operand op s' = SOME w'
Proof
  rpt strip_tac >> Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]
  >- (rename1 `FLOOKUP s.vs_vars y = SOME w` >>
      `y IN FDOM s.vs_vars` by gvs[FLOOKUP_DEF] >>
      `FDOM s.vs_vars SUBSET FDOM s'.vs_vars` by metis_tac[eval_phis_vars_grow] >>
      `y IN FDOM s'.vs_vars` by metis_tac[SUBSET_DEF] >>
      gvs[FLOOKUP_DEF]) >>
  `s'.vs_labels = s.vs_labels` by
    (`s' = s with vs_vars := s'.vs_vars` by metis_tac[eval_phis_only_updates_vs_vars] >>
     pop_assum (fn th => simp[Once th])) >>
  gvs[]
QED

(* For chain positions >= 1 (ISZERO outputs), eval_phis leaves the value alone. *)
Theorem eval_phis_chain_elem_eq:
  !fn0 bb s s' v chain k.
    ssa_form fn0 /\ MEM bb fn0.fn_blocks /\
    eval_phis s bb.bb_instructions = OK s' /\
    ALOOKUP (ao_compute_fn_iszero_targets fn0) v = SOME chain /\
    1 <= k /\ k < LENGTH chain ==>
    eval_operand (EL k chain) s' = eval_operand (EL k chain) s
Proof
  rpt strip_tac >>
  `s' = s with vs_vars := s'.vs_vars` by metis_tac[eval_phis_only_updates_vs_vars] >>
  Cases_on `EL k chain` >> simp[eval_operand_def]
  >- (rename1 `EL k chain = Var w` >>
      `?inst. MEM inst (fn_insts fn0) /\ inst.inst_opcode = ISZERO /\
              inst.inst_operands = [EL (k-1) chain] /\ MEM w inst.inst_outputs` by
        (`(k-1)+1 = k` by DECIDE_TAC >>
         qspecl_then [`fn0`, `v`, `chain`, `k-1`, `w`] mp_tac chain_consecutive_iszero >>
         simp[]) >>
      `!p. MEM p bb.bb_instructions /\ p.inst_opcode = PHI ==>
           ~MEM w p.inst_outputs` by
        (rpt strip_tac >>
         `MEM p (fn_insts fn0)` by metis_tac[mem_block_mem_fn_insts] >>
         `p = inst` by metis_tac[ssa_output_unique] >> gvs[]) >>
      metis_tac[eval_phis_lookup_not_bb_phi]) >>
  qpat_x_assum `s' = _` (fn th => simp[Once th])
QED

(* eval_phis preserves ao_chain_defined_prefix. *)
Theorem eval_phis_ao_chain_defined_prefix:
  !fn0 bb s s'.
    ssa_form fn0 /\ MEM bb fn0.fn_blocks /\
    eval_phis s bb.bb_instructions = OK s' /\
    ao_chain_defined_prefix (ao_compute_fn_iszero_targets fn0) s ==>
    ao_chain_defined_prefix (ao_compute_fn_iszero_targets fn0) s'
Proof
  rpt strip_tac >>
  simp[ao_chain_defined_prefix_def] >> rpt strip_tac >>
  Cases_on `j2 = 0`
  >- (`j1 = 0` by DECIDE_TAC >> gvs[]) >>
  `1 <= j2` by DECIDE_TAC >>
  `eval_operand (EL j2 chain) s' = eval_operand (EL j2 chain) s` by
    (qspecl_then [`fn0`, `bb`, `s`, `s'`, `v`, `chain`, `j2`] mp_tac
       eval_phis_chain_elem_eq >> simp[]) >>
  `?w2. eval_operand (EL j2 chain) s = SOME w2` by metis_tac[] >>
  `?w1. eval_operand (EL j1 chain) s = SOME w1` by
    (qpat_x_assum `ao_chain_defined_prefix _ s` mp_tac >>
     rewrite_tac[ao_chain_defined_prefix_def] >>
     disch_then (qspecl_then [`v`, `chain`, `j1`, `j2`] mp_tac) >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  metis_tac[eval_phis_eval_operand_defined_mono]
QED

Theorem ao_block_inv_preserved:
  !fn0 dfg ra targets bb fuel ctx s v.
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    wf_function fn0 /\ wf_ssa fn0 /\
    fn_inst_wf fn0 /\
    dfg_block_local fn0 /\
    (!b cond true_lbl false_lbl. MEM b fn0.fn_blocks /\
       (LAST b.bb_instructions).inst_opcode = JNZ /\
       (LAST b.bb_instructions).inst_operands =
         [cond; Label true_lbl; Label false_lbl] ==>
       true_lbl <> false_lbl) /\
    MEM bb fn0.fn_blocks /\
    s.vs_current_bb = bb.bb_label /\
    run_block fuel ctx bb s = OK v /\
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
  `~v.vs_halted` by metis_tac[run_block_OK_not_halted] >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by
    (rpt strip_tac >> CCONTR_TAC >> fs[bb_well_formed_def] >>
     `i < LENGTH bb.bb_instructions` by DECIDE_TAC >>
     res_tac >> DECIDE_TAC) >>
  (* successor + reachability *)
  `MEM v.vs_current_bb (bb_succs bb)` by
    (qspecl_then [`fuel`, `ctx`, `bb`, `s`, `v`] mp_tac
       run_block_current_bb_in_succs >>
     impl_tac >- simp[] >> simp[]) >>
  `fn_cfg_edge fn0 bb.bb_label v.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> qexists_tac `bb` >> simp[]) >>
  `fn_reachable fn0 v.vs_current_bb` by metis_tac[fn_reachable_step] >>
  (* decompose run_block into eval_phis then exec_block from the PHI prefix *)
  `?s_phi. eval_phis s bb.bb_instructions = OK s_phi /\
     exec_block fuel ctx bb
       (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK v` by
    (qpat_x_assum `run_block _ _ _ _ = OK _` mp_tac >>
     simp[Once run_block_def] >>
     DISJ_CASES_THEN STRIP_ASSUME_TAC
       (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
     gvs[]) >>
  qabbrev_tac `s_pp =
    s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  (* ao_dfg_inv + ao_chain_defined_prefix: bridge over eval_phis, then exec_block *)
  `ao_dfg_inv (dfg_build_function fn0) s` by
    (qpat_x_assum `ao_dfg_inv _ (s with vs_inst_idx := 0)` mp_tac >>
     simp[ao_dfg_inv_def, lookup_var_def]) >>
  `ao_dfg_inv (dfg_build_function fn0) s_phi` by
    metis_tac[eval_phis_ao_dfg_inv] >>
  `ao_chain_defined_prefix (ao_compute_fn_iszero_targets fn0) s_phi` by
    metis_tac[eval_phis_ao_chain_defined_prefix] >>
  `ao_dfg_inv (dfg_build_function fn0) s_pp` by
    (simp[Abbr `s_pp`] >>
     qpat_x_assum `ao_dfg_inv _ s_phi` mp_tac >>
     simp[ao_dfg_inv_def, lookup_var_def]) >>
  `ao_chain_defined_prefix (ao_compute_fn_iszero_targets fn0) s_pp` by
    (simp[Abbr `s_pp`] >>
     qpat_x_assum `ao_chain_defined_prefix _ s_phi` mp_tac >>
     simp[ao_chain_defined_prefix_def, eval_op_inst_idx]) >>
  `ao_dfg_inv (dfg_build_function fn0) v /\
   ao_chain_defined_prefix (ao_compute_fn_iszero_targets fn0) v` by
    (qspecl_then [`fn0`, `dfg_build_function fn0`,
                  `ao_compute_fn_iszero_targets fn0`, `bb`, `fuel`, `ctx`,
                  `s_pp`, `v`] mp_tac ao_dc_exec_block >>
     impl_tac >- simp[] >> simp[]) >>
  (* strict_dom_iszero_inv via run_block helper *)
  `strict_dom_iszero_inv fn0 (dfg_build_function fn0) v` by
    (qspecl_then [`fn0`, `dfg_build_function fn0`, `bb`, `fuel`, `ctx`,
                  `s`, `v`] mp_tac strict_dom_iszero_inv_run_block_preserved >>
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
  `run_block fuel ctx bb (s with vs_inst_idx := 0) = OK v` by
    metis_tac[run_block_inst_idx_irrel] >>
  `!b cond false_lbl.
     (LAST b.bb_instructions).inst_opcode = JNZ ==>
     (LAST b.bb_instructions).inst_operands =
       [cond; Label false_lbl; Label false_lbl] ==>
     ~MEM b fn0.fn_blocks` by
    (rpt strip_tac >> spose_not_then assume_tac >> metis_tac[]) >>
  `MEM v.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre /\
   range_sound (df_widen_at NONE (range_analyze fn0) v.vs_current_bb 0) v /\
   dfg_sound (dfg_build_function fn0) v.vs_vars /\
   (!vv dinst u. dfg_get_def (dfg_build_function fn0) vv = SOME dinst /\
      vv IN FDOM v.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
      MEM (Var u) dinst.inst_operands ==> u IN FDOM v.vs_vars)` by
    (mp_tac (Q.INST [`fn` |-> `fn0`] range_successor_obligation) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (qspecl_then
        [`bb`, `fuel`, `ctx`, `s with vs_inst_idx := 0`, `v`] mp_tac) >>
     impl_tac
     >- (simp[range_sound_def] >> rpt conj_tac >>
         TRY (first_assum ACCEPT_TAC) >> gvs[range_sound_def]) >>
     simp[]) >>
  (* assemble *)
  conj_tac
  >- (qpat_x_assum `ao_dfg_inv _ v` mp_tac >>
      simp[ao_dfg_inv_def, lookup_var_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

