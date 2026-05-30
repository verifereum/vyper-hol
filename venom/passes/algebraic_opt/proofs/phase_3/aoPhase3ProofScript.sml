(* Phase 3: Main rewrite pass correctness.
 *
 * Uses block_sim_function_error_bb with:
 *   block_inv = ao_dfg_inv ∧ ao_iszero_chain_inv ∧ ao_chain_defined_prefix
 *               ∧ range_sound ∧ cfg_membership
 *
 * TOP-LEVEL: ao_phase3_correct
 *)

Theory aoPhase3Proof
Ancestors
  algebraicOptDefs aoBlockSim aoTargetProps
  aoResolveObligation aoRangeObligation
  aoStepInvObligation aoBlockInvObligation aoPhase1Wf
  aoBlockSimLocal aoStrictDomObligation
  aoBlockInvPreserved aoPhase1DfgLocal
  dfgSoundStep dfgAnalysisProps
  venomExecSemantics venomExecProofs venomWf venomState venomInst
  stateEquiv stateEquivProps execEquivProps
  passSimulationProps passSimulationDefs
  analysisSimDefs rangeAnalysisDefs rangeAnalysisProofs rangeEvalDefs
Libs
  pairLib BasicProvers

val _ = delsimps ["ao_iszero_chain_inv_def",
                  "ao_chains_defined_at_def",
                  "ao_chains_defined_def",
                  "ao_chain_defined_prefix_def"]

Triviality fn0_entry_label[local]:
  !fn. fn_entry_label (fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) =
    fn_entry_label fn
Proof
  simp[fn_entry_label_def, entry_block_def] >>
  gen_tac >> Cases_on `fn.fn_blocks` >> simp[]
QED

Triviality run_blocks_inst_idx_irrel[local]:
  !fuel ctx fn s.
    run_blocks fuel ctx fn s =
    run_blocks fuel ctx fn (s with vs_inst_idx := 0)
Proof
  Induct_on `fuel` >> rpt gen_tac
  >- (ONCE_REWRITE_TAC[run_blocks_def] >> simp[]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[run_blocks_def])) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[run_blocks_def])) >>
  simp_tac (srw_ss()) []
QED

Triviality ao_transform_block_label[local]:
  !mid dfg ra targets bb.
    (ao_transform_block mid dfg ra targets bb).bb_label = bb.bb_label
Proof
  simp[ao_transform_block_def]
QED

Triviality range_sound_in_range_at_inst[local]:
  !ra lbl s.
    range_sound (df_widen_at NONE ra lbl 0) s ==>
    in_range_state (range_at_inst ra lbl 0) s.vs_vars
Proof
  rw[range_at_inst_def] >>
  Cases_on `df_widen_at NONE ra lbl 0` >>
  fs[range_sound_def, range_unwrap_def, in_range_state_def,
     finite_mapTheory.FLOOKUP_EMPTY] >>
  metis_tac[]
QED

Triviality MEM_fn_insts_blocks_local[local]:
  !bbs inst bb.
    MEM bb bbs /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts_blocks bbs)
Proof
  Induct >> rw[fn_insts_blocks_def] >> metis_tac[]
QED

Triviality every_inst_wf_fn_inst_wf[local]:
  !fn. EVERY inst_wf (fn_insts fn) ==> fn_inst_wf fn
Proof
  rw[fn_inst_wf_def, fn_insts_def, listTheory.EVERY_MEM] >>
  metis_tac[MEM_fn_insts_blocks_local]
QED

Theorem ao_phase3_correct:
  !fuel ctx fn s.
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    let targets = ao_compute_fn_iszero_targets fn0 in
    let dfg = dfg_build_function fn0 in
    let ra = range_analyze fn0 in
    let mid = fn_max_inst_id fn0 in
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks in
    let fv = ao_fn_fresh_vars fn in
    wf_function fn /\ wf_ssa fn /\ EVERY inst_wf (fn_insts fn) /\
    ao_fresh_names_disjoint fn /\ dfg_block_local fn /\
    FDOM s.vs_vars = {} /\
    fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn0 s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (run_blocks fuel ctx fn0 s) (run_blocks fuel ctx fn1 s)
Proof
  simp_tac std_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `fn0 = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks` >>
  qabbrev_tac `targets = ao_compute_fn_iszero_targets fn0` >>
  qabbrev_tac `dfg = dfg_build_function fn0` >>
  qabbrev_tac `ra = range_analyze fn0` >>
  qabbrev_tac `mid = fn_max_inst_id fn0` >>
  qabbrev_tac `fv = ao_fn_fresh_vars fn` >>
  qabbrev_tac `bt = ao_transform_block mid dfg ra targets` >>
  qabbrev_tac `fn1 = fn0 with fn_blocks := MAP bt fn0.fn_blocks` >>
  qabbrev_tac `block_inv = \s:venom_state.
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    strict_dom_iszero_inv fn0 dfg s /\
    ao_chain_defined_prefix targets s /\
    range_sound (df_widen_at NONE ra s.vs_current_bb 0) s /\
    MEM s.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre /\
    dfg_sound dfg s.vs_vars /\
    (!vv dinst u. dfg_get_def dfg vv = SOME dinst /\
       vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==> u IN FDOM s.vs_vars) /\
    fn_reachable fn0 s.vs_current_bb` >>
  `fn1 = function_map_transform bt fn0` by
    simp[function_map_transform_def, Abbr `fn1`] >>
  pop_assum SUBST1_TAC >>
  ONCE_REWRITE_TAC[run_blocks_inst_idx_irrel] >>
  (* Fresh-var disjointness facts derived from ao_fresh_names_disjoint. *)
  `(!inst v. MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
             v NOTIN fv) /\
   (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
             v NOTIN fv)` by
    (fs[Abbr `fv`, ao_fresh_names_disjoint_def] >> metis_tac[]) >>
  `ao_targets_wf targets` by
    simp[Abbr `targets`, ao_compute_fn_iszero_targets_wf] >>
  `wf_function fn0 /\ wf_ssa fn0` by (
    `block_map_transform ao_handle_offset_inst =
     \bb. bb with bb_instructions := MAP ao_handle_offset_inst bb.bb_instructions`
      by simp[FUN_EQ_THM, block_map_transform_def] >>
    `fn0 = function_map_transform (block_map_transform ao_handle_offset_inst) fn`
      by asm_simp_tac std_ss [function_map_transform_def, Abbr `fn0`] >>
    pop_assum SUBST1_TAC >>
    conj_tac
    >- (irule ao_phase1_preserves_wf >> simp[])
    >- (irule ao_phase1_preserves_wf_ssa >> simp[])) >>
  `fn_inst_wf fn0` by (
    irule every_inst_wf_fn_inst_wf >>
    `block_map_transform ao_handle_offset_inst =
     \bb. bb with bb_instructions := MAP ao_handle_offset_inst bb.bb_instructions`
      by simp[FUN_EQ_THM, block_map_transform_def] >>
    `fn0 = function_map_transform (block_map_transform ao_handle_offset_inst) fn`
      by asm_simp_tac std_ss [function_map_transform_def, Abbr `fn0`] >>
    pop_assum SUBST1_TAC >> irule ao_phase1_preserves_inst_wf >> simp[]) >>
  `dfg_block_local fn0` by (
    qunabbrev_tac `fn0` >> irule ao_phase1_preserves_dfg_block_local >>
    simp[]) >>
  qspecl_then [`state_equiv fv`, `execution_equiv fv`,
    `block_inv`, `bt`, `fn0`] mp_tac block_sim_function_error_bb >>
  impl_tac >- (
    rpt conj_tac
    >- simp[state_equiv_execution_equiv_valid_state_rel]
    >- metis_tac[state_equiv_trans]
    >- metis_tac[execution_equiv_trans]
    >- (qunabbrev_tac `bt` >> simp[ao_transform_block_label])
    >- (* per-block sim via ao_block_sim_local *)
       (qx_gen_tac `bb` >> strip_tac >>
        qx_genl_tac [`fl`, `cx`, `st`] >> strip_tac >>
        `st.vs_current_bb = bb.bb_label` by fs[] >>
        qpat_x_assum `block_inv st` mp_tac >> simp[Abbr `block_inv`] >>
        strip_tac >>
        `range_sound (df_widen_at NONE ra bb.bb_label 0) st` by
          (qpat_x_assum `range_sound _ st` mp_tac >> fs[]) >>
        `in_range_state (range_at_inst ra bb.bb_label 0) st.vs_vars` by
          (irule range_sound_in_range_at_inst >>
           TRY (first_assum ACCEPT_TAC) >> gvs[]) >>
        qspecl_then [`fn`, `fn0`, `mid`, `dfg`, `ra`, `targets`, `bb`]
          mp_tac ao_block_sim_local >>
        impl_tac
        >- (simp[Abbr `fn0`, Abbr `mid`, Abbr `dfg`, Abbr `ra`,
                 Abbr `targets`, Abbr `fv`] >>
            rpt conj_tac >> simp[] >> metis_tac[]) >>
        disch_then (qspecl_then [`fl`, `cx`, `st`] mp_tac) >>
        impl_tac >- gvs[] >>
        simp[Abbr `bt`, Abbr `fv`])
    >- (* block_inv preserved through exec_block *)
       (qx_genl_tac [`bb`, `fl`, `cx`, `st`, `vt`] >> strip_tac >>
        `(st with vs_inst_idx := 0) = st` by
          rw[venom_state_component_equality] >>
        full_simp_tac (srw_ss()) [Abbr `block_inv`] >>
        qspecl_then [`fn0`, `dfg`, `ra`, `targets`, `bb`, `fl`, `cx`,
                     `st`, `vt`] mp_tac ao_block_inv_preserved >>
        impl_tac
        >- (conj_tac >- simp[Abbr `dfg`] >>
            conj_tac >- simp[Abbr `ra`] >>
            conj_tac >- simp[Abbr `targets`] >>
            rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[]) >>
        strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[])
    >- (* block_inv compat with state_equiv fv *)
       (rpt gen_tac >> simp[Abbr `block_inv`] >> strip_tac >>
        `s1.vs_current_bb = s2.vs_current_bb` by
          fs[state_equiv_def, execution_equiv_def] >>
        `ao_dfg_inv dfg (s2 with vs_inst_idx := 0) /\
         strict_dom_iszero_inv fn0 dfg s2 /\
         ao_chain_defined_prefix targets s2 /\
         range_sound (df_widen_at NONE ra s2.vs_current_bb 0) s2` by
          (qspecl_then [`fn`, `fn0`, `dfg`, `ra`, `targets`, `s1`, `s2`]
             mp_tac ao_block_inv_state_equiv_compat >>
           simp[Abbr `dfg`, Abbr `ra`, Abbr `targets`, Abbr `fn0`,
                Abbr `fv`] >> disch_then irule >> metis_tac[]) >>
        `dfg_sound dfg s2.vs_vars` by
          (qspecl_then [`fn`, `fn0`, `dfg`, `s1`, `s2`]
             mp_tac ao_dfg_sound_state_equiv_compat >>
           simp[Abbr `dfg`, Abbr `fn0`, Abbr `fv`] >>
           disch_then irule >> metis_tac[]) >>
        `!vv dinst u. dfg_get_def dfg vv = SOME dinst /\
           vv IN FDOM s2.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
           MEM (Var u) dinst.inst_operands ==> u IN FDOM s2.vs_vars` by
          (qspecl_then [`fn`, `fn0`, `dfg`, `s1`, `s2`]
             mp_tac ao_ops_defined_state_equiv_compat >>
           simp[Abbr `dfg`, Abbr `fn0`, Abbr `fv`] >>
           disch_then match_mp_tac >> rpt conj_tac >>
           TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[])
    >- (* operand lookup under state_equiv *)
       (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
        `x NOTIN fv` by
          (irule ao_fn0_operand_not_in_fv >>
           rpt conj_tac >>
           gvs[Abbr `fn0`, Abbr `fv`] >> metis_tac[]) >>
        fs[state_equiv_def, execution_equiv_def]))
  >>
  disch_then (qspecl_then [`fuel`, `ctx`,
    `s with vs_inst_idx := 0`] mp_tac) >>
  simp[Abbr `block_inv`] >>
  impl_tac >-
   ((* Initial block_inv at the entry state s with vs_inst_idx := 0. *)
    `block_map_transform ao_handle_offset_inst =
     \bb. bb with bb_instructions := MAP ao_handle_offset_inst bb.bb_instructions`
      by simp[FUN_EQ_THM, block_map_transform_def] >>
    `fn0 = function_map_transform (block_map_transform ao_handle_offset_inst) fn`
      by asm_simp_tac std_ss [function_map_transform_def, Abbr `fn0`] >>
    `wf_function fn0` by
      (pop_assum SUBST1_TAC >> irule ao_phase1_preserves_wf >> simp[]) >>
    `!x. lookup_var x (s with vs_inst_idx := 0) = NONE` by
      fs[lookup_var_def, finite_mapTheory.FLOOKUP_DEF] >>
    `ssa_form fn` by fs[wf_ssa_def] >>
    rpt conj_tac
    >- (* ao_dfg_inv (vacuous: no vars defined yet) *)
       (simp[ao_dfg_inv_def] >> rpt strip_tac >> fs[])
    >- (* strict_dom_iszero_inv *)
       (irule strict_dom_iszero_inv_initial >>
        `fn_entry_label fn0 = SOME s.vs_current_bb` by
          (simp[Abbr `fn0`, fn0_entry_label] >> fs[]) >>
        simp[])
    >- (* ao_chain_defined_prefix *)
       (irule ao_chain_defined_prefix_initial >> qexistsl_tac [`fn`, `fn0`] >>
        rpt conj_tac >> simp[Abbr `targets`, Abbr `fn0`] >> fs[])
    >- (* range_sound (vacuous: vs_vars empty) *)
       (simp[range_sound_def] >>
        Cases_on `df_widen_at NONE ra s.vs_current_bb 0` >>
        fs[in_range_state_def, finite_mapTheory.FLOOKUP_DEF])
    >- (* cfg membership at entry *)
       (`fn_entry_label fn0 = SOME s.vs_current_bb` by
          (simp[Abbr `fn0`, fn0_entry_label] >> fs[]) >>
        irule ao_cfg_initial >> fs[])
    >- (* dfg_sound (vacuous: vs_vars empty) *)
       (`FDOM (s with vs_inst_idx := 0).vs_vars = {}` by fs[] >>
        gvs[dfg_sound_def, dfg_assign_sound_def, dfg_iszero_sound_def,
            dfg_eq_sound_def, dfg_compare_sound_def,
            finite_mapTheory.FLOOKUP_DEF])
    >- (* fn_reachable at entry (reflexive) *)
       (`fn_entry_label fn0 = SOME s.vs_current_bb` by
          (simp[Abbr `fn0`, fn0_entry_label] >> fs[]) >>
        simp[fn_reachable_def] >> qexists_tac `s.vs_current_bb` >>
        asm_simp_tac (srw_ss()) [relationTheory.RTC_REFL])) >>
  disch_then ACCEPT_TAC
QED

val _ = export_theory();
