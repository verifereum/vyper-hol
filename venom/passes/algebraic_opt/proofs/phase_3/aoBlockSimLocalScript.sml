(* Phase 3 — Loop-robust per-block simulation.
 *
 * Builds ao_block_sim_local using analysis_block_sim_inv_at with a
 * position-aware `sound` predicate that carries within_block_iszero_inv
 * and (loop-robust) strict_dom_iszero_inv / ao_chain_defined_prefix /
 * ao_dfg_inv, INSTEAD of the global ao_iszero_chain_inv (which is not
 * preserved across loop back-edges).
 *
 * The per-instruction resolve relation (cond2) is derived freshly at each
 * index via chain_iszero_rel_from_inv from strict_dom + within_block.
 *
 * TOP-LEVEL:
 *   ao_per_inst_sim_fn0_local — loop-robust per-instruction simulation
 *   ao_block_sim_local        — loop-robust per-block simulation
 *)

Theory aoBlockSimLocal
Ancestors
  algebraicOptDefs aoPhase1Wf aoWf aoBlockSim aoTransformInstSim
  aoResolveObligation aoStepInvObligation aoStrictDomObligation
  aoChainStruct aoIsZeroInv aoRangeObligation aoTargetProps
  aoBlockInvObligation
  analysisSimDefs analysisSimProofsBase
  stateEquiv stateEquivProps execEquivParamProps
  venomExecSemantics venomExecProofs venomExecProps
  venomState venomInst venomInstProofs venomInstProps venomWf
  dfgAnalysisProps rangeAnalysisDefs rangeAnalysisProofs dfgSoundStep dfAnalyzeDefs
  indexedLists finite_map
Libs
  pairLib BasicProvers

(* ===== Small structural helpers ===== *)

Triviality idx_df_state_at2[local]:
  !lbl n i. i < n ==>
    df_at 0 (idx_df_state lbl n) lbl i = i
Proof
  rw[df_at_def, idx_df_state_def] >>
  `FINITE (IMAGE (\i. (lbl, i)) (count n))` by simp[] >>
  `(lbl, i) IN IMAGE (\i. (lbl, i)) (count n)` by
    (simp[] >> qexists_tac `i` >> simp[]) >>
  simp[finite_mapTheory.FLOOKUP_FUN_FMAP]
QED

Triviality test_wf_all_distinct[local]:
  !fn0. wf_function fn0 ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) fn0.fn_blocks)
Proof
  rpt strip_tac >> gvs[wf_function_def, fn_labels_def]
QED

Triviality test_lookup_block[local]:
  !fn0 bb.
    wf_function fn0 /\ MEM bb fn0.fn_blocks ==>
    lookup_block bb.bb_label fn0.fn_blocks = SOME bb
Proof
  rpt strip_tac >>
  drule test_wf_all_distinct >> strip_tac >>
  mp_tac (Q.SPECL [`bb.bb_label`, `fn0.fn_blocks`, `bb`]
    MEM_lookup_block) >>
  impl_tac >- simp[] >>
  simp[]
QED

Triviality fn0_inst_fresh_in_fv[local]:
  !fn fn0 bb inst.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    MEM bb fn0.fn_blocks /\
    MEM inst bb.bb_instructions ==>
    ao_fresh_var inst.inst_id "not" IN ao_fn_fresh_vars fn /\
    ao_fresh_var inst.inst_id "iz" IN ao_fn_fresh_vars fn /\
    ao_fresh_var inst.inst_id "xor" IN ao_fn_fresh_vars fn
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  fs[listTheory.MEM_MAP] >> rename1 `MEM bb0 fn.fn_blocks` >>
  gvs[] >>
  fs[listTheory.MEM_MAP] >> rename1 `inst = ao_handle_offset_inst inst'` >>
  `inst.inst_id = inst'.inst_id` by simp[ao_handle_offset_inst_preserves_id] >>
  `MEM inst' (fn_insts fn)` by (irule mem_block_mem_fn_insts >> metis_tac[]) >>
  rpt conj_tac >>
  simp[ao_fn_fresh_vars_def] >>
  qexists_tac `inst'.inst_id` >> simp[ao_handle_offset_inst_preserves_id] >>
  simp[listTheory.MEM_MAP] >> qexists_tac `inst'` >> simp[]
QED

(* ===== Transfer-soundness helpers ===== *)

Triviality wbiz_step_any[local]:
  !fn0 bb idx fuel ctx s s'.
    wf_ssa fn0 /\ wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    inst_wf (EL idx bb.bb_instructions) /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' /\
    within_block_iszero_inv fn0 bb idx s ==>
    within_block_iszero_inv fn0 bb (SUC idx) s'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_terminator (EL idx bb.bb_instructions).inst_opcode`
  >- (simp[within_block_iszero_inv_def] >> rpt gen_tac >> rpt strip_tac >>
      `j < idx` by
        (CCONTR_TAC >> `j = idx` by simp[] >> gvs[is_terminator_def]) >>
      `!v. lookup_var v s' = lookup_var v s` by
        metis_tac[step_terminator_preserves_vars] >>
      `s'.vs_labels = s.vs_labels` by
        metis_tac[step_inst_preserves_labels_always] >>
      qpat_x_assum `within_block_iszero_inv _ _ _ _`
        (mp_tac o REWRITE_RULE[within_block_iszero_inv_def]) >>
      disch_then (qspecl_then [`j`, `x`, `iz_op`] mp_tac) >>
      simp[] >> disch_then (qspecl_then [`val_x`, `val_op`] mp_tac) >>
      impl_tac
      >- (rpt conj_tac >>
          TRY (Cases_on `iz_op` >> fs[eval_operand_def] >> NO_TAC) >>
          gvs[])
      >> simp[])
  >- (`within_block_iszero_inv fn0 bb (SUC idx)
        (s' with vs_inst_idx := SUC s.vs_inst_idx)`
        suffices_by simp[wbiz_inst_idx] >>
      metis_tac[wbiz_step])
QED

Triviality ao_local_transfer_sound[local]:
  !fn0 bb idx fuel ctx s s'.
    wf_function fn0 /\ wf_ssa fn0 /\
    MEM bb fn0.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn0).cfg_dfs_pre /\
    idx < LENGTH bb.bb_instructions /\
    inst_wf (EL idx bb.bb_instructions) /\
    in_range_state
      (range_at_inst (range_analyze fn0) bb.bb_label idx) s.vs_vars /\
    within_block_iszero_inv fn0 bb idx s /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' ==>
    in_range_state
      (range_at_inst (range_analyze fn0) bb.bb_label (SUC idx)) s'.vs_vars /\
    within_block_iszero_inv fn0 bb (SUC idx) s'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all test_lookup_block >> strip_tac >>
  rpt conj_tac
  >- (qspecl_then [`fn0`, `bb.bb_label`, `bb`, `idx`,
        `EL idx bb.bb_instructions`, `fuel`, `ctx`, `s`, `s'`]
        mp_tac range_step_inv >>
      simp_tac std_ss [LET_THM] >> simp[])
  >- metis_tac[wbiz_step_any]
QED

Triviality wbiz_state_equiv_compat[local]:
  !fn0 bb idx fv s1 s2.
    state_equiv fv s1 s2 /\
    within_block_iszero_inv fn0 bb idx s1 /\
    (!j x. j < idx /\ j < LENGTH bb.bb_instructions /\
           MEM x (EL j bb.bb_instructions).inst_outputs ==>
           x NOTIN fv) /\
    (!j op. j < idx /\ j < LENGTH bb.bb_instructions /\
            MEM (Var op) (EL j bb.bb_instructions).inst_operands ==>
            op NOTIN fv) ==>
    within_block_iszero_inv fn0 bb idx s2
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [within_block_iszero_inv_def] >>
  rpt strip_tac >>
  `x NOTIN fv` by metis_tac[] >>
  `lookup_var x s1 = SOME val_x` by
    (qpat_x_assum `lookup_var _ s2 = _` mp_tac >>
     fs[state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand iz_op s1 = SOME val_op` by
    (qpat_x_assum `eval_operand _ s2 = _` mp_tac >>
     `MEM iz_op (EL j bb.bb_instructions).inst_operands` by simp[] >>
     Cases_on `iz_op` >> simp[eval_operand_def]
     >- (rename1 `Var vname` >> strip_tac >>
         `vname NOTIN fv` by metis_tac[] >>
         fs[state_equiv_def, execution_equiv_def, lookup_var_def])
     >- fs[state_equiv_def, execution_equiv_def]) >>
  qpat_x_assum `within_block_iszero_inv _ _ _ _`
    (mp_tac o REWRITE_RULE [within_block_iszero_inv_def]) >>
  disch_then (qspecl_then [`j`, `x`, `iz_op`] mp_tac) >>
  simp[]
QED

(* ISZERO resolution is identity (targets-agnostic) *)
Triviality ao_resolve_iszero_inst_iszero[local]:
  !targets inst.
    inst.inst_opcode = ISZERO ==>
    ao_resolve_iszero_inst targets inst = inst
Proof
  rpt strip_tac >>
  simp[ao_resolve_iszero_inst_def, instruction_component_equality] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM listTheory.MAP_ID])) >>
  irule listTheory.MAP_CONG >> simp[ao_resolve_iszero_op_iszero]
QED

(* ===== Keystone: loop-robust per-instruction simulation ===== *)

Theorem ao_per_inst_sim_fn0_local:
  !fn fn0 mid dfg ra targets bb fuel ctx idx inst s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    mid = fn_max_inst_id fn0 /\
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    wf_function fn0 /\ wf_ssa fn0 /\
    ao_targets_wf targets /\
    ao_chain_defined_prefix targets s /\
    strict_dom_iszero_inv fn0 dfg s /\
    within_block_iszero_inv fn0 bb idx s /\
    in_range_state (range_at_inst ra bb.bb_label idx) s.vs_vars /\
    MEM bb fn0.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    inst = EL idx bb.bb_instructions /\
    bb.bb_label = s.vs_current_bb /\
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    inst_wf inst ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (state_equiv (ao_fn_fresh_vars fn))
      (execution_equiv (ao_fn_fresh_vars fn))
      (execution_equiv (ao_fn_fresh_vars fn))
      (step_inst fuel ctx inst s)
      (run_insts fuel ctx
        (ao_transform_inst mid dfg ra bb.bb_label idx targets inst) s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?e. step_inst fuel ctx inst s = Error e`
  >- (DISJ1_TAC >> metis_tac[])
  >- (
  ho_match_mp_tac (Q.SPEC `ao_fn_fresh_vars fn`
    ao_transform_inst_sim_inst) >> simp[] >>
  `MEM inst bb.bb_instructions` by metis_tac[listTheory.EL_MEM] >>
  drule_all fn0_inst_fresh_in_fv >> simp[] >> strip_tac >> simp[] >>
  `ao_chains_defined_at targets s` by
    metis_tac[ao_chain_defined_prefix_implies_at] >>
  (* cond2: the iszero chain relation, derived freshly from invariants *)
  `!v chain k. MEM (Var v) inst.inst_operands /\
               ALOOKUP targets v = SOME chain /\ k + 1 < LENGTH chain ==>
               !val_k val_k1.
                 eval_operand (EL k chain) s = SOME val_k /\
                 eval_operand (EL (k + 1) chain) s = SOME val_k1 ==>
                 val_k1 = bool_to_word (val_k = 0w)` by
    (assume_tac (Q.SPECL [`fn0`, `dfg`, `targets`, `bb`, `idx`, `inst`, `s`]
       chain_iszero_rel_from_inv) >> gvs[]) >>
  conj_tac
  >- (* resolve sim *)
     (Cases_on `inst.inst_opcode = ISZERO`
      >- (rpt strip_tac >> gvs[ao_resolve_iszero_inst_iszero])
      >- (Cases_on `inst.inst_opcode = PHI`
          >- (`!v chain k. ALOOKUP targets v = SOME chain /\
                 0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w` by
                metis_tac[ao_fn_targets_chain_tail_var] >>
              `!v chain k. MEM (Var v) inst.inst_operands /\
                 ALOOKUP targets v = SOME chain /\
                 (?w0. eval_operand (Var v) s = SOME w0) /\
                 k < LENGTH chain ==>
                 ?w. eval_operand (EL k chain) s = SOME w` by
                (rpt strip_tac >>
                 qpat_x_assum `ao_chains_defined_at targets s`
                   (mp_tac o REWRITE_RULE[ao_chains_defined_at_def]) >>
                 disch_then (qspecl_then [`v`, `chain`] mp_tac) >> simp[]) >>
              irule ao_resolve_phi_sim_local >> simp[] >> metis_tac[])
          >- (Cases_on `MEM inst.inst_opcode [NOP; STOP; SINK; INVALID;
                  CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
                  ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER;
                  PREVRANDAO; CHAINID; SELFBALANCE; BASEFEE; BLOBBASEFEE;
                  CALLDATASIZE; RETURNDATASIZE; CODESIZE; MEMTOP]`
              >- (* zero-eval: operand-independent *)
                 (`inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[]) >>
                  rpt strip_tac >>
                  `step_inst fuel ctx (ao_resolve_iszero_inst targets inst) s =
                     step_inst_base (ao_resolve_iszero_inst targets inst) s` by
                    metis_tac[step_inst_non_invoke,
                              ao_resolve_iszero_inst_opcode] >>
                  `step_inst fuel ctx inst s = step_inst_base inst s` by
                    metis_tac[step_inst_non_invoke] >>
                  `step_inst_base (ao_resolve_iszero_inst targets inst) s =
                     step_inst_base inst s` by
                    (simp[ao_resolve_iszero_inst_def] >>
                     irule step_inst_base_zero_eval_op_irrel >> gvs[]) >>
                  metis_tac[])
              >- (* non-zero-eval: via ao_resolve_iszero_inst_sim_local *)
                 (`!v chain k. MEM (Var v) inst.inst_operands /\
                     ALOOKUP targets v = SOME chain /\ k < LENGTH chain ==>
                     ?w. eval_operand (EL k chain) s = SOME w` by
                    (rpt strip_tac >>
                     `?w0. eval_operand (Var v) s = SOME w0` by
                       (simp[eval_operand_def, lookup_var_def,
                          finite_mapTheory.FLOOKUP_DEF] >>
                        Cases_on `inst.inst_opcode = INVOKE`
                        >- metis_tac[invoke_operand_defined] >>
                        `step_inst fuel ctx inst s = step_inst_base inst s` by
                          metis_tac[step_inst_non_invoke] >>
                        `!e. step_inst_base inst s <> Error e` by
                          (rpt strip_tac >> gvs[]) >>
                        `~MEM inst.inst_opcode [NOP; PHI; STOP; SINK; INVALID;
                            CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
                            ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER;
                            PREVRANDAO; CHAINID; SELFBALANCE; BASEFEE;
                            BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
                            CODESIZE; MEMTOP]` by gvs[] >>
                        metis_tac[step_inst_base_nonerr_var_fdom]) >>
                     qpat_x_assum `ao_chains_defined_at targets s`
                       (mp_tac o REWRITE_RULE[ao_chains_defined_at_def]) >>
                     disch_then (qspecl_then [`v`, `chain`] mp_tac) >>
                     simp[]) >>
                  irule ao_resolve_iszero_inst_sim_local >> simp[] >>
                  metis_tac[]))))
  >- (* range soundness *)
     (qpat_x_assum `fn0 = _` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `ra = _` (SUBST_ALL_TAC o SYM) >>
      rpt strip_tac >>
      irule range_analyze_sound >>
      qexists_tac `s` >> gvs[]))
QED

(* ===== Block-lift helpers ===== *)

Triviality ao_dfg_inv_idx0[local]:
  !dfg s n. ao_dfg_inv dfg (s with vs_inst_idx := n) = ao_dfg_inv dfg s
Proof
  simp[ao_dfg_inv_def, lookup_var_def]
QED

Triviality local_offset_operands[local]:
  !inst. (ao_handle_offset_inst inst).inst_operands = inst.inst_operands \/
         ?l v. inst.inst_opcode = ADD /\
               inst.inst_operands = [Label l; Lit v] /\
               (ao_handle_offset_inst inst).inst_operands = [Lit v; Label l]
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  Cases_on `inst.inst_opcode = ADD` >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

Triviality fn0_blocks_inst_wf[local]:
  !fn fn0 bb.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    EVERY inst_wf (fn_insts fn) /\
    MEM bb fn0.fn_blocks ==>
    EVERY inst_wf bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  fs[listTheory.MEM_MAP] >> rename1 `MEM bb0 fn.fn_blocks` >> gvs[] >>
  simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >> rpt strip_tac >>
  irule ao_handle_offset_inst_wf >>
  fs[listTheory.EVERY_MEM] >> first_x_assum irule >>
  irule mem_block_mem_fn_insts >> metis_tac[]
QED

Triviality dfg_def_var_not_in_fv[local]:
  !fn fn0 dfg x inst.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    dfg = dfg_build_function fn0 /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    dfg_get_def dfg x = SOME inst ==>
    x NOTIN ao_fn_fresh_vars fn
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule dfg_build_function_correct >> strip_tac >>
  qpat_x_assum `MEM inst (fn_insts _)` mp_tac >>
  simp[fn_insts_def] >> strip_tac >>
  drule fn_insts_blocks_map_offset >> strip_tac >> gvs[] >>
  fs[ao_handle_offset_inst_outputs] >>
  first_x_assum irule >> qexists_tac `inst0` >>
  simp[fn_insts_def]
QED

Triviality dfg_def_iszero_operand_not_in_fv[local]:
  !fn fn0 dfg x inst op.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    dfg = dfg_build_function fn0 /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    dfg_get_def dfg x = SOME inst /\
    MEM (Var op) inst.inst_operands ==>
    op NOTIN ao_fn_fresh_vars fn
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule dfg_build_function_correct >> strip_tac >>
  qpat_x_assum `MEM inst (fn_insts _)` mp_tac >>
  simp[fn_insts_def] >> strip_tac >>
  drule fn_insts_blocks_map_offset >> strip_tac >> gvs[] >>
  qspecl_then [`inst0`] strip_assume_tac local_offset_operands >> gvs[] >>
  first_x_assum irule >> qexists_tac `inst0` >>
  simp[fn_insts_def]
QED

(* Clean-context wrapper for strict_dom_iszero_inv_state_equiv_compat:
   discharges the dfg-def freshness obligations via the bridging lemmas. *)
Triviality strict_dom_state_equiv_fv[local]:
  !fn fn0 dfg s1 s2.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    dfg = dfg_build_function fn0 /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    strict_dom_iszero_inv fn0 dfg s1 /\
    state_equiv (ao_fn_fresh_vars fn) s1 s2 ==>
    strict_dom_iszero_inv fn0 dfg s2
Proof
  rpt strip_tac >>
  qspecl_then [`fn0`, `dfg`, `ao_fn_fresh_vars fn`, `s1`, `s2`] mp_tac
    strict_dom_iszero_inv_state_equiv_compat >>
  impl_tac >- (
    rpt conj_tac
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- (rpt strip_tac >> drule_all dfg_def_var_not_in_fv >> simp[])
    >- (rpt strip_tac >> `MEM (Var op) inst.inst_operands` by simp[] >>
        drule_all dfg_def_iszero_operand_not_in_fv >> simp[])) >>
  simp[]
QED

(* dfg_sound transfers across state_equiv (ao_fn_fresh_vars fn): all DFG-def
   vars and their operands are non-fresh, so FLOOKUP agrees between s1 and s2. *)
Theorem ao_dfg_sound_state_equiv_compat:
  !fn fn0 dfg s1 s2.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    dfg = dfg_build_function fn0 /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    state_equiv (ao_fn_fresh_vars fn) s1 s2 /\
    dfg_sound dfg s1.vs_vars ==>
    dfg_sound dfg s2.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  `!w. (?inst. dfg_get_def dfg w = SOME inst) ==>
       FLOOKUP s2.vs_vars w = FLOOKUP s1.vs_vars w` by
    (rpt strip_tac >>
     `w NOTIN ao_fn_fresh_vars fn` by (drule_all dfg_def_var_not_in_fv >> simp[]) >>
     fs[state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `!w inst u. dfg_get_def dfg w = SOME inst /\ MEM (Var u) inst.inst_operands ==>
       FLOOKUP s2.vs_vars u = FLOOKUP s1.vs_vars u` by
    (rpt strip_tac >>
     `u NOTIN ao_fn_fresh_vars fn` by
       (`MEM (Var u) inst.inst_operands` by simp[] >>
        drule_all dfg_def_iszero_operand_not_in_fv >> simp[]) >>
     fs[state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `dfg_assign_sound dfg s1.vs_vars /\ dfg_iszero_sound dfg s1.vs_vars /\
   dfg_eq_sound dfg s1.vs_vars /\ dfg_compare_sound dfg s1.vs_vars`
    by fs[dfg_sound_def] >>
  simp[dfg_sound_def] >> rpt conj_tac
  >- ((* assign *)
      simp[dfg_assign_sound_def] >> rpt gen_tac >> strip_tac >>
      `FLOOKUP s2.vs_vars v = FLOOKUP s1.vs_vars v` by metis_tac[] >>
      `FLOOKUP s2.vs_vars u = FLOOKUP s1.vs_vars u` by metis_tac[listTheory.MEM] >>
      `v IN FDOM s1.vs_vars` by
        (Cases_on `FLOOKUP s1.vs_vars v` >> fs[finite_mapTheory.FLOOKUP_DEF]) >>
      `FLOOKUP s1.vs_vars v = FLOOKUP s1.vs_vars u` suffices_by gvs[] >>
      qpat_x_assum `dfg_assign_sound dfg s1.vs_vars`
        (strip_assume_tac o SIMP_RULE std_ss [dfg_assign_sound_def]) >>
      metis_tac[])
  >- ((* iszero *)
      simp[dfg_iszero_sound_def] >> rpt gen_tac >> strip_tac >> gen_tac >>
      strip_tac >>
      `FLOOKUP s2.vs_vars v = FLOOKUP s1.vs_vars v` by metis_tac[] >>
      `FLOOKUP s2.vs_vars tv = FLOOKUP s1.vs_vars tv` by metis_tac[listTheory.MEM] >>
      `FLOOKUP s1.vs_vars v = SOME w` by gvs[] >>
      `(w <> 0w ==> FLOOKUP s1.vs_vars tv = SOME 0w) /\
       (w = 0w ==> !w'. FLOOKUP s1.vs_vars tv = SOME w' ==> w' <> 0w)`
        suffices_by gvs[] >>
      qpat_x_assum `dfg_iszero_sound dfg s1.vs_vars`
        (strip_assume_tac o SIMP_RULE std_ss [dfg_iszero_sound_def]) >>
      metis_tac[])
  >- ((* eq *)
      simp[dfg_eq_sound_def] >> rpt gen_tac >> strip_tac >> gen_tac >>
      strip_tac >> strip_tac >>
      `FLOOKUP s2.vs_vars v = FLOOKUP s1.vs_vars v` by metis_tac[] >>
      `!u. (lhs = Var u \/ rhs = Var u) ==>
           FLOOKUP s2.vs_vars u = FLOOKUP s1.vs_vars u` by
        (rpt strip_tac >> metis_tac[listTheory.MEM]) >>
      `FLOOKUP s1.vs_vars v = SOME w` by gvs[] >>
      `(!u. lhs = Var u ==> ?wu. FLOOKUP s1.vs_vars u = SOME wu) /\
       (!u. rhs = Var u ==> ?wu. FLOOKUP s1.vs_vars u = SOME wu) /\
       (!u wu wl. lhs = Var u /\ rhs = Lit wl /\
                  FLOOKUP s1.vs_vars u = SOME wu ==> wu = wl) /\
       (!u wu wl. rhs = Var u /\ lhs = Lit wl /\
                  FLOOKUP s1.vs_vars u = SOME wu ==> wu = wl) /\
       (!u1 u2 w1 w2. lhs = Var u1 /\ rhs = Var u2 /\
          FLOOKUP s1.vs_vars u1 = SOME w1 /\ FLOOKUP s1.vs_vars u2 = SOME w2 ==>
          w1 = w2)` suffices_by
        (strip_tac >> rpt conj_tac >> rpt strip_tac >> metis_tac[]) >>
      qpat_x_assum `dfg_eq_sound dfg s1.vs_vars`
        (strip_assume_tac o SIMP_RULE std_ss [dfg_eq_sound_def]) >>
      metis_tac[])
  >- ((* compare *)
      simp[dfg_compare_sound_def] >> rpt gen_tac >> strip_tac >> gen_tac >>
      strip_tac >>
      `FLOOKUP s2.vs_vars v = FLOOKUP s1.vs_vars v` by metis_tac[] >>
      `!u. (lhs = Var u \/ rhs = Var u) ==>
           FLOOKUP s2.vs_vars u = FLOOKUP s1.vs_vars u` by
        (rpt strip_tac >> metis_tac[listTheory.MEM]) >>
      `FLOOKUP s1.vs_vars v = SOME w` by gvs[] >>
      `(!u wl wu. lhs = Var u /\ rhs = Lit wl /\
          FLOOKUP s1.vs_vars u = SOME wu ==>
          ((w <> 0w) =
            (if inst.inst_opcode = LT then w2n wu < w2n wl
             else if inst.inst_opcode = GT then w2n wu > w2n wl
             else if inst.inst_opcode = SLT then w2i wu < w2i wl
             else w2i wu > w2i wl))) /\
       (!u wl wu. rhs = Var u /\ lhs = Lit wl /\
          FLOOKUP s1.vs_vars u = SOME wu ==>
          ((w <> 0w) =
            (if inst.inst_opcode = LT then w2n wl < w2n wu
             else if inst.inst_opcode = GT then w2n wl > w2n wu
             else if inst.inst_opcode = SLT then w2i wl < w2i wu
             else w2i wl > w2i wu)))` suffices_by
        (strip_tac >> rpt conj_tac >> rpt strip_tac >> metis_tac[]) >>
      qpat_x_assum `dfg_compare_sound dfg s1.vs_vars`
        (strip_assume_tac o SIMP_RULE std_ss [dfg_compare_sound_def]) >>
      metis_tac[])
QED

(* The ops-defined invariant transfers across state_equiv: DFG-def vars and
   their tracked operands are non-fresh, so FDOM membership agrees. *)
Theorem ao_ops_defined_state_equiv_compat:
  !fn fn0 dfg s1 s2.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    dfg = dfg_build_function fn0 /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    state_equiv (ao_fn_fresh_vars fn) s1 s2 /\
    (!vv dinst u. dfg_get_def dfg vv = SOME dinst /\ vv IN FDOM s1.vs_vars /\
       dfg_tracked_opcode dinst.inst_opcode /\ MEM (Var u) dinst.inst_operands ==>
       u IN FDOM s1.vs_vars) ==>
    (!vv dinst u. dfg_get_def dfg vv = SOME dinst /\ vv IN FDOM s2.vs_vars /\
       dfg_tracked_opcode dinst.inst_opcode /\ MEM (Var u) dinst.inst_operands ==>
       u IN FDOM s2.vs_vars)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `vv NOTIN ao_fn_fresh_vars fn` by (drule_all dfg_def_var_not_in_fv >> simp[]) >>
  `u NOTIN ao_fn_fresh_vars fn` by
    (drule_all dfg_def_iszero_operand_not_in_fv >> simp[]) >>
  `FLOOKUP s1.vs_vars vv = FLOOKUP s2.vs_vars vv /\
   FLOOKUP s1.vs_vars u = FLOOKUP s2.vs_vars u` by
    fs[state_equiv_def, execution_equiv_def, lookup_var_def] >>
  `vv IN FDOM s1.vs_vars` by
    (Cases_on `FLOOKUP s1.vs_vars vv` >> fs[finite_mapTheory.FLOOKUP_DEF]) >>
  `u IN FDOM s1.vs_vars` by metis_tac[] >>
  Cases_on `FLOOKUP s2.vs_vars u` >> fs[finite_mapTheory.FLOOKUP_DEF]
QED

(* Combined block_inv state_equiv compatibility: all four invariant
   components transfer across state_equiv (ao_fn_fresh_vars fn). Used by
   the phase-3 block_inv compat obligation. *)
Theorem ao_block_inv_state_equiv_compat:
  !fn fn0 dfg ra targets s1 s2.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ao_targets_wf targets /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    state_equiv (ao_fn_fresh_vars fn) s1 s2 /\
    ao_dfg_inv dfg (s1 with vs_inst_idx := 0) /\
    strict_dom_iszero_inv fn0 dfg s1 /\
    ao_chain_defined_prefix targets s1 /\
    range_sound (df_widen_at NONE ra s1.vs_current_bb 0) s1 ==>
    ao_dfg_inv dfg (s2 with vs_inst_idx := 0) /\
    strict_dom_iszero_inv fn0 dfg s2 /\
    ao_chain_defined_prefix targets s2 /\
    range_sound (df_widen_at NONE ra s2.vs_current_bb 0) s2
Proof
  rpt gen_tac >> strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by
    fs[state_equiv_def, execution_equiv_def] >>
  rpt conj_tac
  >- ((* ao_dfg_inv *)
      `state_equiv (ao_fn_fresh_vars fn) (s1 with vs_inst_idx := 0)
                   (s2 with vs_inst_idx := 0)` by
        (qpat_x_assum `state_equiv _ _ _` mp_tac >>
         simp[state_equiv_def, execution_equiv_def, lookup_var_def]) >>
      qspecl_then [`dfg`, `ao_fn_fresh_vars fn`,
                   `s1 with vs_inst_idx := 0`, `s2 with vs_inst_idx := 0`]
        mp_tac ao_dfg_inv_state_equiv_compat >>
      impl_tac >- (
        rpt conj_tac
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC
        >- (rpt strip_tac >> drule_all dfg_def_var_not_in_fv >> simp[])) >>
      simp[])
  >- ((* strict_dom_iszero_inv *)
      qspecl_then [`fn`, `fn0`, `dfg`, `s1`, `s2`] mp_tac
        strict_dom_state_equiv_fv >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[])
  >- ((* ao_chain_defined_prefix *)
      irule ao_chain_defined_prefix_state_equiv_compat >>
      qexistsl_tac [`ao_fn_fresh_vars fn`, `s1`] >> simp[] >>
      rpt strip_tac >>
      metis_tac[ao_chain_vars_not_in_fv])
  >- ((* range_sound *)
      `range_sound (df_widen_at NONE ra s1.vs_current_bb 0) s2`
        suffices_by gvs[] >>
      qspecl_then [`fn`, `fn0`, `ra`, `ao_fn_fresh_vars fn`,
                   `s1.vs_current_bb`, `s1`, `s2`] mp_tac
        ao_range_sound_state_equiv_compat >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >> simp[])
QED

(* ===== Loop-robust per-block simulation ===== *)

Triviality bb_not_terminator_before_last[local]:
  !bb idx.
    bb_well_formed bb /\ SUC idx < LENGTH bb.bb_instructions ==>
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode
Proof
  rpt strip_tac >> fs[bb_well_formed_def] >>
  `idx < LENGTH bb.bb_instructions /\ idx <> PRE (LENGTH bb.bb_instructions)` by
    (qpat_x_assum `SUC idx < LENGTH _` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[arithmeticTheory.PRE_SUB1] >> DECIDE_TAC) >>
  metis_tac[]
QED

Theorem ao_block_sim_local:
  !fn fn0 mid dfg ra targets bb.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    mid = fn_max_inst_id fn0 /\
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    wf_function fn0 /\ wf_ssa fn0 /\
    ao_targets_wf targets /\
    EVERY inst_wf (fn_insts fn) /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    MEM bb fn0.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn0).cfg_dfs_pre ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      s.vs_current_bb = bb.bb_label /\
      in_range_state (range_at_inst ra bb.bb_label 0) s.vs_vars /\
      strict_dom_iszero_inv fn0 dfg s /\
      ao_chain_defined_prefix targets s /\
      ao_dfg_inv dfg (s with vs_inst_idx := 0) ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result (state_equiv (ao_fn_fresh_vars fn))
        (execution_equiv (ao_fn_fresh_vars fn))
        (execution_equiv (ao_fn_fresh_vars fn))
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx (ao_transform_block mid dfg ra targets bb) s)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `fv = ao_fn_fresh_vars fn` >>
  `EVERY inst_wf bb.bb_instructions` by metis_tac[fn0_blocks_inst_wf] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  qabbrev_tac `sound = \(idx:num) (st:venom_state).
    idx < LENGTH bb.bb_instructions ==>
      within_block_iszero_inv fn0 bb idx st /\
      in_range_state (range_at_inst ra bb.bb_label idx) st.vs_vars /\
      strict_dom_iszero_inv fn0 dfg st /\
      ao_chain_defined_prefix targets st /\
      ao_dfg_inv dfg (st with vs_inst_idx := 0) /\
      st.vs_current_bb = bb.bb_label` >>
  rpt gen_tac >> strip_tac >>
  (* Rewrite ao_transform_block to analysis_block_transform *)
  `ao_transform_block mid dfg ra targets bb =
   analysis_block_transform 0
     (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions)))
     (\v inst. ao_transform_inst mid dfg ra bb.bb_label v targets inst) bb` by
    (simp[analysis_block_transform_def, ao_transform_block_def] >>
     `MAPi (\idx inst. ao_transform_inst mid dfg ra bb.bb_label idx targets inst)
          bb.bb_instructions =
      MAPi (\idx inst. ao_transform_inst mid dfg ra bb.bb_label
          (df_at 0 (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions)))
             bb.bb_label idx) targets inst) bb.bb_instructions`
       suffices_by simp[] >>
     irule MAPi_CONG' >> simp[] >> rpt strip_tac >>
     simp[idx_df_state_at2]) >>
  ASM_REWRITE_TAC [] >>
  qspecl_then
    [`state_equiv fv`, `execution_equiv fv`, `sound`,
     `\(st:venom_state). T`,
     `\v inst. ao_transform_inst mid dfg ra bb.bb_label v targets inst`,
     `bb`, `0`, `idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions))`,
     `\(rc:'b) (inst:instruction) v. SUC v`, `ARB:'b`]
    mp_tac analysis_block_sim_inv_at >>
  impl_tac
  >- (rpt conj_tac
      >- simp[state_equiv_execution_equiv_valid_state_rel]
      >- metis_tac[state_equiv_trans]
      >- metis_tac[execution_equiv_trans]
      (* per-inst sim *)
      >- (rpt strip_tac >>
          `df_at 0 (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions))) bb.bb_label idx = idx` by
            (irule idx_df_state_at2 >> simp[]) >>
          fs[] >>
          `within_block_iszero_inv fn0 bb idx s' /\
           in_range_state (range_at_inst ra bb.bb_label idx) s'.vs_vars /\
           strict_dom_iszero_inv fn0 dfg s' /\
           ao_chain_defined_prefix targets s' /\
           ao_dfg_inv dfg (s' with vs_inst_idx := 0) /\
           s'.vs_current_bb = bb.bb_label` by
            (qpat_x_assum `sound idx s'` mp_tac >> simp[Abbr `sound`]) >>
          qspecl_then [`fn`, `fn0`, `mid`, `dfg`, `ra`, `targets`, `bb`,
            `fuel`, `ctx`, `idx`, `EL idx bb.bb_instructions`, `s'`]
            mp_tac ao_per_inst_sim_fn0_local >>
          impl_tac >- (fs[listTheory.EVERY_EL] >> rfs[]) >>
          simp[])
      (* inst_transform_structural *)
      >- simp[ao_transform_inst_structural]
      (* EVERY inst_wf *)
      >- simp[]
      (* operand agreement *)
      >- (rpt strip_tac >>
          `x NOTIN fv` by
            (irule ao_fn0_operand_not_in_fv >>
             rpt conj_tac >> gvs[Abbr `fv`] >> metis_tac[]) >>
          fs[state_equiv_def, execution_equiv_def])
      (* transfer_sound *)
      >- (rpt strip_tac >>
          `df_at 0 (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions))) bb.bb_label idx = idx` by
            (irule idx_df_state_at2 >> simp[]) >>
          `df_at 0 (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions))) bb.bb_label (SUC idx) =
             SUC idx` by (irule idx_df_state_at2 >> simp[]) >>
          fs[] >>
          rename1 `step_inst fl cx (EL idx bb.bb_instructions) sp = OK sp'` >>
          `within_block_iszero_inv fn0 bb idx sp /\
           in_range_state (range_at_inst ra bb.bb_label idx) sp.vs_vars /\
           strict_dom_iszero_inv fn0 dfg sp /\
           ao_chain_defined_prefix targets sp /\
           ao_dfg_inv dfg (sp with vs_inst_idx := 0) /\
           sp.vs_current_bb = bb.bb_label` by
            (qpat_x_assum `sound idx sp` mp_tac >> simp[Abbr `sound`]) >>
          simp[Abbr `sound`] >> strip_tac >>
          `~is_terminator (EL idx bb.bb_instructions).inst_opcode` by
            metis_tac[bb_not_terminator_before_last] >>
          `MEM (EL idx bb.bb_instructions) bb.bb_instructions` by
            (irule listTheory.EL_MEM >> simp[]) >>
          `MEM (EL idx bb.bb_instructions) (fn_insts fn0)` by
            metis_tac[mem_block_mem_fn_insts] >>
          rpt conj_tac
          >- metis_tac[wbiz_step_any]
          >- (qpat_x_assum `ra = _` SUBST_ALL_TAC >>
              drule_all ao_local_transfer_sound >> simp[])
          >- (irule strict_dom_iszero_inv_step_preserved_local >>
              simp[] >> rfs[] >> fs[listTheory.EVERY_EL] >> rfs[] >>
              metis_tac[])
          >- (`ssa_form fn0` by fs[wf_ssa_def] >>
              qpat_x_assum `targets = _` SUBST_ALL_TAC >>
              irule ao_chain_defined_prefix_step_non_term >>
              simp[markerTheory.Abbrev_def] >>
              fs[listTheory.EVERY_EL] >> rfs[] >> metis_tac[])
          >- (`ssa_form fn0` by fs[wf_ssa_def] >>
              `inst_wf (EL idx bb.bb_instructions)` by
                (fs[listTheory.EVERY_EL] >> rfs[]) >>
              `ao_dfg_inv dfg sp` by fs[ao_dfg_inv_idx0] >>
              simp[ao_dfg_inv_idx0] >>
              drule_all ao_dfg_inv_step_any >> simp[])
          >- metis_tac[step_preserves_control_flow])
      (* sound preserved by R_ok *)
      >- (rpt gen_tac >> strip_tac >>
          reverse (Cases_on `v < LENGTH bb.bb_instructions`)
          >- gvs[Abbr `sound`] >>
          `within_block_iszero_inv fn0 bb v s1 /\
           in_range_state (range_at_inst ra bb.bb_label v) s1.vs_vars /\
           strict_dom_iszero_inv fn0 dfg s1 /\
           ao_chain_defined_prefix targets s1 /\
           ao_dfg_inv dfg (s1 with vs_inst_idx := 0) /\
           s1.vs_current_bb = bb.bb_label` by
            (qpat_x_assum `sound v s1` mp_tac >> simp[Abbr `sound`]) >>
          simp[Abbr `sound`] >>
          `s1.vs_current_bb = s2.vs_current_bb` by fs[state_equiv_def] >>
          rpt conj_tac
          >- (qspecl_then [`fn0`, `bb`, `v`, `fv`, `s1`, `s2`] mp_tac
                wbiz_state_equiv_compat >>
              impl_tac >- (rpt conj_tac
                >- first_assum ACCEPT_TAC
                >- gvs[]
                >- (rpt strip_tac >>
                    `MEM (EL j bb.bb_instructions) bb.bb_instructions` by
                      (irule listTheory.EL_MEM >> simp[]) >>
                    qspecl_then [`fn`, `fn0`, `fv`, `bb`,
                      `EL j bb.bb_instructions`, `x`] mp_tac
                      ao_fn0_output_not_in_fv >>
                    impl_tac >- (gvs[Abbr `fv`] >> metis_tac[]) >> simp[])
                >- (rpt strip_tac >>
                    `MEM (EL j bb.bb_instructions) bb.bb_instructions` by
                      (irule listTheory.EL_MEM >> simp[]) >>
                    qspecl_then [`fn`, `fn0`, `fv`, `bb`,
                      `EL j bb.bb_instructions`, `op`] mp_tac
                      ao_fn0_operand_not_in_fv >>
                    impl_tac >- (gvs[Abbr `fv`] >> metis_tac[]) >> simp[])) >>
              simp[])
          >- (irule ao_in_range_state_equiv_compat >>
              qexistsl_tac [`fn`, `fn0`, `fv`, `s1`] >> gvs[Abbr `fv`] >>
              metis_tac[])
          >- (qspecl_then [`fn`, `fn0`, `dfg`, `s1`, `s2`] mp_tac
                strict_dom_state_equiv_fv >>
              impl_tac >- (gvs[Abbr `fv`] >> metis_tac[]) >> simp[])
          >- (irule ao_chain_defined_prefix_state_equiv_compat >>
              qexistsl_tac [`fv`, `s1`] >> simp[] >> rpt strip_tac >>
              metis_tac[ao_chain_vars_not_in_fv])
          >- (`state_equiv fv (s1 with vs_inst_idx := 0)
                               (s2 with vs_inst_idx := 0)` by
                (qpat_x_assum `state_equiv _ s1 s2` mp_tac >>
                 simp[state_equiv_def, execution_equiv_def, lookup_var_def]) >>
              irule ao_dfg_inv_state_equiv_compat >>
              qexistsl_tac [`fv`, `s1 with vs_inst_idx := 0`] >> simp[] >>
              metis_tac[dfg_def_var_not_in_fv])
          >- metis_tac[])
      (* df_at chain = transfer *)
      >- (rpt strip_tac >>
          `df_at 0 (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions))) bb.bb_label idx = idx` by
            (irule idx_df_state_at2 >> simp[]) >>
          `df_at 0 (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions))) bb.bb_label (SUC idx) =
             SUC idx` by (irule idx_df_state_at2 >> simp[]) >>
          simp[])
      (* state_inv preserved through step *)
      >- simp[]
      (* state_inv preserved through R_ok *)
      >- simp[]) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  `df_at 0 (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions))) bb.bb_label 0 = 0` by
    (irule idx_df_state_at2 >> simp[]) >>
  simp[] >>
  `sound 0 s` by
    (simp[Abbr `sound`] >> strip_tac >>
     simp[within_block_iszero_inv_def] >> gvs[ao_dfg_inv_idx0]) >>
  simp[]
QED

val _ = export_theory();
