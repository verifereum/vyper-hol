(* Step-level invariant obligations for algebraic optimization.
 *
 * Three obligations required by analysis_block_sim_inv_at in
 * ao_block_sim_range (algebraicOptProofsScript.sml):
 *
 *   1. in_range_state compatible with state_equiv fv
 *   2. sinv (dfg + chain_inv + chains_defined) preserved by step_inst
 *   3. sinv compatible with state_equiv fv
 *
 * Also: chain variable freshness (needed by 3 and block-level compat).
 *)

Theory aoStepInvObligation
Ancestors
  algebraicOptDefs aoResolveObligation aoRangeObligation
  aoTargetProps aoBlockInvObligation aoPhase1Wf aoPhase3Wf
  stateEquiv venomWf venomExecSemantics venomExecProofs venomState
  venomInst venomInstProofs venomInstProps
  analysisSimDefs rangeAnalysisProofs rangeAnalysisDefs rangeEvalDefs
  dfgAnalysisProps dfAnalyzeWidenDefs
Libs
  pairLib BasicProvers

(* ===== Chain variable source lemmas ===== *)

Triviality fn_insts_blocks_map_offset:
  !bbs inst.
    MEM inst (fn_insts_blocks
      (MAP (\b. b with bb_instructions :=
        MAP ao_handle_offset_inst b.bb_instructions) bbs)) ==>
    ?inst0. MEM inst0 (fn_insts_blocks bbs) /\
            inst = ao_handle_offset_inst inst0
Proof
  Induct >> rpt strip_tac
  >- fs[fn_insts_blocks_def, listTheory.MAP]
  >- (fs[fn_insts_blocks_def, listTheory.MAP,
         listTheory.MEM_APPEND, listTheory.MEM_MAP] >>
      metis_tac[])
QED

Triviality chain_el_step:
  !acc inst v chain k x.
    ALOOKUP (ao_compute_iszero_step acc inst) v = SOME chain /\
    k < LENGTH chain /\ EL k chain = Var x ==>
    (?v' chain' k'. ALOOKUP acc v' = SOME chain' /\
       k' < LENGTH chain' /\ EL k' chain' = Var x) \/
    MEM (Var x) inst.inst_operands \/
    MEM x inst.inst_outputs
Proof
  rpt gen_tac >> simp[ao_compute_iszero_step_def] >>
  every_case_tac >> gvs[LET_THM] >>
  TRY (strip_tac >> TRY DISJ1_TAC >> metis_tac[]) >>
  strip_tac >> Cases_on `h = v` >> gvs[] >>
  TRY (TRY DISJ1_TAC >> metis_tac[]) >>
  gvs[listTheory.LENGTH_SNOC] >>
  Cases_on `k` >>
  gvs[listTheory.EL, listTheory.HD, listTheory.TL,
      listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC,
      listTheory.SNOC] >>
  TRY (Cases_on `n` >>
       gvs[listTheory.EL, listTheory.HD, listTheory.TL] >> NO_TAC) >>
  Cases_on `x'` >>
  gvs[listTheory.SNOC, listTheory.HD, listTheory.TL,
      listTheory.EL, listTheory.LENGTH] >>
  TRY (DISJ1_TAC >> first_assum (irule_at Any) >>
       qexists_tac `0` >> gvs[listTheory.EL, listTheory.HD] >> NO_TAC) >>
  rename1 `(SNOC (Var h) tl_x)❲n❳ = Var x` >>
  `n < LENGTH tl_x \/ n = LENGTH tl_x` by DECIDE_TAC
  >- (gvs[listTheory.EL_SNOC] >>
      DISJ1_TAC >>
      metis_tac[listTheory.EL, listTheory.TL, listTheory.LENGTH,
                DECIDE ``n < m ==> SUC n < SUC m``])
  >- gvs[listTheory.EL_LENGTH_SNOC]
QED

Triviality chain_el_source:
  !insts acc v chain k x.
    ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v = SOME chain /\
    k < LENGTH chain /\ EL k chain = Var x ==>
    (?v' chain' k'. ALOOKUP acc v' = SOME chain' /\
       k' < LENGTH chain' /\ EL k' chain' = Var x) \/
    (?inst. MEM inst insts /\ MEM (Var x) inst.inst_operands) \/
    (?inst. MEM inst insts /\ MEM x inst.inst_outputs)
Proof
  Induct >> rpt strip_tac
  >- (gvs[] >> TRY DISJ1_TAC >> metis_tac[])
  >- (fs[Once listTheory.FOLDL] >>
      first_x_assum
        (qspecl_then [`ao_compute_iszero_step acc h`,
                      `v`, `chain`, `k`, `x`] mp_tac) >>
      simp[] >> strip_tac
      >- (drule_all chain_el_step >> strip_tac
          >- (DISJ1_TAC >> metis_tac[])
          >- (DISJ2_TAC >> DISJ1_TAC >> metis_tac[])
          >- (DISJ2_TAC >> DISJ2_TAC >> metis_tac[]))
      >- (DISJ2_TAC >> DISJ1_TAC >> metis_tac[])
      >- (DISJ2_TAC >> DISJ2_TAC >> metis_tac[]))
QED

Triviality handle_offset_preserves_operands:
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

Theorem ao_chain_vars_not_in_fv:
  !fn fn0 targets fv v chain k x.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    fv = ao_fn_fresh_vars fn /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==> v NOTIN fv) /\
    ALOOKUP targets v = SOME chain /\
    k < LENGTH chain /\ EL k chain = Var x ==>
    x NOTIN fv
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  fs[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  drule_all chain_el_source >> strip_tac >> gvs[] >>
  qpat_x_assum `MEM inst _` mp_tac >>
  simp[fn_insts_def] >> strip_tac >>
  drule fn_insts_blocks_map_offset >> strip_tac >> gvs[] >>
  TRY (fs[ao_handle_offset_inst_outputs] >>
       first_x_assum irule >> qexists_tac `inst0` >>
       simp[fn_insts_def] >> NO_TAC) >>
  qspecl_then [`inst0`] strip_assume_tac handle_offset_preserves_operands >>
  gvs[] >>
  qpat_x_assum `!inst v. _ /\ MEM (Var _) _ ==> _` irule >>
  qexists_tac `inst0` >> simp[fn_insts_def]
QED

(* ===== Range state equivalence compatibility ===== *)

Theorem ao_in_range_state_equiv_compat:
  !fn fn0 ra lbl n fv s1 s2.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ra = range_analyze fn0 /\
    fv = ao_fn_fresh_vars fn /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==> v NOTIN fv) /\
    state_equiv fv s1 s2 /\
    in_range_state (range_at_inst ra lbl n) s1.vs_vars ==>
    in_range_state (range_at_inst ra lbl n) s2.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  fs[in_range_state_def] >> rpt strip_tac >>
  `v NOTIN fv` suffices_by
    (strip_tac >>
     `FLOOKUP s1.vs_vars v = FLOOKUP s2.vs_vars v` by
       fs[state_equiv_def, execution_equiv_def, lookup_var_def] >>
     `FLOOKUP s1.vs_vars v = SOME w` by gvs[] >>
     metis_tac[]) >>
  `v IN FDOM (range_at_inst ra lbl n)` by
    fs[finite_mapTheory.FLOOKUP_DEF] >>
  `?inst0. MEM inst0 (fn_insts fn0) /\
           (MEM v inst0.inst_outputs \/ MEM (Var v) inst0.inst_operands)` by
    (irule range_at_inst_fdom_outputs >> qexists_tac `lbl` >>
     qexists_tac `n` >> gvs[]) >>
  `?inst_orig. MEM inst_orig (fn_insts fn) /\
               inst0 = ao_handle_offset_inst inst_orig` by
    (gvs[fn_insts_def] >> metis_tac[fn_insts_blocks_map_offset]) >>
  gvs[]
  >- (`MEM v inst_orig.inst_outputs` by gvs[ao_handle_offset_inst_outputs] >>
      metis_tac[])
  >- (qspecl_then [`inst_orig`] strip_assume_tac
        handle_offset_preserves_operands >> gvs[] >>
      metis_tac[])
QED

(* ===== sinv step preservation ===== *)

Triviality mem_block_mem_fn_insts_blocks:
  !bbs bb inst.
    MEM bb bbs /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts_blocks bbs)
Proof
  Induct >> simp[fn_insts_blocks_def] >>
  metis_tac[listTheory.MEM_APPEND]
QED

Triviality mem_block_mem_fn_insts:
  !fn bb inst.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts fn)
Proof
  simp[fn_insts_def] >> metis_tac[mem_block_mem_fn_insts_blocks]
QED

Triviality mem_flat_map_intro:
  !x f b ls. MEM b ls /\ MEM x (f b) ==> MEM x (FLAT (MAP f ls))
Proof
  rpt strip_tac >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]
QED

Triviality all_distinct_flat_map_unique:
  !ls f a b x.
    ALL_DISTINCT (FLAT (MAP f ls)) /\
    MEM a ls /\ MEM b ls /\
    MEM x (f a) /\ MEM x (f b) ==>
    a = b
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[listTheory.ALL_DISTINCT_APPEND] >>
  metis_tac[mem_flat_map_intro]
QED

Triviality is_terminator_cases:
  !opc. is_terminator opc ==>
    opc = JMP \/ opc = JNZ \/ opc = DJMP \/ opc = RET \/
    opc = RETURN \/ opc = REVERT \/ opc = STOP \/ opc = SINK \/
    opc = SELFDESTRUCT \/ opc = INVALID
Proof
  Cases >> simp[is_terminator_def]
QED

Triviality step_term_call_ctx_tac:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
     inst.inst_opcode = DJMP) ==>
    s'.vs_call_ctx = s.vs_call_ctx
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_def, step_inst_base_def, AllCaseEqs(),
       jump_to_def] >>
  rpt strip_tac >> gvs[]
QED

Triviality step_term_call_ctx_halt:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    (inst.inst_opcode = RET \/ inst.inst_opcode = RETURN \/
     inst.inst_opcode = REVERT \/ inst.inst_opcode = STOP \/
     inst.inst_opcode = SINK \/ inst.inst_opcode = SELFDESTRUCT \/
     inst.inst_opcode = INVALID) ==>
    s'.vs_call_ctx = s.vs_call_ctx
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `_ = OK _` mp_tac >>
  simp[step_inst_def, step_inst_base_def, AllCaseEqs()]
QED

Triviality step_preserves_call_ctx_any:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx
Proof
  rpt strip_tac >>
  reverse (Cases_on `is_terminator inst.inst_opcode`)
  >- metis_tac[step_preserves_call_ctx]
  >- (drule is_terminator_cases >> strip_tac >>
      metis_tac[step_term_call_ctx_tac, step_term_call_ctx_halt])
QED

Triviality ao_dfg_inv_inst_idx_irrel:
  !dfg s n. ao_dfg_inv dfg (s with vs_inst_idx := n) = ao_dfg_inv dfg s
Proof
  simp[ao_dfg_inv_def, lookup_var_def]
QED

Triviality ao_dfg_inv_step_non_output:
  !dfg inst fuel ctx s s' y inst_def val.
    ao_dfg_inv dfg s /\
    step_inst fuel ctx inst s = OK s' /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    ~MEM y inst.inst_outputs /\
    dfg_get_def dfg y = SOME inst_def /\
    lookup_var y s' = SOME val ==>
    (inst_def.inst_opcode = ADDRESS ==>
     val = w2w s'.vs_call_ctx.cc_address) /\
    (inst_def.inst_opcode = SIGNEXTEND ==>
     !w inner_op. inst_def.inst_operands = [Lit w; inner_op] ==>
     ?inner_val. val = sign_extend w inner_val)
Proof
  rpt strip_tac >> (
    `lookup_var y s' = lookup_var y s` by
      (Cases_on `is_terminator inst.inst_opcode`
       >- metis_tac[step_terminator_preserves_vars]
       >- metis_tac[step_preserves_non_output_vars]) >>
    `lookup_var y s = SOME val` by gvs[] >>
    fs[ao_dfg_inv_def] >> res_tac >> gvs[] >> metis_tac[])
QED

Triviality ao_dfg_inv_step_output:
  !dfg fn0 bb inst fuel ctx s s' y val.
    ssa_form fn0 /\ dfg = dfg_build_function fn0 /\
    MEM bb fn0.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst_wf inst /\
    ao_dfg_inv dfg s /\
    step_inst fuel ctx inst s = OK s' /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    MEM y inst.inst_outputs /\
    dfg_get_def dfg y = SOME inst /\
    lookup_var y s' = SOME val ==>
    (inst.inst_opcode = ADDRESS ==>
     val = w2w s'.vs_call_ctx.cc_address) /\
    (inst.inst_opcode = SIGNEXTEND ==>
     !w inner_op. inst.inst_operands = [Lit w; inner_op] ==>
     ?inner_val. val = sign_extend w inner_val)
Proof
  rpt strip_tac >> gvs[] >> (
    `~is_terminator inst.inst_opcode` by
      (CCONTR_TAC >> gvs[] >>
       `lookup_var y s' = lookup_var y s` by
         metis_tac[step_terminator_preserves_vars] >>
       fs[is_terminator_def]) >>
    Cases_on `inst.inst_opcode = INVOKE` >- gvs[] >>
    fs[step_inst_non_invoke] >>
    qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
    simp[Once step_inst_base_def] >>
    gvs[exec_read0_def, exec_pure2_def, eval_operand_def,
        AllCaseEqs(), inst_wf_def] >>
    strip_tac >> gvs[update_var_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
    metis_tac[])
QED

Triviality ao_dfg_inv_step_any:
  !dfg fn0 bb inst fuel ctx s s'.
    ssa_form fn0 /\ dfg = dfg_build_function fn0 /\
    MEM bb fn0.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst_wf inst /\
    ao_dfg_inv dfg s /\
    step_inst fuel ctx inst s = OK s' ==>
    ao_dfg_inv dfg s'
Proof
  rpt strip_tac >>
  `s'.vs_call_ctx = s.vs_call_ctx` by
    metis_tac[step_preserves_call_ctx_any] >>
  simp[ao_dfg_inv_def] >> rpt gen_tac >> strip_tac >>
  rename1 `dfg_get_def _ y = SOME inst_def` >>
  rename1 `lookup_var y s' = SOME val` >>
  Cases_on `MEM y inst.inst_outputs`
  >- (`inst = inst_def` by
        (`MEM inst (fn_insts fn0)` by metis_tac[mem_block_mem_fn_insts] >>
         `MEM inst_def (fn_insts fn0) /\ MEM y inst_def.inst_outputs` by
           metis_tac[dfg_build_function_correct] >>
         qspecl_then [`fn_insts fn0`, `\i. i.inst_outputs`,
                      `inst`, `inst_def`, `y`]
           mp_tac all_distinct_flat_map_unique >>
         impl_tac >- fs[ssa_form_def] >>
         simp[]) >>
      gvs[] >>
      metis_tac[ao_dfg_inv_step_output])
  >- metis_tac[ao_dfg_inv_step_non_output]
QED

Triviality eval_operand_step_preserved:
  !fuel ctx inst s s' op.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    (!x. op = Var x ==> ~MEM x inst.inst_outputs) ==>
    eval_operand op s' = eval_operand op s
Proof
  rpt strip_tac >> Cases_on `op` >> gvs[eval_operand_def]
  >- (`lookup_var s'' s' = lookup_var s'' s` suffices_by simp[] >>
      irule step_preserves_non_output_vars >> metis_tac[])
  >- (`s'.vs_labels = s.vs_labels` by metis_tac[step_preserves_labels] >>
      gvs[])
QED

Triviality eval_operand_terminator_preserved:
  !fuel ctx inst s s' op.
    step_inst fuel ctx inst s = OK s' /\
    is_terminator inst.inst_opcode ==>
    eval_operand op s' = eval_operand op s
Proof
  rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def]
  >- (irule step_terminator_preserves_vars >> metis_tac[])
  >- metis_tac[step_inst_preserves_labels_always]
QED

Triviality step_inst_fdom_subset:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst_wf inst ==>
    FDOM s.vs_vars SUBSET FDOM s'.vs_vars
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (drule is_terminator_cases >> strip_tac >> gvs[] >>
      qpat_x_assum `_ = OK _` mp_tac >>
      simp[step_inst_def, step_inst_base_def, AllCaseEqs(),
           jump_to_def] >>
      rpt strip_tac >> gvs[])
  >- (drule_all step_inst_fdom >> strip_tac >>
      simp[pred_setTheory.SUBSET_DEF])
QED

Triviality eval_operand_fdom_mono:
  !op s s'.
    FDOM s.vs_vars SUBSET FDOM s'.vs_vars /\
    s'.vs_labels = s.vs_labels /\
    (?w. eval_operand op s = SOME w) ==>
    ?w'. eval_operand op s' = SOME w'
Proof
  Cases >> simp[eval_operand_def, lookup_var_def] >>
  rpt strip_tac >>
  fs[finite_mapTheory.FLOOKUP_DEF, pred_setTheory.SUBSET_DEF] >>
  metis_tac[]
QED

(* Helper: chain_inv preserved through non-terminator step *)
Triviality chain_inv_step_non_term[local]:
  !fn0 targets inst fuel ctx s s'.
    Abbrev (targets = ao_compute_fn_iszero_targets fn0) /\
    ssa_form fn0 /\
    ao_targets_wf targets /\
    MEM inst (fn_insts fn0) /\
    inst_wf inst /\
    ~is_terminator inst.inst_opcode /\
    (!x. MEM x inst.inst_outputs ==> lookup_var x s = NONE) /\
    ao_chain_defined_prefix targets s /\
    ao_iszero_chain_inv targets s /\
    step_inst fuel ctx inst s = OK s' ==>
    ao_iszero_chain_inv targets s'
Proof
  rpt strip_tac >>
  simp_tac std_ss [ao_iszero_chain_inv_def] >>
  rpt gen_tac >> rpt strip_tac >>
  qpat_x_assum `ao_iszero_chain_inv targets s`
    (mp_tac o REWRITE_RULE [ao_iszero_chain_inv_def]) >>
  strip_tac >>
  Cases_on `(?x. EL (k + 1) chain = Var x /\ MEM x inst.inst_outputs)`
  >- (* Case: chain[k+1] is inst output = ISZERO case *)
     (gvs[] >>
      rename1 `MEM y inst.inst_outputs` >>
      `0 < k + 1` by DECIDE_TAC >>
      qspecl_then [`fn0`, `targets`, `v`, `chain`,
        `k + 1`, `y`] mp_tac chain_var_is_iszero_output >>
      impl_tac >- (gvs[markerTheory.Abbrev_def] >> DECIDE_TAC) >>
      strip_tac >>
      `inst' = inst` by
        (qspecl_then [`fn_insts fn0`, `\i. i.inst_outputs`,
                      `inst'`, `inst`, `y`]
           mp_tac all_distinct_flat_map_unique >>
         impl_tac >- gvs[ssa_form_def] >>
         simp[]) >>
      gvs[] >>
      `inst.inst_outputs = [y]` by
        (fs[inst_wf_def] >>
         Cases_on `inst.inst_outputs` >> gvs[] >>
         Cases_on `t` >> gvs[]) >>
      `lookup_var y s = NONE` by metis_tac[] >>
      `eval_operand (EL k chain) s' =
       eval_operand (EL k chain) s` by
        (irule eval_operand_step_preserved >> simp[] >>
         qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[] >>
         rpt strip_tac >> gvs[] >>
         CCONTR_TAC >> gvs[] >>
         qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
         simp[step_inst_non_invoke, is_terminator_def,
              Once step_inst_base_def, exec_pure1_def,
              eval_operand_def, lookup_var_def]) >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- gvs[is_terminator_def]
      >- (fs[step_inst_non_invoke] >>
          qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
          simp[Once step_inst_base_def, exec_pure1_def] >>
          every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
          gvs[eval_operand_def, update_var_def, lookup_var_def,
              finite_mapTheory.FLOOKUP_UPDATE]))
  >- (Cases_on `(?x. EL k chain = Var x /\ MEM x inst.inst_outputs)`
      >- (* Case: chain[k] is inst output, chain[k+1] is not.
            By prefix property + freshness: chain[k+1] is undefined
            in s, hence in s' (not an inst output). Vacuously true. *)
         (gvs[] >>
          rename1 `MEM y inst.inst_outputs` >>
          `eval_operand (Var y) s = NONE` by
            (simp[eval_operand_def] >> metis_tac[]) >>
          `eval_operand (EL (k + 1) chain) s = NONE` by
            (CCONTR_TAC >>
             `?w. eval_operand (EL (k + 1) chain) s = SOME w` by
               (Cases_on `eval_operand (EL (k + 1) chain) s` >> gvs[]) >>
             qpat_x_assum `ao_chain_defined_prefix _ _`
               (mp_tac o SIMP_RULE std_ss [ao_chain_defined_prefix_def]) >>
             disch_then (qspecl_then [`v`, `chain`, `k`, `k + 1`]
               mp_tac) >>
             simp[] >> metis_tac[]) >>
          `eval_operand (EL (k + 1) chain) s' =
           eval_operand (EL (k + 1) chain) s` by
            (irule eval_operand_step_preserved >> simp[] >>
             qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[] >>
             metis_tac[]) >>
          gvs[])
      >- (* Case: neither is inst output — both preserved *)
         (`eval_operand (EL k chain) s' =
           eval_operand (EL k chain) s` by
            (irule eval_operand_step_preserved >> simp[] >>
             qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[] >>
             metis_tac[]) >>
          `eval_operand (EL (k + 1) chain) s' =
           eval_operand (EL (k + 1) chain) s` by
            (irule eval_operand_step_preserved >> simp[] >>
             qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[] >>
             metis_tac[]) >>
          gvs[] >> metis_tac[]))
QED

(* Helper: chain_defined_prefix preserved through non-terminator step *)
Triviality prefix_inv_step_non_term[local]:
  !fn0 targets inst fuel ctx s s'.
    Abbrev (targets = ao_compute_fn_iszero_targets fn0) /\
    ssa_form fn0 /\
    MEM inst (fn_insts fn0) /\
    inst_wf inst /\
    ~is_terminator inst.inst_opcode /\
    (!x. MEM x inst.inst_outputs ==> lookup_var x s = NONE) /\
    ao_chain_defined_prefix targets s /\
    step_inst fuel ctx inst s = OK s' ==>
    ao_chain_defined_prefix targets s'
Proof
  rpt strip_tac >>
  simp_tac std_ss [ao_chain_defined_prefix_def] >>
  rpt strip_tac >>
  rename1 `ALOOKUP targets v' = SOME chain'` >>
  rename1 `j1 <= j2` >>
  Cases_on `?x. EL j2 chain' = Var x /\ MEM x inst.inst_outputs`
  >- (* j2 element is inst output: inst is ISZERO reading j2-1 *)
     (gvs[] >>
      rename1 `MEM y inst.inst_outputs` >>
      Cases_on `j1 = j2` >- metis_tac[] >>
      `j1 < j2 /\ 0 < j2` by DECIDE_TAC >>
      qspecl_then [`fn0`, `targets`, `v'`, `chain'`,
        `j2`, `y`] mp_tac chain_var_is_iszero_output >>
      impl_tac >- (gvs[markerTheory.Abbrev_def] >> DECIDE_TAC) >>
      strip_tac >>
      `inst' = inst` by
        (qspecl_then [`fn_insts fn0`, `\i. i.inst_outputs`,
                      `inst'`, `inst`, `y`]
           mp_tac all_distinct_flat_map_unique >>
         impl_tac >- gvs[ssa_form_def] >>
         simp[]) >>
      gvs[] >>
      `j1 <= j2 - 1 /\ j2 - 1 < LENGTH chain'` by DECIDE_TAC >>
      `?w1. eval_operand (EL j1 chain') s = SOME w1` by
        (qpat_x_assum `ao_chain_defined_prefix _ _`
           (mp_tac o SIMP_RULE std_ss
             [ao_chain_defined_prefix_def]) >>
         disch_then (qspecl_then [`v'`, `chain'`, `j1`, `j2 - 1`]
           mp_tac) >>
         impl_tac >- (simp[] >>
           fs[step_inst_non_invoke, is_terminator_def] >>
           qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
           simp[Once step_inst_base_def, exec_pure1_def] >>
           `j2 - 1 + 1 = j2` by DECIDE_TAC >> gvs[] >>
           every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
           metis_tac[]) >>
         simp[]) >>
      metis_tac[eval_operand_fdom_mono,
                step_inst_fdom_subset,
                step_inst_preserves_labels_always])
  >- (* j2 element is NOT inst output: preserved from s *)
     (`eval_operand (EL j2 chain') s' =
       eval_operand (EL j2 chain') s` by
        (irule eval_operand_step_preserved >> metis_tac[]) >>
      `?w2. eval_operand (EL j2 chain') s = SOME w2` by
        metis_tac[] >>
      `j1 < LENGTH chain'` by DECIDE_TAC >>
      `?w1. eval_operand (EL j1 chain') s = SOME w1` by
        (qpat_x_assum `ao_chain_defined_prefix _ _`
           (mp_tac o SIMP_RULE std_ss
             [ao_chain_defined_prefix_def]) >>
         disch_then (qspecl_then [`v'`, `chain'`, `j1`, `j2`]
           mp_tac) >>
         simp[]) >>
      metis_tac[eval_operand_fdom_mono,
                step_inst_fdom_subset,
                step_inst_preserves_labels_always])
QED

(* Helper: terminator step preserves all chain operands *)
Triviality chain_operands_terminator_preserved[local]:
  !fuel ctx inst s s' targets v chain k.
    step_inst fuel ctx inst s = OK s' /\
    is_terminator inst.inst_opcode /\
    ALOOKUP targets v = SOME chain /\
    k < LENGTH chain ==>
    eval_operand (EL k chain) s' = eval_operand (EL k chain) s
Proof
  metis_tac[eval_operand_terminator_preserved]
QED

(* Combined step preservation *)
Theorem ao_sinv_step_preserved:
  !fn fn0 dfg targets bb idx fuel ctx s s'.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    dfg = dfg_build_function fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ssa_form fn0 /\
    ao_targets_wf targets /\
    MEM bb fn0.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    inst_wf (EL idx bb.bb_instructions) /\
    (!x. MEM x (EL idx bb.bb_instructions).inst_outputs ==>
         lookup_var x s = NONE) /\
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    ao_iszero_chain_inv targets s /\
    ao_chain_defined_prefix targets s /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' ==>
    ao_dfg_inv dfg (s' with vs_inst_idx := 0) /\
    ao_iszero_chain_inv targets s' /\
    ao_chain_defined_prefix targets s'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fn0 = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qpat_x_assum `dfg = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qpat_x_assum `targets = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `MEM inst bb.bb_instructions` by
    (simp[Abbr `inst`] >> irule listTheory.EL_MEM >> simp[]) >>
  `MEM inst (fn_insts fn0)` by metis_tac[mem_block_mem_fn_insts] >>
  rpt conj_tac
  >- (* ao_dfg_inv *)
     (`ao_dfg_inv dfg s` by metis_tac[ao_dfg_inv_inst_idx_irrel] >>
      `ao_dfg_inv dfg s'` by metis_tac[ao_dfg_inv_step_any] >>
      metis_tac[ao_dfg_inv_inst_idx_irrel])
  >- (* ao_iszero_chain_inv *)
     (Cases_on `is_terminator inst.inst_opcode`
      >- (qspecl_then [`targets`, `inst`, `fuel`, `ctx`, `s`, `s'`]
            mp_tac ao_iszero_chain_inv_step_preserved >>
          simp[] >> disch_then irule >>
          metis_tac[eval_operand_terminator_preserved])
      >- (qspecl_then [`fn0`, `targets`, `inst`, `fuel`, `ctx`, `s`, `s'`]
            mp_tac chain_inv_step_non_term >>
          simp[]))
  >- (* ao_chain_defined_prefix *)
     (Cases_on `is_terminator inst.inst_opcode`
      >- (qspecl_then [`targets`, `inst`, `fuel`, `ctx`, `s`, `s'`]
            mp_tac ao_chain_defined_prefix_step_preserved >>
          simp[] >> disch_then irule >>
          metis_tac[eval_operand_terminator_preserved])
      >- (qspecl_then [`fn0`, `targets`, `inst`, `fuel`, `ctx`, `s`, `s'`]
            mp_tac prefix_inv_step_non_term >>
          simp[]))
QED

(* ===== sinv state_equiv compatibility ===== *)

Triviality ao_dfg_inv_state_equiv_compat:
  !dfg fv s1 s2.
    state_equiv fv s1 s2 /\ ao_dfg_inv dfg s1 /\
    (!x inst. dfg_get_def dfg x = SOME inst ==> x NOTIN fv) ==>
    ao_dfg_inv dfg s2
Proof
  simp[ao_dfg_inv_def] >> rpt strip_tac >>
  `x NOTIN fv` by metis_tac[] >>
  `lookup_var x s1 = lookup_var x s2` by
    fs[state_equiv_def, execution_equiv_def] >>
  `lookup_var x s1 = SOME val` by gvs[] >>
  `s1.vs_call_ctx = s2.vs_call_ctx` by
    fs[state_equiv_def, execution_equiv_def] >>
  res_tac >> gvs[] >> metis_tac[]
QED

Triviality ao_dfg_outputs_not_in_fv:
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

Theorem ao_sinv_state_equiv_compat:
  !fn fn0 dfg targets fv s1 s2.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    dfg = dfg_build_function fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    fv = ao_fn_fresh_vars fn /\
    ao_targets_wf targets /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==> v NOTIN fv) /\
    state_equiv fv s1 s2 /\
    ao_dfg_inv dfg (s1 with vs_inst_idx := 0) /\
    ao_iszero_chain_inv targets s1 /\
    ao_chain_defined_prefix targets s1 ==>
    ao_dfg_inv dfg (s2 with vs_inst_idx := 0) /\
    ao_iszero_chain_inv targets s2 /\
    ao_chain_defined_prefix targets s2
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (`state_equiv fv (s1 with vs_inst_idx := 0)
                       (s2 with vs_inst_idx := 0)` by
        (qpat_x_assum `state_equiv _ _ _` mp_tac >>
         simp[state_equiv_def, execution_equiv_def, lookup_var_def]) >>
      `!x inst'. dfg_get_def dfg x = SOME inst' ==> x NOTIN fv` by
        metis_tac[ao_dfg_outputs_not_in_fv] >>
      metis_tac[ao_dfg_inv_state_equiv_compat])
  >- (irule ao_iszero_chain_inv_state_equiv_compat >>
      qexistsl_tac [`fv`, `s1`] >> simp[] >>
      rpt strip_tac >>
      metis_tac[ao_chain_vars_not_in_fv])
  >- (irule ao_chain_defined_prefix_state_equiv_compat >>
      simp[] >> metis_tac[ao_chain_vars_not_in_fv])
QED

(* ===== range_sound state_equiv compatibility ===== *)

Theorem ao_range_sound_state_equiv_compat:
  !fn fn0 ra fv lbl s1 s2.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ra = range_analyze fn0 /\
    fv = ao_fn_fresh_vars fn /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==> v NOTIN fv) /\
    state_equiv fv s1 s2 /\
    range_sound (df_widen_at NONE ra lbl 0) s1 ==>
    range_sound (df_widen_at NONE ra lbl 0) s2
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `df_widen_at NONE ra lbl 0` >>
  gvs[range_sound_def, in_range_state_def] >>
  rpt strip_tac >>
  `v NOTIN ao_fn_fresh_vars fn` suffices_by
    (strip_tac >>
     `FLOOKUP s1.vs_vars v = FLOOKUP s2.vs_vars v` by
       fs[state_equiv_def, execution_equiv_def, lookup_var_def] >>
     `FLOOKUP s1.vs_vars v = SOME w` by gvs[] >>
     metis_tac[]) >>
  `v IN FDOM (range_at_inst
    (range_analyze
      (fn with fn_blocks :=
        MAP (\bb. bb with bb_instructions :=
          MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks))
    lbl 0)` by
    (simp[range_at_inst_def, range_unwrap_def] >>
     fs[finite_mapTheory.FLOOKUP_DEF]) >>
  `?inst0. MEM inst0 (fn_insts
    (fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks)) /\
    (MEM v inst0.inst_outputs \/ MEM (Var v) inst0.inst_operands)` by
    (irule range_at_inst_fdom_outputs >> qexists_tac `lbl` >>
     qexists_tac `0` >> simp[]) >>
  `?inst_orig. MEM inst_orig (fn_insts fn) /\
               inst0 = ao_handle_offset_inst inst_orig` by
    (gvs[fn_insts_def] >> metis_tac[fn_insts_blocks_map_offset]) >>
  gvs[]
  >- (`MEM v inst_orig.inst_outputs` by gvs[ao_handle_offset_inst_outputs] >>
      metis_tac[])
  >- (qspecl_then [`inst_orig`] strip_assume_tac
        handle_offset_preserves_operands >> gvs[] >>
      metis_tac[])
QED
