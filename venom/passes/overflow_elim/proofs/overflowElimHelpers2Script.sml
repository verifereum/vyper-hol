(*
 * Overflow Check Elimination — Helpers Part 2
 *
 * assert_local, extraction lemmas for dfg_prefix_sound, and
 * contradiction and simulation using weak chain closure.
 *)

Theory overflowElimHelpers2
Ancestors
  overflowElimHelpers
  overflowElimDefs
  assertElimProofs
  analysisSimDefs
  analysisSimProps
  passSimulationDefs
  passSimulationProps
  passSharedDefs
  passSharedProps
  stateEquiv
  stateEquivProps
  venomExecSemantics
  venomState
  venomInst
  venomWf
  venomInstProps
  venomExecProofs
  venomExecProps
  execEquivParamProps
  rangeAnalysisDefs
  rangeEvalDefs
  valueRangeDefs
  rangeAnalysisProofs
  dfAnalyzeWidenDefs
  dfgDefs
  dfgAnalysisProps
  dfgSoundDefs
  dfgSoundProofs
  worklistDefs
  list
  finite_map

(* Producer locality for ASSERT operands: the DFG producer of any
   ASSERT operand in a block is in that block and at an earlier position.
   This is a well-formedness condition satisfied by the Venom pipeline. *)
Definition assert_local_def:
  assert_local fn <=>
    !bb inst u prod.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = ASSERT /\
      MEM (Var u) inst.inst_operands /\
      dfg_get_def (dfg_build_function fn) u = SOME prod ==>
      MEM prod bb.bb_instructions /\
      !i j. i < LENGTH bb.bb_instructions /\
            j < LENGTH bb.bb_instructions /\
            EL i bb.bb_instructions = prod /\
            EL j bb.bb_instructions = inst ==>
            i < j
End

(* Eliminator for try_elim_add_overflow_v: extracts operand structure *)
Theorem try_elim_add_overflow_v_elim:
  !dfg rs lt_inst.
    try_elim_add_overflow_v dfg rs lt_inst ==>
    ?res_op x_op add_inst add_op0 add_op1 y.
      lt_inst.inst_operands = [res_op; x_op] /\
      get_producer dfg res_op = SOME add_inst /\
      add_inst.inst_opcode = ADD /\
      add_inst.inst_operands = [add_op0; add_op1] /\
      (if add_op0 = x_op then y = add_op1
       else add_op1 = x_op /\ y = add_op0) /\
      range_nonneg (range_get_range_v rs x_op) /\
      range_nonneg (range_get_range_v rs y) /\
      vr_hi (range_get_range_v rs x_op) +
      vr_hi (range_get_range_v rs y) <= UINT256_MAX_int
Proof
  rpt strip_tac >> fs[try_elim_add_overflow_v_def] >>
  BasicProvers.every_case_tac >> fs[]
QED

(* Eliminator for try_elim_sub_underflow_v: extracts operand structure *)
Theorem try_elim_sub_underflow_v_elim:
  !dfg rs gt_inst.
    try_elim_sub_underflow_v dfg rs gt_inst ==>
    ?res_op x_op sub_inst sub_y.
      gt_inst.inst_operands = [res_op; x_op] /\
      get_producer dfg res_op = SOME sub_inst /\
      sub_inst.inst_opcode = SUB /\
      sub_inst.inst_operands = [x_op; sub_y] /\
      range_nonneg (range_get_range_v rs x_op) /\
      range_nonneg (range_get_range_v rs sub_y) /\
      vr_lo (range_get_range_v rs x_op) >= vr_hi (range_get_range_v rs sub_y)
Proof
  rpt strip_tac >> fs[try_elim_sub_underflow_v_def] >>
  BasicProvers.every_case_tac >> fs[]
QED

(* ================================================================
   LT/GT contradiction helpers — each takes only the facts needed
   for its branch.
   ================================================================ *)

(* LT case: ADD overflow can't produce a true comparison *)
Theorem contradiction_lt[local]:
  !fn bb rs cmp_v cmp_inst s idx kc cmp_w.
    try_elim_add_overflow_v (dfg_build_function fn) rs cmp_inst /\
    cmp_inst.inst_opcode = LT /\
    dfg_get_def (dfg_build_function fn) cmp_v = SOME cmp_inst /\
    FLOOKUP s.vs_vars cmp_v = SOME cmp_w /\ cmp_w <> 0w /\
    dfg_prefix_sound (dfg_build_function fn) bb s.vs_vars idx /\
    in_range_state rs s.vs_vars /\
    cmp_v IN FDOM s.vs_vars /\
    kc < idx /\ kc < LENGTH bb.bb_instructions /\
    EL kc bb.bb_instructions = cmp_inst /\
    MEM bb fn.fn_blocks /\
    fn_inst_wf fn /\
    dfg_block_local fn ==>
    F
Proof
  rpt gen_tac >> strip_tac >>
  drule try_elim_add_overflow_v_elim >> strip_tac >>
  rename1 `get_producer _ res_op = SOME add_inst` >>
  Cases_on `res_op` >> gvs[get_producer_def] >>
  rename1 `dfg_get_def _ res_v = SOME add_inst` >>
  (* Locate add_inst via dfg_block_local *)
  `MEM (EL kc bb.bb_instructions) bb.bb_instructions` by
    metis_tac[MEM_EL] >>
  `MEM add_inst bb.bb_instructions /\
   !i j. i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
         EL i bb.bb_instructions = add_inst /\
         EL j bb.bb_instructions = EL kc bb.bb_instructions ==> i < j` by
    (mp_tac dfg_block_local_elim >>
     disch_then (qspecl_then [`fn`, `cmp_v`, `EL kc bb.bb_instructions`,
       `res_v`, `add_inst`, `bb`] mp_tac) >>
     simp[dfg_tracked_opcode_def]) >>
  `?ka. ka < LENGTH bb.bb_instructions /\ EL ka bb.bb_instructions = add_inst` by
    metis_tac[MEM_EL] >>
  `kc < LENGTH bb.bb_instructions` by DECIDE_TAC >>
  `ka < kc` by
    (first_x_assum (qspecl_then [`ka`, `kc`] mp_tac) >> simp[]) >>
  `ka < idx` by DECIDE_TAC >>
  (* FDOM for res_v *)
  `res_v IN FDOM s.vs_vars` by
    (mp_tac dfg_prefix_fdom_closure >>
     disch_then (qspecl_then [`dfg_build_function fn`, `bb`, `s.vs_vars`,
       `idx`, `cmp_v`, `EL kc bb.bb_instructions`, `res_v`, `kc`] mp_tac) >>
     simp[dfg_tracked_opcode_def]) >>
  (* No-Label guards from range_nonneg *)
  imp_res_tac range_nonneg_not_label >>
  (* Compare soundness *)
  mp_tac dfg_prefix_compare_sound >>
  disch_then (qspecl_then [`dfg_build_function fn`, `bb`, `s.vs_vars`,
    `idx`, `cmp_v`, `EL kc bb.bb_instructions`, `Var res_v`, `x_op`, `kc`] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  (* Arith soundness *)
  mp_tac dfg_prefix_arith_sound >>
  disch_then (qspecl_then [`dfg_build_function fn`, `bb`, `s.vs_vars`,
    `idx`, `res_v`, `add_inst`, `add_op0`, `add_op1`, `ka`] mp_tac) >>
  (impl_tac >- (fs[] >> metis_tac[])) >> strip_tac >>
  (* Unify: w1 = w1'+w2', resolve if-then-else, connect cmp_w *)
  `FLOOKUP s.vs_vars res_v = SOME w1` by fs[eval_op_env_def] >>
  `w1 = w1' + w2'` by fs[] >>
  `cmp_w = bool_to_word (w2n (w1' + w2') < w2n w2)` by gvs[] >>
  (* Range facts *)
  `in_range (range_get_range_v rs add_op0) w1'` by
    (irule range_get_range_v_sound >> metis_tac[]) >>
  `in_range (range_get_range_v rs add_op1) w2'` by
    (irule range_get_range_v_sound >> metis_tac[]) >>
  `in_range (range_get_range_v rs x_op) w2` by
    (irule range_get_range_v_sound >> metis_tac[]) >>
  (* Contradiction: no overflow => cmp_w = 0w, contradicts cmp_w ≠ 0w *)
  Cases_on `add_op0 = x_op`
  >- (`y = add_op1` by fs[] >>
      `eval_op_env x_op s.vs_vars = SOME w1'` by fs[] >>
      `w1' = w2` by fs[] >>
      pop_assum SUBST_ALL_TAC >>
      `bool_to_word (w2n (w2 + w2') < w2n w2) = 0w` by
        (irule add_no_overflow_lt_zero >>
         MAP_EVERY qexists_tac
           [`range_get_range_v rs x_op`, `range_get_range_v rs add_op1`] >>
         fs[]) >>
      fs[])
  >- (`add_op1 = x_op /\ y = add_op0` by fs[] >>
      `eval_op_env x_op s.vs_vars = SOME w2'` by fs[] >>
      `w2' = w2` by fs[] >>
      pop_assum SUBST_ALL_TAC >>
      `bool_to_word (w2n (w1' + w2) < w2n w2) = 0w` by
        (`w2n (w1' + w2) = w2n (w2 + w1')` by
           simp[wordsTheory.WORD_ADD_COMM] >>
         pop_assum SUBST1_TAC >>
         irule add_no_overflow_lt_zero >>
         MAP_EVERY qexists_tac
           [`range_get_range_v rs x_op`, `range_get_range_v rs add_op0`] >>
         fs[]) >>
      fs[])
QED

(* GT case: SUB underflow can't produce a true comparison *)
Theorem contradiction_gt[local]:
  !fn bb rs cmp_v cmp_inst s idx kc cmp_w.
    try_elim_sub_underflow_v (dfg_build_function fn) rs cmp_inst /\
    cmp_inst.inst_opcode = GT /\
    dfg_get_def (dfg_build_function fn) cmp_v = SOME cmp_inst /\
    FLOOKUP s.vs_vars cmp_v = SOME cmp_w /\ cmp_w <> 0w /\
    dfg_prefix_sound (dfg_build_function fn) bb s.vs_vars idx /\
    in_range_state rs s.vs_vars /\
    cmp_v IN FDOM s.vs_vars /\
    kc < idx /\ kc < LENGTH bb.bb_instructions /\
    EL kc bb.bb_instructions = cmp_inst /\
    MEM bb fn.fn_blocks /\
    fn_inst_wf fn /\
    dfg_block_local fn ==>
    F
Proof
  rpt gen_tac >> strip_tac >>
  drule try_elim_sub_underflow_v_elim >> strip_tac >>
  Cases_on `res_op` >> gvs[get_producer_def] >>
  rename1 `dfg_get_def _ res_v = SOME sub_inst` >>
  (* Locate sub_inst *)
  `MEM (EL kc bb.bb_instructions) bb.bb_instructions` by
    metis_tac[MEM_EL] >>
  `MEM sub_inst bb.bb_instructions /\
   !i j. i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
         EL i bb.bb_instructions = sub_inst /\
         EL j bb.bb_instructions = EL kc bb.bb_instructions ==> i < j` by
    (mp_tac dfg_block_local_elim >>
     disch_then (qspecl_then [`fn`, `cmp_v`, `EL kc bb.bb_instructions`,
       `res_v`, `sub_inst`, `bb`] mp_tac) >>
     simp[dfg_tracked_opcode_def]) >>
  `?ka. ka < LENGTH bb.bb_instructions /\ EL ka bb.bb_instructions = sub_inst` by
    metis_tac[MEM_EL] >>
  `kc < LENGTH bb.bb_instructions` by DECIDE_TAC >>
  `ka < kc` by
    (first_x_assum (qspecl_then [`ka`, `kc`] mp_tac) >> simp[]) >>
  `ka < idx` by DECIDE_TAC >>
  (* FDOM for res_v *)
  `res_v IN FDOM s.vs_vars` by
    (mp_tac dfg_prefix_fdom_closure >>
     disch_then (qspecl_then [`dfg_build_function fn`, `bb`, `s.vs_vars`,
       `idx`, `cmp_v`, `EL kc bb.bb_instructions`, `res_v`, `kc`] mp_tac) >>
     simp[dfg_tracked_opcode_def]) >>
  (* No-Label guards from range_nonneg *)
  imp_res_tac range_nonneg_not_label >>
  (* Compare soundness *)
  mp_tac dfg_prefix_compare_sound >>
  disch_then (qspecl_then [`dfg_build_function fn`, `bb`, `s.vs_vars`,
    `idx`, `cmp_v`, `EL kc bb.bb_instructions`, `Var res_v`, `x_op`, `kc`] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  (* Arith soundness *)
  mp_tac dfg_prefix_arith_sound >>
  disch_then (qspecl_then [`dfg_build_function fn`, `bb`, `s.vs_vars`,
    `idx`, `res_v`, `sub_inst`, `x_op`, `sub_y`, `ka`] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  (* Unify: w1 = w1'-w2' via FLOOKUP injectivity *)
  RULE_ASSUM_TAC (REWRITE_RULE [eval_op_env_def]) >>
  gvs[] >>
  `in_range (range_get_range_v rs x_op) w1'` by
    (irule range_get_range_v_sound >> metis_tac[]) >>
  `in_range (range_get_range_v rs sub_y) w2'` by
    (irule range_get_range_v_sound >> metis_tac[]) >>
  `bool_to_word (w2n (w1' - w2') > w2n w1') = 0w` by
    (irule sub_no_underflow_gt_zero >>
     MAP_EVERY qexists_tac
       [`range_get_range_v rs x_op`, `range_get_range_v rs sub_y`] >>
     fs[])
QED

(* Pointwise overflow contradiction using dfg_prefix_sound instead of
   dfg_ext_sound. Derives chain positions from dfg_block_local and
   assert_local, FDOM membership from eval_operand and dfg_prefix_sound. *)
Theorem overflow_check_contradiction_pw:
  !fn bb rs v s op idx.
    let dfg = dfg_build_function fn in
    try_elim_overflow_check_v dfg rs v /\
    v.inst_operands = [op] /\
    dfg_prefix_sound dfg bb s.vs_vars idx /\
    in_range_state rs s.vs_vars /\
    eval_operand op s = SOME 0w /\
    (* Weak chain closure: outputs of tracked insts at positions < idx are in FDOM *)
    (!chain_v chain_inst k.
       dfg_get_def dfg chain_v = SOME chain_inst /\
       dfg_tracked_opcode chain_inst.inst_opcode /\
       k < idx /\ k < LENGTH bb.bb_instructions /\
       EL k bb.bb_instructions = chain_inst ==>
       chain_v IN FDOM s.vs_vars) /\
    (* ASSERT position and structure *)
    idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = v /\
    v.inst_opcode = ASSERT /\
    (* Function structure for position derivation *)
    MEM bb fn.fn_blocks /\
    fn_inst_wf fn /\
    dfg_block_local fn /\
    assert_local fn ==>
    F
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  rpt gen_tac >> strip_tac >>
  fs[try_elim_overflow_check_v_def] >>
  BasicProvers.every_case_tac >> fs[] >> rfs[] >> rpt (pop_assum mp_tac) >>
  simp[] >> rpt strip_tac >>
  Cases_on `op` >> fs[get_producer_def] >>
  rename1 `dfg_get_def (dfg_build_function fn) assert_v = SOME iszero_inst` >>
  `FLOOKUP s.vs_vars assert_v = SOME 0w` by
    fs[eval_operand_def, lookup_var_def] >>
  Cases_on `h` >> fs[get_producer_def] >>
  rename1 `iszero_inst.inst_operands = [Var cmp_v]` >>
  rename1 `dfg_get_def (dfg_build_function fn) cmp_v = SOME cmp_inst` >>
  (* --- Locate iszero_inst via assert_local --- *)
  `MEM v bb.bb_instructions` by metis_tac[MEM_EL] >>
  `MEM iszero_inst bb.bb_instructions /\
   !i j. i < LENGTH bb.bb_instructions /\
         j < LENGTH bb.bb_instructions /\
         EL i bb.bb_instructions = iszero_inst /\
         EL j bb.bb_instructions = v ==> i < j` by
    (fs[assert_local_def] >>
     first_x_assum (qspecl_then [`bb`,`v`,`assert_v`,`iszero_inst`] mp_tac) >>
     simp[]) >>
  `?ki. ki < LENGTH bb.bb_instructions /\ EL ki bb.bb_instructions = iszero_inst` by
    metis_tac[MEM_EL] >>
  `ki < idx` by metis_tac[] >>
  `assert_v IN FDOM s.vs_vars` by metis_tac[FDOM_FLOOKUP] >>
  (* --- Locate cmp_inst via dfg_block_local --- *)
  `MEM cmp_inst bb.bb_instructions /\
   !i j. i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
         EL i bb.bb_instructions = cmp_inst /\
         EL j bb.bb_instructions = iszero_inst ==> i < j` by
    (mp_tac dfg_block_local_elim >>
     disch_then (qspecl_then [`fn`, `assert_v`, `iszero_inst`,
       `cmp_v`, `cmp_inst`, `bb`] mp_tac) >>
     simp[dfg_tracked_opcode_def]) >>
  `?kc. kc < LENGTH bb.bb_instructions /\ EL kc bb.bb_instructions = cmp_inst` by
    metis_tac[MEM_EL] >>
  `kc < ki` by metis_tac[] >>
  `kc < idx` by DECIDE_TAC >>
  (* --- FDOM membership via dfg_prefix_sound cascade --- *)
  `cmp_v IN FDOM s.vs_vars` by
    (mp_tac dfg_prefix_fdom_closure >>
     disch_then (qspecl_then [`dfg_build_function fn`, `bb`, `s.vs_vars`,
       `idx`, `assert_v`, `iszero_inst`, `cmp_v`, `ki`] mp_tac) >>
     simp[dfg_tracked_opcode_def]) >>
  (* Iszero soundness *)
  `!w'. FLOOKUP s.vs_vars cmp_v = SOME w' ==> w' <> 0w` by
    (mp_tac dfg_prefix_iszero_sound >>
     disch_then (qspecl_then [`dfg_build_function fn`, `bb`, `s.vs_vars`,
       `idx`, `assert_v`, `iszero_inst`, `cmp_v`, `ki`] mp_tac) >>
     simp[] >> strip_tac >>
     first_x_assum (qspec_then `0w` mp_tac) >> simp[]) >>
  `?cmp_w. FLOOKUP s.vs_vars cmp_v = SOME cmp_w /\ cmp_w <> 0w` by
    (Cases_on `FLOOKUP s.vs_vars cmp_v` >- fs[FLOOKUP_DEF] >>
     metis_tac[]) >>
  (* Dispatch to LT/GT branch helpers *)
  `kc < LENGTH bb.bb_instructions` by DECIDE_TAC >>
  Cases_on `cmp_inst.inst_opcode = LT` >> gvs[]
  >- (mp_tac (Q.SPECL [`fn`, `bb`, `rs`, `cmp_v`,
        `EL kc bb.bb_instructions`, `s`, `idx`, `kc`, `cmp_w`]
        contradiction_lt) >> simp[])
  >- (mp_tac (Q.SPECL [`fn`, `bb`, `rs`, `cmp_v`,
        `EL kc bb.bb_instructions`, `s`, `idx`, `kc`, `cmp_w`]
        contradiction_gt) >> simp[])
QED

(* Like overflow_elim_sim but uses dfg_prefix_sound instead of dfg_ext_sound.
   Uses weak chain closure (only for positions < idx) plus structural
   preconditions to derive the full chain when needed. *)
Theorem overflow_elim_sim_pw:
  !fn bb idx v fuel ctx inst s.
    let dfg = dfg_build_function fn in
    range_sound v s /\
    dfg_prefix_sound dfg bb s.vs_vars idx /\
    (* Weak chain closure *)
    (!chain_v chain_inst k.
       dfg_get_def dfg chain_v = SOME chain_inst /\
       dfg_tracked_opcode chain_inst.inst_opcode /\
       k < idx /\ k < LENGTH bb.bb_instructions /\
       EL k bb.bb_instructions = chain_inst ==>
       chain_v IN FDOM s.vs_vars) /\
    (* Position and structure *)
    idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = inst /\
    MEM bb fn.fn_blocks /\
    fn_inst_wf fn /\
    dfg_block_local fn /\
    assert_local fn /\
    inst_wf inst ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (step_inst fuel ctx inst s)
      (step_inst fuel ctx (overflow_elim_inst_v dfg (range_unwrap v) inst) s)
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = ASSERT`
  (* Non-ASSERT: transform is identity *)
  >~[`inst.inst_opcode <> ASSERT`]
  >- (simp[overflow_elim_inst_v_def] >>
      metis_tac[lift_result_refl, state_equiv_refl, execution_equiv_refl]) >>
  (* ASSERT case *)
  simp[overflow_elim_inst_v_def] >>
  IF_CASES_TAC
  (* try_elim = F: transform is identity *)
  >~[`~try_elim_overflow_check_v _ _ _`]
  >- metis_tac[lift_result_refl, state_equiv_refl, execution_equiv_refl] >>
  (* try_elim = T: ASSERT becomes NOP *)
  `LENGTH inst.inst_operands = 1` by fs[inst_wf_def] >>
  `?op. inst.inst_operands = [op]` by
    (Cases_on `inst.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[]) >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`, `op`] step_inst_assert_1) >>
  simp[] >> disch_then (fn th => REWRITE_TAC [th]) >>
  Cases_on `eval_operand op s`
  >- (DISJ1_TAC >> qexists_tac `"undefined operand"` >> simp[]) >>
  rename1 `SOME w` >>
  reverse (Cases_on `w = 0w`)
  >- simp[mk_nop_inst_correct, lift_result_def, state_equiv_refl] >>
  CCONTR_TAC >> gvs[] >>
  mp_tac (PURE_REWRITE_RULE [LET_THM] overflow_check_contradiction_pw) >>
  disch_then (qspecl_then [`fn`, `bb`, `range_unwrap v`,
       `EL idx bb.bb_instructions`, `s`, `op`, `idx`] mp_tac) >>
  simp[] >>
  Cases_on `v` >>
  fs[range_sound_def, range_unwrap_def, in_range_state_def, FLOOKUP_DEF] >>
  metis_tac[]
QED
