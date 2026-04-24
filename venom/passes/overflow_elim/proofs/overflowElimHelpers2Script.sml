(*
 * Overflow Check Elimination — Helpers Part 2
 *
 * Pointwise DFG soundness (dfg_prefix_sound), assert_local,
 * contradiction and simulation using weak chain closure,
 * and SSA-based variable preservation lemmas.
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
  venomExecProps
  execEquivParamProps
  rangeAnalysisDefs
  rangeEvalDefs
  valueRangeDefs
  variableRangeAnalysisProps
  rangeAnalysisProofs
  dfAnalyzeWidenDefs
  dfgDefs
  dfgAnalysisProps
  dfgSoundStep
  worklistDefs
  list
  finite_map

(* dfg_prefix_sound: pointwise DFG soundness for entries at positions < idx.
   For each tracked DFG entry v defined by instruction dinst at position k < idx
   in block bb: if v ∈ FDOM env, then the appropriate soundness condition holds
   (dfg_sound for ASSIGN/ISZERO/EQ/compare, dfg_arith_sound for ADD/SUB,
   dfg_compare_full_sound for LT/GT, plus FDOM closure for operands). *)
Definition dfg_prefix_sound_def:
  dfg_prefix_sound dfg bb env idx <=>
    (* For tracked entries at positions < idx: *)
    (!v dinst k.
       dfg_get_def dfg v = SOME dinst /\
       k < idx /\ k < LENGTH bb.bb_instructions /\
       EL k bb.bb_instructions = dinst /\
       v IN FDOM env ==>
       (* FDOM closure for operands *)
       (!u. MEM (Var u) dinst.inst_operands /\
            dfg_tracked_opcode dinst.inst_opcode ==> u IN FDOM env) /\
       (* dfg_iszero entry sound — matches dfg_iszero_sound form *)
       (dinst.inst_opcode = ISZERO ==>
         !inp. dinst.inst_operands = [Var inp] ==>
           !w. FLOOKUP env v = SOME w ==>
             (w <> 0w ==> FLOOKUP env inp = SOME 0w) /\
             (w = 0w ==> !w'. FLOOKUP env inp = SOME w' ==> w' <> 0w)) /\
       (* dfg_arith entry sound *)
       ((dinst.inst_opcode = ADD \/ dinst.inst_opcode = SUB) ==>
         !op1 op2. dinst.inst_operands = [op1; op2] /\
           (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
           ?w1 w2.
             eval_op_env op1 env = SOME w1 /\
             eval_op_env op2 env = SOME w2 /\
             FLOOKUP env v = SOME
               (if dinst.inst_opcode = ADD
                then word_add w1 w2 else word_sub w1 w2)) /\
       (* dfg_compare_full entry sound *)
       ((dinst.inst_opcode = LT \/ dinst.inst_opcode = GT) ==>
         !op1 op2. dinst.inst_operands = [op1; op2] /\
           (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
           ?w1 w2.
             eval_op_env op1 env = SOME w1 /\
             eval_op_env op2 env = SOME w2 /\
             FLOOKUP env v = SOME (bool_to_word
               (if dinst.inst_opcode = LT
                then w2n w1 < w2n w2
                else w2n w1 > w2n w2))))
End

(* dfg_prefix_sound at 0: trivially true (no entries at negative positions) *)
Theorem dfg_prefix_sound_0:
  !dfg bb env. dfg_prefix_sound dfg bb env 0
Proof
  simp[dfg_prefix_sound_def]
QED

(* Extraction lemmas for dfg_prefix_sound *)
Theorem dfg_prefix_iszero_sound:
  !dfg bb env idx v inst inp k.
    dfg_prefix_sound dfg bb env idx /\
    dfg_get_def dfg v = SOME inst /\
    inst.inst_opcode = ISZERO /\
    inst.inst_operands = [Var inp] /\
    v IN FDOM env /\
    k < idx /\ k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = inst ==>
    !w. FLOOKUP env v = SOME w ==>
      (w <> 0w ==> FLOOKUP env inp = SOME 0w) /\
      (w = 0w ==> !w'. FLOOKUP env inp = SOME w' ==> w' <> 0w)
Proof
  simp[dfg_prefix_sound_def] >> metis_tac[]
QED

Theorem dfg_prefix_arith_sound:
  !dfg bb env idx v inst op1 op2 k.
    dfg_prefix_sound dfg bb env idx /\
    dfg_get_def dfg v = SOME inst /\
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
    inst.inst_operands = [op1; op2] /\
    (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) /\
    v IN FDOM env /\
    k < idx /\ k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = inst ==>
    ?w1 w2.
      eval_op_env op1 env = SOME w1 /\
      eval_op_env op2 env = SOME w2 /\
      FLOOKUP env v = SOME
        (if inst.inst_opcode = ADD then word_add w1 w2 else word_sub w1 w2)
Proof
  simp[dfg_prefix_sound_def] >> metis_tac[]
QED

Theorem dfg_prefix_compare_sound:
  !dfg bb env idx v inst op1 op2 k.
    dfg_prefix_sound dfg bb env idx /\
    dfg_get_def dfg v = SOME inst /\
    (inst.inst_opcode = LT \/ inst.inst_opcode = GT) /\
    inst.inst_operands = [op1; op2] /\
    (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) /\
    v IN FDOM env /\
    k < idx /\ k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = inst ==>
    ?w1 w2.
      eval_op_env op1 env = SOME w1 /\
      eval_op_env op2 env = SOME w2 /\
      FLOOKUP env v = SOME (bool_to_word
        (if inst.inst_opcode = LT
         then w2n w1 < w2n w2
         else w2n w1 > w2n w2))
Proof
  simp[dfg_prefix_sound_def] >> metis_tac[]
QED

Theorem dfg_prefix_fdom_closure:
  !dfg bb env idx v inst u k.
    dfg_prefix_sound dfg bb env idx /\
    dfg_get_def dfg v = SOME inst /\
    dfg_tracked_opcode inst.inst_opcode /\
    MEM (Var u) inst.inst_operands /\
    v IN FDOM env /\
    k < idx /\ k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = inst ==>
    u IN FDOM env
Proof
  simp[dfg_prefix_sound_def] >> metis_tac[]
QED

(* dfg_ext_sound implies dfg_prefix_sound at any idx *)
Theorem dfg_ext_sound_implies_prefix:
  !dfg fn bb env idx.
    dfg_ext_sound dfg env /\
    dfg = dfg_build_function fn /\
    fn_inst_wf fn /\
    MEM bb fn.fn_blocks ==>
    dfg_prefix_sound dfg bb env idx
Proof
  rw[dfg_prefix_sound_def, dfg_ext_sound_def] >>
  rpt strip_tac >> gvs[]
  >- metis_tac[] (* FDOM closure *)
  >- (fs[dfg_sound_def, dfg_iszero_sound_def] >> metis_tac[])
  >- (fs[dfg_sound_def, dfg_iszero_sound_def] >> metis_tac[])
  (* ADD/SUB: from dfg_arith_sound *)
  >- (qpat_x_assum `dfg_arith_sound _ _`
        (mp_tac o REWRITE_RULE [dfg_arith_sound_def]) >>
      disch_then (qspecl_then [`v`, `EL k bb.bb_instructions`,
        `op1`, `op2`] mp_tac) >> simp[])
  >- (qpat_x_assum `dfg_arith_sound _ _`
        (mp_tac o REWRITE_RULE [dfg_arith_sound_def]) >>
      disch_then (qspecl_then [`v`, `EL k bb.bb_instructions`,
        `op1`, `op2`] mp_tac) >> simp[])
  (* LT/GT: from dfg_compare_full_sound *)
  >- (qpat_x_assum `dfg_compare_full_sound _ _`
        (mp_tac o REWRITE_RULE [dfg_compare_full_sound_def]) >>
      disch_then (qspecl_then [`v`, `EL k bb.bb_instructions`,
        `op1`, `op2`] mp_tac) >> simp[])
  >- (qpat_x_assum `dfg_compare_full_sound _ _`
        (mp_tac o REWRITE_RULE [dfg_compare_full_sound_def]) >>
      disch_then (qspecl_then [`v`, `EL k bb.bb_instructions`,
        `op1`, `op2`] mp_tac) >> simp[])
QED

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

(* Convenience wrapper of dfg_block_local *)
Theorem dfg_block_local_elim:
  !fn v inst u inst_u bb.
    dfg_block_local fn /\
    dfg_get_def (dfg_build_function fn) v = SOME inst /\
    MEM (Var u) inst.inst_operands /\
    dfg_tracked_opcode inst.inst_opcode /\
    dfg_get_def (dfg_build_function fn) u = SOME inst_u /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst_u bb.bb_instructions /\
    !i j. i < LENGTH bb.bb_instructions /\
          j < LENGTH bb.bb_instructions /\
          EL i bb.bb_instructions = inst_u /\
          EL j bb.bb_instructions = inst ==>
          i < j
Proof
  REWRITE_TAC[dfg_tracked_opcode_def, dfg_block_local_def] >> metis_tac[]
QED

(* Helper: derive MEM + position ordering from dfg_block_local *)
Triviality dfg_block_local_pos[local]:
  !fn v inst u inst_u bb j.
    dfg_block_local fn /\
    dfg_get_def (dfg_build_function fn) v = SOME inst /\
    MEM (Var u) inst.inst_operands /\
    dfg_tracked_opcode inst.inst_opcode /\
    dfg_get_def (dfg_build_function fn) u = SOME inst_u /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    j < LENGTH bb.bb_instructions /\
    EL j bb.bb_instructions = inst ==>
    MEM inst_u bb.bb_instructions /\
    ?i. i < j /\ i < LENGTH bb.bb_instructions /\
        EL i bb.bb_instructions = inst_u
Proof
  rpt strip_tac
  >- (drule_all dfg_block_local_elim >> simp[])
  >> (drule_all dfg_block_local_elim >> strip_tac) >>
  `?nn. nn < LENGTH bb.bb_instructions /\ EL nn bb.bb_instructions = inst_u` by
    metis_tac[MEM_EL] >>
  qexists_tac `nn` >> simp[]
QED

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
   for its branch, avoiding the 40+ assumption accumulation issue.
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

(* ================================================================
   Section 6b: dfg_prefix_sound preservation through step_inst
   ================================================================ *)

(* Helper: exec_pure2 output FLOOKUP *)
Theorem exec_pure2_flookup:
  !f inst s s' out.
    exec_pure2 f inst s = OK s' /\
    inst.inst_outputs = [out] ==>
    ?w1 w2 op1 op2. inst.inst_operands = [op1; op2] /\
            eval_operand op1 s = SOME w1 /\
            eval_operand op2 s = SOME w2 /\
            FLOOKUP s'.vs_vars out = SOME (f w1 w2) /\
            !v. v <> out ==> FLOOKUP s'.vs_vars v = FLOOKUP s.vs_vars v
Proof
  rpt gen_tac >> strip_tac >>
  fs[exec_pure2_def] >> BasicProvers.every_case_tac >> gvs[] >>
  fs[update_var_def, FLOOKUP_UPDATE]
QED

(* Helper: exec_pure1 output FLOOKUP *)
Theorem exec_pure1_flookup:
  !f inst s s' out.
    exec_pure1 f inst s = OK s' /\
    inst.inst_outputs = [out] ==>
    ?w op. inst.inst_operands = [op] /\
           eval_operand op s = SOME w /\
           FLOOKUP s'.vs_vars out = SOME (f w) /\
           !v. v <> out ==> FLOOKUP s'.vs_vars v = FLOOKUP s.vs_vars v
Proof
  rpt gen_tac >> strip_tac >>
  fs[exec_pure1_def] >> BasicProvers.every_case_tac >> gvs[] >>
  fs[update_var_def, FLOOKUP_UPDATE]
QED

(* Helpers for SSA-based variable preservation *)
Theorem ALL_DISTINCT_FLAT_IMP:
  !l x:'a list. ALL_DISTINCT (FLAT l) /\ MEM x l ==> ALL_DISTINCT x
Proof
  Induct >> simp[] >> rpt strip_tac >> fs[ALL_DISTINCT_APPEND]
QED

(* Element of a block is in fn_insts *)
Theorem fn_insts_has_block_el:
  !fn bb k.
    MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions ==>
    MEM (EL k bb.bb_instructions) (fn_insts fn)
Proof
  rw[fn_insts_def] >>
  `!bbs. MEM bb bbs /\ k < LENGTH bb.bb_instructions ==>
    MEM (EL k bb.bb_instructions) (fn_insts_blocks bbs)` suffices_by
    metis_tac[] >>
  Induct >> rw[fn_insts_blocks_def, MEM_APPEND] >> metis_tac[MEM_EL]
QED

(* Two different instructions in a block with unique inst_ids cannot be equal *)
Theorem block_distinct_insts:
  !bb fn k1 k2.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    k1 < LENGTH bb.bb_instructions /\ k2 < LENGTH bb.bb_instructions /\
    k1 <> k2 ==>
    EL k1 bb.bb_instructions <> EL k2 bb.bb_instructions
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (fs[wf_function_def, fn_inst_ids_distinct_def] >>
     `MEM (MAP (\i. i.inst_id) bb.bb_instructions)
          (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)` by
       (simp[MEM_MAP] >> metis_tac[]) >>
     metis_tac[ALL_DISTINCT_FLAT_IMP]) >>
  gvs[] >>
  `EL k1 (MAP (\i. i.inst_id) bb.bb_instructions) =
   EL k2 (MAP (\i. i.inst_id) bb.bb_instructions)` by
    simp[EL_MAP] >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]
QED

(* SSA: two different instructions in the same block have disjoint outputs *)
Theorem block_ssa_disjoint_outputs:
  !bb fn k1 k2 v.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    k1 < LENGTH bb.bb_instructions /\ k2 < LENGTH bb.bb_instructions /\
    k1 <> k2 /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) /\
    MEM v (EL k1 bb.bb_instructions).inst_outputs ==>
    ~MEM v (EL k2 bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `EL k1 bb.bb_instructions <> EL k2 bb.bb_instructions` by
    metis_tac[block_distinct_insts] >>
  `MEM (EL k1 bb.bb_instructions) (fn_insts fn)` by
    metis_tac[fn_insts_has_block_el] >>
  `MEM (EL k2 bb.bb_instructions) (fn_insts fn)` by
    metis_tac[fn_insts_has_block_el] >>
  metis_tac[]
QED

(* The key step lemma: executing a non-terminator instruction preserves
   FLOOKUP for variables that are outputs of OTHER instructions in the block. *)
Theorem step_preserves_other_output:
  !fn bb idx k v fuel ctx s s'.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) /\
    idx < LENGTH bb.bb_instructions /\
    k < LENGTH bb.bb_instructions /\ k <> idx /\
    MEM v (EL k bb.bb_instructions).inst_outputs /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' ==>
    FLOOKUP s'.vs_vars v = FLOOKUP s.vs_vars v
Proof
  rpt strip_tac >>
  `~MEM v (EL idx bb.bb_instructions).inst_outputs` by
    metis_tac[block_ssa_disjoint_outputs] >>
  `lookup_var v s' = lookup_var v s` by
    metis_tac[step_preserves_non_output_vars] >>
  fs[lookup_var_def]
QED

(* eval_op_env transfers when FLOOKUP agrees on Var operands *)
Theorem eval_op_env_transfer:
  !op env env' w. eval_op_env op env = SOME w /\
    (!u. op = Var u ==> FLOOKUP env' u = FLOOKUP env u) ==>
    eval_op_env op env' = SOME w
Proof
  Cases >> simp[eval_op_env_def]
QED

(* For a variable u that is an operand of a tracked instruction at position k < idx:
   executing the instruction at position idx preserves FLOOKUP u. *)
Theorem step_preserves_operand_flookup:
  !fn bb idx k v u fuel ctx s s'.
    wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) /\
    dfg_block_local fn /\
    idx < LENGTH bb.bb_instructions /\
    k < LENGTH bb.bb_instructions /\ k < idx /\
    dfg_tracked_opcode (EL k bb.bb_instructions).inst_opcode /\
    MEM (Var u) (EL k bb.bb_instructions).inst_operands /\
    MEM v (EL k bb.bb_instructions).inst_outputs /\
    dfg_get_def (dfg_build_function fn) v = SOME (EL k bb.bb_instructions) /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' ==>
    FLOOKUP s'.vs_vars u = FLOOKUP s.vs_vars u
Proof
  rpt strip_tac >>
  Cases_on `dfg_get_def (dfg_build_function fn) u`
  >- (
    `~MEM u (EL idx bb.bb_instructions).inst_outputs` by (
      CCONTR_TAC >> gvs[] >>
      `MEM (EL idx bb.bb_instructions) (fn_insts fn)` by
        metis_tac[fn_insts_has_block_el] >>
      imp_res_tac dfg_build_function_defs_complete >> gvs[]) >>
    `lookup_var u s' = lookup_var u s` by
      metis_tac[step_preserves_non_output_vars] >>
    fs[lookup_var_def])
  >- (
    rename1 `SOME inst_u` >>
    `MEM (EL k bb.bb_instructions) bb.bb_instructions` by
      metis_tac[MEM_EL] >>
    `MEM inst_u bb.bb_instructions /\
     !i j. i < LENGTH bb.bb_instructions /\
           j < LENGTH bb.bb_instructions /\
           EL i bb.bb_instructions = inst_u /\
           EL j bb.bb_instructions = EL k bb.bb_instructions ==>
           i < j` by
      (mp_tac dfg_block_local_elim >>
       disch_then (qspecl_then [`fn`,`v`,`EL k bb.bb_instructions`,
                                `u`,`inst_u`,`bb`] mp_tac) >>
       impl_tac >- simp[] >> metis_tac[]) >>
    `?ku. ku < LENGTH bb.bb_instructions /\ EL ku bb.bb_instructions = inst_u` by
      metis_tac[MEM_EL] >>
    `ku < k` by metis_tac[] >>
    `ku <> idx` by simp[] >>
    `MEM u inst_u.inst_outputs` by metis_tac[dfg_build_function_correct] >>
    metis_tac[step_preserves_other_output])
QED

(* ================================================================
   Per-opcode reduction of step_inst_base to update_var form
   ================================================================ *)

Theorem step_inst_base_assign:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ step_inst_base inst st = OK st' ==>
  ?w. eval_operand op st = SOME w /\
      st' = update_var out w st
Proof
  strip_tac >> gvs[step_inst_base_def, AllCaseEqs()]
QED

Theorem step_inst_base_iszero:
  inst.inst_opcode = ISZERO /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ step_inst_base inst st = OK st' ==>
  ?w. eval_operand op st = SOME w /\
      st' = update_var out (bool_to_word (w = 0w)) st
Proof
  strip_tac >> gvs[step_inst_base_def, exec_pure1_def, AllCaseEqs()]
QED

Theorem step_inst_base_add:
  inst.inst_opcode = ADD /\ inst.inst_operands = [op1; op2] /\
  inst.inst_outputs = [out] /\ step_inst_base inst st = OK st' ==>
  ?w1 w2. eval_operand op1 st = SOME w1 /\ eval_operand op2 st = SOME w2 /\
           st' = update_var out (w1 + w2) st
Proof
  strip_tac >> gvs[step_inst_base_def, exec_pure2_def, AllCaseEqs()]
QED

Theorem step_inst_base_sub:
  inst.inst_opcode = SUB /\ inst.inst_operands = [op1; op2] /\
  inst.inst_outputs = [out] /\ step_inst_base inst st = OK st' ==>
  ?w1 w2. eval_operand op1 st = SOME w1 /\ eval_operand op2 st = SOME w2 /\
           st' = update_var out (w1 - w2) st
Proof
  strip_tac >> gvs[step_inst_base_def, exec_pure2_def, AllCaseEqs()]
QED

Theorem step_inst_base_lt:
  inst.inst_opcode = LT /\ inst.inst_operands = [op1; op2] /\
  inst.inst_outputs = [out] /\ step_inst_base inst st = OK st' ==>
  ?w1 w2. eval_operand op1 st = SOME w1 /\ eval_operand op2 st = SOME w2 /\
           st' = update_var out (bool_to_word (w2n w1 < w2n w2)) st
Proof
  strip_tac >> gvs[step_inst_base_def, exec_pure2_def, AllCaseEqs()]
QED

Theorem step_inst_base_gt:
  inst.inst_opcode = GT /\ inst.inst_operands = [op1; op2] /\
  inst.inst_outputs = [out] /\ step_inst_base inst st = OK st' ==>
  ?w1 w2. eval_operand op1 st = SOME w1 /\ eval_operand op2 st = SOME w2 /\
           st' = update_var out (bool_to_word (w2n w1 > w2n w2)) st
Proof
  strip_tac >> gvs[step_inst_base_def, exec_pure2_def, AllCaseEqs()]
QED

Theorem step_inst_base_eq:
  inst.inst_opcode = EQ /\ inst.inst_operands = [op1; op2] /\
  inst.inst_outputs = [out] /\ step_inst_base inst st = OK st' ==>
  ?w1 w2. eval_operand op1 st = SOME w1 /\ eval_operand op2 st = SOME w2 /\
           st' = update_var out (bool_to_word (w1 = w2)) st
Proof
  strip_tac >> gvs[step_inst_base_def, exec_pure2_def, AllCaseEqs()]
QED

Theorem step_inst_base_slt:
  inst.inst_opcode = SLT /\ inst.inst_operands = [op1; op2] /\
  inst.inst_outputs = [out] /\ step_inst_base inst st = OK st' ==>
  ?w1 w2. eval_operand op1 st = SOME w1 /\ eval_operand op2 st = SOME w2 /\
           st' = update_var out (bool_to_word (word_lt w1 w2)) st
Proof
  strip_tac >> gvs[step_inst_base_def, exec_pure2_def, AllCaseEqs()]
QED

Theorem step_inst_base_sgt:
  inst.inst_opcode = SGT /\ inst.inst_operands = [op1; op2] /\
  inst.inst_outputs = [out] /\ step_inst_base inst st = OK st' ==>
  ?w1 w2. eval_operand op1 st = SOME w1 /\ eval_operand op2 st = SOME w2 /\
           st' = update_var out (bool_to_word (word_gt w1 w2)) st
Proof
  strip_tac >> gvs[step_inst_base_def, exec_pure2_def, AllCaseEqs()]
QED


(* ================================================================
   dfg_prefix_sound step lemma (promoted from overflowElimProofs)
   ================================================================ *)

(* Transfer lemma: if FLOOKUP is preserved for the output variable and all
   operand variables, then a single entry's conditions transfer between envs. *)
Theorem dfg_prefix_sound_entry_transfer:
  !dfg bb env env' v dinst k idx.
    dfg_prefix_sound dfg bb env idx /\
    dfg_get_def dfg v = SOME dinst /\
    k < idx /\ k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = dinst /\
    v IN FDOM env' /\
    FLOOKUP env' v = FLOOKUP env v /\
    (!u. MEM (Var u) dinst.inst_operands /\
         dfg_tracked_opcode dinst.inst_opcode ==>
         FLOOKUP env' u = FLOOKUP env u) ==>
    (* FDOM closure *)
    (!u. MEM (Var u) dinst.inst_operands /\
         dfg_tracked_opcode dinst.inst_opcode ==> u IN FDOM env') /\
    (* ISZERO *)
    (dinst.inst_opcode = ISZERO ==>
      !inp. dinst.inst_operands = [Var inp] ==>
        !w. FLOOKUP env' v = SOME w ==>
          (w <> 0w ==> FLOOKUP env' inp = SOME 0w) /\
          (w = 0w ==> !w'. FLOOKUP env' inp = SOME w' ==> w' <> 0w)) /\
    (* ADD/SUB *)
    ((dinst.inst_opcode = ADD \/ dinst.inst_opcode = SUB) ==>
      !op1 op2. dinst.inst_operands = [op1; op2] /\
        (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
        ?w1 w2.
          eval_op_env op1 env' = SOME w1 /\
          eval_op_env op2 env' = SOME w2 /\
          FLOOKUP env' v = SOME
            (if dinst.inst_opcode = ADD
             then word_add w1 w2 else word_sub w1 w2)) /\
    (* LT/GT *)
    ((dinst.inst_opcode = LT \/ dinst.inst_opcode = GT) ==>
      !op1 op2. dinst.inst_operands = [op1; op2] /\
        (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
        ?w1 w2.
          eval_op_env op1 env' = SOME w1 /\
          eval_op_env op2 env' = SOME w2 /\
          FLOOKUP env' v = SOME (bool_to_word
            (if dinst.inst_opcode = LT
             then w2n w1 < w2n w2
             else w2n w1 > w2n w2)))
Proof
  rpt gen_tac \\ strip_tac
  \\ qpat_x_assum `dfg_prefix_sound _ _ _ _`
       (fn th => mp_tac (REWRITE_RULE [dfg_prefix_sound_def] th))
  \\ disch_then (qspecl_then [`v`, `dinst`, `k`] mp_tac)
  \\ (impl_tac >- (simp[] \\ metis_tac[FDOM_FLOOKUP]))
  \\ strip_tac
  \\ rpt conj_tac
  (* FDOM closure *)
  >- (rpt strip_tac \\ res_tac \\ metis_tac[FDOM_FLOOKUP])
  (* ISZERO *)
  >- (rpt strip_tac
      \\ `FLOOKUP env' inp = FLOOKUP env inp`
           by (first_x_assum match_mp_tac
               \\ gvs[dfg_tracked_opcode_def])
      \\ metis_tac[])
  (* ADD/SUB *)
  >- (rpt strip_tac \\ fs[]
      \\ MAP_EVERY qexists_tac [`w1`, `w2`]
      \\ gvs[dfg_tracked_opcode_def]
      \\ metis_tac[eval_op_env_transfer])
  (* LT/GT *)
  >- (rpt strip_tac \\ fs[]
      \\ MAP_EVERY qexists_tac [`w1`, `w2`]
      \\ gvs[dfg_tracked_opcode_def]
      \\ metis_tac[eval_op_env_transfer])
QED

(* Operand FLOOKUP preservation: executing a different instruction
   at position idx preserves FLOOKUP for operands of an earlier entry. *)
Theorem operand_flookup_preserved_dinst:
  !fn bb idx k v dinst u' fuel ctx s s'.
    wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) /\
    dfg_block_local fn /\
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    idx < LENGTH bb.bb_instructions /\
    k < LENGTH bb.bb_instructions /\ k < idx /\
    EL k bb.bb_instructions = dinst /\
    dfg_tracked_opcode dinst.inst_opcode /\
    MEM (Var u') dinst.inst_operands /\
    MEM v dinst.inst_outputs /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' ==>
    FLOOKUP s'.vs_vars u' = FLOOKUP s.vs_vars u'
Proof
  rpt strip_tac >>
  Cases_on `dfg_get_def (dfg_build_function fn) u'`
  >- (
    `~MEM u' (EL idx bb.bb_instructions).inst_outputs` by (
      CCONTR_TAC >> gvs[] >>
      `MEM (EL idx bb.bb_instructions) (fn_insts fn)` by
        metis_tac[fn_insts_has_block_el] >>
      imp_res_tac dfg_build_function_defs_complete >> gvs[]) >>
    `lookup_var u' s' = lookup_var u' s` by
      metis_tac[step_preserves_non_output_vars] >>
    fs[lookup_var_def])
  >- (
    rename1 `SOME inst_u` >>
    `MEM dinst bb.bb_instructions` by metis_tac[MEM_EL] >>
    mp_tac dfg_block_local_elim >>
    disch_then (qspecl_then [`fn`,`v`,`dinst`,`u'`,`inst_u`,`bb`] mp_tac) >>
    (impl_tac >- fs[]) >>
    strip_tac >>
    `?ku. ku < LENGTH bb.bb_instructions /\ EL ku bb.bb_instructions = inst_u` by
      metis_tac[MEM_EL] >>
    `ku < k` by metis_tac[] >>
    `ku <> idx` by simp[] >>
    `MEM u' inst_u.inst_outputs` by metis_tac[dfg_build_function_correct] >>
    metis_tac[step_preserves_other_output])
QED

(* For a tracked instruction, the output variable cannot be an operand variable. *)
Theorem dfg_output_neq_operand_var:
  !fn v inst u bb idx.
    dfg_block_local fn /\
    dfg_get_def (dfg_build_function fn) v = SOME inst /\
    MEM (Var u) inst.inst_operands /\
    dfg_tracked_opcode inst.inst_opcode /\
    MEM bb fn.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = inst ==> v <> u
Proof
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  mp_tac dfg_block_local_elim >>
  disch_then (qspecl_then [`fn`,`u`,`bb.bb_instructions❲idx❳`,
    `u`,`bb.bb_instructions❲idx❳`,`bb`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[MEM_EL]) >>
  strip_tac >> `idx < idx` by metis_tac[] >> DECIDE_TAC
QED

(* For tracked opcodes, if step_inst_base succeeds with single output,
   then every operand evaluates in the pre-state. *)
Theorem tracked_step_operand_evaluable:
  !inst s s' v op.
    dfg_tracked_opcode inst.inst_opcode /\
    inst.inst_outputs = [v] /\
    step_inst_base inst s = OK s' /\
    MEM op inst.inst_operands ==>
    ?w. eval_operand op s = SOME w
Proof
  rpt strip_tac >>
  qpat_x_assum `dfg_tracked_opcode _`
    (strip_assume_tac o REWRITE_RULE[dfg_tracked_opcode_def]) >> gvs[] >>
  gvs[step_inst_base_def]
  >- (gvs[AllCaseEqs()] >> Cases_on `inst.inst_operands` >> gvs[] >>
      Cases_on `t` >> gvs[])
  >- (imp_res_tac exec_pure1_flookup >> gvs[])
  >> (imp_res_tac exec_pure2_flookup >> gvs[])
QED

(* Derive step_inst_base from tracked opcode + step_inst *)
Theorem tracked_step_inst_base:
  !inst fuel ctx s s'.
    dfg_tracked_opcode inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    step_inst_base inst s = OK s'
Proof
  rpt strip_tac >>
  qpat_x_assum `dfg_tracked_opcode _`
    (strip_assume_tac o REWRITE_RULE[dfg_tracked_opcode_def]) >>
  gvs[step_inst_non_invoke]
QED

(* Derive FLOOKUP preservation for non-output vars from tracked step *)
Theorem tracked_step_flookup:
  !inst v fuel ctx s s'.
    dfg_tracked_opcode inst.inst_opcode /\
    inst.inst_outputs = [v] /\
    step_inst fuel ctx inst s = OK s' ==>
    !u. u <> v ==> FLOOKUP s'.vs_vars u = FLOOKUP s.vs_vars u
Proof
  rpt strip_tac >>
  `is_effect_free_op inst.inst_opcode` by
    (qpat_x_assum `dfg_tracked_opcode _`
       (strip_assume_tac o REWRITE_RULE[dfg_tracked_opcode_def]) >>
     gvs[is_effect_free_op_def]) >>
  `state_equiv (set inst.inst_outputs) s s'` by
    metis_tac[step_effect_free_state_equiv] >>
  gvs[state_equiv_def, execution_equiv_def] >>
  `lookup_var u s = lookup_var u s'` by
    (first_x_assum match_mp_tac >> simp[]) >>
  fs[lookup_var_def]
QED

(* Case 2 helper: tracked opcode at k = idx *)
Triviality dfg_prefix_sound_step_tracked[local]:
  !fn bb idx v fuel ctx s s'.
    dfg_prefix_sound (dfg_build_function fn) bb s.vs_vars idx /\
    fn_inst_wf fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) /\
    dfg_block_local fn /\
    idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' /\
    v IN FDOM s'.vs_vars /\
    dfg_get_def (dfg_build_function fn) v = SOME (EL idx bb.bb_instructions) /\
    dfg_tracked_opcode (EL idx bb.bb_instructions).inst_opcode ==>
    (* FDOM closure *)
    (!u. MEM (Var u) (EL idx bb.bb_instructions).inst_operands /\
         dfg_tracked_opcode (EL idx bb.bb_instructions).inst_opcode ==>
         u IN FDOM s'.vs_vars) /\
    (* ISZERO *)
    ((EL idx bb.bb_instructions).inst_opcode = ISZERO ==>
      !inp. (EL idx bb.bb_instructions).inst_operands = [Var inp] ==>
        !w. FLOOKUP s'.vs_vars v = SOME w ==>
          (w <> 0w ==> FLOOKUP s'.vs_vars inp = SOME 0w) /\
          (w = 0w ==> !w'. FLOOKUP s'.vs_vars inp = SOME w' ==> w' <> 0w)) /\
    (* ADD/SUB *)
    ((EL idx bb.bb_instructions).inst_opcode = ADD \/
     (EL idx bb.bb_instructions).inst_opcode = SUB ==>
      !op1 op2. (EL idx bb.bb_instructions).inst_operands = [op1; op2] /\
        (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
        ?w1 w2.
          eval_op_env op1 s'.vs_vars = SOME w1 /\
          eval_op_env op2 s'.vs_vars = SOME w2 /\
          FLOOKUP s'.vs_vars v = SOME
            (if (EL idx bb.bb_instructions).inst_opcode = ADD
             then word_add w1 w2 else word_sub w1 w2)) /\
    (* LT/GT *)
    ((EL idx bb.bb_instructions).inst_opcode = LT \/
     (EL idx bb.bb_instructions).inst_opcode = GT ==>
      !op1 op2. (EL idx bb.bb_instructions).inst_operands = [op1; op2] /\
        (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
        ?w1 w2.
          eval_op_env op1 s'.vs_vars = SOME w1 /\
          eval_op_env op2 s'.vs_vars = SOME w2 /\
          FLOOKUP s'.vs_vars v = SOME (bool_to_word
            (if (EL idx bb.bb_instructions).inst_opcode = LT
             then w2n w1 < w2n w2
             else w2n w1 > w2n w2)))
Proof
  rpt gen_tac \\ strip_tac
  \\ imp_res_tac tracked_step_inst_base
  \\ imp_res_tac tracked_step_flookup
  \\ mp_tac dfg_tracked_inst_outputs
  \\ disch_then (qspecl_then [`fn`, `v`, `EL idx bb.bb_instructions`] mp_tac)
  \\ simp[]
  \\ strip_tac
  \\ conj_tac
  >- (
    rpt strip_tac
    >> `u <> v` by metis_tac[dfg_output_neq_operand_var, MEM_EL]
    >> `FLOOKUP s'.vs_vars u = FLOOKUP s.vs_vars u` by metis_tac[]
    >> `?w. eval_operand (Var u) s = SOME w` by
         metis_tac[tracked_step_operand_evaluable, MEM]
    >> gvs[eval_operand_def, lookup_var_def]
    >> metis_tac[FDOM_FLOOKUP]
  )
  >> qpat_x_assum `dfg_tracked_opcode _`
       (strip_assume_tac o REWRITE_RULE[dfg_tracked_opcode_def])
  >> gvs[]
  >> `dfg_tracked_opcode (EL idx bb.bb_instructions).inst_opcode` by
       simp[dfg_tracked_opcode_def]
  >> `!u. MEM (Var u) (EL idx bb.bb_instructions).inst_operands ==> u <> v` by
       (rpt strip_tac >>
        `MEM (Var u) (EL idx bb.bb_instructions).inst_operands` by simp[] >>
        `v <> u` by metis_tac[dfg_output_neq_operand_var, MEM_EL] >>
        metis_tac[])
  (* ISZERO *)
  >> TRY (
    rpt strip_tac
    >> `inp <> v` by (first_x_assum match_mp_tac >> gvs[])
    >> imp_res_tac step_inst_base_iszero
    >> gvs[update_var_def, FLOOKUP_UPDATE, eval_operand_def, lookup_var_def]
    >> CCONTR_TAC >> gvs[bool_to_word_def]
    >> NO_TAC)
  (* ADD/SUB/LT/GT *)
  >> rpt strip_tac
  >> (drule_all step_inst_base_add ORELSE drule_all step_inst_base_sub
      ORELSE drule_all step_inst_base_lt ORELSE drule_all step_inst_base_gt)
  >> strip_tac
  >> MAP_EVERY qexists_tac [`w1`, `w2`]
  >> gvs[update_var_def, FLOOKUP_UPDATE]
  >> (Cases_on `op1` >> Cases_on `op2`
      >> gvs[eval_op_env_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE])
QED

(* dfg_prefix_sound is preserved by executing one non-terminator instruction. *)
Theorem dfg_prefix_sound_step:
  !fn bb idx fuel ctx s s'.
    dfg_prefix_sound (dfg_build_function fn) bb s.vs_vars idx /\
    fn_inst_wf fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    dfg_block_local fn /\
    idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' ==>
    dfg_prefix_sound (dfg_build_function fn) bb s'.vs_vars (SUC idx)
Proof
  rpt strip_tac
  >> REWRITE_TAC [dfg_prefix_sound_def] >> rpt gen_tac >> strip_tac
  >> `k < idx \/ k = idx` by DECIDE_TAC
  (* Case 1: k < idx — transfer from prior env *)
  >- (
    `k < LENGTH bb.bb_instructions` by DECIDE_TAC >>
    `k <> idx` by DECIDE_TAC >>
    imp_res_tac dfg_build_function_correct >>
    `FLOOKUP s'.vs_vars v = FLOOKUP s.vs_vars v` by
      metis_tac[step_preserves_other_output] >>
    mp_tac dfg_prefix_sound_entry_transfer >>
    disch_then (qspecl_then [`dfg_build_function fn`, `bb`,
      `s.vs_vars`, `s'.vs_vars`, `v`, `dinst`, `k`, `idx`] mp_tac) >>
    (impl_tac THEN1 (
      simp[] >> rpt strip_tac >>
      metis_tac[operand_flookup_preserved_dinst])) >>
    simp[]
  )
  (* Case 2: k = idx *)
  >- (
    qpat_x_assum `k = idx` SUBST_ALL_TAC
    >> qpat_x_assum `_ = dinst` (SUBST_ALL_TAC o SYM)
    >> Cases_on `dfg_tracked_opcode (EL idx bb.bb_instructions).inst_opcode`
    >- (drule_all_then ACCEPT_TAC dfg_prefix_sound_step_tracked)
    >> gvs[dfg_tracked_opcode_def]
  )
QED

