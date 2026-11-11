(*
 * Overflow Check Elimination — Helpers
 *
 * Integer facts for the no-overflow argument, and the per-lattice-value
 * form overflow_elim_inst_v of the transform with its equivalence to
 * overflow_elim_function.
 *)

Theory overflowElimHelpers
Ancestors
  overflowElimDefs rangePassProofs
  analysisSimDefs analysisSimProps
  passSimulationDefs passSimulationProps
  passSharedDefs passSharedProps
  stateEquiv stateEquivProps
  venomExecSemantics venomState venomInst venomWf
  venomInstProps venomExecProps
  execEquivParamProps
  rangeAnalysisDefs rangeEvalDefs valueRangeDefs
  rangeAnalysisProofs
  dfAnalyzeWidenDefs
  dfgDefs dfgAnalysisProps dfgSoundDefs dfgSoundProofs
  worklistDefs
  list finite_map
  passTransform
Libs
  BasicProvers

(* ================================================================
   Section 2: The core arithmetic soundness argument
   ================================================================ *)

(* Helper: range_nonneg + in_range ==> non-negative word value *)
Theorem range_nonneg_in_range_nonneg_w2i:
  !r w. range_nonneg r /\ in_range r w ==> 0 <= w2i w /\ w2i w <= vr_hi r
Proof
  Cases_on `r` >> simp[range_nonneg_def, in_range_def, vr_hi_def] >>
  rpt strip_tac >> Omega.OMEGA_TAC
QED

(* Helper: non-negative w2i implies w2n = Num(w2i) *)
Theorem nonneg_w2i_eq_w2n:
  !(w: 256 word). 0 <= w2i w ==> w2n w = Num (w2i w)
Proof
  rpt strip_tac >>
  Cases_on `word_msb w`
  >- (fs[integer_wordTheory.w2i_def] >>
      `w2n w < dimword (:256)` by simp[wordsTheory.w2n_lt] >>
      Omega.OMEGA_TAC)
  >- simp[integer_wordTheory.w2i_def]
QED

Theorem Num_UINT256_MAX_int:
  Num UINT256_MAX_int + 1 = dimword (:256)
Proof
  simp[UINT256_MAX_def, integer_wordTheory.UINT_MAX_def,
       wordsTheory.UINT_MAX_def, wordsTheory.dimword_def] >>
  simp[integerTheory.NUM_OF_INT, integerTheory.INT_SUB] >>
  `0 < 2n ** dimindex (:256)` by simp[] >> simp[]
QED

(* The add overflow argument:
   If x,y have nonneg ranges with hi(x)+hi(y) <= UINT256_MAX,
   then w2n(x+y) >= w2n(x), so lt(x+y, x) = 0w *)
Theorem add_no_overflow_lt_zero:
  !wx wy xr yr.
    range_nonneg xr /\ range_nonneg yr /\
    in_range xr wx /\ in_range yr wy /\
    vr_hi xr + vr_hi yr <= UINT256_MAX_int ==>
    bool_to_word (w2n (word_add wx wy) < w2n wx) = 0w
Proof
  rpt strip_tac >>
  imp_res_tac range_nonneg_in_range_nonneg_w2i >>
  `w2n wx = Num (w2i wx)` by metis_tac[nonneg_w2i_eq_w2n] >>
  `w2n wy = Num (w2i wy)` by metis_tac[nonneg_w2i_eq_w2n] >>
  `w2n wx + w2n wy < dimword (:256)` by
    (`0 <= vr_hi xr /\ 0 <= vr_hi yr` by
       (Cases_on `xr` >> Cases_on `yr` >>
        fs[range_nonneg_def, vr_hi_def] >> Omega.OMEGA_TAC) >>
     `Num (w2i wx) + Num (w2i wy) <= Num (vr_hi xr + vr_hi yr)` by
       Omega.OMEGA_TAC >>
     `Num (vr_hi xr + vr_hi yr) <= Num UINT256_MAX_int` by
       Omega.OMEGA_TAC >>
     `Num UINT256_MAX_int < dimword (:256)` by
       (mp_tac Num_UINT256_MAX_int >> DECIDE_TAC) >>
     DECIDE_TAC) >>
  imp_res_tac wordsTheory.w2n_add_2 >>
  simp[bool_to_word_def]
QED

(* The sub underflow argument:
   If x,y have nonneg ranges with lo(x) >= hi(y),
   then w2n(x-y) <= w2n(x), so gt(x-y, x) = 0w *)
Theorem sub_no_underflow_gt_zero:
  !wx wy xr yr.
    range_nonneg xr /\ range_nonneg yr /\
    in_range xr wx /\ in_range yr wy /\
    vr_lo xr >= vr_hi yr ==>
    bool_to_word (w2n (word_sub wx wy) > w2n wx) = 0w
Proof
  rpt strip_tac >>
  imp_res_tac range_nonneg_in_range_nonneg_w2i >>
  `0 <= w2i wx /\ 0 <= w2i wy` by simp[] >>
  `w2n wx = Num (w2i wx)` by metis_tac[nonneg_w2i_eq_w2n] >>
  `w2n wy = Num (w2i wy)` by metis_tac[nonneg_w2i_eq_w2n] >>
  `w2n wy <= w2n wx` by
    (Cases_on `xr` >> Cases_on `yr` >>
     fs[range_nonneg_def, vr_lo_def, vr_hi_def, in_range_def] >>
     Omega.OMEGA_TAC) >>
  `wy <=+ wx` by simp[wordsTheory.WORD_LS] >>
  imp_res_tac wordsTheory.word_sub_w2n >>
  simp[bool_to_word_def]
QED

(* ================================================================
   Section 3: Transform equivalence
   ================================================================

   Show overflow_elim_function = clear_nops(analysis_function_transform_widen ...)
   by connecting overflow_elim_block_insts to MAPi. *)

(* Helper: overflow_elim_block_insts from offset k = MAPi from k *)
Theorem overflow_elim_block_insts_eq_mapi:
  !insts dfg ra lbl k.
    overflow_elim_block_insts dfg ra lbl k insts =
    MAPi (\i inst. overflow_elim_inst dfg ra lbl (k + i) inst) insts
Proof
  Induct >> simp[overflow_elim_block_insts_def, indexedListsTheory.MAPi_def] >>
  rpt strip_tac >>
  simp[combinTheory.o_DEF] >>
  first_x_assum (qspecl_then [`dfg`, `ra`, `lbl`, `k + 1`] mp_tac) >>
  strip_tac >>
  irule listTheory.LIST_EQ >> simp[indexedListsTheory.EL_MAPi] >>
  rpt strip_tac >>
  `k + 1 + x = k + SUC x` by DECIDE_TAC >>
  `k + (x + 1) = k + SUC x` by DECIDE_TAC >>
  simp[]
QED




(* ================================================================
   Section 4: Per-instruction simulation
   ================================================================ *)

(* The sound predicate for overflow_elim includes range + dfg_ext *)
(* overflow_elim_inst needs (ra, lbl, idx) for range_get_range, but the
   framework only provides v = df_widen_at NONE ra lbl idx. Since
   range_get_range ra lbl idx op = operand_range (range_unwrap v) op
   (see range_get_range_eq_v, overflow_elim_inst_eq_v, overflow_elim_inst_via_widen),
   the transform can be expressed via v alone. *)

(* If range_nonneg holds for operand_range, the operand is not a Label.
   Label -> VR_Top, range_nonneg VR_Top = F. *)
Theorem range_nonneg_not_label:
  !rs op. range_nonneg (operand_range rs op) ==> (!lbl. op <> Label lbl)
Proof
  Cases_on `op` >> simp[operand_range_def, range_nonneg_def]
QED

(* _v variants: take range state directly instead of (ra, lbl, idx) *)

Definition try_elim_add_overflow_v_def:
  try_elim_add_overflow_v dfg rs (lt_inst : instruction) =
    case lt_inst.inst_operands of
      [res_op; x_op] =>
        (case get_producer dfg res_op of
           SOME add_inst =>
             if add_inst.inst_opcode <> ADD then F
             else (case add_inst.inst_operands of
               [add_op0; add_op1] =>
                 let y_op =
                   if add_op0 = x_op then SOME add_op1
                   else if add_op1 = x_op then SOME add_op0
                   else NONE
                 in
                 (case y_op of
                    NONE => F
                  | SOME y =>
                      let x_range = operand_range rs x_op in
                      let y_range = operand_range rs y in
                      range_nonneg x_range /\ range_nonneg y_range /\
                      vr_hi x_range + vr_hi y_range <= UINT256_MAX_int)
             | _ => F)
         | NONE => F)
    | _ => F
End

Definition try_elim_sub_underflow_v_def:
  try_elim_sub_underflow_v dfg rs (gt_inst : instruction) =
    case gt_inst.inst_operands of
      [res_op; x_op] =>
        (case get_producer dfg res_op of
           SOME sub_inst =>
             if sub_inst.inst_opcode <> SUB then F
             else (case sub_inst.inst_operands of
               [sub_x; sub_y] =>
                 if sub_x <> x_op then F
                 else
                   let x_range = operand_range rs x_op in
                   let y_range = operand_range rs sub_y in
                   range_nonneg x_range /\ range_nonneg y_range /\
                   vr_lo x_range >= vr_hi y_range
             | _ => F)
         | NONE => F)
    | _ => F
End

Definition try_elim_overflow_check_v_def:
  try_elim_overflow_check_v dfg rs (assert_inst : instruction) =
    case assert_inst.inst_operands of
      [assert_op] =>
        (case get_producer dfg assert_op of
           SOME iszero_inst =>
             if iszero_inst.inst_opcode <> ISZERO then F
             else (case iszero_inst.inst_operands of
               [cmp_op] =>
                 (case get_producer dfg cmp_op of
                    SOME cmp_inst =>
                      if cmp_inst.inst_opcode = LT then
                        try_elim_add_overflow_v dfg rs cmp_inst
                      else if cmp_inst.inst_opcode = GT then
                        try_elim_sub_underflow_v dfg rs cmp_inst
                      else F
                  | NONE => F)
             | _ => F)
         | NONE => F)
    | _ => F
End

Definition overflow_elim_inst_v_def:
  overflow_elim_inst_v dfg rs inst =
    if inst.inst_opcode <> ASSERT then inst
    else if try_elim_overflow_check_v dfg rs inst
    then mk_nop_inst inst
    else inst
End

(* Equivalence: the _v versions compute the same as the originals *)
Theorem try_elim_add_overflow_eq_v:
  !dfg ra lbl idx lt_inst.
    try_elim_add_overflow dfg ra lbl idx lt_inst =
    try_elim_add_overflow_v dfg (range_at_inst ra lbl idx) lt_inst
Proof
  rpt gen_tac >>
  simp[try_elim_add_overflow_def, try_elim_add_overflow_v_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[rangeAnalysisProofsTheory.range_get_range_eq_v]
QED

Theorem try_elim_sub_underflow_eq_v:
  !dfg ra lbl idx gt_inst.
    try_elim_sub_underflow dfg ra lbl idx gt_inst =
    try_elim_sub_underflow_v dfg (range_at_inst ra lbl idx) gt_inst
Proof
  rpt gen_tac >>
  simp[try_elim_sub_underflow_def, try_elim_sub_underflow_v_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[rangeAnalysisProofsTheory.range_get_range_eq_v]
QED

Theorem try_elim_overflow_check_eq_v:
  !dfg ra lbl idx inst.
    try_elim_overflow_check dfg ra lbl idx inst =
    try_elim_overflow_check_v dfg (range_at_inst ra lbl idx) inst
Proof
  rpt gen_tac >>
  simp[try_elim_overflow_check_def, try_elim_overflow_check_v_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[try_elim_add_overflow_eq_v, try_elim_sub_underflow_eq_v]
QED

Theorem overflow_elim_inst_eq_v:
  !dfg ra lbl idx inst.
    overflow_elim_inst dfg ra lbl idx inst =
    overflow_elim_inst_v dfg (range_at_inst ra lbl idx) inst
Proof
  simp[overflow_elim_inst_def, overflow_elim_inst_v_def,
       try_elim_overflow_check_eq_v]
QED

(* The _v variant takes the abstract domain value directly *)

(* Connect to framework: the transform via df_widen_at *)
Theorem overflow_elim_inst_via_widen:
  !dfg ra lbl idx inst.
    overflow_elim_inst dfg ra lbl idx inst =
    overflow_elim_inst_v dfg (range_unwrap (df_widen_at NONE ra lbl idx)) inst
Proof
  simp[overflow_elim_inst_eq_v, range_at_inst_def]
QED

(* Transform equivalence: overflow_elim_function =
   clear_nops(analysis_function_transform_widen NONE ra
     (\v inst. [overflow_elim_inst_v dfg (range_unwrap v) inst]) fn) *)
Theorem overflow_elim_function_eq:
  !fn.
    let dfg = dfg_build_function fn in
    let ra = range_analyze fn in
    overflow_elim_function fn =
    clear_nops_function
      (analysis_function_transform_widen NONE ra
        (\v inst. [overflow_elim_inst_v dfg (range_unwrap v) inst]) fn)
Proof
  simp[overflow_elim_function_def, LET_THM,
       analysis_function_transform_widen_def,
       function_map_transform_def,
       analysis_block_transform_widen_def] >>
  rpt gen_tac >>
  AP_TERM_TAC >> (* clear_nops_function *)
  simp[ir_function_component_equality] >>
  irule listTheory.LIST_EQ >>
  simp[listTheory.EL_MAP, listTheory.LENGTH_MAP] >>
  rpt strip_tac >>
  simp[overflow_elim_block_def, basic_block_component_equality] >>
  simp[overflow_elim_block_insts_eq_mapi] >>
  (* MAPi (\i inst. overflow_elim_inst dfg ra (EL x fn.fn_blocks).bb_label (0+i) inst) =
     FLAT (MAPi (\i inst. [overflow_elim_inst_v dfg (range_unwrap (df_widen_at NONE ra lbl i)) inst]) ...) *)
  simp[flat_mapi_singleton, analysis_block_transform_widen_def,
       analysis_block_transform_def, basic_block_component_equality] >>
  irule listTheory.LIST_EQ >>
  simp[indexedListsTheory.EL_MAPi] >>
  rpt strip_tac >>
  simp[overflow_elim_inst_via_widen]
QED

(* ================================================================
   Range-DFG chain contradiction helpers
   ================================================================

   When try_elim_overflow_check_v succeeds, the DFG chain
   ASSERT → ISZERO → LT/GT → ADD/SUB constrains variable values.
   Combined with range analysis, the ASSERT operand cannot be 0w. *)

