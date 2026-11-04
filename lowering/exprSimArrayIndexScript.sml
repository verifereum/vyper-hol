(*
 * Array subscripts: the bounds check and the element pointer (#636,
 * Places row 1)
 *
 * compile_array_subscript reads the array's length (a load at the base, by
 * its loader compile_ptr_load, for
 * a dynamic array, the static count otherwise), asserts the index is in
 * range (not negative, for a signed index, and below the length), and
 * hands out the element's pointer: the base, past the length word for a
 * dynamic array, plus the index times the element size.  These are the
 * fragment lemmas the array case of compile_subscript_sim (exprSimPlaces)
 * needs: the code runs to the pointer for an index in range, and aborts
 * for one out of range, where the source raises a RuntimeError
 * (evaluate_subscripts array_index, or extend_storage_place's "array ...
 * oob" check), which expr_exit relates to any Abort.
 *
 * TOP-LEVEL:
 *   array_bounds_valid, array_bounds_valid_run — the range test before
 *                                the ASSERT, and its code
 *   array_bounds_check, array_elem_ptr — the two halves of
 *                                compile_array_subscript after the length
 *   compile_array_subscript_split — compile_array_subscript is the length,
 *                                the check and the pointer in turn
 *   array_len_ok               — the length operand's code runs to the
 *                                length: the loader's for a dynamic array
 *   array_len_ok_MLOAD, array_len_ok_SLOAD, array_len_ok_TLOAD,
 *   array_len_ok_CALLDATALOAD — compile_ptr_load at memory, storage,
 *                                transient and calldata
 *   array_len_ok_static
 *   idx_in_range               — the index is not negative (for a signed
 *                                index) and below the length
 *   array_bounds_check_ok, array_bounds_check_oob — the check passes an
 *                                index in range and aborts otherwise
 *   array_elem_ptr_run         — the pointer's code
 *   compile_array_subscript_ok, compile_array_subscript_oob — the whole
 *                                subscript, by the index's range
 *   straight_fresh_array_check_ptr — the check and the pointer write only
 *                                fresh variables
 *
 * The proofs chain the emitted instructions with emitTacticsLib's tactics.
 *
 * Helpers: comp_bind_FST_SND, bool_to_word_eq_0,
 *   word_or_bool_to_word, current_insts_emitted, array_bounds_valid_extends,
 *   array_bounds_check_extends, array_elem_ptr_extends,
 *   compile_array_subscript_extends, compile_array_subscript_run
 *)

Theory exprSimArrayIndex
Ancestors
  arithmeticProps exprLoweringProps emitHelperProps freshWrites exprSimOps
  emitHelper fragExec
  exprLowering compileEnv venomExecSemantics venomState venomInst
Libs
  emitTacticsLib

(* ===== The lowering, split ===== *)

(* The check's operand: 1 for an index in range, 0 otherwise. *)
Definition array_bounds_valid_def:
  array_bounds_valid idx_op len_op is_signed_idx =
    comp_bind (if is_signed_idx then emit_op SLT [idx_op; Lit 0w]
               else comp_return (Lit 0w)) (\is_neg.
    comp_bind (emit_op LT [idx_op; len_op]) (\is_oob.
    comp_bind (emit_op ISZERO [is_oob]) (\not_oob.
    comp_bind (emit_op OR [is_neg; not_oob]) (\invalid.
    emit_op ISZERO [invalid]))))
End

Definition array_bounds_check_def:
  array_bounds_check idx_op len_op is_signed_idx =
    comp_bind (array_bounds_valid idx_op len_op is_signed_idx) (\valid.
    emit_void ASSERT [valid])
End

Definition array_elem_ptr_def:
  array_elem_ptr base_op idx_op is_dynamic word_scale elem_size =
    comp_bind (if is_dynamic then emit_op ADD [base_op; Lit (n2w word_scale)]
               else comp_return base_op) (\data_ptr.
    comp_bind (emit_op MUL [idx_op; Lit (n2w elem_size)]) (\offset.
    emit_op ADD [data_ptr; offset]))
End

Theorem comp_bind_FST_SND[local]:
  !m f cs. comp_bind m f cs = f (FST (m cs)) (SND (m cs))
Proof
  simp[comp_bind_def, pairTheory.UNCURRY, LET_THM] >>
  rpt gen_tac >> Cases_on `m cs` >> simp[]
QED

Theorem compile_array_subscript_split:
  !base_op idx_op dyn cnt ws esz sgn loader.
    compile_array_subscript base_op idx_op dyn cnt ws esz sgn loader =
    comp_bind (if dyn then loader base_op
               else comp_return (Lit (n2w cnt))) (\len_op.
    comp_ignore_bind (array_bounds_check idx_op len_op sgn)
      (array_elem_ptr base_op idx_op dyn ws esz))
Proof
  simp[FUN_EQ_THM, compile_array_subscript_def, array_bounds_check_def,
       array_bounds_valid_def, array_elem_ptr_def, comp_ignore_bind_def,
       comp_bind_FST_SND, LET_THM]
QED

(* ===== Word facts ===== *)

Theorem bool_to_word_eq_0[local]:
  !b. (bool_to_word b = 0w) <=> ~b
Proof
  Cases >> simp[bool_to_word_def]
QED

Theorem word_or_bool_to_word[local]:
  !a b. word_or (bool_to_word a) (bool_to_word b) = bool_to_word (a \/ b)
Proof
  Cases >> Cases >> simp[bool_to_word_def, wordsTheory.WORD_OR_CLAUSES]
QED

(* ===== The length ===== *)

(* The length operand's code, from st, only appends instructions and runs
   to the length len: the loader's load at the base for a dynamic array,
   the static count otherwise. *)
Definition array_len_ok_def:
  array_len_ok dyn cnt loader base_op ss len <=>
    if dyn then
      !st lop st'.
        loader base_op st = (lop, st') /\ fresh_vars_wrt st ss ==>
        st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
        ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
              eval_operand lop ss' = SOME len /\
              same_blocks st st' /\ fresh_vars_wrt st' ss' /\
              (!op w. eval_operand op ss = SOME w ==>
                      eval_operand op ss' = SOME w)
    else len = n2w cnt
End

Theorem array_len_ok_static:
  !cnt loader base_op ss. array_len_ok F cnt loader base_op ss (n2w cnt)
Proof
  simp[array_len_ok_def]
QED

Theorem array_len_ok_MLOAD:
  !c imm cnt base_op ss b.
    eval_operand base_op ss = SOME b ==>
    array_len_ok T cnt (compile_ptr_load c imm LocMemory) base_op ss (mload (w2n b) ss)
Proof
  rw[array_len_ok_def, contextTheory.compile_ptr_load_def] >>
  imp_res_tac emit_op_extends >> drule_all emit_op_MLOAD_correct >>
  strip_tac >> metis_tac[]
QED

Theorem array_len_ok_SLOAD:
  !c imm cnt base_op ss b.
    eval_operand base_op ss = SOME b ==>
    array_len_ok T cnt (compile_ptr_load c imm LocStorage) base_op ss (sload b ss)
Proof
  rw[array_len_ok_def, contextTheory.compile_ptr_load_def] >>
  imp_res_tac emit_op_extends >> drule_all emit_op_SLOAD_correct >>
  strip_tac >> metis_tac[]
QED

Theorem array_len_ok_TLOAD:
  !c imm cnt base_op ss b.
    eval_operand base_op ss = SOME b ==>
    array_len_ok T cnt (compile_ptr_load c imm LocTransient) base_op ss (tload b ss)
Proof
  rw[array_len_ok_def, contextTheory.compile_ptr_load_def] >>
  imp_res_tac emit_op_extends >>
  qspecl_then [`TLOAD`, `tload`] mp_tac emit_op_read1_correct >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  simp[step_inst_base_def, exec_read1_def] >> strip_tac >>
  first_x_assum (qspecl_then [`b`, `ss`] mp_tac) >> simp[] >>
  strip_tac >> metis_tac[]
QED

Theorem array_len_ok_CALLDATALOAD:
  !c imm cnt base_op ss b.
    eval_operand base_op ss = SOME b ==>
    array_len_ok T cnt (compile_ptr_load c imm LocCalldata) base_op ss
      (word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n b) ss.vs_call_ctx.cc_calldata ++
                   REPLICATE 32 0w)))
Proof
  rw[array_len_ok_def, contextTheory.compile_ptr_load_def] >>
  imp_res_tac emit_op_extends >> drule_all emit_op_CALLDATALOAD_correct >>
  simp[] >> strip_tac >> metis_tac[]
QED

(* ===== The bounds check ===== *)

(* The index i is in range for the length len: not negative, for a signed
   index, and below the length. *)
Definition idx_in_range_def:
  idx_in_range sgn (i:bytes32) (len:bytes32) <=>
    ~(sgn /\ word_lt i 0w) /\ w2n i < w2n len
End

(* The check's operand before the ASSERT. *)
Theorem array_bounds_valid_run:
  !idx_op len_op sgn st st' ss i len valid.
    array_bounds_valid idx_op len_op sgn st = (valid, st') /\
    eval_operand idx_op ss = SOME i /\ eval_operand len_op ss = SOME len /\
    fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
          st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
          same_blocks st st' /\ fresh_vars_wrt st' ss' /\
          (!op w. eval_operand op ss = SOME w ==>
                  eval_operand op ss' = SOME w) /\
          eval_operand valid ss' =
            SOME (bool_to_word (idx_in_range sgn i len))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
  simp[array_bounds_valid_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  Cases_on `sgn` >> gvs[comp_return_def]
  >- (drule_all (elim_lit 2 emit_op_SLT_correct) >> strip_tac >>
      imp_res_tac emit_op_extends >>
      chain_step emit_op_LT_correct >>
      chain_step emit_op_ISZERO_correct >>
      chain_step emit_op_OR_correct >>
      chain_step emit_op_ISZERO_correct >>
      gvs[bool_to_word_eq_0, word_or_bool_to_word, wordsTheory.WORD_OR_CLAUSES,
          same_blocks_def, idx_in_range_def] >>
      metis_tac[]) >>
  drule_all emit_op_LT_correct >> strip_tac >>
  imp_res_tac emit_op_extends >>
  chain_step emit_op_ISZERO_correct >>
  chain_step (elim_lit 1 emit_op_OR_correct) >>
  chain_step emit_op_ISZERO_correct >>
  gvs[bool_to_word_eq_0, word_or_bool_to_word, wordsTheory.WORD_OR_CLAUSES,
      same_blocks_def, idx_in_range_def] >>
  metis_tac[]
QED

Theorem array_bounds_check_ok:
  !idx_op len_op sgn st st' ss i len.
    array_bounds_check idx_op len_op sgn st = ((), st') /\
    eval_operand idx_op ss = SOME i /\ eval_operand len_op ss = SOME len /\
    fresh_vars_wrt st ss /\ idx_in_range sgn i len ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
          st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
          same_blocks st st' /\ fresh_vars_wrt st' ss' /\
          (!op w. eval_operand op ss = SOME w ==>
                  eval_operand op ss' = SOME w)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `array_bounds_check _ _ _ _ = _` mp_tac >>
  simp[array_bounds_check_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule_all array_bounds_valid_run >> strip_tac >>
  gvs[bool_to_word_def] >>
  drule emit_void_ASSERT_ok_full >>
  disch_then (qspecl_then [`1w`, `ss'`] mp_tac) >> simp[] >> strip_tac >>
  gvs[] >> imp_res_tac emit_void_extends >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `ss'` >> gvs[] >> metis_tac[same_blocks_trans]
QED

Theorem current_insts_emitted[local]:
  !st st'.
    (?L. st'.cs_current_insts = st.cs_current_insts ++ L) ==>
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  rw[emitted_insts_def] >> simp[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem array_bounds_valid_extends[local]:
  !idx_op len_op sgn st valid st'.
    array_bounds_valid idx_op len_op sgn st = (valid, st') ==>
    ?L. st'.cs_current_insts = st.cs_current_insts ++ L
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
  simp[array_bounds_valid_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  Cases_on `sgn` >> gvs[comp_return_def] >>
  imp_res_tac emit_op_extends >> metis_tac[listTheory.APPEND_ASSOC]
QED

Theorem array_bounds_check_extends[local]:
  !idx_op len_op sgn st u st'.
    array_bounds_check idx_op len_op sgn st = (u, st') ==>
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  rpt gen_tac >> strip_tac >> irule current_insts_emitted >>
  qpat_x_assum `array_bounds_check _ _ _ _ = _` mp_tac >>
  simp[array_bounds_check_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule array_bounds_valid_extends >> strip_tac >>
  imp_res_tac emit_void_extends >> metis_tac[listTheory.APPEND_ASSOC]
QED

Theorem array_bounds_check_oob:
  !idx_op len_op sgn st st' ss i len.
    array_bounds_check idx_op len_op sgn st = ((), st') /\
    eval_operand idx_op ss = SOME i /\ eval_operand len_op ss = SOME len /\
    fresh_vars_wrt st ss /\ ~idx_in_range sgn i len ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `array_bounds_check _ _ _ _ = _` mp_tac >>
  simp[array_bounds_check_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule_all array_bounds_valid_run >> strip_tac >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac emit_void_extends >>
  drule_all run_inst_seq_chain >> strip_tac >> gvs[]
QED

(* ===== The element pointer ===== *)

Theorem array_elem_ptr_run:
  !base_op idx_op dyn ws esz st p st' ss b i.
    array_elem_ptr base_op idx_op dyn ws esz st = (p, st') /\
    eval_operand base_op ss = SOME b /\ eval_operand idx_op ss = SOME i /\
    fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
          st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
          same_blocks st st' /\ fresh_vars_wrt st' ss' /\
          (!op w. eval_operand op ss = SOME w ==>
                  eval_operand op ss' = SOME w) /\
          eval_operand p ss' =
            SOME ((if dyn then b + n2w ws else b) + i * n2w esz)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
  simp[array_elem_ptr_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  Cases_on `dyn` >> gvs[comp_return_def]
  >- (drule_all (elim_lit 2 emit_op_ADD_correct) >> strip_tac >>
      imp_res_tac emit_op_extends >>
      chain_step (elim_lit 2 emit_op_MUL_correct) >>
      chain_step emit_op_ADD_correct >>
      metis_tac[same_blocks_trans]) >>
  drule_all (elim_lit 2 emit_op_MUL_correct) >> strip_tac >>
  imp_res_tac emit_op_extends >>
  chain_step emit_op_ADD_correct >>
  metis_tac[same_blocks_trans]
QED

Theorem array_elem_ptr_extends[local]:
  !base_op idx_op dyn ws esz st p st'.
    array_elem_ptr base_op idx_op dyn ws esz st = (p, st') ==>
    ?L. st'.cs_current_insts = st.cs_current_insts ++ L
Proof
  rpt gen_tac >> simp[array_elem_ptr_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  Cases_on `dyn` >> gvs[comp_return_def] >>
  imp_res_tac emit_op_extends >> gvs[] >> metis_tac[listTheory.APPEND_ASSOC]
QED

(* ===== The whole subscript ===== *)

Theorem compile_array_subscript_extends[local]:
  !base_op idx_op dyn cnt ws esz sgn loader st p st' ss len.
    compile_array_subscript base_op idx_op dyn cnt ws esz sgn loader st =
      (p, st') /\
    fresh_vars_wrt st ss /\ array_len_ok dyn cnt loader base_op ss len ==>
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  rpt gen_tac >>
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> irule current_insts_emitted >>
  imp_res_tac array_bounds_check_extends >>
  imp_res_tac array_elem_ptr_extends >>
  Cases_on `dyn` >> gvs[comp_return_def, array_len_ok_def]
  >- (first_x_assum drule_all >> strip_tac >> gvs[] >>
      metis_tac[listTheory.APPEND_ASSOC]) >>
  metis_tac[listTheory.APPEND_ASSOC]
QED

Theorem compile_array_subscript_run[local]:
  !base_op idx_op dyn cnt ws esz sgn loader st p st' ss b i len.
    compile_array_subscript base_op idx_op dyn cnt ws esz sgn loader st =
      (p, st') /\
    eval_operand base_op ss = SOME b /\ eval_operand idx_op ss = SOME i /\
    fresh_vars_wrt st ss /\ array_len_ok dyn cnt loader base_op ss len /\
    idx_in_range sgn i len ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
          same_blocks st st' /\ fresh_vars_wrt st' ss' /\
          (!op w. eval_operand op ss = SOME w ==>
                  eval_operand op ss' = SOME w) /\
          eval_operand p ss' =
            SOME ((if dyn then b + n2w ws else b) + i * n2w esz)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> fs[oneTheory.one] >>
  Cases_on `dyn` >> gvs[comp_return_def, array_len_ok_def]
  >- (first_x_assum drule_all >> strip_tac >>
      imp_res_tac emit_op_extends >> forward_all_evals >>
      drule_all array_bounds_check_ok >> strip_tac >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
      forward_all_evals >>
      drule_all array_elem_ptr_run >> strip_tac >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
      metis_tac[same_blocks_trans]) >>
  `eval_operand (Lit (n2w cnt)) ss = SOME (n2w cnt)` by
    simp[eval_operand_lit] >>
  drule_all array_bounds_check_ok >> strip_tac >>
  forward_all_evals >>
  drule_all array_elem_ptr_run >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  metis_tac[same_blocks_trans]
QED

Theorem compile_array_subscript_ok:
  !base_op idx_op dyn cnt ws esz sgn loader st p st' ss b i len.
    compile_array_subscript base_op idx_op dyn cnt ws esz sgn loader st =
      (p, st') /\
    eval_operand base_op ss = SOME b /\ eval_operand idx_op ss = SOME i /\
    fresh_vars_wrt st ss /\ array_len_ok dyn cnt loader base_op ss len /\
    idx_in_range sgn i len ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
          st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
          same_blocks st st' /\ fresh_vars_wrt st' ss' /\
          (!op w. eval_operand op ss = SOME w ==>
                  eval_operand op ss' = SOME w) /\
          eval_operand p ss' =
            SOME ((if dyn then b + n2w ws else b) + i * n2w esz)
Proof
  rpt strip_tac >> drule_all compile_array_subscript_extends >> strip_tac >>
  drule_all compile_array_subscript_run >> simp[]
QED

(* The code after the length (the check and the pointer) only computes
   into fresh variables: frag_exec_straight_fresh applies to it, and the
   length's load is a fragment of its own. *)
Theorem straight_fresh_array_check_ptr:
  !idx_op len_op sgn base_op dyn ws esz.
    straight_fresh
      (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
         (array_elem_ptr base_op idx_op dyn ws esz))
Proof
  rw[array_bounds_check_def, array_bounds_valid_def, array_elem_ptr_def] >>
  rpt (FIRST [irule straight_fresh_bind >> conj_tac,
              irule straight_fresh_ignore_bind >> conj_tac,
              gen_tac >> BETA_TAC,
              irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
              irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
              MATCH_ACCEPT_TAC straight_fresh_return,
              IF_CASES_TAC])
QED

Theorem compile_array_subscript_oob:
  !base_op idx_op dyn cnt ws esz sgn loader st p st' ss b i len.
    compile_array_subscript base_op idx_op dyn cnt ws esz sgn loader st =
      (p, st') /\
    eval_operand base_op ss = SOME b /\ eval_operand idx_op ss = SOME i /\
    fresh_vars_wrt st ss /\ array_len_ok dyn cnt loader base_op ss len /\
    ~idx_in_range sgn i len ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> fs[oneTheory.one] >>
  drule array_elem_ptr_extends >> strip_tac >>
  reverse (Cases_on `dyn`) >> gvs[comp_return_def, array_len_ok_def]
  >- (`eval_operand (Lit (n2w cnt)) ss = SOME (n2w cnt)` by
        simp[eval_operand_lit] >>
      drule_all array_bounds_check_oob >> strip_tac >>
      qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts st mid) ss = _` >>
      imp_res_tac array_bounds_check_extends >>
      qspecl_then [`st`, `mid`, `st'`, `ss`] mp_tac abort_propagates >>
      simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  imp_res_tac emit_op_extends >> forward_all_evals >>
  drule_all array_bounds_check_oob >> strip_tac >>
  imp_res_tac array_bounds_check_extends >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts st mid) ss = Abort _ _` >>
  qspecl_then [`st`, `mid`, `st'`, `ss`] mp_tac abort_propagates >>
  simp[]
QED

(* The suffix after the length load, independently of the loader. *)
Theorem array_check_ptr_ok:
  !a j l sgn dyn ws esz sa p sb ss b i len.
    comp_ignore_bind (array_bounds_check j l sgn)
      (array_elem_ptr a j dyn ws esz) sa = (p,sb) /\
    eval_operand a ss = SOME b /\ eval_operand j ss = SOME i /\
    eval_operand l ss = SOME len /\ fresh_vars_wrt sa ss /\
    idx_in_range sgn i len ==>
    ?t. run_inst_seq (emitted_insts sa sb) ss = OK t /\
        eval_operand p t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `comp_ignore_bind _ _ _ = _` mp_tac >>
  simp[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[oneTheory.one] >>
  drule_all array_bounds_check_ok >> strip_tac >>
  forward_all_evals >>
  drule_all array_elem_ptr_run >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  rename1 `eval_operand p t = SOME _` >> qexists_tac `t` >> simp[]
QED

Theorem array_check_ptr_oob:
  !a j l sgn dyn ws esz sa p sb ss i len.
    comp_ignore_bind (array_bounds_check j l sgn)
      (array_elem_ptr a j dyn ws esz) sa = (p,sb) /\
    eval_operand j ss = SOME i /\ eval_operand l ss = SOME len /\
    fresh_vars_wrt sa ss /\ ~idx_in_range sgn i len ==>
    ?t. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort t
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `comp_ignore_bind _ _ _ = _` mp_tac >>
  simp[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[oneTheory.one] >>
  drule_all array_bounds_check_oob >> strip_tac >>
  drule array_elem_ptr_extends >> strip_tac >>
  drule array_bounds_check_extends >> strip_tac >>
  qmatch_asmsub_rename_tac `array_elem_ptr a j dyn ws esz mid = _` >>
  qspecl_then [`sa`, `mid`, `sb`, `ss`] mp_tac abort_propagates >>
  simp[] >> strip_tac >> rename1 `run_inst_seq _ ss = Abort Revert_abort t` >>
  qexists_tac `t` >> simp[]
QED

Theorem array_check_ptr_frag:
  !ctx func cenv cx es a j l sgn dyn ws esz sa p sb s0 b i len.
    comp_ignore_bind (array_bounds_check j l sgn)
      (array_elem_ptr a j dyn ws esz) sa = (p,sb) /\
    (!x. a = Var x ==> not_fresh_at sa x) /\
    (!x. j = Var x ==> not_fresh_at sa x) /\
    (!x. l = Var x ==> not_fresh_at sa x) /\
    local_ptrs_reserved cenv sa /\ idx_in_range sgn i len ==>
    frag_exec ctx sa sb
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
        (eval_operand a s = SOME b /\ eval_operand j s = SOME i /\
         eval_operand l s = SOME len))
      (\s. stmt_state_rel ctx func cenv cx es s /\
        eval_operand p s = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
               lookup_var x s = SOME w) /\
        (!aid v. FLOOKUP s0.vs_allocas aid = SOME v ==>
                 FLOOKUP s.vs_allocas aid = SOME v) /\
        s.vs_memory = s0.vs_memory) (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac frag_exec_straight_fresh >>
  qexistsl_tac [`comp_ignore_bind (array_bounds_check j l sgn)
      (array_elem_ptr a j dyn ws esz)`, `\a. F`] >>
  simp[straight_fresh_array_check_ptr] >> conj_tac
  >- (rpt strip_tac >> simp[eval_operand_drop_fresh]) >>
  rpt strip_tac >> irule array_check_ptr_ok >>
  simp[] >> qexistsl_tac [`a`, `j`, `l`, `len`, `sgn`] >> simp[]
QED

Theorem array_check_ptr_frag_oob:
  !ctx func cenv cx es a j l sgn dyn ws esz sa p sb s0 i len Q.
    comp_ignore_bind (array_bounds_check j l sgn)
      (array_elem_ptr a j dyn ws esz) sa = (p,sb) /\
    (!x. j = Var x ==> not_fresh_at sa x) /\
    (!x. l = Var x ==> not_fresh_at sa x) /\ ~idx_in_range sgn i len ==>
    frag_exec ctx sa sb
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
        (eval_operand j s = SOME i /\ eval_operand l s = SOME len))
      Q (\r. ?t. r = Abort Revert_abort t)
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac (INST_TYPE [``:'a`` |-> ``:operand``] frag_exec_straight_fresh_abort) >>
  qexistsl_tac [`comp_ignore_bind (array_bounds_check j l sgn)
      (array_elem_ptr a j dyn ws esz)`, `p`, `\a. a = Revert_abort`] >>
  simp[straight_fresh_array_check_ptr] >> conj_tac
  >- (rpt strip_tac >> simp[eval_operand_drop_fresh]) >>
  rpt strip_tac >> simp[] >> irule array_check_ptr_oob >>
  simp[] >> goal_assum (drule_at (Pat `comp_ignore_bind _ _ _ = _`)) >> simp[]
QED

Theorem compile_array_dynamic_read_outcome:
  !ctx func cenv cx es a j cnt ws esz sgn opc v sa p sb s0 b i.
    compile_array_subscript a j T cnt ws esz sgn
      (\a. emit_op opc [a]) sa = (p,sb) /\
    ~is_terminator opc /\ opc <> INVOKE /\
    (!id dst. step_inst_base (mk_inst id opc [a] [dst]) s0 =
       OK (update_var dst v s0)) /\
    (!x. a = Var x ==> not_fresh_at sa x) /\
    (!x. j = Var x ==> not_fresh_at sa x) /\
    eval_operand a s0 = SOME b /\ eval_operand j s0 = SOME i /\
    local_ptrs_reserved cenv sa ==>
    frag_exec ctx sa sb
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. idx_in_range sgn i v /\ stmt_state_rel ctx func cenv cx es s /\
        eval_operand p s = SOME ((b + n2w ws) + i * n2w esz) /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
               lookup_var x s = SOME w) /\
        (!aid v. FLOOKUP s0.vs_allocas aid = SOME v ==>
                 FLOOKUP s.vs_allocas aid = SOME v) /\
        s.vs_memory = s0.vs_memory)
      (\r. ~idx_in_range sgn i v /\ ?t. r = Abort Revert_abort t)
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `frag_exec ctx sa sb _ _ exit` >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_array_subscript_split, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op opc [a] sa = (lop,mid)` >>
  `sa.cs_next_var <= mid.cs_next_var /\
   (!x. lop = Var x ==> not_fresh_at mid x) /\
   local_ptrs_reserved cenv mid /\ cs_extends sa mid` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, fresh_var_def, emit_inst_def, fresh_id_def,
          emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     simp[emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[not_fresh_at_def,
       cs_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_all emit_op_read_frame_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `frag_exec ctx sa mid pre loadpost _` >>
  `frag_exec ctx sa mid pre loadpost exit` by
    (irule frag_exec_pre_exit >> goal_assum (drule_at (Pat `frag_exec _ _ _ _ _ _`)) >> simp[]) >>
  irule frag_exec_then >>
  qexistsl_tac [`loadpost`, `mid`] >> simp[] >>
  simp[Abbr `pre`, Abbr `loadpost`] >>
  reverse conj_tac
  >- (simp[] >> irule cs_extends_same_block >>
      drule (REWRITE_RULE [straight_fresh_def] straight_fresh_array_check_ptr) >>
      simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  gen_tac >> simp[] >> strip_tac >>
  `(!x. a = Var x ==> not_fresh_at mid x) /\
   (!x. j = Var x ==> not_fresh_at mid x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `t.vs_labels = s0.vs_labels` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_inst_idx := _|> = _`
      (mp_tac o AP_TERM ``\s:venom_state. s.vs_labels``) >> simp[]) >>
  `eval_operand a t = SOME b /\ eval_operand j t = SOME i` by
    (Cases_on `a` >> Cases_on `j` >>
     gvs[eval_operand_def]) >>
  qmatch_goalsub_abbrev_tac `frag_exec ctx mid sb _ post exit` >>
  reverse (Cases_on `idx_in_range sgn i v`)
  >- (drule_all array_check_ptr_frag_oob >>
      disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`] mp_tac) >>
      disch_then (qspec_then `t` mp_tac) >>
      disch_then (qspec_then `post` mp_tac) >>
      disch_then (mp_then Any match_mp_tac frag_exec_weaken) >>
      simp[Abbr `exit`]) >>
  simp[Abbr `post`] >>
  drule_all array_check_ptr_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es`] mp_tac) >>
  disch_then (qspec_then `t` mp_tac) >>
  disch_then (qspec_then `b` mp_tac) >>
  disch_then (mp_then Any match_mp_tac frag_exec_weaken) >>
  `t.vs_allocas = s0.vs_allocas /\ t.vs_memory = s0.vs_memory` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_inst_idx := _|> = _`
      (mp_tac o AP_TERM ``\s:venom_state. (s.vs_allocas,s.vs_memory)``) >> simp[]) >>
  simp[] >> gen_tac >> strip_tac >> rpt strip_tac >>
  qpat_x_assum `!x w. not_fresh_at mid x /\ _ ==> _` irule >>
  conj_tac >- simp[] >>
  irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]
QED

(* The three mutable address spaces share one read/check/pointer fragment. *)
Theorem compile_array_dynamic_outcome:
  !ctx func cenv cx es a j cnt ws esz sgn ctor imm loc sa p sb s0 b i v.
    compile_array_subscript a j T cnt ws esz sgn
      (compile_ptr_load ctor imm loc) sa = (p,sb) /\
    (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
    v = (if loc = LocMemory then mload (w2n b) s0
         else if loc = LocStorage then sload b s0 else tload b s0) /\
    (!x. a = Var x ==> not_fresh_at sa x) /\
    (!x. j = Var x ==> not_fresh_at sa x) /\
    eval_operand a s0 = SOME b /\ eval_operand j s0 = SOME i /\
    local_ptrs_reserved cenv sa ==>
    frag_exec ctx sa sb
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. idx_in_range sgn i v /\ stmt_state_rel ctx func cenv cx es s /\
        eval_operand p s = SOME ((b + n2w ws) + i * n2w esz) /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
               lookup_var x s = SOME w) /\
        (!aid w. FLOOKUP s0.vs_allocas aid = SOME w ==>
                 FLOOKUP s.vs_allocas aid = SOME w) /\
        s.vs_memory = s0.vs_memory)
      (\r. ~idx_in_range sgn i v /\ ?t. r = Abort Revert_abort t)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `opc = if loc = LocMemory then MLOAD
                    else if loc = LocStorage then SLOAD else TLOAD` >>
  `compile_ptr_load ctor imm loc = (\a. emit_op opc [a])` by
    (simp[FUN_EQ_THM] >> Cases_on `loc` >>
     gvs[contextTheory.compile_ptr_load_def, Abbr `opc`]) >>
  gvs[] >> irule compile_array_dynamic_read_outcome >> simp[] >>
  qexistsl_tac [`a`, `cnt`, `j`, `opc`] >> simp[] >>
  gvs[Abbr `opc`, is_terminator_def,
      step_MLOAD, step_SLOAD, step_inst_base_def, exec_read1_def]
QED

Theorem compile_storage_array_dynamic_outcome:
  !ctx func cenv cx es a j cnt ws esz sgn ctor imm sa p sb s0 b i.
    compile_array_subscript a j T cnt ws esz sgn
      (compile_ptr_load ctor imm LocStorage) sa = (p,sb) /\
    (!x. a = Var x ==> not_fresh_at sa x) /\
    (!x. j = Var x ==> not_fresh_at sa x) /\
    eval_operand a s0 = SOME b /\ eval_operand j s0 = SOME i /\
    local_ptrs_reserved cenv sa ==>
    frag_exec ctx sa sb
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. idx_in_range sgn i (sload b s0) /\ stmt_state_rel ctx func cenv cx es s /\
        eval_operand p s = SOME ((b + n2w ws) + i * n2w esz) /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
               lookup_var x s = SOME w) /\
        (!aid v. FLOOKUP s0.vs_allocas aid = SOME v ==>
                 FLOOKUP s.vs_allocas aid = SOME v) /\
        s.vs_memory = s0.vs_memory)
      (\r. ~idx_in_range sgn i (sload b s0) /\ ?t. r = Abort Revert_abort t)
Proof
  rpt strip_tac >>
  `compile_ptr_load ctor imm LocStorage = (\a. emit_op SLOAD [a])` by
    simp[FUN_EQ_THM, contextTheory.compile_ptr_load_def] >>
  gvs[] >> irule compile_array_dynamic_read_outcome >>
  simp[] >> qexistsl_tac [`a`, `cnt`, `j`, `SLOAD`] >>
  simp[is_terminator_def, step_SLOAD]
QED

Theorem compile_storage_array_dynamic_frag:
  !ctx func cenv cx es a j cnt ws esz sgn ctor imm sa p sb s0 b i.
    compile_array_subscript a j T cnt ws esz sgn
      (compile_ptr_load ctor imm LocStorage) sa = (p,sb) /\
    (!x. a = Var x ==> not_fresh_at sa x) /\
    (!x. j = Var x ==> not_fresh_at sa x) /\
    eval_operand a s0 = SOME b /\ eval_operand j s0 = SOME i /\
    local_ptrs_reserved cenv sa /\ idx_in_range sgn i (sload b s0) ==>
    frag_exec ctx sa sb
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. stmt_state_rel ctx func cenv cx es s /\
        eval_operand p s = SOME ((b + n2w ws) + i * n2w esz) /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
               lookup_var x s = SOME w) /\
        (!aid v. FLOOKUP s0.vs_allocas aid = SOME v ==>
                 FLOOKUP s.vs_allocas aid = SOME v) /\
        s.vs_memory = s0.vs_memory) (\r. F)
Proof
  rpt strip_tac >> drule_all compile_storage_array_dynamic_outcome >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es`] mp_tac) >> simp[]
QED

Theorem compile_storage_array_dynamic_frag_oob:
  !ctx func cenv cx es a j cnt ws esz sgn ctor imm sa p sb s0 b i Q.
    compile_array_subscript a j T cnt ws esz sgn
      (compile_ptr_load ctor imm LocStorage) sa = (p,sb) /\
    (!x. a = Var x ==> not_fresh_at sa x) /\
    (!x. j = Var x ==> not_fresh_at sa x) /\
    eval_operand a s0 = SOME b /\ eval_operand j s0 = SOME i /\
    local_ptrs_reserved cenv sa /\ ~idx_in_range sgn i (sload b s0) ==>
    frag_exec ctx sa sb
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      Q (\r. ?t. r = Abort Revert_abort t)
Proof
  rpt strip_tac >> drule_all compile_storage_array_dynamic_outcome >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es`] mp_tac) >> simp[] >>
  disch_then (mp_then Any match_mp_tac frag_exec_weaken) >> simp[]
QED

Theorem compile_array_static_frag:
  !ctx func cenv cx es a j cnt ws esz sgn loader sa p sb s0 b i.
    compile_array_subscript a j F cnt ws esz sgn loader sa = (p,sb) /\
    (!x. a = Var x ==> not_fresh_at sa x) /\
    (!x. j = Var x ==> not_fresh_at sa x) /\
    eval_operand a s0 = SOME b /\ eval_operand j s0 = SOME i /\
    local_ptrs_reserved cenv sa /\ idx_in_range sgn i (n2w cnt) ==>
    frag_exec ctx sa sb
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. stmt_state_rel ctx func cenv cx es s /\
        eval_operand p s = SOME (b + i * n2w esz) /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
               lookup_var x s = SOME w) /\
        (!aid v. FLOOKUP s0.vs_allocas aid = SOME v ==>
                 FLOOKUP s.vs_allocas aid = SOME v) /\
        s.vs_memory = s0.vs_memory) (\r. F)
Proof
  rpt strip_tac >>
  gvs[compile_array_subscript_split, comp_bind_def, comp_return_def] >>
  `!x. Lit (n2w cnt) = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all array_check_ptr_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es`] mp_tac) >>
  disch_then (qspec_then `s0` mp_tac) >> disch_then (qspec_then `b` mp_tac) >>
  disch_then (mp_then Any match_mp_tac frag_exec_weaken) >>
  simp[eval_operand_def]
QED

Theorem compile_array_static_frag_oob:
  !ctx func cenv cx es a j cnt ws esz sgn loader sa p sb s0 i Q.
    compile_array_subscript a j F cnt ws esz sgn loader sa = (p,sb) /\
    (!x. j = Var x ==> not_fresh_at sa x) /\
    eval_operand j s0 = SOME i /\ ~idx_in_range sgn i (n2w cnt) ==>
    frag_exec ctx sa sb
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      Q (\r. ?t. r = Abort Revert_abort t)
Proof
  rpt strip_tac >>
  gvs[compile_array_subscript_split, comp_bind_def, comp_return_def] >>
  `!x. Lit (n2w cnt) = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all array_check_ptr_frag_oob >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`] mp_tac) >>
  disch_then (qspec_then `s0` mp_tac) >> disch_then (qspec_then `Q` mp_tac) >>
  disch_then (mp_then Any match_mp_tac frag_exec_weaken) >>
  simp[eval_operand_def]
QED
