(*
 * Array subscripts: the bounds check and the element pointer (#636,
 * Places row 1)
 *
 * compile_array_subscript reads the array's length (a load at the base for
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
 *   array_bounds_check, array_elem_ptr — the two halves of
 *                                compile_array_subscript after the length
 *   compile_array_subscript_split — compile_array_subscript is the length,
 *                                the check and the pointer in turn
 *   array_len_ok               — the length operand's code runs to the
 *                                length: a load for a dynamic array
 *   array_len_ok_MLOAD, array_len_ok_SLOAD, array_len_ok_static
 *   idx_in_range               — the index is not negative (for a signed
 *                                index) and below the length
 *   array_bounds_check_ok, array_bounds_check_oob — the check passes an
 *                                index in range and aborts otherwise
 *   array_elem_ptr_run         — the pointer's code
 *   compile_array_subscript_ok, compile_array_subscript_oob — the whole
 *                                subscript, by the index's range
 *
 * Helpers: elim_lit, forward_all_evals, collapse_run, chain_step (the
 *   tactics of arithmeticProps), bool_to_word_eq_0, word_or_bool_to_word,
 *   array_bounds_valid_run
 *)

Theory exprSimArrayIndex
Ancestors
  arithmeticProps exprLoweringProps emitHelperProps
  exprLowering compileEnv venomExecSemantics venomState venomInst

(* ===== Tactics (as in arithmeticProps) ===== *)

(* Specialize the n-th operand of an emit_op_*_correct theorem to a Lit. *)
fun elim_lit n th =
  let
    val (vars, _) = strip_forall (concl th)
    val op_var = List.nth (vars, n-1)
    val v_var = List.nth (vars, n+1)
    val lit_const = prim_mk_const{Name="Lit",Thy="venomState"}
  in
    th |> SPEC_ALL
       |> INST [op_var |-> mk_comb(lit_const, v_var)]
       |> SIMP_RULE (srw_ss()) [eval_operand_lit]
       |> GENL (List.filter (fn v => not (aconv v op_var)) vars)
  end;

(* Forward every eval_operand fact through every preservation fact
   (oldest first). *)
fun forward_all_evals (asl, g) =
  let
    fun is_pres t =
      (let val (vs, body) = strip_forall t
       in length vs = 2 andalso is_imp body andalso
          let val (ant, _) = dest_imp body
              val (lhs_t, _) = dest_eq ant
              val (f, _) = strip_comb lhs_t
          in fst (dest_const f) = "eval_operand"
          end
       end) handle _ => false
    fun is_eval t =
      (not (is_forall t) andalso
       let val (lhs_t, rhs_t) = dest_eq t
           val (f, _) = strip_comb lhs_t
           val (some_c, _) = dest_comb rhs_t
       in fst (dest_const f) = "eval_operand" andalso
          fst (dest_const some_c) = "SOME"
       end) handle _ => false
    val pres_list = rev (List.filter is_pres asl)
    fun apply_one_pres pres_t (asl', g') =
      let val pres_th = ASSUME pres_t
          val evals = List.filter is_eval asl'
          fun forward_one eval_t (asl'', g'') =
            (let val new_th = MATCH_MP (SPEC_ALL pres_th) (ASSUME eval_t)
             in if List.exists (aconv (concl new_th)) asl''
                then ALL_TAC (asl'', g'')
                else assume_tac new_th (asl'', g'')
             end handle _ => ALL_TAC (asl'', g''))
      in EVERY (map forward_one evals) (asl', g')
      end
  in
    EVERY (map apply_one_pres pres_list) (asl, g)
  end;

fun collapse_run (eq_th : thm) : tactic = fn (asl, g) =>
  let val rhs_tm = rhs (concl eq_th)
      fun matches_rhs a =
        (aconv (lhs (concl (ASSUME a))) rhs_tm) handle _ => false
  in case List.find matches_rhs asl of
       SOME a_str => assume_tac (TRANS eq_th (ASSUME a_str)) (asl, g)
     | NONE => raise mk_HOL_ERR "collapse_run" "collapse_run" "no matching run"
  end;

fun chain_step th : tactic =
  forward_all_evals >>
  drule_all th >> strip_tac >>
  TRY (imp_res_tac emit_op_extends >>
       drule_all run_inst_seq_chain >> strip_tac >>
       qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run);

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
  !base_op idx_op dyn cnt ws esz sgn opc.
    compile_array_subscript base_op idx_op dyn cnt ws esz sgn opc =
    comp_bind (if dyn then emit_op opc [base_op]
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

(* The length operand's code, from st, runs to the length len: a load at
   the base for a dynamic array, the static count otherwise. *)
Definition array_len_ok_def:
  array_len_ok dyn cnt opc base_op ss len <=>
    if dyn then
      !st lop st'.
        emit_op opc [base_op] st = (lop, st') /\ fresh_vars_wrt st ss ==>
        ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
              eval_operand lop ss' = SOME len /\
              same_blocks st st' /\ fresh_vars_wrt st' ss' /\
              (!op w. eval_operand op ss = SOME w ==>
                      eval_operand op ss' = SOME w)
    else len = n2w cnt
End

Theorem array_len_ok_static:
  !cnt opc base_op ss. array_len_ok F cnt opc base_op ss (n2w cnt)
Proof
  simp[array_len_ok_def]
QED

Theorem array_len_ok_MLOAD:
  !cnt base_op ss b.
    eval_operand base_op ss = SOME b ==>
    array_len_ok T cnt MLOAD base_op ss (mload (w2n b) ss)
Proof
  rw[array_len_ok_def] >> drule_all emit_op_MLOAD_correct >>
  strip_tac >> metis_tac[]
QED

Theorem array_len_ok_SLOAD:
  !cnt base_op ss b.
    eval_operand base_op ss = SOME b ==>
    array_len_ok T cnt SLOAD base_op ss (sload b ss)
Proof
  rw[array_len_ok_def] >> drule_all emit_op_SLOAD_correct >>
  strip_tac >> metis_tac[]
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

Theorem compile_array_subscript_ok:
  !base_op idx_op dyn cnt ws esz sgn opc st p st' ss b i len.
    compile_array_subscript base_op idx_op dyn cnt ws esz sgn opc st =
      (p, st') /\
    eval_operand base_op ss = SOME b /\ eval_operand idx_op ss = SOME i /\
    fresh_vars_wrt st ss /\ array_len_ok dyn cnt opc base_op ss len /\
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

Theorem compile_array_subscript_oob:
  !base_op idx_op dyn cnt ws esz sgn opc st p st' ss b i len.
    compile_array_subscript base_op idx_op dyn cnt ws esz sgn opc st =
      (p, st') /\
    eval_operand base_op ss = SOME b /\ eval_operand idx_op ss = SOME i /\
    fresh_vars_wrt st ss /\ array_len_ok dyn cnt opc base_op ss len /\
    ~idx_in_range sgn i len ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> fs[oneTheory.one] >>
  drule array_elem_ptr_extends >> strip_tac >>
  Cases_on `dyn` >> gvs[comp_return_def, array_len_ok_def] >>
  TRY (`eval_operand (Lit (n2w cnt)) ss = SOME (n2w cnt)` by
         simp[eval_operand_lit] >>
       drule_all array_bounds_check_oob >> strip_tac >>
       qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts st mid) ss = _` >>
       imp_res_tac array_bounds_check_extends >>
       qspecl_then [`st`, `mid`, `st'`, `ss`] mp_tac abort_propagates >>
       simp[] >> NO_TAC) >>
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
