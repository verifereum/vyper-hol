(* Actual straight-line clamp execution, independent of simulation judgments. *)
Theory exprSimExtract32Run
Ancestors
  exprSimExtract32Read exprSimExtract32Value convertScalarOutputs exprSimHash
  fragGasMode
  builtinBytes builtinProps arithmeticProps emitHelperProps emitHelper
  exprLowering exprLoweringProps compileEnv fragExec venomExecSemantics venomInst venomState
  vyperTypeSystem vyperValue vyperContext valueEncoding words integer_word list rich_list

Theorem extract32_clamp_address_run:
  !raw sa op sb s w.
    compile_clamp_basetype raw (BaseT AddressT) sa = (op,sb) /\
    eval_operand raw s = SOME w /\ fresh_vars_wrt sa s ==>
    ?u. if w2n w < 2 ** 160 then
      run_inst_seq (emitted_insts sa sb) s = OK u /\
      eval_operand op u = SOME w
    else run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort u
Proof
  rpt strip_tac >>
  gvs[compile_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op GT [op; Lit _] sa = (gt,sc)` >>
  rename1 `emit_op ISZERO [gt] sc = (ok,sd)` >>
  rename1 `emit_void ASSERT [ok] sd = ((),sf)` >>
  `eval_operand (Lit (n2w (2 ** 160 - 1))) s =
     SOME (n2w (2 ** 160 - 1))` by simp[eval_operand_lit] >>
  fs[] >>
  drule_all emit_op_GT_correct >>
  disch_then (qx_choose_then `s1` strip_assume_tac) >>
  drule_all emit_op_ISZERO_correct >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  drule_all emit_void_ASSERT_ok_or_revert >>
  simp[bool_to_word_def] >> strip_tac >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `run_inst_seq (emitted_insts sa sd) s = OK s2 /\
   sd.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sd` by
    (drule_all run_inst_seq_chain >> simp[]) >>
  `run_inst_seq (emitted_insts sa sf) s =
   run_inst_seq (emitted_insts sd sf) s2` by
    (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
  gvs[wordsTheory.dimword_def]
QED

Theorem extract32_clamp_fixed_run:
  !raw m sa op sb s w.
    m <= 32 /\
    compile_clamp_basetype raw (BaseT (BytesT (Fixed m))) sa = (op,sb) /\
    eval_operand raw s = SOME w /\ fresh_vars_wrt sa s ==>
    ?u. if w << (m * 8) = 0w then
      run_inst_seq (emitted_insts sa sb) s = OK u /\
      eval_operand op u = SOME w
    else run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort u
Proof
  rpt strip_tac >>
  Cases_on `m < 32`
  >- (gvs[compile_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      rename1 `emit_op SHL [Lit _; op] sa = (shifted,sc)` >>
      rename1 `emit_op ISZERO [shifted] sc = (ok,sd)` >>
      rename1 `emit_void ASSERT [ok] sd = ((),sf)` >>
      `eval_operand (Lit (n2w (m * 8))) s = SOME (n2w (m * 8))`
        by simp[eval_operand_lit] >>
      fs[] >>
      drule_all scalar_emit_SHL_correct >>
      disch_then (qx_choose_then `s1` strip_assume_tac) >>
      drule_all emit_op_ISZERO_correct >>
      disch_then (qx_choose_then `s2` strip_assume_tac) >>
      drule_all emit_void_ASSERT_ok_or_revert >>
      simp[bool_to_word_def, wordsTheory.dimword_def] >> strip_tac >>
      imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
      `run_inst_seq (emitted_insts sa sd) s = OK s2 /\
       sd.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sd` by
        metis_tac[run_inst_seq_chain] >>
      `run_inst_seq (emitted_insts sa sf) s =
       run_inst_seq (emitted_insts sd sf) s2` by
        (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
      `m * 8 < dimword (:256)` by
        (simp[wordsTheory.dimword_def] >> decide_tac) >>
      gvs[wordsTheory.w2n_n2w] >> metis_tac[]) >>
  `m = 32` by decide_tac >>
  gvs[compile_clamp_basetype_def, comp_return_def, emitted_insts_refl,
      run_inst_seq_def, wordsTheory.LSL_LIMIT]
QED

Theorem extract32_clamp_numeric_run:
  !raw ty sa op sb s w.
    ((?n. ty = BaseT (UintT n) /\ n <= 256) \/
     (?n. ty = BaseT (IntT n) /\ n <= 256)) /\
    compile_clamp_basetype raw ty sa = (op,sb) /\
    eval_operand raw s = SOME w /\ fresh_vars_wrt sa s ==>
    ?u. if arithmeticProps$in_type_range ty (math_val ty w) then
      run_inst_seq (emitted_insts sa sb) s = OK u /\
      eval_operand op u = SOME w
    else run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort u
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_clamp_basetype_def] >>
  Cases_on `n < 256` >> gvs[comp_return_def, emitted_insts_refl, run_inst_seq_def]
  >- suspend "uint_small"
  >- suspend "uint_full"
  >- suspend "int_small" >>
  suspend "int_full"
QED

Resume extract32_clamp_numeric_run[uint_small]:
  Cases_on `in_type_range (BaseT (UintT n)) (math_val (BaseT (UintT n)) w)` >> simp[]
  >- (irule arithmeticPropsTheory.clamp_and_return_ok >>
      qexistsl_tac [`sa`, `raw`, `s`, `BaseT (UintT n)`] >>
      simp[emitted_insts_refl, run_inst_seq_def, type_bits_def]) >>
  irule arithmeticPropsTheory.clamp_and_return_out_of_range >>
  qexistsl_tac [`sa`, `op`, `raw`, `s`, `BaseT (UintT n)`, `w`] >>
  simp[emitted_insts_refl, run_inst_seq_def, type_bits_def]
QED

Resume extract32_clamp_numeric_run[uint_full]:
  `n = 256` by decide_tac >> gvs[] >>
  simp[arithmeticPropsTheory.in_type_range_def, arithmeticPropsTheory.math_val_def,
       type_bits_def, is_signed_type_def] >>
  mp_tac (Q.ISPEC `w:bytes32` wordsTheory.w2n_lt) >>
  simp[wordsTheory.dimword_def]
QED

Resume extract32_clamp_numeric_run[int_small]:
  Cases_on `in_type_range (BaseT (IntT n)) (math_val (BaseT (IntT n)) w)` >> simp[]
  >- (irule arithmeticPropsTheory.clamp_and_return_ok >>
      qexistsl_tac [`sa`, `raw`, `s`, `BaseT (IntT n)`] >>
      simp[emitted_insts_refl, run_inst_seq_def, type_bits_def]) >>
  irule arithmeticPropsTheory.clamp_and_return_out_of_range >>
  qexistsl_tac [`sa`, `op`, `raw`, `s`, `BaseT (IntT n)`, `w`] >>
  simp[emitted_insts_refl, run_inst_seq_def, type_bits_def]
QED

Resume extract32_clamp_numeric_run[int_full]:
  `n = 256` by decide_tac >> gvs[] >>
  simp[arithmeticPropsTheory.in_type_range_def, arithmeticPropsTheory.math_val_def,
       type_bits_def, is_signed_type_def] >>
  mp_tac (Q.ISPEC `w:bytes32` integer_wordTheory.w2i_le) >>
  mp_tac (Q.ISPEC `w:bytes32` integer_wordTheory.w2i_ge) >>
  simp[wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def,
       wordsTheory.dimword_def, wordsTheory.dimword_IS_TWICE_INT_MIN]
QED

Finalise extract32_clamp_numeric_run

Theorem extract32_clamp_source_success:
  !raw bt win sa op sb s v.
    extract32_result_base_ok bt /\ LENGTH win = 32 /\
    (case bt of UintT n => n <= 256 | IntT n => 0 < n /\ n <= 256 |
                BytesT (Fixed m) => m <= 32 | _ => T) /\
    compile_clamp_basetype raw (BaseT bt) sa = (op,sb) /\
    eval_operand raw s = SOME (word_of_bytes T (0w:bytes32) win) /\
    fresh_vars_wrt sa s /\ evaluate_extract32 win 0 bt = INL v ==>
    ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
        eval_operand op u = SOME (typed_val_to_w256 (BaseTV bt) v) /\
        fresh_vars_wrt sb u /\ (u with vs_vars := s.vs_vars) = s /\
        (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
       eval_operand op u = SOME (typed_val_to_w256 (BaseTV bt) v)` suffices_by
    (strip_tac >> qexists_tac `u` >> simp[] >>
     drule_all extract32_clamp_success_frame >> simp[]) >>
  Cases_on `bt` >> gvs[extract32_result_base_ok_def]
  >- suspend "uint"
  >- suspend "int"
  >- suspend "bytes" >>
  suspend "address"
QED

Resume extract32_clamp_source_success[uint]:
  gvs[evaluate_extract32_def, extract32_convert_uint, AllCaseEqs()] >>
  simp[extract32_numeric_encoding] >>
  `TAKE 32 win = win` by metis_tac[TAKE_LENGTH_ID] >> gvs[] >>
  drule_at (Pos (el 2)) extract32_clamp_numeric_run >>
  simp[arithmeticPropsTheory.math_val_def, is_signed_type_def] >>
  disch_then drule >> simp[TAKE_LENGTH_ID_rwt]
QED

Resume extract32_clamp_source_success[int]:
  gvs[evaluate_extract32_def, extract32_convert_int, AllCaseEqs()] >>
  simp[extract32_numeric_encoding] >>
  `TAKE 32 win = win` by metis_tac[TAKE_LENGTH_ID] >> gvs[] >>
  drule_at (Pos (el 2)) extract32_clamp_numeric_run >>
  simp[arithmeticPropsTheory.math_val_def, is_signed_type_def] >>
  disch_then drule >> simp[TAKE_LENGTH_ID_rwt]
QED

Resume extract32_clamp_source_success[bytes]:
  Cases_on `b` >> gvs[extract32_result_base_ok_def] >>
  gvs[evaluate_extract32_def, AllCaseEqs(), TAKE_LENGTH_ID_rwt] >>
  drule_all extract32_fixed_encoding >> strip_tac >> simp[] >>
  drule_all extract32_suffix_shift >> strip_tac >>
  drule_all extract32_clamp_fixed_run >> gvs[]
QED

Resume extract32_clamp_source_success[address]:
  gvs[evaluate_extract32_def, AllCaseEqs(), TAKE_LENGTH_ID_rwt] >>
  drule_all extract32_address_bytes_encoding >> strip_tac >> simp[] >>
  drule_all extract32_address_prefix_bound >> strip_tac >>
  drule_all extract32_clamp_address_run >> gvs[]
QED

Finalise extract32_clamp_source_success

Theorem extract32_clamp_source_error:
  !raw bt win sa op sb s msg.
    extract32_result_base_ok bt /\ LENGTH win = 32 /\
    (case bt of UintT n => n <= 256 | IntT n => 0 < n /\ n <= 256 |
                BytesT (Fixed m) => m <= 32 | _ => T) /\
    compile_clamp_basetype raw (BaseT bt) sa = (op,sb) /\
    eval_operand raw s = SOME (word_of_bytes T (0w:bytes32) win) /\
    fresh_vars_wrt sa s /\ evaluate_extract32 win 0 bt = INR (RuntimeError msg) ==>
    ?u. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort u
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bt` >> gvs[extract32_result_base_ok_def]
  >- suspend "uint"
  >- suspend "int"
  >- suspend "bytes" >>
  suspend "address"
QED

Resume extract32_clamp_source_error[uint]:
  gvs[evaluate_extract32_def, extract32_convert_uint, AllCaseEqs(), TAKE_LENGTH_ID_rwt] >>
  drule_at (Pos (el 2)) extract32_clamp_numeric_run >>
  simp[arithmeticPropsTheory.math_val_def, is_signed_type_def] >>
  disch_then drule >> simp[TAKE_LENGTH_ID_rwt]
QED

Resume extract32_clamp_source_error[int]:
  gvs[evaluate_extract32_def, extract32_convert_int, AllCaseEqs(), TAKE_LENGTH_ID_rwt] >>
  drule_at (Pos (el 2)) extract32_clamp_numeric_run >>
  simp[arithmeticPropsTheory.math_val_def, is_signed_type_def] >>
  disch_then drule >> simp[TAKE_LENGTH_ID_rwt]
QED

Resume extract32_clamp_source_error[bytes]:
  Cases_on `b` >> gvs[extract32_result_base_ok_def] >>
  gvs[evaluate_extract32_def, AllCaseEqs(), TAKE_LENGTH_ID_rwt] >>
  drule_all extract32_suffix_shift >> strip_tac >>
  `~EVERY ($= 0w) (DROP n win)` by
    (simp[EVERY_MEM, EXISTS_MEM] >> gvs[EXISTS_MEM] >> metis_tac[]) >>
  drule_all extract32_clamp_fixed_run >> gvs[]
QED

Resume extract32_clamp_source_error[address]:
  gvs[evaluate_extract32_def, AllCaseEqs(), TAKE_LENGTH_ID_rwt] >>
  drule_all extract32_address_prefix_bound >> strip_tac >>
  `~EVERY ($= 0w) (TAKE 12 win)` by
    (simp[EVERY_MEM, EXISTS_MEM] >> gvs[EXISTS_MEM] >> metis_tac[]) >>
  drule_all extract32_clamp_address_run >> gvs[]
QED

Finalise extract32_clamp_source_error

Theorem extract32_load_window:
  !len dp off sa raw sm s bs n p m.
    val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s.vs_memory /\
    LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
    p + 32 + LENGTH bs < dimword (:256) /\ n + 32 <= LENGTH bs /\
    eval_operand len s = SOME (n2w (LENGTH bs)) /\
    eval_operand dp s = SOME (n2w (p + 32)) /\
    eval_operand off s = SOME (n2w n) /\ fresh_vars_wrt sa s /\
    compile_extract32_load len dp off sa = (raw,sm) ==>
    ?u. run_inst_seq (emitted_insts sa sm) s = OK u /\
        eval_operand raw u = SOME (word_of_bytes T (0w:bytes32) (TAKE 32 (DROP n bs))) /\
        fresh_vars_wrt sm u /\ (u with vs_vars := s.vs_vars) = s /\
        (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all builtinPropsTheory.compile_extract32_correct >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> strip_tac >>
  `p + 32 + n < dimword (:256)` by decide_tac >>
  `w2n (n2w (p + 32) + n2w n : bytes32) = p + 32 + n` by
    (pure_rewrite_tac[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
     simp[arithmeticTheory.LESS_MOD]) >>
  drule_all extract32_memory_slice >> strip_tac >>
  drule_all extract32_load_success_frame >> strip_tac >>
  qexists_tac `ss'` >> gvs[mload_def, mem_word_at_def, mem_bytes_at_def]
QED

Theorem extract32_tail_success:
  !len dp off sa raw sm op sb s bs n p m bt v.
    extract32_result_base_ok bt /\
    (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
                BytesT (Fixed k) => k <= 32 | _ => T) /\
    val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s.vs_memory /\
    LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
    p + 32 + LENGTH bs < dimword (:256) /\
    eval_operand len s = SOME (n2w (LENGTH bs)) /\
    eval_operand dp s = SOME (n2w (p + 32)) /\
    eval_operand off s = SOME (n2w n) /\ fresh_vars_wrt sa s /\
    compile_extract32_load len dp off sa = (raw,sm) /\
    compile_clamp_basetype raw (BaseT bt) sm = (op,sb) /\
    evaluate_extract32 bs n bt = INL v ==>
    ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
        eval_operand op u = SOME (typed_val_to_w256 (BaseTV bt) v) /\
        fresh_vars_wrt sb u /\ (u with vs_vars := s.vs_vars) = s /\
        (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  `n + 32 <= LENGTH bs` by
    (qpat_x_assum `evaluate_extract32 _ _ _ = _` mp_tac >>
     simp[Once evaluate_extract32_def] >> IF_CASES_TAC >> simp[]) >>
  drule_all extract32_load_window >>
  disch_then (qx_choose_then `s1` strip_assume_tac) >>
  `LENGTH (TAKE 32 (DROP n bs)) = 32` by simp[LENGTH_TAKE] >>
  drule_all extract32_source_window >> strip_tac >>
  `evaluate_extract32 (TAKE 32 (DROP n bs)) 0 bt = INL v` by metis_tac[] >>
  drule_all extract32_clamp_source_success >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  drule_at (Pos (el 2)) (extract32_read_extends |> Q.ISPEC `compile_extract32_load len dp off`) >>
  simp[extract32_read_load] >> strip_tac >>
  drule_at (Pos (el 2)) (extract32_read_extends |> Q.ISPEC `compile_clamp_basetype raw (BaseT bt)`) >>
  simp[extract32_read_clamp_basetype] >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK s2` by
    (`sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by simp[] >>
     drule_all run_inst_seq_chain >> simp[]) >>
  qexists_tac `s2` >> simp[] >> conj_tac
  >- (qpat_x_assum `s2 with vs_vars := _ = _` mp_tac >>
      qpat_x_assum `s1 with vs_vars := _ = _` mp_tac >>
      simp[venom_state_component_equality]) >>
  rpt strip_tac >>
  `not_fresh_at sm x` by (irule freshWritesTheory.not_fresh_at_mono >> simp[] >>
    qexists_tac `sa` >> simp[]) >>
  metis_tac[]
QED

Theorem extract32_tail_error:
  !len dp off sa raw sm op sb s bs n p m bt msg.
    extract32_result_base_ok bt /\
    (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
                BytesT (Fixed k) => k <= 32 | _ => T) /\
    val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s.vs_memory /\
    LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
    p + 32 + LENGTH bs < dimword (:256) /\
    eval_operand len s = SOME (n2w (LENGTH bs)) /\
    eval_operand dp s = SOME (n2w (p + 32)) /\
    eval_operand off s = SOME (n2w n) /\ fresh_vars_wrt sa s /\
    compile_extract32_load len dp off sa = (raw,sm) /\
    compile_clamp_basetype raw (BaseT bt) sm = (op,sb) /\
    evaluate_extract32 bs n bt = INR (RuntimeError msg) ==>
    ?u. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort u
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 2)) (extract32_read_extends |> Q.ISPEC `compile_extract32_load len dp off`) >>
  simp[extract32_read_load] >> strip_tac >>
  drule_at (Pos (el 2)) (extract32_read_extends |> Q.ISPEC `compile_clamp_basetype raw (BaseT bt)`) >>
  simp[extract32_read_clamp_basetype] >> strip_tac >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by simp[] >>
  Cases_on `n + 32 <= LENGTH bs`
  >- (drule_all extract32_load_window >>
      disch_then (qx_choose_then `s1` strip_assume_tac) >>
      `LENGTH (TAKE 32 (DROP n bs)) = 32` by simp[LENGTH_TAKE] >>
      drule_all extract32_source_window >> strip_tac >>
      `evaluate_extract32 (TAKE 32 (DROP n bs)) 0 bt = INR (RuntimeError msg)` by metis_tac[] >>
      drule_all extract32_clamp_source_error >> strip_tac >>
      drule_all run_inst_seq_chain >> simp[] >> metis_tac[]) >>
  drule_all builtinPropsTheory.compile_extract32_correct >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> strip_tac >>
  `!u. run_inst_seq (emitted_insts sa sm) s <> OK u` by simp[] >>
  drule_all run_inst_seq_chain_err >> simp[] >> metis_tac[]
QED

(* Counted lifting uses the actual run and the tail's compiler certificate. *)
Theorem extract32_tail_run_path:
  compile_extract32_load len dp off sa = (raw,sm) /\
  compile_clamp_basetype raw ty sm = (op,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  gas_marked_path F ctx func s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  drule_all extract32_tail_straight_noext >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by gvs[EVERY_MEM] >>
  drule_all hash_run_path >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  simp[]
QED

Theorem extract32_tail_abort_path:
  compile_extract32_load len dp off sa = (raw,sm) /\
  compile_clamp_basetype raw ty sm = (op,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?n j. gas_marked_path F ctx func s n (Abort a (u with vs_inst_idx := j))
Proof
  strip_tac >>
  drule_all extract32_tail_straight_noext >> strip_tac >>
  irule hash_abort_path >> simp[] >>
  qexistsl_tac [`emitted_insts sa sb`, `sa`, `sb`] >>
  gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND, EVERY_MEM] >>
  metis_tac[]
QED
