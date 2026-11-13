(* Counted immutable array indexing at the actual index endpoint. *)
Theory popNestedImmutableIndexMemory
Ancestors
  popNestedImmutableConstructorMemory popNestedImmutableTransport
  popNestedArrayCheckMemory exprSimBopRestWordLoadSafety
  fragExecMem exprSimArrayIndex freshWrites context emitHelperProps
  compileEnv list rich_list pair fragExec emitHelper exprLoweringProps bodyUnopFragMemory
Libs
  pairLib

Theorem imm_array_ctor_seq_mem_ok[local]:
  !base idx dyn cnt ws esz sgn imm sa dst sb s b.
  compile_array_subscript base idx dyn cnt ws esz sgn
    (compile_ptr_load T imm LocCode) sa = (dst,sb) /\
  eval_operand base s = SOME b /\
  (dyn ==> w2n b + 32 <= s.vs_alloca_next) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt gen_tac >> simp[compile_array_subscript_split, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  mp_tac straight_fresh_array_check_ptr >>
  simp[straight_fresh_def] >> disch_then drule >> strip_tac >>
  `same_blocks sa cs' /\ sa.cs_next_var <= cs'.cs_next_var /\
   cs'.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa cs'` by
    (Cases_on `dyn` >> gvs[comp_return_def] >>
     Cases_on `imm` >>
     gvs[compile_ptr_load_def, compile_imm_load_word_def,
         emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_var_def, fresh_id_def, emit_def, same_blocks_def, emitted_insts_def,
         DROP_LENGTH_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `emitted_insts sa sb = emitted_insts sa cs' ++ emitted_insts cs' sb` by
    (irule emitted_insts_append >> simp[]) >>
  pop_assum SUBST1_TAC >> irule run_inst_seq_mem_ok_append >>
  conj_tac >- metis_tac[writes_fresh_mem_ok] >>
  reverse (Cases_on `dyn`)
  >- (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
      simp[comp_return_def] >> strip_tac >>
      simp[NoAsms, emitted_insts_def, DROP_LENGTH_TOO_LONG,
           run_inst_seq_mem_ok_def]) >>
  irule rest_word_ptr_load_mem_ok >> simp[] >>
  qexistsl [`b`, `base'`] >>
  qexistsl [`T`, `imm`, `LocCode`, `len_op`] >>
  simp[] >> Cases_on `imm` >> gvs[]
QED

Theorem imm_array_ctor_code_optional[local]:
  !base idx dyn cnt ws esz sgn imm sa p sb.
    compile_array_subscript base idx dyn cnt ws esz sgn
      (compile_ptr_load T imm LocCode) sa = (p,sb) ==>
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\inst. (fresh_write_op inst.inst_opcode \/ inst.inst_opcode = ILOAD) /\
      EVERY (\x. ~not_fresh_at sa x) inst.inst_outputs) (emitted_insts sa sb)
Proof
  rpt gen_tac >> Cases_on `imm` >>
  metis_tac[imm_array_ctor_none_code, imm_array_ctor_code]
QED

Theorem imm_array_ctor_run_optional[local]:
  !base idx dyn cnt ws esz sgn imm sa p sb s b i len.
    compile_array_subscript base idx dyn cnt ws esz sgn
      (compile_ptr_load T imm LocCode) sa = (p,sb) /\
    eval_operand base s = SOME b /\ eval_operand idx s = SOME i /\
    (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
    (!x. base = Var x ==> not_fresh_at sa x) /\
    (!x. idx = Var x ==> not_fresh_at sa x) /\
    (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at sa x) /\
    len = (if dyn then mload (w2n b) s else n2w cnt) ==>
    if idx_in_range sgn i len then
      ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        eval_operand p t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
        t = s with vs_vars := t.vs_vars /\
        (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
    else ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  rpt gen_tac >> Cases_on `imm` >> simp[] >> strip_tac
  >- (drule_all imm_array_ctor_none_run >> simp[]) >>
  drule_all imm_array_ctor_run >> simp[]
QED

Theorem imm_array_ctor_path_mem[local]:
  !base idx dyn cnt ws esz sgn imm sa p sb s b i len ctx func.
    compile_array_subscript base idx dyn cnt ws esz sgn
      (compile_ptr_load T imm LocCode) sa = (p,sb) /\
    eval_operand base s = SOME b /\ eval_operand idx s = SOME i /\
    (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
    (!x. base = Var x ==> not_fresh_at sa x) /\
    (!x. idx = Var x ==> not_fresh_at sa x) /\
    (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at sa x) /\
    len = (if dyn then mload (w2n b) s else n2w cnt) /\
    (dyn ==> w2n b + 32 <= s.vs_alloca_next) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    if idx_in_range sgn i len then
      ?t. gas_marked_path T ctx func s 0
          (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
        eval_operand p t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
        t = s with vs_vars := t.vs_vars /\
        (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
    else ?t j. gas_marked_path T ctx func s 0
          (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  rpt gen_tac >> strip_tac >>
  drule imm_array_ctor_code_optional >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `EVERY (\ins. ins.inst_opcode <> GAS /\ ins.inst_opcode <> INVOKE /\
       ~is_terminator ins.inst_opcode) (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> metis_tac[imm_readonly_opcode]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule imm_array_ctor_seq_mem_ok >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all imm_array_ctor_run_optional >>
  Cases_on `idx_in_range sgn i len` >> simp[] >> strip_tac
  >- (qexists_tac `t` >> simp[] >>
      `LENGTH (FILTER (\ins. ins.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
        (simp[LENGTH_EQ_NUM_compute, FILTER_EQ_NIL, EVERY_MEM] >>
         fs[EVERY_MEM] >> metis_tac[]) >>
      drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_path_mem >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
      simp[gas_marked_path_def] >> impl_tac
      >- (simp[] >> fs[EVERY_MEM]) >>
      simp[]) >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >> simp[] >> metis_tac[]
QED
