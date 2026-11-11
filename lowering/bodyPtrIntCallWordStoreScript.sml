(* Counted word copies, independent of physical type annotations. *)
Theory bodyPtrIntCallWordStore
Ancestors
  augAssignPtrLoad augAssignPtrStore fragGasSeqPtr fragExec
  context emitHelper emitHelperProps exprLoweringProps
  compileEnv bodyPtrDefs ptrDiscipline venomState venomInst
  venomExecSemantics venomMemDefs venomMemProofs valueEncoding
  finite_map pred_set arithmetic forPtrWord typedCopyAgreement vyperTypeSystem

Theorem emit_word_copy_counted:
  !D ctx fn PG sa sm sb src dst out G tn s a b.
    emit_op MLOAD [Var src] sa = (Var out,sm) /\
    emit_void MSTORE [Var dst;Var out] sm = ((),sb) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?H tf z.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK z) /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
      z.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
      tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
      z.vs_fmp = s.vs_fmp /\ z.vs_accounts = s.vs_accounts /\
      z.vs_transient = s.vs_transient /\ z.vs_call_ctx = s.vs_call_ctx /\
      (!x. not_fresh_at sa x ==>
        lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b <= i /\ i < w2n b+32) ==>
        mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_var_def, fresh_id_def, emit_def,
         cs_extends_def, emitted_blocks_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all augAssignPtrLoadTheory.emit_mload_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf 32` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `eval_operand (Var out) sf = SOME (mload (w2n a) s)` by
    simp[eval_operand_def] >>
  drule_all augAssignPtrStoreTheory.emit_mstore_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf' (OK sf')` by
    (drule_all fragGasPathPtrTheory.gas_path_ptr_then >> simp[]) >>
  `!i. ~(w2n b <= i /\ i < w2n b+32) ==>
    mem_bytes_at i 1 sf'.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> simp[] >>
     gvs[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint]) >>
  `tnf'.t_imm = tn.t_imm` by
    simp[step_taint_def, imm_taint_def, adopt_reset_def, mk_inst_def] >>
  `!x. op_taint tnf' (Var x) = op_taint tnf (Var x)` by
    (gen_tac >> simp[op_taint_def]) >>
  qexistsl_tac [`Gf`, `tnf'`, `sf'`] >>
  simp[] >>
  simp[mstore_def, update_var_def]
QED

Theorem word_arg_type_fits_eq[local]:
  !st dt. arg_type_fits st dt /\ is_word_type dt ==> st = dt
Proof
  Cases_on `dt` >> Cases_on `st` >>
  gvs[arg_type_fits_def, is_word_type_def] >>
  rename1 `is_word_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[arg_type_fits_def, is_word_type_def] >>
  rename1 `is_word_type (BaseT (BytesT bd))` >> Cases_on `bd` >>
  gvs[arg_type_fits_def, is_word_type_def] >>
  Cases_on `b'` >> gvs[arg_type_fits_def] >>
  rename1 `arg_type_fits (BaseT (BytesT bd')) _` >> Cases_on `bd'` >>
  gvs[arg_type_fits_def]
QED

Theorem intcall_store_word_counted:
  !D ctx fn PG ce sa sb src dst st dt tenv stv dtv v G tn s a b.
    compile_store_memory_typed ce (Var dst) dt (Var src) st sa = ((),sb) /\
    is_word_type dt /\ arg_type_fits st dt /\
    evaluate_type tenv st = SOME stv /\ evaluate_type tenv dt = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a) m) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?H tf z.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK z) /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
      (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
        val_in_memory dtv v (w2n b) m) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
      z.vs_fmp = s.vs_fmp /\ z.vs_accounts = s.vs_accounts /\
      z.vs_transient = s.vs_transient /\ z.vs_call_ctx = s.vs_call_ctx /\
      (!x. not_fresh_at sa x ==>
        lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b <= i /\ i < w2n b+32) ==>
        mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `st = dt` by metis_tac[word_arg_type_fits_eq] >> gvs[] >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[for_typed_word_robust_clean] >>
  `?out sm. emit_op MLOAD [Var src] sa = (Var out,sm) /\
    emit_void MSTORE [Var dst;Var out] sm = ((),sb)` by
    (drule compile_store_memory_typed_word >>
     disch_then (qspecl_then [`dt`, `Var src`, `Var dst`, `ce`] assume_tac) >>
     Cases_on `emit_op MLOAD [Var src] sa` >>
     drule emitted_insts_emit_op >> strip_tac >>
     gvs[comp_bind_def]) >>
  drule_all emit_word_copy_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`H`, `tf`, `z`] >> simp[] >>
  metis_tac[for_word_store_robust]
QED
