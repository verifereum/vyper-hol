(* The CopyOf prefix ends before allocation, so its size bound needs no
   FMP room or allocation-history invariant. *)
Theory dallocaCreateCopy
Ancestors
  builtinCreate context exprLoweringProps emitHelper emitHelperProps compileEnv
  dallocaCreateGeometry loweringStateRelDefs
  venomExecSemantics venomInst venomState list rich_list words finite_map

Theorem create_copy_alloc_prefix:
  !target value salt rof sa result sb.
    compile_create_copy target value salt rof sa = (result,sb) ==>
    ?code a1 a2 shifted a3 preamble a4 size a5 ptr a6.
      emit_op EXTCODESIZE [target] sa = (code,a1) /\
      emit_void ASSERT [code] a1 = ((),a2) /\
      emit_op SHL [Lit 56w;code] a2 = (shifted,a3) /\
      emit_op OR
        [Lit 0x620000003d81600b3d39f3w;shifted] a3 = (preamble,a4) /\
      emit_op ADD [code;Lit 32w] a4 = (size,a5) /\
      compile_alloc_dynamic size a5 = (ptr,a6)
Proof
  rpt gen_tac >> strip_tac >>
  drule create_copy_create_prefix >>
  disch_then (qx_choosel_then
    [`code`,`a1`,`a2`,`shifted`,`a3`,`preamble`,`a4`,`total_size`,`a5`,
     `alloc_ptr`,`a6`,`a7`,`code_dst`,`a8`,`a9`,`buf`,`a10`,`len`,`sc`,
     `created`,`sd`] strip_assume_tac) >>
  qexistsl_tac [`code`,`a1`,`a2`,`shifted`,`a3`,`preamble`,`a4`,
    `total_size`,`a5`,`alloc_ptr`,`a6`] >> simp[]
QED

Theorem create_copy_prefix:
  !target sa code a1 a2 shifted a3 preamble a4 size a5 s addr t.
    emit_op EXTCODESIZE [target] sa = (code,a1) /\
    emit_void ASSERT [code] a1 = ((),a2) /\
    emit_op SHL [Lit 56w;code] a2 = (shifted,a3) /\
    emit_op OR
      [Lit 0x620000003d81600b3d39f3w;shifted] a3 = (preamble,a4) /\
    emit_op ADD [code;Lit 32w] a4 = (size,a5) /\
    eval_operand target s = SOME addr /\
    LENGTH (lookup_account (w2w addr) s.vs_accounts).code <= 24576 /\
    run_inst_seq (emitted_insts sa a5) s = OK t ==>
    eval_operand size t =
      SOME (n2w (LENGTH (lookup_account (w2w addr) s.vs_accounts).code + 32)) /\
    t.vs_accounts = s.vs_accounts /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_fmp = s.vs_fmp /\
    w2n (n2w (LENGTH (lookup_account (w2w addr) s.vs_accounts).code + 32)
      : bytes32) <= 24608 /\
    w2n (n2w (LENGTH (lookup_account (w2w addr) s.vs_accounts).code + 32)
      : bytes32) < 2 ** 64
Proof
  rpt gen_tac >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  fs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[] >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_read1_def, exec_pure2_def, bind_outputs_def, eval_operand_def,
      lookup_var_update_var, update_var_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE, fresh_var_distinct, AllCaseEqs()] >>
  `LENGTH (lookup_account (w2w addr) s.vs_accounts).code + 32 < dimword (:256)` by
    (fs[dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >> decide_tac) >>
  simp[word_add_n2w, w2n_n2w] >> decide_tac
QED
