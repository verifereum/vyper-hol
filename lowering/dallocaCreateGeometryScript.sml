(* Stop at the consuming CREATE instruction, before the result checker can
   switch blocks. The allocation and CREATE share these actual SSA operands. *)
Theory dallocaCreateGeometry
Ancestors
  builtinCreate context exprLoweringProps emitHelper emitHelperProps compileEnv
  loweringStateRelDefs dallocaBounds
  venomExecSemantics venomInst venomState list rich_list words finite_map

(* Project away memory before simplifying an execution's repeated states. *)
val memory_field_rewrites = map
  (SIMP_CONV (srw_ss()) [mstore_def, write_memory_with_expansion_def])
  [``(mstore off value st).vs_vars``,
   ``(mstore off value st).vs_fmp``,
   ``(mstore off value st).vs_accounts``,
   ``(mstore off value st).vs_call_ctx``,
   ``(write_memory_with_expansion off data st).vs_vars``,
   ``(write_memory_with_expansion off data st).vs_fmp``,
   ``(write_memory_with_expansion off data st).vs_accounts``,
   ``(write_memory_with_expansion off data st).vs_call_ctx``];

Theorem create_copy_create_prefix:
  !target value salt rof sa result sb.
    compile_create_copy target value salt rof sa = (result,sb) ==>
    ?code a1 a2 shifted a3 preamble a4 size a5 alloc_ptr a6 a7
      code_dst a8 a9 buf a10 len sc created sd.
      emit_op EXTCODESIZE [target] sa = (code,a1) /\
      emit_void ASSERT [code] a1 = ((),a2) /\
      emit_op SHL [Lit 56w;code] a2 = (shifted,a3) /\
      emit_op OR [Lit 0x620000003d81600b3d39f3w;shifted] a3 =
        (preamble,a4) /\
      emit_op ADD [code;Lit 32w] a4 = (size,a5) /\
      compile_alloc_dynamic size a5 = (alloc_ptr,a6) /\
      emit_void MSTORE [alloc_ptr;preamble] a6 = ((),a7) /\
      emit_op ADD [alloc_ptr;Lit 32w] a7 = (code_dst,a8) /\
      emit_void EXTCODECOPY [target;code_dst;Lit 0w;code] a8 = ((),a9) /\
      emit_op ADD [alloc_ptr;Lit 21w] a9 = (buf,a10) /\
      emit_op ADD [code;Lit 11w] a10 = (len,sc) /\
      (case salt of NONE => emit_op CREATE [value;buf;len]
       | SOME salt_op => emit_op CREATE2 [value;buf;len;salt_op]) sc =
        (created,sd) /\
      compile_check_create_result created rof sd = (result,sb)
Proof
  rpt gen_tac >> Cases_on `salt` >>
  simp[compile_create_copy_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum $ drule_at Any)
QED

Theorem create_emit_completed_bound:
  !salt value buf len sc created sd s t.
    (case salt of NONE => emit_op CREATE [value;buf;len]
     | SOME salt_op => emit_op CREATE2 [value;buf;len;salt_op]) sc =
      (created,sd) /\
    run_inst_seq (emitted_insts sc sd) s = OK t ==>
    ?sz.
      eval_operand len s = SOME sz /\
      venomLayout$ceil32 (w2n sz) <= 65536 /\
      w2n (sz + 21w) = w2n sz + 21 /\
      venomLayout$ceil32 (w2n (sz + 21w)) <= 65536
Proof
  rpt gen_tac >> Cases_on `salt` >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> fs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[] >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      AllCaseEqs()] >>
  drule dalloca_completed_create_size_bound >> strip_tac >>
  drule dalloca_completed_copy_size_bound >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem create_copy_allocation_geometry:
  !target sa code a1 a2 shifted a3 preamble a4 size a5 alloc_ptr a6 a7
    code_dst a8 a9 buf a10 len sc s0 pre t.
    emit_op EXTCODESIZE [target] sa = (code,a1) /\
    emit_void ASSERT [code] a1 = ((),a2) /\
    emit_op SHL [Lit 56w;code] a2 = (shifted,a3) /\
    emit_op OR [Lit 0x620000003d81600b3d39f3w;shifted] a3 = (preamble,a4) /\
    emit_op ADD [code;Lit 32w] a4 = (size,a5) /\
    compile_alloc_dynamic size a5 = (alloc_ptr,a6) /\
    emit_void MSTORE [alloc_ptr;preamble] a6 = ((),a7) /\
    emit_op ADD [alloc_ptr;Lit 32w] a7 = (code_dst,a8) /\
    emit_void EXTCODECOPY [target;code_dst;Lit 0w;code] a8 = ((),a9) /\
    emit_op ADD [alloc_ptr;Lit 21w] a9 = (buf,a10) /\
    emit_op ADD [code;Lit 11w] a10 = (len,sc) /\
    run_inst_seq (emitted_insts a4 a5) s0 = OK pre /\
    run_inst_seq (emitted_insts a5 sc) pre = OK t ==>
    ?sz create_len.
      eval_operand size pre = SOME sz /\
      eval_operand buf t = SOME (pre.vs_fmp + 21w) /\
      eval_operand len t = SOME create_len /\ sz = create_len + 21w /\
      t.vs_fmp = pre.vs_fmp + n2w (venomLayout$ceil32 (w2n sz)) /\
      t.vs_accounts = pre.vs_accounts /\ t.vs_call_ctx = pre.vs_call_ctx
Proof
  rpt gen_tac >>
  simp[compile_alloc_dynamic_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> fs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ s0 = _` mp_tac >>
  qpat_x_assum `run_inst_seq _ pre = _` mp_tac >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >> rpt strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, exec_write2_def, bind_outputs_def, eval_operand_def,
      lookup_var_update_var, update_var_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE, fresh_var_distinct,
      AllCaseEqs()] >>
  gvs (memory_field_rewrites @ [lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, fresh_var_distinct]) >>
  simp[GSYM WORD_ADD_ASSOC, word_add_n2w]
QED

Theorem create_blueprint_allocation_geometry:
  !code args_len sa size sm alloc_ptr sn target offset se sc args_ptr pre t.
    emit_op ADD [code;args_len] sa = (size,sm) /\
    compile_alloc_dynamic size sm = (alloc_ptr,sn) /\
    emit_void EXTCODECOPY [target;alloc_ptr;offset;code] sn = ((),se) /\
    (if args_len = Lit 0w then sc = se else
       ?args_dest sx.
         emit_op ADD [alloc_ptr;code] se = (args_dest,sx) /\
         compile_copy_memory_dynamic args_dest args_ptr args_len sx = ((),sc)) /\
    run_inst_seq (emitted_insts sm sc) pre = OK t ==>
    ?sz.
      eval_operand size pre = SOME sz /\
      eval_operand size t = SOME sz /\
      eval_operand alloc_ptr t = SOME pre.vs_fmp /\
      t.vs_fmp = pre.vs_fmp + n2w (venomLayout$ceil32 (w2n sz)) /\
      t.vs_accounts = pre.vs_accounts /\ t.vs_call_ctx = pre.vs_call_ctx
Proof
  rpt gen_tac >> strip_tac >> Cases_on `args_len = Lit 0w` >> gvs[] >>
  fs[compile_alloc_dynamic_def, compile_copy_memory_dynamic_def,
     emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  gvs[] >> fs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, bind_outputs_def, eval_operand_def,
      lookup_var_update_var, update_var_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE, fresh_var_distinct,
      mcopy_def, write_memory_with_expansion_def, AllCaseEqs()]
QED

Theorem create_blueprint_create_prefix:
  !target value salt offset code args_ptr args_len rof sa result sb.
    compile_create_blueprint_append target value salt offset
      code args_ptr args_len rof sa = (result,sb) ==>
    ?size sm alloc_ptr sn se sc created sd.
      emit_op ADD [code;args_len] sa = (size,sm) /\
      compile_alloc_dynamic size sm = (alloc_ptr,sn) /\
      emit_void EXTCODECOPY [target;alloc_ptr;offset;code] sn = ((),se) /\
      (if args_len = Lit 0w then sc = se else
         ?args_dest sx.
           emit_op ADD [alloc_ptr;code] se = (args_dest,sx) /\
           compile_copy_memory_dynamic args_dest args_ptr args_len sx =
             ((),sc)) /\
      (case salt of NONE => emit_op CREATE [value;alloc_ptr;size]
       | SOME salt_op => emit_op CREATE2 [value;alloc_ptr;size;salt_op]) sc =
        (created,sd) /\
      compile_check_create_result created rof sd = (result,sb)
Proof
  rpt gen_tac >> Cases_on `salt` >> Cases_on `args_len = Lit 0w` >>
  simp[compile_create_blueprint_append_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum $ drule_at Any)
QED
