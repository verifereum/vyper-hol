Theory createSizeBlueprintExtent
Ancestors
  dallocaCreateGeometry builtinCreate context compileEnv emitHelper emitHelperProps
  exprLoweringProps loweringStateRelDefs venomExecSemantics venomInst venomState
  vyperCreate list rich_list words integer_word finite_map arithmetic

(* EXTCODESIZE samples the size after constructor and keyword evaluation.
   The literal guard tests the signed difference word. *)
Theorem create_blueprint_checked_code[local]:
  compile_create_blueprint_check lit target off ca = (code,cb) /\
  run_inst_seq (emitted_insts ca cb) s = OK t /\
  eval_operand target s = SOME addr /\ eval_operand off s = SOME ow /\
  (!x. off = Var x ==> not_fresh_at ca x) ==>
  eval_operand code t = SOME
    (n2w (blueprint_copy_size (w2n ow)
      (lookup_account (w2w addr) s.vs_accounts).code)) /\
  (if lit then blueprint_size_ok
      (blueprint_copy_size (w2n ow)
        (lookup_account (w2w addr) s.vs_accounts).code)
   else w2n ow < LENGTH (lookup_account (w2w addr) s.vs_accounts).code)
Proof
  Cases_on `lit` >>
  simp[compile_create_blueprint_check_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> fs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[] >> strip_tac >>
  Cases_on `off` >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_read1_def, exec_pure2_def, bind_outputs_def, eval_operand_def,
      lookup_var_update_var, update_var_def, lookup_var_def,
      FLOOKUP_UPDATE, fresh_var_distinct, not_fresh_at_def, AllCaseEqs()] >>
  gvs[blueprint_copy_size_def, blueprint_size_ok_def,
      venomExecProofsTheory.bool_to_word_neq_0w,
      WORD_GREATER, WORD_LTi, word_0_w2i] >>
  metis_tac[MOD_LESS_EQ, ZERO_LT_dimword, LESS_LESS_EQ_TRANS, GREATER_DEF]
QED

Theorem create_blueprint_args_add[local]:
  emit_op ADD [code;args_len] sa = (size_op,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK pre /\
  eval_operand code s = SOME cw /\ eval_operand args_len s = SOME aw ==>
  eval_operand size_op pre = SOME (cw + aw)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> fs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[] >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, bind_outputs_def, eval_operand_def,
      lookup_var_update_var, update_var_def, lookup_var_def,
      FLOOKUP_UPDATE, AllCaseEqs()]
QED

(* The size operand at the CREATE/CREATE2 cut is the same SSA operand
   as at the initial ADD; allocation and copying do not replace it. *)
Theorem create_blueprint_pre_dispatch_extent:
  compile_create_blueprint_check lit target off ca = (code,cb) /\
  run_inst_seq (emitted_insts ca cb) s = OK t /\
  eval_operand target s = SOME addr /\ eval_operand off s = SOME ow /\
  (!x. off = Var x ==> not_fresh_at ca x) /\
  dest_create_args (CreateFromBlueprint F) has_salt vs = SOME ops /\
  ops.co_code_src = AddressCodeSource (w2w addr) /\
  ops.co_code_offset = SOME (w2n ow) /\ accounts = s.vs_accounts /\
  eval_operand code u = eval_operand code t /\
  eval_operand args_len u = SOME (n2w (LENGTH args_enc)) /\
  emit_op ADD [code;args_len] sa = (size_op,sm) /\
  run_inst_seq (emitted_insts sa sm) u = OK pre /\
  compile_alloc_dynamic size_op sm = (alloc_ptr,sn) /\
  emit_void EXTCODECOPY [target;alloc_ptr;off;code] sn = ((),se) /\
  (if args_len = Lit 0w then sc = se else
     ?args_dest sx.
       emit_op ADD [alloc_ptr;code] se = (args_dest,sx) /\
       compile_copy_memory_dynamic args_dest args_ptr args_len sx = ((),sc)) /\
  run_inst_seq (emitted_insts sm sc) pre = OK final ==>
  ?n w. blueprint_prefix_size has_salt lit vs accounts = SOME n /\
        eval_operand size_op final = SOME w /\ w2n w <= n + LENGTH args_enc
Proof
  strip_tac >>
  drule_all create_blueprint_checked_code >> strip_tac >>
  drule_all create_blueprint_allocation_geometry >> strip_tac >>
  fs[] >> drule_all create_blueprint_args_add >>
  simp[blueprint_prefix_size_def, word_add_n2w, w2n_n2w] >>
  metis_tac[MOD_LESS_EQ, ZERO_LT_dimword]
QED
