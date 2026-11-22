Theory entryBlueprintRawLength
Ancestors
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv context stmtReasonMemory
  venomExecSemantics venomState venomInst list rich_list words

(* Only the two instructions after unwrap are replayed here. In particular,
   the MLOAD's input state is the output of the snapshot/unwrap prefix,
   and the load result is not the buffer's data pointer. *)
Theorem raw_blueprint_length_suffix[local]:
  cfn ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_create_blueprint_args cfn ce T later [e] ca = ((data,len),cb) /\
  eval_operand raw_op u = SOME p /\
  run_inst_seq (emitted_insts cu cb) u = OK r ==>
  len = Var (STRING #"%" (toString cu.cs_next_var)) /\
  eval_operand len r = SOME (mload (w2n p) u)
Proof
  strip_tac >>
  qpat_x_assum `compile_create_blueprint_args _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_create_blueprint_args_def, comp_bind_def, comp_return_def] >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> fs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ u = OK _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_def, step_mload_eq, step_add_eq, AllCaseEqs()] >>
  strip_tac >> gvs[eval_operand_def, lookup_var_update_var, fresh_var_distinct]
QED

(* The unchecked-prefix producer need only validate the actual header word
   at unwrap and show that the length's SSA binding reaches the extent ADD.
   It need not establish representation of the payload beyond the header. *)
Theorem raw_blueprint_length_at_add:
  cfn ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_create_blueprint_args cfn ce T later [e] ca = ((data,len),cb) /\
  eval_operand raw_op u = SOME p /\
  w2n (mload (w2n p) u) < 2 ** 64 /\
  run_inst_seq (emitted_insts cu cb) u = OK r /\
  (!x. len = Var x ==> lookup_var x t = lookup_var x r) ==>
  ?aw. eval_operand len t = SOME aw /\ w2n aw < 2 ** 64
Proof
  strip_tac >> drule_all raw_blueprint_length_suffix >> strip_tac >>
  qexists_tac `mload (w2n p) u` >> gvs[eval_operand_def]
QED
