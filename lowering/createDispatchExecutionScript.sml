(* Exact execution of the production unchecked CREATE dispatch. The checked
   result CFG is handled separately; no preparation or callback is assumed. *)
Theory createDispatchExecution
Ancestors
  builtinCreate createOracleExecution emitHelperProps exprLoweringProps
  venomExecSemantics venomCallOracleDefs venomState venomInst compileEnv
  emitHelper option

Theorem compile_create_dispatch_unchecked_execution:
  ∀code_ptr code_len value_op salt cs result cs' s v p n salt_value.
  compile_create_dispatch code_ptr code_len value_op salt F cs = (result,cs') ∧
  eval_operand value_op s = SOME v ∧
  eval_operand code_ptr s = SOME p ∧ eval_operand code_len s = SOME n ∧
  OPTREL (λop w. eval_operand op s = SOME w) salt salt_value ⇒
  ∃out.
    result = Var out ∧
    let consumed = consume_create_outcome (venom_create_request s v p n salt_value) s in
    run_inst_seq (emitted_insts cs cs') s =
      OK (update_var out (FST consumed) (SND consumed)) ∧
    eval_operand result (update_var out (FST consumed) (SND consumed)) =
      SOME (FST consumed)
Proof
  rpt gen_tac >> Cases_on `salt` >> Cases_on `salt_value` >>
  simp[optionTheory.OPTREL_def, compile_create_dispatch_def,
       compile_check_create_result_def, comp_bind_def, comp_return_def,
       pairTheory.UNCURRY] >>
  rpt strip_tac >> imp_res_tac emitted_insts_emit_op >> gvs[] >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_create_def,
       eval_operand_update_var]
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createDispatchExecution");
