(* Guard-mode consistency for checker-admitted constructor headers. Vyper's
   frontend rejects explicit guarded constructors, but the HOL checker also
   admits consistent nonpayable/payable/view constructors after AST mutation. *)
Theory constructorGuardProps
Ancestors
  moduleLowering context compileEnv venomInst vyperCompiler

Definition constructor_guard_env_def:
  constructor_guard_env is_view = (ARB : compile_env) with
    ce_nonreentrant := (T,global_nonreentrant_slot,T,is_view)
End

(* The constructor body ends in a jump to its shared exit block, which holds
   the unlock and the epilogue, so the opcodes are read across both blocks. *)
Definition deploy_opcodes_def:
  deploy_opcodes (st : compile_state) =
    MAP (\i. i.inst_opcode)
      (FLAT (MAP (\bb. bb.bb_instructions) (REVERSE st.cs_blocks)) ++
       st.cs_current_insts)
End

Theorem constructor_guard_view_opcodes:
  deploy_opcodes
    (SND (compile_generate_deploy T 1 0 [] 0 []
      (constructor_guard_env T) [] T T global_nonreentrant_slot T
      (initial_compile_state "entry"))) =
    [TLOAD; EQ; ISZERO; ASSERT; JMP; ALLOCA; CODECOPY; RETURN]
Proof
  simp[deploy_opcodes_def, compile_generate_deploy_def, constructor_guard_env_def,
       fresh_label_def, new_block_def,
       compile_register_constructor_args_def,
       stmtLoweringTheory.compile_stmt_def, compile_internal_fn_bodies_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, comp_get_def,
       compile_nonreentrant_lock_def, compile_nonreentrant_unlock_def,
       compile_constructor_epilogue_def, global_nonreentrant_slot_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_inst_def,
       emitHelperTheory.emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       initial_compile_state_def, block_is_terminated_def] >>
  EVAL_TAC
QED

Theorem constructor_guard_mutable_opcodes:
  deploy_opcodes
    (SND (compile_generate_deploy T 1 0 [] 0 []
      (constructor_guard_env F) [] T T global_nonreentrant_slot T
      (initial_compile_state "entry"))) =
    [TLOAD; EQ; ISZERO; ASSERT; TSTORE; JMP; TSTORE; ALLOCA; CODECOPY; RETURN]
Proof
  simp[deploy_opcodes_def, compile_generate_deploy_def, constructor_guard_env_def,
       fresh_label_def, new_block_def,
       compile_register_constructor_args_def,
       stmtLoweringTheory.compile_stmt_def, compile_internal_fn_bodies_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, comp_get_def,
       compile_nonreentrant_lock_def, compile_nonreentrant_unlock_def,
       compile_constructor_epilogue_def, global_nonreentrant_slot_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_inst_def,
       emitHelperTheory.emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       initial_compile_state_def, block_is_terminated_def] >>
  EVAL_TAC
QED
