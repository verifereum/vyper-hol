(* Counted constructor single-word writes, including zero headers. *)
Theory immutableDeployAssignWord
Ancestors
  immutableCopyExecution placeTypedCopyPath context compileEnv
  venomState venomInst fragExec exprLoweringProps

Theorem immutable_assign_word_path:
  compile_imm_store_word (SOME region) dst value sa = ((),sb) /\
  eval_operand region s = SOME 0w /\ eval_operand dst s = SOME a /\
  eval_operand value s = SOME v /\ fresh_vars_wrt sa s /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. immutable_execution_frame sa s sb u /\
    gas_marked_path F ctx func s 0
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    u.vs_memory = (mstore (w2n a) v s).vs_memory /\
    u.vs_immutables = s.vs_immutables |+ (w2n a,v)
Proof
  strip_tac >> drule_all immutable_store_execution_frame >> strip_tac >>
  qexists_tac `s'` >> simp[] >>
  irule place_copy_seq_path >> simp[] >> qexists_tac `sa` >>
  fs[immutable_execution_frame_def] >>
  drule compile_imm_store_word_result >> strip_tac >>
  simp[emitted_insts_def, listTheory.DROP_APPEND, mk_inst_def,
       is_terminator_def]
QED
