(* TOP-LEVEL: the actual bytes/string materialization fragment preserves
   its typed source value, including reused allocation and SSA outputs. *)
Theory bytesSnapshotProps
Ancestors
  bytesSnapshotCode bytesSnapshotExec bytesSnapshotMemory memoryValueSnapshot
  memoryValueDefs valueLoadProps eventTopicValueProps abiBytestringCode
  compileEnv context exprLoweringProps fragBlockPath fragExec instIdxIndep
  venomState list words

Theorem compile_materialize_bytes_execution:
  !cenv ty src cs op cs' ss src_addr.
    is_bytestring_type ty /\
    compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') /\
    type_memory_bytes cenv ty < dimword(:256) /\
    eval_operand src ss = SOME src_addr /\
    EVERY (\name. src <> Var name) (compiler_var_names cs.cs_next_var 5) ==>
    run_inst_seq (emitted_insts cs cs') ss =
      OK (bytes_snapshot_result cs.cs_next_id cs.cs_next_var
        (type_memory_bytes cenv ty) src_addr ss)
Proof
  rpt strip_tac >> drule_all compile_materialize_bytes_code >> strip_tac >>
  simp[bytes_snapshot_execution]
QED

Theorem compile_materialize_bytes_path:
  !tenv ctx func cenv ty tv v src cs op cs' ss src_addr.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
    compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') /\
    type_memory_bytes cenv ty < dimword(:256) /\ type_memory_size tv < dimword(:256) /\
    lowered_value_rel ty tv v src ss /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. src <> Var name) (compiler_var_names cs.cs_next_var 5) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. out = (bytes_snapshot_result cs.cs_next_id cs.cs_next_var
        (type_memory_bytes cenv ty) src_addr ss with vs_inst_idx := LENGTH cs'.cs_current_insts) /\
      fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ lowered_value_rel ty tv v op out /\
      eval_operand op out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 5) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt strip_tac >> drule_all compile_materialize_bytes_execution >> strip_tac >>
  drule_all compile_materialize_bytes_code >> strip_tac >>
  `~is_word_type ty` by (drule_all bytestring_type_not_word >> simp[]) >>
  `memory_value_rel tv v (w2n src_addr) ss.vs_memory /\ value_has_type tv v` by
    gvs[lowered_value_rel_def] >>
  `memory_value_rel tv v (w2n (memory_snapshot_addr cs.cs_next_id ss))
    (bytes_snapshot_result cs.cs_next_id cs.cs_next_var
      (type_memory_bytes cenv ty) src_addr ss).vs_memory` by
    (mp_tac (Q.SPECL [`tenv`, `ty`, `tv`, `v`, `cs.cs_next_id`, `cs.cs_next_var`,
       `type_memory_bytes cenv ty`, `src_addr`, `ss`] bytes_snapshot_result_layout) >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`,
    `bytes_snapshot_result cs.cs_next_id cs.cs_next_var
      (type_memory_bytes cenv ty) src_addr ss`] fragment_path_emitted) >>
  impl_tac >- simp[bytes_snapshot_straight] >> strip_tac >>
  qexists_tac `(bytes_snapshot_result cs.cs_next_id cs.cs_next_var
    (type_memory_bytes cenv ty) src_addr ss) with
      vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  simp[lowered_value_rel_def, eval_op_inst_idx,
    SIMP_RULE (srw_ss()) [] bytes_snapshot_result_operand,
    bytes_snapshot_result_operand_frame]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed bytes/string snapshot path theorem: " ^ name)
  end) (DB.thms "bytesSnapshotProps")
