(* TOP-LEVEL: compile_alloc_buffer emits the actual ALLOCA, exposing the
   result operand, instruction ID and precise compiler-state increments. *)
Theory abiBufferAllocationCode
Ancestors
  memoryValueSnapshot context compileEnv exprLoweringProps emitHelper emitHelperProps
  fragExec list rich_list words

Theorem compile_alloc_buffer_code:
  !byte_count cs buf cs'.
    compile_alloc_buffer byte_count cs = (buf,cs') ==>
    buf.buf_operand = Var (STRING #"%" (toString cs.cs_next_var)) /\ buf.buf_size = byte_count /\
    emitted_insts cs cs' = [mk_inst cs.cs_next_id ALLOCA [Lit (n2w byte_count)]
      [STRING #"%" (toString cs.cs_next_var)]] /\
    same_blocks cs cs' /\ cs'.cs_current_bb = cs.cs_current_bb /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    cs'.cs_next_var = cs.cs_next_var + 1 /\ cs'.cs_next_id = cs.cs_next_id + 1
Proof
  simp[compile_alloc_buffer_def, emit_op_def, fresh_id_def, fresh_var_def,
    emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, emitted_insts_def,
    same_blocks_def, DROP_APPEND1, DROP_LENGTH_NIL]
QED

Theorem compile_alloc_buffer_execution:
  !byte_count cs buf cs' ss.
    compile_alloc_buffer byte_count cs = (buf,cs') /\ byte_count < dimword(:256) ==>
    run_inst_seq (emitted_insts cs cs') ss =
      OK (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var byte_count ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_alloc_buffer_code >> strip_tac >>
  simp[run_inst_seq_def, memory_snapshot_allocation_step]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual buffer allocation code: " ^ name)
  end) (DB.thms "abiBufferAllocationCode")
