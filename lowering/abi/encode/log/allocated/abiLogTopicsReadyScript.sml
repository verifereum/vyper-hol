(* TOP-LEVEL: topic production preserves future allocation addresses and
   derives packing-name avoidance. APIs: copy_frame_allocation_address,
   log_args_before_names, log_topic_header. *)
Theory abiLogTopicsReady
Ancestors
  typedCopyStateFrame typedLogArgs abiFieldOperands abiAllocationFrame
  memoryValueSnapshot compileEnv venomState list pair words

Theorem log_args_before_names:
  !args bound start num_names.
    EVERY (\arg. abi_operand_before bound (FST arg)) args /\ bound <= start ==>
    log_args_avoid args (compiler_var_names start num_names)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [log_args_avoid_def, EVERY_MEM] >> qx_gen_tac `arg` >> DISCH_TAC >>
  mp_tac (Q.SPECL [`bound`, `FST (arg:operand # type)`, `start`, `num_names`] abi_operand_before_names) >>
  impl_tac >- fs[EVERY_MEM] >> simp_tac bool_ss [EVERY_MEM]
QED

Theorem copy_frame_allocation_address:
  !before after id var_base capacity output_id.
    copy_state_frame before after ==>
    memory_snapshot_addr output_id (memory_snapshot_allocated id var_base capacity after) =
      memory_snapshot_addr output_id (memory_snapshot_allocated id var_base capacity before)
Proof
  rpt gen_tac >> DISCH_TAC >> drule copy_state_frame_allocator >> strip_tac >>
  mp_tac (Q.SPECL [`before`, `after`, `id`, `capacity`] abi_allocation_frame_fields) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  simp[memory_snapshot_allocated_def, memory_snapshot_addr_def, update_var_def]
QED

Theorem log_topic_header:
  !bound ops ss topics sig_hash.
    EVERY (abi_operand_before bound) ops /\ eval_operands ops ss = SOME topics ==>
    EVERY (abi_operand_before bound) (Lit (n2w sig_hash)::ops) /\
    eval_operands (Lit (n2w sig_hash)::ops) ss = SOME (n2w sig_hash::topics)
Proof
  simp[eval_operands_def, eval_operand_def, abi_operand_before_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed topic-to-data preparation: " ^ name)
  end) (DB.thms "abiLogTopicsReady")
