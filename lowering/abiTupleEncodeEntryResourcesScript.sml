(* Incoming resource conditions need only the tuple producer's predicted ID;
   the real staged compiler state supplies the same allocation site. *)
Theory abiTupleEncodeEntryResources
Ancestors
  abiTupleEncodeCounters abiBuiltinEncodeResources compileEnv
  venomState words list arithmetic

Theorem abi_tuple_encode_resources_site:
  compile_alloc_buffer n st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) ==>
  (abi_builtin_encode_resources staged method_id_opt sb source_cap p maxlen first last b cap s <=>
   abi_builtin_encode_resources
     (st with cs_next_id := st.cs_next_id+1+abi_tuple_encode_inst_count ce (MAP SND xs))
     method_id_opt sb source_cap p maxlen first last b cap s)
Proof
  strip_tac >> drule_all abi_tuple_encode_stage_id >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_builtin_encode_resources_def, LET_THM]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_TUPLE_ENCODE_ENTRY_RESOURCES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI tuple encoder resource site not kernel closed: " ^ n)
  end) (DB.thms "abiTupleEncodeEntryResources");
