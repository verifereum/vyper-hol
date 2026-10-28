(* TOP-LEVEL: the final LOG leaves the encoder's actual scratch allocation
   profile unchanged, so complete log code and its encoder share readiness. *)
Theory abiNativeLogCode
Ancestors
  abiNativeEncodingDefs compileAllocaProvenance emitHelperProps compileEnv
  venomInst list

Theorem compiler_alloca_ids_emit_LOG:
  !root_cs mid cs' ops outs.
    emit_inst LOG ops outs mid = ((),cs') ==>
    compiler_alloca_ids root_cs cs' = compiler_alloca_ids root_cs mid
Proof
  rpt gen_tac >> DISCH_TAC >> drule emit_inst_extends >> strip_tac >>
  simp[compiler_alloca_ids_def, FILTER_APPEND_DISTRIB, mk_inst_def]
QED

Theorem abi_native_log_ready:
  !func root_cs mid cs' ops outs source_id target_id src_addr span dst_addr payload ss.
    emit_inst LOG ops outs mid = ((),cs') ==>
    (abi_native_memory_ready func root_cs cs' source_id target_id src_addr span dst_addr payload ss <=>
     abi_native_memory_ready func root_cs mid source_id target_id src_addr span dst_addr payload ss)
Proof
  rpt gen_tac >> DISCH_TAC >> drule compiler_alloca_ids_emit_LOG >>
  disch_then (qspec_then `root_cs` ASSUME_TAC) >> simp[abi_native_memory_ready_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native LOG allocation profile: " ^ name)
  end) (DB.thms "abiNativeLogCode")
