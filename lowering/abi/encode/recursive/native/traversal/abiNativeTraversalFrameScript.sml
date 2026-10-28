(* TOP-LEVEL: extend exact enclosing memory and operand frames through an
   arbitrary recursive native result. Earlier scratch windows are retained
   in the later allocation map, including across cached loop iterations. *)
Theory abiNativeTraversalFrame
Ancestors
  abiNativeEncodingDefs abiNativeResources abiMemoryLeafRun abiFieldOperands
  abiAllocationWindows abiMemoryFrameCover abiMemoryFrame allocationGrowth
  compileAllocaProvenance compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_traversal_memory_step:
  !root_cs root_after root_dst root_payload initial ss out.
    abi_memory_frame ((w2n (root_dst:bytes32),LENGTH (root_payload:word8 list))::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) ss) initial ss /\
    allocation_growth ss out /\
    abi_memory_frame ((w2n root_dst,LENGTH root_payload)::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) ss out ==>
    abi_memory_frame ((w2n root_dst,LENGTH root_payload)::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) initial out
Proof
  rpt gen_tac >> strip_tac >>
  `abi_memory_frame ((w2n root_dst,LENGTH root_payload)::
    abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) initial ss` by
    (qspecl_then [`ss`, `out`, `compiler_alloca_ids root_cs root_after`,
       `compiler_alloca_ids root_cs root_after`, `(w2n root_dst,LENGTH root_payload)`, `initial`, `ss`]
       mp_tac abi_allocation_windows_frame_growth >> simp[]) >>
  irule abi_memory_frame_trans_same >> qexists_tac `ss` >> simp[]
QED

Theorem abi_native_traversal_operands_step:
  !ctx func root_cs cs mid ret dst_addr payload scratch initial ss out.
    root_cs.cs_next_var <= cs.cs_next_var /\
    (!arg_op. abi_operand_before root_cs.cs_next_var arg_op ==>
      eval_operand arg_op ss = eval_operand arg_op initial) /\
    abi_encoding_result ctx func cs mid ret (dst_addr:bytes32) payload scratch ss out ==>
    !arg_op. abi_operand_before root_cs.cs_next_var arg_op ==>
      eval_operand arg_op out = eval_operand arg_op initial
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  qx_gen_tac `arg_op` >> DISCH_TAC >>
  `abi_operand_before cs.cs_next_var arg_op` by
    (irule abi_operand_before_mono >> qexists_tac `root_cs.cs_next_var` >> simp[]) >>
  qpat_x_assum `!arg_op. abi_operand_before cs.cs_next_var arg_op ==> _`
    (qspec_then `arg_op` mp_tac) >>
  qpat_x_assum `!arg_op. abi_operand_before root_cs.cs_next_var arg_op ==> _`
    (qspec_then `arg_op` mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed enclosing native traversal frames: " ^ name)
  end) (DB.thms "abiNativeTraversalFrame")
