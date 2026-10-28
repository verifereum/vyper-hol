(* TOP-LEVEL: runtime loop edges retain the enclosing traversal without
   treating repeated child code as fresh compilation. The compiler context
   can be selected again from a genuine enclosing compiler prefix. *)
Theory abiNativeTraversalLoop
Ancestors
  abiNativeTraversal abiNativeTraversalFrame abiAllocationTrace abiAllocationWindows abiStateFrame
  abiMemoryFrame abiFieldOperands allocationPathGrowth compileAllocaProvenance compileIdFlow compileEnv
  fragExec fragBlockPath venomMemDefs venomState list words arithmetic

Theorem abi_native_traversal_context:
  !ctx func root_cs root_after root_dst root_payload initial cs ss next_cs.
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial cs ss /\
    cs_extends root_cs next_cs /\ root_cs.cs_next_var <= next_cs.cs_next_var /\ compiler_id_history next_cs ==>
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial next_cs ss
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_traversal_def] >> strip_tac >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_traversal_runtime_step:
  !ctx func root_cs root_after root_dst root_payload initial cs ss out.
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial cs ss /\ alloca_inv initial /\
    fragment_path ctx func ss out /\
    abi_allocation_trace 32 (compiler_alloca_ids root_cs root_after) ss out /\
    abi_memory_frame ((w2n root_dst,LENGTH root_payload)::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) ss out /\
    (!arg_op. abi_operand_before root_cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
    abi_state_frame ss out ==>
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial cs out
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_traversal_allocation >> strip_tac >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  `allocation_growth ss out` by
    (qspecl_then [`ctx`, `func`, `ss`, `out`] mp_tac fragment_path_allocation_growth >> simp[]) >>
  `abi_memory_frame ((w2n root_dst,LENGTH root_payload)::
    abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) initial out` by
    (drule_all abi_native_traversal_memory_step >> simp[]) >>
  `abi_allocation_trace 32 (compiler_alloca_ids root_cs root_after) initial out` by
    (irule abi_allocation_trace_trans >> qexists_tac `ss` >> simp[]) >>
  `fragment_path ctx func initial out` by
    (irule fragment_path_trans >> qexists_tac `ss` >> simp[]) >>
  `abi_state_frame initial out` by
    (irule abi_state_frame_trans >> qexists_tac `ss` >> simp[]) >>
  `!arg_op. abi_operand_before root_cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op initial` by
    (rpt gen_tac >> DISCH_TAC >>
     qpat_assum `!arg_op. abi_operand_before _ _ ==> eval_operand _ out = eval_operand _ ss`
       (qspec_then `arg_op` mp_tac) >>
     qpat_assum `!arg_op. abi_operand_before _ _ ==> eval_operand _ ss = eval_operand _ initial`
       (qspec_then `arg_op` mp_tac) >> simp[]) >>
  PURE_REWRITE_TAC [abi_native_traversal_def] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native traversal across actual runtime loop edges: " ^ name)
  end) (DB.thms "abiNativeTraversalLoop")
