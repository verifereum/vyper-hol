(* TOP-LEVEL: an actual recursive result advances the shared enclosing
   traversal invariant. Compiler history/extensions are supplied by the
   real remaining compiler action, separately from runtime preservation. *)
Theory abiNativeTraversalStep
Ancestors
  abiNativeTraversal abiNativeTraversalFrame abiNativeEncodingDefs abiNativeResources abiMemoryLeafRun
  abiAllocationWindows abiAllocationTrace abiStateFrame allocationPathGrowth
  compileAllocaProfiles compileAllocaProvenance compileIdFlow compileEnv fragExec fragBlockPath venomMemDefs venomState list words arithmetic

Theorem abi_native_traversal_step:
  !ctx func root_cs root_after root_dst root_payload initial cs mid ret dst_addr payload scratch ss out.
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial cs ss /\
    alloca_inv initial /\
    abi_encoding_result ctx func cs mid ret (dst_addr:bytes32) payload scratch ss out /\
    abi_allocation_trace 32 (compiler_alloca_ids cs mid) ss out /\
    abi_memory_frame ((w2n root_dst,LENGTH root_payload)::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) ss out /\
    cs_extends cs mid /\ cs_extends mid root_after /\
    cs.cs_next_var <= mid.cs_next_var /\ compiler_id_history mid ==>
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial mid out
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_traversal_allocation >> strip_tac >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  qpat_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  `allocation_growth ss out` by
    (qspecl_then [`ctx`, `func`, `ss`, `out`] mp_tac fragment_path_allocation_growth >> simp[]) >>
  `abi_memory_frame ((w2n root_dst,LENGTH root_payload)::
    abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) initial out` by
    (drule_all abi_native_traversal_memory_step >> simp[]) >>
  `set (compiler_alloca_ids cs mid) SUBSET set (compiler_alloca_ids root_cs root_after)` by
    (irule compiler_alloca_profile_subprofile >> simp[]) >>
  `abi_allocation_trace 32 (compiler_alloca_ids root_cs root_after) ss out` by
    (drule_all abi_allocation_trace_weaken >> simp[]) >>
  `abi_allocation_trace 32 (compiler_alloca_ids root_cs root_after) initial out` by
    (irule abi_allocation_trace_trans >> qexists_tac `ss` >> simp[]) >>
  `!arg_op. abi_operand_before root_cs.cs_next_var arg_op ==>
    eval_operand arg_op out = eval_operand arg_op initial` by
    (qspecl_then [`ctx`, `func`, `root_cs`, `cs`, `mid`, `ret`, `dst_addr`, `payload`,
       `scratch`, `initial`, `ss`, `out`] mp_tac abi_native_traversal_operands_step >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `fragment_path ctx func initial out` by
    (irule fragment_path_trans >> qexists_tac `ss` >> simp[]) >>
  `abi_state_frame initial out` by
    (irule abi_state_frame_trans >> qexists_tac `ss` >> simp[]) >>
  `cs_extends root_cs mid` by
    (irule cs_extends_trans >> qexists_tac `cs` >> simp[]) >>
  `root_cs.cs_next_var <= mid.cs_next_var` by decide_tac >>
  PURE_REWRITE_TAC [abi_native_traversal_def] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_traversal_native_step:
  !ctx func root_cs root_after root_dst root_payload initial cs mid ret dst_addr payload ss out.
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial cs ss /\
    alloca_inv initial /\
    abi_native_encoding_result ctx func cs mid ret (dst_addr:bytes32) payload ss out /\
    cs_extends cs mid /\ cs_extends mid root_after /\
    cs.cs_next_var <= mid.cs_next_var /\ compiler_id_history mid /\
    w2n root_dst <= w2n dst_addr /\
    w2n dst_addr + LENGTH payload <= w2n root_dst + LENGTH root_payload ==>
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial mid out
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends root_cs cs` by
    (qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
     first_assum MATCH_ACCEPT_TAC) >>
  `abi_memory_frame ((w2n root_dst,LENGTH root_payload)::
    abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) ss out` by
    (qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `dst_addr`, `payload`, `ss`, `out`,
       `root_cs`, `root_after`, `root_dst`, `root_payload`]
       mp_tac abi_native_result_enclosing_frame >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qpat_x_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def]) >>
  drule_all abi_native_traversal_step >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native traversal advancement: " ^ name)
  end) (DB.thms "abiNativeTraversalStep")
