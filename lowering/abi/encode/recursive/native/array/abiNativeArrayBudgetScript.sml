(* TOP-LEVEL: actual enclosing traversal traces retain the complete root
   budget, compatible cached requests and owned input/output at any cut. *)
Theory abiNativeArrayBudget
Ancestors
  abiNativeTraversal abiNativeResources abiNativeEncodingDefs compileEnv fragExec venomState list words arithmetic

Theorem abi_native_traversal_root_ready:
  !ctx func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload initial cs ss.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr payload initial cs ss ==>
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload ss
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  qspecl_then [`func`, `root_cs`, `root_after`, `source_id`, `target_id`, `root_addr`, `source_capacity`,
    `dst_addr`, `payload`, `initial`, `root_cs`, `root_after`, `ss`, `root_addr`, `source_capacity`, `dst_addr`, `payload`]
    mp_tac abi_native_child_ready >> impl_tac >- asm_simp_tac (srw_ss()) [cs_extends_refl] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed retained native root allocation readiness: " ^ name)
  end) (DB.thms "abiNativeArrayBudget")
