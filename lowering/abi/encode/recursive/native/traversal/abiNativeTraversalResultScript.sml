(* TOP-LEVEL: close an enclosing traversal as a native result once its
   final control position, return value and bytes are known. A containing
   output arena may also include an earlier length header. *)
Theory abiNativeTraversalResult
Ancestors
  abiNativeTraversal abiNativeEncodingDefs abiMemoryLeafRun abiMemoryFrameCover abiMemoryFrame
  abiAllocationWindows compileAllocaProvenance compileEnv venomState list words arithmetic

Theorem abi_native_traversal_result:
  !ctx func root_cs root_after root_dst root_payload initial point ss ret dst_addr payload.
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial point ss /\
    w2n (dst_addr:bytes32) <= w2n root_dst /\
    w2n root_dst + LENGTH root_payload <= w2n dst_addr + LENGTH (payload:word8 list) /\
    ss.vs_current_bb = root_after.cs_current_bb /\ ss.vs_inst_idx = LENGTH root_after.cs_current_insts /\
    eval_operand ret ss = SOME (n2w (LENGTH payload)) /\ read_memory (w2n dst_addr) (LENGTH payload) ss = payload ==>
    abi_native_encoding_result ctx func root_cs root_after ret dst_addr payload initial ss
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  `abi_memory_frame ((w2n dst_addr,LENGTH payload)::abi_allocation_windows (compiler_alloca_ids root_cs root_after) ss) initial ss` by
    (irule abi_memory_frame_cover >>
     qexists_tac `(w2n root_dst,LENGTH root_payload)::abi_allocation_windows (compiler_alloca_ids root_cs root_after) ss` >>
     conj_tac >- (
       simp_tac bool_ss [abi_writes_cover_def, MEM] >> MAP_EVERY qx_gen_tac [`write_base`, `write_len`] >> strip_tac
       >- (gvs[] >> qexistsl_tac [`w2n dst_addr`, `LENGTH payload`] >> simp[]) >>
       qexistsl_tac [`write_base`, `write_len`] >> simp[]) >> first_assum MATCH_ACCEPT_TAC) >>
  PURE_REWRITE_TAC [abi_native_encoding_result_def, abi_encoding_result_def] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed enclosing traversal to complete native result: " ^ name)
  end) (DB.thms "abiNativeTraversalResult")
