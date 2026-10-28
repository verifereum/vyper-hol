(* TOP-LEVEL: the actual recursive Log encoder writes only into nonlocal
   allocation slots. Their runtime records are private after allocation
   growth, including cached slots and nested recursive scratch buffers. *)
Theory abiNativeLogPrivacy
Ancestors
  abiAllocaProvenance abiNativeLogCode abiLogCode sourceAllocationPrivacy
  sourceMemoryFrames sourceAbiFrames allocationGrowth abiAllocationWindows
  compileAllocaProvenance compileEnv fragExec venomState list words

Theorem compile_log_abi_emit_writer_instructions:
  !dst src info topics cs cs' func cenv scopes.
    compile_log_abi_emit dst src info topics cs = ((),cs') /\ fn_has_code cs cs' func /\
    (!name entry p capacity. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) capacity) ==> abi_operand_before cs.cs_next_var (Var p)) ==>
    !id. MEM id (compiler_alloca_ids cs cs') ==> ?inst q.
      MEM inst (fn_insts func) /\ inst.inst_id = id /\ inst.inst_outputs = [q] /\ not_local_ptr cenv scopes q
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_log_abi_emit _ _ _ _ _ = _` (mp_tac o REWRITE_RULE [compile_log_abi_emit_split]) >>
  disch_then (qx_choose_then `size_op` (qx_choose_then `mid` strip_assume_tac)) >>
  drule_all compile_log_abi_emit_code >> strip_tac >>
  `compiler_alloca_ids cs cs' = compiler_alloca_ids cs mid` by
    (qspecl_then [`cs`, `mid`, `cs'`, `Lit (n2w (LENGTH topics))::REVERSE topics ++ [size_op;dst]`, `[]`]
       mp_tac compiler_alloca_ids_emit_LOG >> simp[]) >>
  qspecl_then [`dst`, `src`, `info`, `cs`, `size_op`, `mid`, `func`, `cenv`, `scopes`]
    mp_tac compile_abi_encode_writer_instructions >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qpat_x_assum `compiler_alloca_ids cs cs' = _` (fn th => PURE_REWRITE_TAC [th]) >> first_assum MATCH_ACCEPT_TAC
QED

Theorem compile_log_scratch_writes_private:
  !dst src info topics cs cs' func cenv scopes before after.
    compile_log_abi_emit dst src info topics cs = ((),cs') /\ fn_has_code cs cs' func /\
    (!name entry p capacity. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) capacity) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    allocation_growth before after /\ alloca_inv after /\ fn_inst_ids_distinct func /\
    local_ptrs_rel func cenv scopes before /\
    source_alloca_floor cenv scopes (compiler_alloca_ids cs cs') before ==>
    source_writes_separated cenv scopes before (abi_allocation_windows (compiler_alloca_ids cs cs') after)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`dst`, `src`, `info`, `topics`, `cs`, `cs'`, `func`, `cenv`, `scopes`]
    mp_tac compile_log_abi_emit_writer_instructions >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qspecl_then [`func`, `cenv`, `scopes`, `compiler_alloca_ids cs cs'`, `before`, `after`]
    mp_tac source_profile_writes_private >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native Log scratch privacy: " ^ name)
  end) (DB.thms "abiNativeLogPrivacy")
