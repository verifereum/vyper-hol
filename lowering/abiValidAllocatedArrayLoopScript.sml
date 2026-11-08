(* Successful typed-prefix traversal of allocated decoder arrays. *)
Theory abiValidAllocatedArrayLoop
Ancestors
  abiValidAllocatedArrayPrefix abiValidAllocatedArraySource abiValidAllocatedMembers
  abiMalformedTraversal abiMalformedRecursiveInterface abiMalformedSiteFrame
  abiDecoderExecution abiDecoderLoop abiDecoderContract abiDecoderReentry
  abiValidAllocatedContract abiDecoderArrayBackedge
  exprSimDefs exprLoweringProps compileEnv venomState venomMemDefs venomMemProps
  valueEncodingProps valueEncoding venomExecSemantics finite_map pred_set words list arithmetic

Theorem abi_valid_allocated_backedge_effect:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\ st.cs_next_var <= first /\ first <= next /\
  next < ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (slot,32) /\ inst.inst_id IN sites ==>
  abi_valid_allocated_effect ctx func cenv cx es first sites dstid 0 0 s
    (jump_to hdr (mstore slot w (update_var (STRING #"%" (toString next)) w s))) /\
  fresh_vars_wrt ceiling
    (jump_to hdr (mstore slot w (update_var (STRING #"%" (toString next)) w s)))
Proof
  strip_tac >> drule_all abi_malformed_backedge_resource >>
  disch_then (qspecl_then [`w`, `hdr`, `dstid`] strip_assume_tac) >>
  simp[abi_valid_allocated_effect_def] >>
  simp[jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  simp[abi_valid_allocated_frame_def] >> rpt strip_tac >>
  `a+1 <= slot \/ slot+32 <= a` by
    (qpat_x_assum `~abi_malformed_site_range _ _ _ _ _` mp_tac >>
     simp[abi_malformed_site_range_def, jump_to_def, mstore_def,
       update_var_def, write_memory_with_expansion_def] >>
     rpt strip_tac >>
     Cases_on `a+1 <= slot \/ slot+32 <= a` >> simp[] >>
     `slot <= a /\ a+1 <= slot+32` by decide_tac >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `s`, `w` |-> `w`, `p` |-> `slot`,
    `q` |-> `a`, `n` |-> `1`] mstore_mem_bytes_at_disjoint) >>
  simp[mstore_def, update_var_def, write_memory_with_expansion_def]
QED
