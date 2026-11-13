(* Recover caller bytes from the decoder's actual allocation footprint. *)
Theory extcallReturnDecoderCallerMemory
Ancestors
  exprSimAbiDecodeLocalSeparation exprSimAbiDecodeResources
  exprSimAbiDecodeCoverageMutual exprSimAbiDecodeCoverageActions
  exprSimAbiDecodeSuffixWrites exprSimAbiGasBridge
  allocationGrowth abiDecoderFrame localPtrsProps exprLoweringProps
  loweringStateRelDefs compileEnv venomState venomInst finite_map list arithmetic

Theorem extcall_return_decoder_interval_instruction[local]:
  compile_abi_decode_to_buf dst src opc base_op hi info st = ((),fin) /\
  fn_has_code st fin func /\ local_ptrs_reserved ce st /\
  st.cs_next_id <= id /\ id < fin.cs_next_id ==>
  ?i. MEM i (fn_insts func) /\ i.inst_id = id /\
    !q. MEM q i.inst_outputs ==> not_local_ptr ce scopes q
Proof
  strip_tac >>
  `cs_extends st fin /\ ?i. MEM i (frag_code st fin) /\ i.inst_id = id` by
    (mp_tac (cj 1 abi_decode_id_coverage_mutual) >>
     simp[abi_decode_id_coverage_def] >> metis_tac[]) >>
  `!i q. MEM i (frag_code st fin) /\ MEM q i.inst_outputs ==>
    ?n. st.cs_next_var <= n /\ q = STRING #"%" (toString n)` by
    (mp_tac (cj 1 abi_decode_fresh_writes_mutual) >>
     simp[abi_decode_fresh_writes_def] >> metis_tac[]) >>
  qexists_tac `i` >> conj_tac
  >- metis_tac[abi_decode_resources_code_member] >>
  simp[] >> metis_tac[local_ptrs_reserved_fresh]
QED

Theorem extcall_return_decoder_local_bytes:
  compile_abi_decode_to_buf dst src opc base_op hi info st = ((),fin) /\
  fn_has_code st fin func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ local_ptrs_rel func ce scopes s /\
  alloca_inv t /\ allocation_growth s t /\
  abi_decode_footprint_frame ((d,outsize)::afp) s t /\
  (!b sz. MEM (b,sz) afp ==> ?inst.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    st.cs_next_id <= inst.inst_id /\ inst.inst_id < fin.cs_next_id /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz)) /\
  (!name lo len. local_region ce scopes s name lo len ==>
    d+outsize <= lo \/ lo+len <= d) ==>
  !name lo len. local_region ce scopes s name lo len ==>
    mem_bytes_at lo len t.vs_memory = mem_bytes_at lo len s.vs_memory
Proof
  strip_tac >>
  qabbrev_tac `u = s with <|vs_allocas := t.vs_allocas;
    vs_alloca_next := t.vs_alloca_next|>` >>
  `alloca_inv u` by
    (irule alloca_inv_fields >> qexists_tac `t` >> simp[Abbr `u`]) >>
  `local_ptrs_rel func ce scopes u` by
    (irule local_ptrs_rel_frame >> qexists_tac `s` >>
     fs[Abbr `u`, allocation_growth_def, lookup_var_def] >> metis_tac[]) >>
  `!name lo len. local_region ce scopes u name lo len <=>
    local_region ce scopes s name lo len` by
    simp[Abbr `u`, local_region_def, lookup_var_def] >>
  suspend "bytes"
QED

Resume extcall_return_decoder_local_bytes[bytes]:
  markerLib.RESUME_TAC >> rpt gen_tac >> strip_tac >>
  `!id. st.cs_next_id <= id /\ id < fin.cs_next_id ==>
    ?i. MEM i (fn_insts func) /\ i.inst_id = id /\
      !q. MEM q i.inst_outputs ==> not_local_ptr ce scopes q` by
    metis_tac[extcall_return_decoder_interval_instruction] >>
  `!id b sz. st.cs_next_id <= id /\ id < fin.cs_next_id /\
    FLOOKUP u.vs_allocas id = SOME (b,sz) ==>
    regions_disjoint b sz lo len` by
    (rpt gen_tac >> strip_tac >> irule abi_decode_interval_local_disjoint >>
     qexistsl_tac [`ce`,`st.cs_next_id`,`func`,`id`,`fin.cs_next_id`,
       `name`,`u`,`scopes`] >> simp[]) >>
  fs[abi_decode_footprint_frame_def] >> first_x_assum irule >>
  rw[abi_footprint_disjoint_def]
  >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!b sz. MEM (b,sz) afp ==> _` drule >> strip_tac >>
  `regions_disjoint d' sz lo len` by
    (qpat_x_assum `!id b sz. _` irule >>
     qexists_tac `inst.inst_id` >> fs[Abbr `u`]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Finalise extcall_return_decoder_local_bytes
