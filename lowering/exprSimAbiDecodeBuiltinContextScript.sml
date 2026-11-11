(* Initialize the owned recursive decoder after builtin setup. *)
Theory exprSimAbiDecodeBuiltinContext
Ancestors
  exprSimAbiDecodeBuiltinSetup exprSimAbiDecodeOwnedContext
  exprSimAbiDecodeCallerAudit exprSimAbiDecodeMemberExecute
  abiBuiltinDecodeSetup abiBuiltinSetupReach abiBuiltinAllocation
  abiDecoderSiteEffect actualDecoderSites abiDecoderFrame
  abiDecoderContract abiDecoderReentry abiDecoderCoherence
  compileEnv valueEncoding valueEncodingProps venomState
  words arithmetic list finite_map pred_set

Theorem abi_decode_builtin_context:
  abi_builtin_decode_setup data lo hi (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  st.cs_next_var <= ready.cs_next_var /\ ready.cs_next_var <= limit_st.cs_next_var /\
  abi_builtin_allocation_frame st.cs_next_var
    (abi_builtin_decode_output_site st lo hi) (type_memory_bytes ce ty) s t /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st lo hi) = NONE /\
      d = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st lo hi) =
      SOME(d,type_memory_bytes ce ty)) /\
  eval_operand (FST ops) t = SOME(n2w d) /\
  eval_operand (FST (SND ops)) t = SOME(n2w(p+32)) /\
  eval_operand (SND (SND ops)) t = SOME(n2w(LENGTH bs)) /\
  fresh_vars_wrt limit_st t /\ abi_decode_entry ready t /\
  decode_site_resources ctx func s /\ decode_site_resources ctx func t /\
  fn_inst_ids_distinct func /\
  bs = mem_bytes_at (p+32) (LENGTH bs) s.vs_memory /\
  p+32+LENGTH bs <= s.vs_alloca_next /\
  p+32+LENGTH bs < dimword(:256) /\
  d+type_memory_bytes ce ty < dimword(:256) /\
  (!clamp. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp ==>
    32 <= LENGTH bs) /\
  abi_footprint_disjoint (p+32) (LENGTH bs) [(d,type_memory_bytes ce ty)] /\
  (!id b sz. id IN abi_decode_sites ready.cs_next_id last /\
    FLOOKUP s.vs_allocas id = SOME(b,sz) ==>
    abi_footprint_disjoint (p+32) (LENGTH bs) [(b,sz)]) /\
  scratch = ({a | t.vs_alloca_next <= a} UNION
    {a | ?id b sz. id IN abi_decode_sites ready.cs_next_id last /\
      FLOOKUP t.vs_allocas id = SOME(b,sz) /\ b <= a /\ a < b+sz}) ==>
  abi_decode_owned (abi_decode_sites ready.cs_next_id last) scratch
    d (type_memory_bytes ce ty) t /\
  abi_decode_context_pre ctx func ce env ty tv limit_st st.cs_next_var
    (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce ty})
    (abi_decode_sites ready.cs_next_id last) ready
    (FST ops) (Lit 0w) (FST (SND ops)) (SND (SND ops)) (p+32) bs 0 d t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `alloca_inv s` by fs[decode_site_resources_def] >>
  `abi_builtin_decode_output_site st lo hi NOTIN abi_decode_sites ready.cs_next_id last`
    by metis_tac[abi_decode_setup_output_excluded] >>
  `abi_decode_owned (abi_decode_sites ready.cs_next_id last) scratch
     d (type_memory_bytes ce ty) t` by
    (gvs[] >> irule abi_decode_builtin_setup_ownership >> metis_tac[]) >>
  drule_all abi_decode_setup_source_sites >> strip_tac >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  drule abi_builtin_decode_setup_bounded_operands >> strip_tac >>
  `abi_decode_site_writes (abi_decode_sites ready.cs_next_id last)
      d (type_memory_bytes ce ty) t SUBSET
    scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce ty}` by
    metis_tac[abi_decode_owned_writes] >>
  `t.vs_memory = s.vs_memory` by fs[abi_builtin_allocation_frame_def] >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (drule abi_decode_builtin_setup_progress >>
     simp[exprSimAbiDecodeSiteProvenanceTheory.abi_decode_alloc_progress_def]) >>
  `!a. p+32 <= a /\ a < p+32+LENGTH bs ==>
    ~(d <= a /\ a < d+type_memory_bytes ce ty)` by
    (fs[abi_footprint_disjoint_def] >> rpt strip_tac >> decide_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[abi_decode_context_pre_def, abi_decoder_operand_live_def, eval_operand_def] >>
  rpt conj_tac >- metis_tac[] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
