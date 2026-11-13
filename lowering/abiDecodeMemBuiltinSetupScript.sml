(* Actual allocation reservations at the builtin decoder's memory entry. *)
Theory abiDecodeMemBuiltinSetup
Ancestors
  abiDecodeMemHeader exprSimAbiDecodeBuiltin exprSimAbiDecodeOwnedContext
  exprSimAbiDecodeSiteOwnership exprSimAbiDecodeBuiltinSetup
  exprSimAbiDecodeSiteProvenance abiBuiltinDecodeSetup abiBuiltinSetupReach
  abiBuiltinAllocation actualDecoderSites abiDecoderSiteEffect abiDecoderFrame
  abiDecoderContract allocaSiteResource valueEncoding valueEncodingProps
  exprLoweringProps abiDecoderReentry valueEncodingDefs
  compileEnv context venomState finite_map words list pred_set arithmetic

Theorem abi_decode_mem_setup_resources:
  abi_builtin_decode_setup data lo hi outsz st = (ops,ready) /\
  abi_builtin_decode_site_resources ctx func st last lo hi outsz (LENGTH bs) p d s /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
  abi_builtin_allocation_frame st.cs_next_var
    (abi_builtin_decode_output_site st lo hi) outsz s t /\
  decode_site_resources ctx func t ==>
  p+32+LENGTH bs < dimword(:256) /\
  p+32+LENGTH bs <= t.vs_alloca_next /\
  mem_bytes_at (p+32) (LENGTH bs) t.vs_memory = bs /\
  d+outsz < dimword(:256) /\ d+outsz <= t.vs_alloca_next /\
  (p+32+LENGTH bs <= d \/ d+outsz <= p+32) /\
  FLOOKUP t.vs_allocas (abi_builtin_decode_output_site st lo hi) = SOME(d,outsz) /\
  abi_builtin_decode_output_site st lo hi < ready.cs_next_id /\
  (!id b sz. ready.cs_next_id <= id /\ id < last /\
    FLOOKUP t.vs_allocas id = SOME(b,sz) ==>
    p+32+LENGTH bs <= b \/ b+sz <= p+32) /\
  EVERY (abi_decoder_operand_live ready.cs_next_var)
    [Lit 0w; FST ops; FST (SND ops); SND (SND ops)] /\
  FST (SND ops) <> Lit 0w /\ SND (SND ops) <> Lit 0w
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_builtin_decode_site_resources _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_builtin_decode_site_resources_def] >> strip_tac >>
  `s.vs_alloca_next < dimword(:256)` by
    (irule alloca_room_next_lt >> metis_tac[decode_site_resources_def]) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (drule abi_decode_builtin_setup_progress >>
     simp[abi_decode_alloc_progress_def]) >>
  `FLOOKUP t.vs_allocas (abi_builtin_decode_output_site st lo hi) = SOME(d,outsz)` by
    metis_tac[abi_decode_setup_output_registered] >>
  `d+outsz <= t.vs_alloca_next` by
    metis_tac[decode_site_resources_alloca_below] >>
  `t.vs_memory = s.vs_memory` by fs[abi_builtin_allocation_frame_def] >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  drule abi_builtin_decode_setup_bounded_operands >> strip_tac >>
  `!id. ready.cs_next_id <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id` by
    (rpt strip_tac >> irule abi_builtin_allocation_frame_outside >>
     goal_assum (drule_at Any) >> decide_tac) >>
  `st.cs_next_id <= ready.cs_next_id` by
    simp[abi_builtin_decode_output_site_def] >>
  `!id b sz. ready.cs_next_id <= id /\ id < last /\
    FLOOKUP t.vs_allocas id = SOME(b,sz) ==>
    abi_footprint_disjoint (p+32) (LENGTH bs) [(b,sz)]` by
    (rpt strip_tac >>
     `st.cs_next_id <= id` by decide_tac >>
     `FLOOKUP s.vs_allocas id = SOME(b,sz)` by metis_tac[] >>
     qpat_assum `!id b sz. st.cs_next_id <= id /\ _ ==> _` drule_all >> simp[]) >>
  gvs[val_in_memory_def, abi_footprint_disjoint_def,
      abi_decoder_operand_live_def] >>
  rpt conj_tac >> rpt strip_tac >>
  qpat_assum `!id b sz. _ /\ _ /\ FLOOKUP t.vs_allocas id = _ ==> _` drule_all >>
  simp[]
QED
