(* Relate scratch footprints to the existing caller-facing decoder effects. *)
Theory abiDecodeMemSiteEffect
Ancestors
  exprSimAbiDecodeImmutableFrame abiDecoderFrame abiDecoderSiteEffect
  exprSimAbiDecodeEndpointFrame allocationGrowth actualDecoderSites
  valueEncodingProps finite_map pred_set arithmetic list

Theorem abi_decode_footprint_memory_frame:
  abi_decode_footprint_frame fp s t /\
  (!b n a. MEM (b,n) fp /\ b <= a /\ a < b+n ==> a IN writes) ==>
  decode_memory_frame writes s t
Proof
  strip_tac >> rw[decode_memory_frame_def] >>
  irule abi_decode_window_bytewise >> rpt strip_tac >>
  `abi_footprint_disjoint i 1 fp` by
    (rw[abi_footprint_disjoint_def] >>
     Cases_on `i+1 <= d \/ d+sz <= i` >- simp[] >>
     `d <= i /\ i < d+sz` by decide_tac >>
     `i IN writes` by metis_tac[] >>
     qpat_x_assum `!a. p <= a /\ _ ==> a NOTIN writes`
       (qspec_then `i` mp_tac) >> asm_rewrite_tac[] >> decide_tac) >>
  drule_all abi_decode_footprint_frame_slice >> simp[]
QED

Theorem abi_decode_footprint_upper_frame:
  abi_decode_footprint_frame fp s t /\
  (!b n. MEM (b,n) fp ==> b+n <= t.vs_alloca_next) ==>
  decode_upper_frame s t
Proof
  strip_tac >> rewrite_tac[decode_upper_frame_def] >>
  irule abi_decode_footprint_memory_frame >> qexists_tac `fp` >>
  asm_rewrite_tac[] >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> decide_tac
QED

Theorem abi_decode_allocation_growth_floor:
  allocation_growth s t ==>
  abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas t
Proof
  strip_tac >> simp_tac bool_ss [abi_decode_allocation_floor_def] >>
  conj_tac >- metis_tac[allocation_growth_next] >>
  rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas aid`
  >- metis_tac[allocation_growth_new] >>
  drule_all allocation_growth_old >> simp[]
QED

Theorem abi_decode_footprint_site_effect:
  decode_site_resources ctx fn t /\ allocation_growth s t /\
  decode_static_frame s t /\
  (!op. abi_decoder_operand_live next op ==> eval_operand op t = eval_operand op s) /\
  abi_decode_footprint_frame fp s t /\
  (!b n a. MEM (b,n) fp /\ b <= a /\ a < b+n ==> a IN writes) /\
  (!b n. MEM (b,n) fp ==> b+n <= t.vs_alloca_next) ==>
  decode_site_effect ctx fn next writes s t
Proof
  strip_tac >> simp_tac bool_ss [decode_site_effect_def] >>
  rpt conj_tac >>
  metis_tac[allocation_growth_old, allocation_growth_next,
    abi_decode_footprint_memory_frame, abi_decode_footprint_upper_frame]
QED
