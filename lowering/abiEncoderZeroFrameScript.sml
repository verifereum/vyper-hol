(* Zero-aware observation of padded memory windows. *)
Theory abiEncoderZeroFrame
Ancestors
  abiDecoderFrame abiEncoderOpenInputFrame valueEncoding valueEncodingProofs
  venomMemDefs venomState list arithmetic

Theorem abi_encoder_mem_bytes_singletons:
  (!a. p <= a /\ a < p+n ==>
    mem_bytes_at a 1 m = mem_bytes_at a 1 m') ==>
  mem_bytes_at p n m = mem_bytes_at p n m'
Proof
  strip_tac >> irule LIST_EQ >> simp[LENGTH_mem_bytes_at_proof] >>
  qx_gen_tac `index` >> strip_tac >>
  first_x_assum (qspec_then `p+index` mp_tac) >> simp[] >>
  disch_then (mp_tac o Q.AP_TERM `EL 0`) >>
  simp[EL_mem_bytes_at]
QED

Theorem abi_encoder_footprint_frame_zero_slice:
  abi_decode_footprint_frame ((d,sz)::fp) s t /\
  regions_disjoint (p,n) (d,sz) /\ abi_footprint_disjoint p n fp ==>
  mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
Proof
  strip_tac >> irule abi_encoder_mem_bytes_singletons >> rpt strip_tac >>
  irule abi_decode_footprint_frame_slice >>
  goal_assum (drule_at Any) >>
  simp_tac bool_ss [abi_footprint_disjoint_def, MEM] >>
  rpt gen_tac >> strip_tac
  >- (gvs[abi_encoder_zero_aware_separation] >> decide_tac) >>
  qpat_x_assum `abi_footprint_disjoint _ _ _`
    (mp_tac o PURE_REWRITE_RULE [abi_footprint_disjoint_def]) >>
  disch_then drule >> decide_tac
QED
