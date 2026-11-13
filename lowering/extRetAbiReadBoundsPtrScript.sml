(* Capacity and allocation coverage of semantic encoder reads. *)
Theory extRetAbiReadBoundsPtr
Ancestors
  extRetAbiReadCleanPtr abiEncoderInput ptrCoverage bodyPtrDefs
  words finite_map list arithmetic

Theorem abi_encoder_read_window_bounds:
  !ei av sb a n. abi_encoder_read_window ei av sb a n ==>
    !at cap mem. abi_encoder_input ei at av sb cap mem ==>
      sb <= a /\ a+n <= sb+cap
Proof
  ho_match_mp_tac abi_encoder_read_window_ind >> rpt conj_tac
  >- simp[abi_encoder_input_word_iff]
  >- simp[abi_encoder_input_copy_iff]
  >- simp[abi_encoder_input_bytes_iff]
  >- simp[abi_encoder_input_bytes_iff]
  >- (simp[abi_encoder_array_input_iff] >> rpt strip_tac >> decide_tac)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[abi_encoder_array_input_iff] >> strip_tac >>
      first_x_assum (qspecl_then [`ct`, `mem_sz`, `mem`] mp_tac) >>
      impl_tac >- simp[AC ADD_COMM ADD_ASSOC] >>
      `32 + LENGTH avs * mem_sz <= cap` by simp[MULT_COMM] >>
      drule_all abi_encoder_array_slot_bound >> decide_tac)
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[abi_encoder_complex_input_iff] >> strip_tac >>
  qpat_x_assum `!at cap mem. _`
    (qspecl_then [`EL i ats`, `mem_sz`, `mem`] mp_tac) >>
  impl_tac >- metis_tac[] >>
  drule_all abi_encoder_member_slot_bound >> decide_tac
QED

Theorem abi_encoder_read_window_covers:
  !ei av sb a n at cap mem G tn p s w b sz q s' G' tn'.
    abi_encoder_read_window ei av sb a n /\
    abi_encoder_input ei at av sb cap mem /\ 0 < n /\
    ptr_covers G tn p s cap /\ lookup_var p s = SOME w /\
    sb = w2n w /\ FLOOKUP G p = SOME (b,sz) /\
    b+sz <= dimword(:256) /\
    lookup_var q s' = SOME (w+n2w (a-sb)) /\
    FLOOKUP G' q = SOME (b,sz) /\ op_taint tn' (Var q) = {} ==>
    ptr_covers G' tn' q s' n
Proof
  rpt strip_tac >> drule_all abi_encoder_read_window_bounds >> strip_tac >>
  `a-sb < cap /\ (a-sb)+n <= cap` by decide_tac >>
  irule ptr_covers_offset >> metis_tac[]
QED
