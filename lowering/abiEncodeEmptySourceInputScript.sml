(* Address-independent input closure for empty live source windows. *)
Theory abiEncodeEmptySourceInput
Ancestors
  abiEncoderWindow abiEncoderInput contractABI list arithmetic

Theorem empty_source_window_rebase_ind[local]:
  !ei at av sb cap mem.
    abi_encoder_window_input ei at av sb cap mem ==>
    cap = 0 ==> !db mem'. abi_encoder_window_input ei at av db 0 mem'
Proof
  ho_match_mp_tac abi_encoder_window_input_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[]
  >- (rpt gen_tac >> irule window_copy >> gvs[valueEncodingTheory.mem_bytes_at_def])
  >> rpt gen_tac >> irule window_complex >> qexists_tac `ats` >>
  simp[] >> rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qexists_tac `0` >> simp[]
QED

Theorem empty_source_window_rebase:
  abi_encoder_window_input ei at av sb 0 mem ==>
  abi_encoder_window_input ei at av db 0 mem'
Proof
  metis_tac[empty_source_window_rebase_ind]
QED

Theorem empty_source_complex_child:
  abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb 0 mem /\
  i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
  ?ats. abi_encoder_tuple_type at ats /\
    LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
    abi_sz = abi_member_head_size (EL i ats) /\
    dyn = is_dynamic (EL i ats) /\
    abi_encoder_member_span (TAKE i infos) = 0 /\
    !db mem'. abi_encoder_window_input ei (EL i ats) (EL i avs) db 0 mem'
Proof
  strip_tac >> drule_all abi_encoder_window_complex_child >> strip_tac >>
  `child_cap = 0 /\ abi_encoder_member_span (TAKE i infos) = 0` by decide_tac >>
  gvs[] >> qexists_tac `ats` >> simp[] >>
  metis_tac[empty_source_window_rebase]
QED
