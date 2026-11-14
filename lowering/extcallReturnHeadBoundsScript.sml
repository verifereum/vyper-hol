(* A typed nonvoid return has a positive checked ABI head. *)
Theory extcallReturnHeadBounds
Ancestors
  abiDecoderLayoutBounds exprSimAbiDecodeComplexOutcome abiDecoderCoherence
  compileEnv vyperABI vyperTypeSystem list arithmetic

Theorem return_wrapped_head_positive:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty ==>
  0 < abi_static_size ce.ce_struct_fields
    (if needs_external_call_wrap ty then TupleT [ty] else ty)
Proof
  strip_tac >> Cases_on `needs_external_call_wrap ty`
  >- (simp[Once abi_static_size_def, GSYM abi_embedded_static_size_def] >>
      irule abi_decode_assignable_embedded_head_positive >> metis_tac[]) >>
  Cases_on `ty` >> gvs[needs_external_call_wrap_def] >>
  rename1 `TupleT tys` >>
  `tys <> []` by (Cases_on `tys` >> gvs[]) >>
  `?tvs. LIST_REL (abi_decoder_coherent ce env sf) tys tvs` by
    metis_tac[abi_decoder_coherent_tuple_iff] >>
  `EVERY (assignable_type env) tys` by
    gvs[assignable_type_def] >>
  simp[Once abi_static_size_def, GSYM abi_embedded_static_size_def] >>
  irule abi_decode_nonempty_positive_head_sum >> simp[] >>
  gvs[EVERY_EL, LIST_REL_EL_EQN] >> rpt strip_tac >>
  irule abi_decode_assignable_embedded_head_positive >> metis_tac[]
QED

Theorem return_wrapped_capacity_positive:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty ==>
  0 < abi_size_bound ce.ce_struct_fields
    (if needs_external_call_wrap ty then TupleT [ty] else ty)
Proof
  strip_tac >> drule_all return_wrapped_head_positive >> strip_tac >>
  metis_tac[abi_static_size_le_size_bound, LESS_LESS_EQ_TRANS]
QED
