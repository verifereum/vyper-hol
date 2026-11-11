(* Total bounded outcomes for coherent, recursively width-valid types. *)
Theory abiMalformedWidthOutcome
Ancestors
  abiMalformedWidthDynamic abiMalformedOutcomeParents abiMalformedOutcomeContract
  abiMalformedBoundedContract abiMalformedParentContracts abiMalformedConstructorInduction
  abiDecoderCoherence vyperTypeSystem vyperTyping list rich_list

Theorem abi_malformed_width_coherent_outcome:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    abi_decode_bytes_widths env ty ==>
    abi_malformed_bounded_type_outcome ce env sf ty tv
Proof
  ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
  >- (rpt strip_tac >> irule abi_malformed_bounded_to_outcome >>
      irule abi_malformed_unbounded_implies_bounded >>
      irule abi_malformed_base_type_contract >> simp[])
  >- (rpt strip_tac >> irule abi_malformed_bounded_to_outcome >>
      irule abi_malformed_unbounded_implies_bounded >>
      irule abi_malformed_flag_type_contract >> simp[])
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume abi_malformed_width_coherent_outcome[array]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  `abi_decode_bytes_widths env ty` by fs[abi_decode_bytes_widths_def] >>
  Cases_on `bound`
  >- (irule abi_malformed_bounded_fixed_outcome >> simp[]) >>
  irule abi_malformed_width_dynamic_outcome >> simp[]
QED
Resume abi_malformed_width_coherent_outcome[tuple]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  irule abi_malformed_bounded_tuple_outcome >> simp[] >>
  fs[abi_decode_bytes_widths_def, LIST_REL_EL_EQN, EVERY_EL] >>
  rpt strip_tac >> metis_tac[]
QED
Resume abi_malformed_width_coherent_outcome[struct]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  irule abi_malformed_bounded_struct_outcome >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[abi_decode_bytes_widths_def, LIST_REL_EL_EQN, EVERY_EL, EVERY_MAP, EL_MAP] >>
  rpt strip_tac >> metis_tac[]
QED
Finalise abi_malformed_width_coherent_outcome
