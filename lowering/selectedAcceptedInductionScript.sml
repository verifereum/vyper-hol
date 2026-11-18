(* Constructor induction for accepted decoding, leaving only the nonbulk loop. *)
Theory selectedAcceptedInduction
Ancestors
  selectedAcceptedAtomic selectedAcceptedBulk selectedAcceptedMembers
  selectedAcceptedInterfaces calldataRecursiveProducers abiDecoderCoherence
  vyperAST vyperValue compileEnv exprLowering abiEncoder list finite_map

Triviality coherent_output_unique:
  abi_decoder_coherent ce env sf ty u /\ abi_decoder_coherent ce env sf ty v ==>
  u = v
Proof
  metis_tac[abi_decoder_coherent_header, abi_decoder_header_def, optionTheory.SOME_11]
QED

(* Transport the indexed child IH to the member runner's coherent outputs. *)
Triviality coherent_children_accept:
  LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
                    selected_decoder_accepts ce env sf ty tv) tys tvs /\
  LIST_REL (abi_decoder_coherent ce env sf) tys uvs ==>
  LIST_REL (selected_decoder_accepts ce env sf) tys uvs
Proof
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  metis_tac[coherent_output_unique]
QED

Theorem selected_argument_decoder_accepts_from_nonbulk:
  (!ce env sf ty tv maxn ei asz msz dyn.
    abi_decoder_coherent ce env sf ty tv /\
    selected_decoder_accepts ce env sf ty tv /\
    abi_decoder_header ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
    type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
      DecDynArray ei asz msz dyn maxn /\ (dyn \/ dec_info_needs_clamp ei) ==>
    selected_decoder_accepts ce env sf (ArrayT ty (Dynamic maxn))
      (ArrayTV tv (Dynamic maxn))) ==>
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    selected_decoder_accepts ce env sf ty tv
Proof
  strip_tac >> ho_match_mp_tac calldata_coherent_induction >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (irule selected_atomic_accepts >> Cases_on `bt` >>
      gvs[is_word_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bound` >> Cases_on `bound` >>
      gvs[is_word_type_def, is_bytestring_type_def, abi_decoder_scalar_valid_def])
  >- (irule selected_atomic_accepts >> simp[is_word_type_def])
  >- (Cases_on `bound`
      >- (match_mp_tac (cj 3 selected_members_accepts) >> conj_tac
          >- (irule abiDecoderCoherenceTheory.array >> simp[]) >>
          qpat_x_assum `!ce env sf ty tv maxn ei asz msz dyn. _` kall_tac >>
          metis_tac[coherent_output_unique]) >>
      rename1 `ArrayT ty (Dynamic maxn)` >>
      Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
                dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
      >- (first_x_assum match_mp_tac >> simp[type_to_abi_dec_info_def]) >>
      irule selected_bulk_accepts >> gvs[type_to_abi_dec_info_def])
  >- (match_mp_tac (cj 1 selected_members_accepts) >> conj_tac
      >- (irule abiDecoderCoherenceTheory.tuple >>
          gvs[LIST_REL_CONJ, SF ETA_ss]) >>
      metis_tac[coherent_children_accept]) >>
  match_mp_tac (cj 2 selected_members_accepts) >> conj_tac
  >- (irule abiDecoderCoherenceTheory.struct_case >>
      gvs[LIST_REL_CONJ, SF ETA_ss] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[coherent_children_accept]
QED
