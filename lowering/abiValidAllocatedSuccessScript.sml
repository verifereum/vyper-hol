(* Successful allocation-backed decoding for every coherent type: the
   decoder success induction the extcall return seam consumes. *)
Theory abiValidAllocatedSuccess
Ancestors
  abiValidAllocatedMembers abiValidAllocatedLeaves abiValidAllocatedAggregate
  abiValidAllocatedDynamic abiDecoderCoherence abiValidAllocatedContract
  exprLowering list

Theorem abi_valid_allocated_success:
  !ce env sf ty tv. abi_valid_allocated_type_contract ce env sf ty tv
Proof
  `!ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
      abi_valid_allocated_type_contract ce env sf ty tv` by
    (ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
     >- (rpt gen_tac >> strip_tac >>
         rewrite_tac[abi_valid_allocated_type_contract_def] >>
         rpt gen_tac >> strip_tac >>
         Cases_on `bt` >>
         TRY (rename1 `BytesT bound` >> Cases_on `bound`) >>
         qmatch_goalsub_abbrev_tac `type_memory_bytes ce ty` >>
         FIRST
           [(`?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp`
               by simp[Abbr `ty`, type_to_abi_dec_info_def]) >>
            drule_all abi_valid_allocated_primitive_reach >>
            strip_tac >> qexists_tac `t` >> simp[],
            drule_at Any abi_valid_allocated_bytes_reach >>
            disch_then (qspec_then `n` mp_tac) >> simp[] >>
            strip_tac >> qexists_tac `t` >> simp[]])
     >- (rpt gen_tac >> strip_tac >>
         rewrite_tac[abi_valid_allocated_type_contract_def] >>
         rpt gen_tac >> strip_tac >>
         metis_tac[abi_valid_allocated_primitive_reach, type_to_abi_dec_info_def])
     >- (rpt gen_tac >> strip_tac >> Cases_on `bound` >>
         FIRST [irule abi_valid_allocated_dynamic_array,
                irule abi_valid_allocated_fixed_array] >> simp[])
     >- (rpt strip_tac >> irule abi_valid_allocated_tuple >>
         fs[LIST_REL_CONJ, SF ETA_ss]) >>
     rpt strip_tac >> irule abi_valid_allocated_struct >> fs[LIST_REL_CONJ, SF ETA_ss]) >>
  rpt gen_tac >> Cases_on `abi_decoder_coherent ce env sf ty tv`
  >- metis_tac[] >>
  simp[abi_valid_allocated_type_contract_def, abi_valid_allocated_entry_def]
QED
