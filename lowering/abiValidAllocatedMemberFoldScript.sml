(* Successful allocated member traversal by contract composition. *)
Theory abiValidAllocatedMemberFold
Ancestors
  abiValidAllocatedMemberJoin abiValidAllocatedMemberEntry
  abiValidAllocatedMembers abiValidAllocatedContract abiDecoderMemberCons
  abiDecoderContract compileEnv venomState list

Theorem abi_valid_allocated_members_cons:
  abi_decoder_coherent ce env sf ty tv /\
  abi_valid_allocated_type_contract ce env sf ty tv /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  abi_valid_allocated_members_contract ce env sf tys tvs ==>
  abi_valid_allocated_members_contract ce env sf (ty::tys) (tv::tvs)
Proof
  strip_tac >>
  rewrite_tac[abi_valid_allocated_members_contract_def] >>
  rpt gen_tac >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_members_entry`
    (mp_tac o CONJUNCT2 o PURE_REWRITE_RULE [abi_valid_allocated_members_entry_def]) >>
  strip_tac >>
  drule abi_decoder_member_cons_trace >> strip_tac >>
  drule_all abi_valid_allocated_members_head_entry >> strip_tac >> gvs[] >>
  qhdtm_x_assum `abi_valid_allocated_type_contract`
    (mp_tac o PURE_REWRITE_RULE [abi_valid_allocated_type_contract_def]) >>
  disch_then drule >> strip_tac >>
  drule_all abi_valid_allocated_members_tail_entry >> strip_tac >>
  qhdtm_x_assum `abi_valid_allocated_members_contract`
    (mp_tac o PURE_REWRITE_RULE [abi_valid_allocated_members_contract_def]) >>
  disch_then drule >> strip_tac >>
  qexists_tac `t''` >>
  drule_all abi_valid_allocated_members_cons_post >> simp[]
QED

Theorem abi_valid_allocated_members_fold:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL (abi_valid_allocated_type_contract ce env sf) tys tvs ==>
  abi_valid_allocated_members_contract ce env sf tys tvs
Proof
  qid_spec_tac `tvs` >> Induct_on `tys` >>
  simp[LIST_REL_CONS1, abi_valid_allocated_members_nil] >>
  rpt strip_tac >> gvs[abi_valid_allocated_members_cons]
QED
