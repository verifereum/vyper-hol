(* Execute every actual remaining member under precise child hypotheses.
   TOP-LEVEL: abi_scratch_members_correct_all closes member-list recursion.
   Helpers isolate nonempty source structure and physical effect composition. *)
Theory abiScratchMembersCorrect
Ancestors
  abiScratchMembers abiScratchMembersAdvance abiScratchEncoderContract abiScratchAfterAddress
  abiScratchMembersInterpret abiScratchMembersIndex abiEncoderMemberSpine
  abiScratchEffect abiEncoderMemberCode abiEncoderInput abiDecoderMemberPhases
  abiDecoderDynamicLoopSetup abiDecoderLoop abiDecoderReentry abiDecoderContract fragExec
  compileEnv valueEncoding contractABI venomState list arithmetic

Theorem abi_scratch_members_inv_nonempty:
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) tys avs pre pvs active dyn_ptr site slot
    first last lo st limit_st src dst sb so ho d hl output_size b cap initial ==>
  tys <> [] /\ avs <> []
Proof
  strip_tac >> qpat_x_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  disch_then (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  simp_tac bool_ss [abi_encoder_complex_input_iff] >> rpt strip_tac >>
  Cases_on `tys` >> Cases_on `avs` >> gvs[abi_encoder_tuple_type_def]
QED

Theorem abi_scratch_members_compose:
  abi_decoder_address_frame next initial ready /\
  abi_scratch_effect first last lo mid child_next limit_st d sz b cap ready encoded /\
  abi_scratch_effect first last lo hi suffix_next limit_st d sz b cap encoded actual /\
  mid <= hi /\ next <= child_next /\ next <= suffix_next /\ first <= lo /\ hi <= last /\
  abi_decode_sim ctx func initial ready /\ abi_decode_sim ctx func ready encoded /\
  abi_decode_sim ctx func encoded actual ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual /\
  abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_effect first last lo hi next limit_st d sz b cap initial encoded` by
    (mp_tac (Q.INST [`child_lo` |-> `lo:num`, `child_hi` |-> `mid:num`,
       `child_next` |-> `child_next:num`, `child_d` |-> `d:num`, `child_sz` |-> `sz:num`,
       `actual` |-> `encoded:venom_state`] abi_scratch_effect_after_address) >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last lo hi next limit_st d sz b cap encoded actual` by
    (irule abi_scratch_effect_widen >> qexistsl_tac [`d`, `hi`, `lo`, `suffix_next`, `sz`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  conj_tac
  >- (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >> qexists_tac `encoded` >> simp[]) >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> simp[]
QED

Theorem abi_scratch_members_correct_instance[local]:
  !infos. abi_scratch_members_correct infos
Proof
  gen_tac >> simp_tac bool_ss [abi_scratch_members_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (Q.INST [`hi` |-> `end_st.cs_next_id`] abi_scratch_members_index_initial) >>
  disch_then (qspecl_then [`func`,`end_st`,`ctx`] assume_tac) >>
  `abi_encoder_spine_code func limit_st end_st.cs_next_id (dst,src,dyn_ptr)
    infos (st,so,ho) (out,end_st)` by
    simp[abi_encoder_spine_code_def] >>
  drule_all abi_scratch_members_generate >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac []
QED

Theorem abi_scratch_members_correct_cons:
  abi_scratch_members_correct infos ==>
  abi_scratch_members_correct ((ei,abi_sz,mem_sz,dyn)::infos)
Proof
  strip_tac >> MATCH_ACCEPT_TAC abi_scratch_members_correct_instance
QED

Theorem abi_scratch_members_correct_all:
  !infos. abi_scratch_members_correct infos
Proof
  MATCH_ACCEPT_TAC abi_scratch_members_correct_instance
QED
