Theory abiDecoderCorrectLeaves
Ancestors
  abiDecoderCorrect abiDecoderReentryPointer abiDecoderPrimitiveCaller abiDecoderEffect
  abiDecoderProtectedScratch abiDecoderAllocation abiDecoderCoherence abiDecoderTypedContract
  abiDecoderArrayInitExec abiDecoderReentry abiDecoderContract abiDecoderLoop abiDecoderFrame
  fragExec compileEnv emitHelperProps valueEncoding venomState words list exprLowering
  vyperValue vyperAST

(* Primitive word decoders satisfy the same recursive allocation/frame contract. *)
Theorem abi_decoder_scratch_free_effect:
  fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\
  abi_decode_frame d sz s t /\ t.vs_halted = s.vs_halted /\ (d + sz <= b \/ b + cap <= d) ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_budget first last b cap t` by
    (mp_tac abi_decoder_budget_transport >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(d,sz);(b,cap)] s t` by
    (irule abi_decoder_frame_from_output >> simp[]) >>
  mp_tac (Q.INST [`outsz` |-> `sz:num`] abi_decoder_bulk_scratch_preservation) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  asm_simp_tac bool_ss [abi_decoder_effect_def, abi_decoder_scratch_frame_def] >>
  rpt strip_tac >> `id IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >> metis_tac[]
QED

Theorem abi_decoder_correct_word:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==> abi_decoder_correct ce env sf ty tv
Proof
  strip_tac >> simp_tac bool_ss [abi_decoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[Excl "enc_def"] >>
  (drule abi_decoder_primitive_source >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_pre_output_separated >> disch_then assume_tac >>
  drule_all abi_decoder_primitive_reentry_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
    `lo` |-> `start.cs_next_id`, `hi` |-> `end_st.cs_next_id`, `next` |-> `start.cs_next_var`,
    `sz` |-> `type_memory_bytes ce ty`] abi_decoder_scratch_free_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac bool_ss [] >> metis_tac[])
QED

(* Bytes and String satisfy the recursive decoder contract without allocation. *)
Theorem abi_decoder_correct_bytestring:
  type_to_abi_dec_info sf ce ty = DecBytestring n ==> abi_decoder_correct ce env sf ty tv
Proof
  strip_tac >> simp_tac bool_ss [abi_decoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[Excl "enc_def"] >>
  (qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_pre_output_separated >> disch_then assume_tac >>
  drule_all abi_decoder_bytestring_reentry_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
    `lo` |-> `start.cs_next_id`, `hi` |-> `end_st.cs_next_id`, `next` |-> `start.cs_next_var`,
    `sz` |-> `type_memory_bytes ce ty`] abi_decoder_scratch_free_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [])
QED

(* Primitive, Bytes, String and flag cases of the recursive correctness theorem. *)
Theorem abi_decoder_correct_base:
  abi_decoder_correct ce env sf (BaseT bt) (BaseTV bt)
Proof
  `(?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp) \/
   (?n. type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring n)` by
    (Cases_on `bt` >> simp[type_to_abi_dec_info_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def]) >>
  FIRST [drule_all abi_decoder_correct_word >> simp[],
    drule_all abi_decoder_correct_bytestring >> simp[]]
QED

Theorem abi_decoder_correct_flag:
  abi_decoder_correct ce env sf (FlagT nsid) (FlagTV n)
Proof
  irule abi_decoder_correct_word >> simp[Once type_to_abi_dec_info_def]
QED
