(* Constructor-facing core adapters for the counted physical encoder. *)
Theory bodyIntCallEncoderCountedExport
Ancestors
  bodyIntCallEncoderCountedLeaves bodyIntCallEncoderCountedComplex
  bodyIntCallEncoderCountedArrays bodyIntCallEncoderCountedSpine
  bodyIntCallEncoderCountedMembers
  abiScratchMemberContract abiScratchEncoderContract abiEncoderMemberSpine
  abiEncoderAdmissible abiScratchEncoderCaller abiEncoderInput abiEncoderSequence
  abiDecoderContract abiDecoderLoop compileEnv valueEncoding contractABI
  venomState words arithmetic list pair fragGasPath

Theorem intcall_encoder_word_core:
  abi_encoder_spine_core_code func (AbiPrimWord,dst,src,st,en,out) /\
  abi_scratch_member_core_pre (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
    (AbiPrimWord,dst,src,st,en,out) initial ==>
  ?actual. intcall_encoder_core_path ctx func (AbiPrimWord,dst,src,st,en,out) initial actual /\
    abi_scratch_member_core_post (ctx,func) (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
      (AbiPrimWord,dst,src,st,en,out) initial actual
Proof
  simp_tac bool_ss [abi_encoder_spine_core_code_def, abi_scratch_member_core_pre_def] >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `sb < dimword (:256) /\ d < dimword (:256)` by decide_tac >>
  drule_all intcall_encoder_word_counted >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule intcall_encoder_path_sim >> disch_tac >>
  qexists_tac `actual` >>
  asm_simp_tac bool_ss [intcall_encoder_core_path_def, abi_scratch_member_core_post_def] >>
  fs[abi_encoder_sequence_post_def] >> goal_assum (drule_at Any)
QED

Theorem intcall_encoder_copy_core:
  abi_encoder_spine_core_code func (AbiCopy sz,dst,src,st,en,out) /\
  abi_scratch_member_core_pre (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
    (AbiCopy sz,dst,src,st,en,out) initial ==>
  ?actual. intcall_encoder_core_path ctx func (AbiCopy sz,dst,src,st,en,out) initial actual /\
    abi_scratch_member_core_post (ctx,func) (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
      (AbiCopy sz,dst,src,st,en,out) initial actual
Proof
  simp_tac bool_ss [abi_encoder_spine_core_code_def, abi_scratch_member_core_pre_def] >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `sz <= source_cap` by fs[abi_encoder_input_copy_iff] >>
  `sb < dimword (:256) /\ d < dimword (:256) /\ sz < dimword (:256)` by decide_tac >>
  drule_all intcall_encoder_copy_counted >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule intcall_encoder_path_sim >> disch_tac >>
  qexists_tac `actual` >>
  asm_simp_tac bool_ss [intcall_encoder_core_path_def, abi_scratch_member_core_post_def] >>
  fs[abi_encoder_sequence_post_def] >> goal_assum (drule_at Any)
QED

Theorem intcall_encoder_bytes_core:
  abi_encoder_spine_core_code func (AbiBytestring maxlen,dst,src,st,en,out) /\
  abi_scratch_member_core_pre (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
    (AbiBytestring maxlen,dst,src,st,en,out) initial ==>
  ?actual. intcall_encoder_core_path ctx func (AbiBytestring maxlen,dst,src,st,en,out) initial actual /\
    abi_scratch_member_core_post (ctx,func) (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
      (AbiBytestring maxlen,dst,src,st,en,out) initial actual
Proof
  simp_tac bool_ss [abi_encoder_spine_core_code_def, abi_scratch_member_core_pre_def] >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `sb < dimword (:256)` by decide_tac >>
  drule_all intcall_encoder_bytes_counted >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule intcall_encoder_path_sim >> disch_tac >>
  qexists_tac `actual` >>
  asm_simp_tac bool_ss [intcall_encoder_core_path_def, abi_scratch_member_core_post_def] >>
  fs[abi_encoder_sequence_post_def] >> goal_assum (drule_at Any)
QED

Theorem intcall_encoder_array_core:
  (!value resources cd cs cst cen co r. abi_encoder_admissible ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,cst,cen,co) r u) /\
  abi_encoder_admissible (AbiDynArray ei asz msz active) /\
  abi_encoder_spine_core_code func (AbiDynArray ei asz msz active,dst,src,st,en,out) /\
  abi_scratch_member_core_pre (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
    (AbiDynArray ei asz msz active,dst,src,st,en,out) initial ==>
  ?actual. intcall_encoder_core_path ctx func (AbiDynArray ei asz msz active,dst,src,st,en,out) initial actual /\
    abi_scratch_member_core_post (ctx,func) (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
      (AbiDynArray ei asz msz active,dst,src,st,en,out) initial actual
Proof
  strip_tac >>
  `abi_encoder_admissible ei` by fs[abi_encoder_admissible_def] >>
  drule abi_scratch_encoder_admissible >> disch_tac >>
  `if active then abi_scratch_encoder ei else abi_encoder_static_leaf ei` by
    (Cases_on `active` >> fs[abi_encoder_admissible_def]) >>
  qpat_assum `abi_encoder_spine_core_code _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_spine_core_code_def]) >>
  qpat_assum `abi_scratch_member_core_pre _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_member_core_pre_def]) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `ct` (qx_choose_then `avs` (MAP_EVERY assume_tac o CONJUNCTS)) o
      PURE_REWRITE_RULE [abi_encoder_array_input_iff]) >>
  qpat_x_assum `at = Array NONE ct` SUBST_ALL_TAC >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  drule_all intcall_scratch_array_run >> strip_tac >>
  drule intcall_encoder_path_sim >> disch_tac >>
  qexists_tac `actual` >>
  asm_simp_tac bool_ss [intcall_encoder_core_path_def, abi_scratch_member_core_post_def] >>
  goal_assum (drule_at Any)
QED

Theorem intcall_encoder_complex_core:
  (!value resources ei cd cs st en out r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,st,en,out) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,st,en,out) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,st,en,out) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,st,en,out) r u) /\
  EVERY (\(ei,az,mz,dyn). P ei) infos /\
  abi_encoder_admissible (AbiComplex infos) /\
  abi_encoder_spine_core_code func (AbiComplex infos,dst,src,st,en,out) /\
  abi_scratch_member_core_pre (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
    (AbiComplex infos,dst,src,st,en,out) initial ==>
  ?actual. intcall_encoder_core_path ctx func (AbiComplex infos,dst,src,st,en,out) initial actual /\
    abi_scratch_member_core_post (ctx,func) (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
      (AbiComplex infos,dst,src,st,en,out) initial actual
Proof
  strip_tac >>
  `abi_encoder_members_admissible infos` by fs[abi_encoder_admissible_def] >>
  drule (cj 2 abi_scratch_encoder_admissible_mutual) >> disch_tac >>
  `!value ei cd cs st en out r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,st,en,out) /\
    abi_scratch_member_core_pre value (first,last,b,cap,limit_st) (ei,cd,cs,st,en,out) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,st,en,out) r u /\
      abi_scratch_member_core_post (ctx,func) value (first,last,b,cap,limit_st)
        (ei,cd,cs,st,en,out) r u` by metis_tac[] >>
  drule intcall_scratch_members_counted_callback >> disch_tac >>
  Cases_on `EXISTS (\(_,_,_,dyn). dyn) infos`
  >- (drule_all intcall_scratch_complex_dynamic >> simp[]) >>
  drule_all intcall_scratch_complex_static >> simp[]
QED

Theorem intcall_encoder_admissible_mutual:
  (!ei. abi_encoder_admissible ei ==>
    !ctx func value resources dst src st en out initial.
    abi_encoder_spine_core_code func (ei,dst,src,st,en,out) /\
    abi_scratch_member_core_pre value resources (ei,dst,src,st,en,out) initial ==>
    ?actual. intcall_encoder_core_path ctx func (ei,dst,src,st,en,out) initial actual /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,dst,src,st,en,out) initial actual) /\
  (!infos. abi_encoder_members_admissible infos ==>
    EVERY (\(ei,az,mz,dyn).
      !ctx func value resources dst src st en out initial.
      abi_encoder_spine_core_code func (ei,dst,src,st,en,out) /\
      abi_scratch_member_core_pre value resources (ei,dst,src,st,en,out) initial ==>
      ?actual. intcall_encoder_core_path ctx func (ei,dst,src,st,en,out) initial actual /\
        abi_scratch_member_core_post (ctx,func) value resources (ei,dst,src,st,en,out) initial actual) infos)
Proof
  ho_match_mp_tac abi_encoder_admissible_ind >>
  simp_tac bool_ss [EVERY_DEF, abi_encoder_admissible_def] >> rpt conj_tac
  >- (rpt gen_tac >> PairCases_on `value` >> PairCases_on `resources` >>
      MATCH_ACCEPT_TAC intcall_encoder_word_core)
  >- (rpt gen_tac >> PairCases_on `value` >> PairCases_on `resources` >>
      MATCH_ACCEPT_TAC intcall_encoder_copy_core)
  >- (rpt gen_tac >> PairCases_on `value` >> PairCases_on `resources` >>
      MATCH_ACCEPT_TAC intcall_encoder_bytes_core)
  >- (rpt gen_tac >> disch_tac >> strip_tac >> rpt gen_tac >>
      PairCases_on `value` >> PairCases_on `resources` >> strip_tac >>
      irule intcall_encoder_array_core >>
      asm_simp_tac bool_ss [abi_encoder_admissible_def] >> metis_tac[])
  >- (rpt gen_tac >> disch_tac >> disch_tac >>
      first_x_assum drule >> disch_tac >> rpt gen_tac >>
      PairCases_on `value` >> PairCases_on `resources` >> strip_tac >>
      irule intcall_encoder_complex_core >>
      asm_simp_tac bool_ss [abi_encoder_admissible_def] >>
      qexists_tac `\ei. MEM ei (MAP FST infos)` >>
      conj_tac
      >- (fs[EVERY_MEM, MEM_MAP, EXISTS_PROD, FORALL_PROD] >> metis_tac[]) >>
      simp[EVERY_MEM, MEM_MAP, EXISTS_PROD, FORALL_PROD] >> metis_tac[]) >>
  simp_tac (srw_ss()) [] >> metis_tac[]
QED

Theorem intcall_encoder_admissible_core:
  abi_encoder_admissible ei /\
  abi_encoder_spine_core_code func (ei,dst,src,st,en,out) /\
  abi_scratch_member_core_pre value resources (ei,dst,src,st,en,out) initial ==>
  ?actual. intcall_encoder_core_path ctx func (ei,dst,src,st,en,out) initial actual /\
    abi_scratch_member_core_post (ctx,func) value resources (ei,dst,src,st,en,out) initial actual
Proof
  strip_tac >> drule (cj 1 intcall_encoder_admissible_mutual) >>
  disch_then drule_all >> simp[]
QED

Theorem intcall_encoder_translation_core:
  abi_encoder_spine_core_code func (type_to_abi_enc_info sf ce ty,dst,src,st,en,out) /\
  abi_scratch_member_core_pre value resources
    (type_to_abi_enc_info sf ce ty,dst,src,st,en,out) initial ==>
  ?actual. intcall_encoder_core_path ctx func
      (type_to_abi_enc_info sf ce ty,dst,src,st,en,out) initial actual /\
    abi_scratch_member_core_post (ctx,func) value resources
      (type_to_abi_enc_info sf ce ty,dst,src,st,en,out) initial actual
Proof
  strip_tac >> irule intcall_encoder_admissible_core >>
  asm_simp_tac bool_ss [abi_encoder_translation_admissible]
QED

Theorem intcall_encoder_scratch_counted:
  abi_encoder_admissible ei /\
  compile_abi_encode_to_buf dst src ei start = (out,end_st) /\ fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input ei at av start src dst sb source_cap d (LENGTH (enc at av))
    first last b cap initial /\ abi_decoder_budget first last b cap initial /\
  first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual n. gas_path ctx func initial n (OK actual) /\
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule abi_scratch_encoder_admissible >> disch_tac >>
  `abi_encoder_spine_core_code func (ei,dst,src,start,end_st,out)` by
    asm_simp_tac bool_ss [abi_encoder_spine_core_code_def] >>
  `abi_scratch_member_core_pre (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
    (ei,dst,src,start,end_st,out) initial` by
    asm_simp_tac bool_ss [abi_scratch_member_core_pre_def] >>
  drule_all intcall_encoder_admissible_core >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  fs[intcall_encoder_core_path_def, abi_scratch_member_core_post_def] >>
  qexistsl_tac [`actual`, `n`] >> asm_rewrite_tac []
QED
