(* Full coherence induction for canonical DLOAD with actual-site credit. *)
Theory ctorAbiActualRecursive
Ancestors
 ctorAbiActualArrayClosure ctorAbiActualComplex ctorAbiActualLabelWord
 ctorAbiActualLabelBytes ctorAbiActualLabelEmpty abiDecoderCoherence
 exprLowering compileEnv rich_list

val C = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\ unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels``;

Theorem ctor_actual_primitive_run:
 type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==> (^C) ty tv
Proof
 strip_tac >> BETA_TAC >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule_all ctor_actual_word_labels_run >> strip_tac >>
 qexists `actual` >> asm_rewrite_tac[]
QED

Theorem ctor_actual_bytes_run:
 type_to_abi_dec_info sf ce ty = DecBytestring n ==> (^C) ty tv
Proof
 strip_tac >> BETA_TAC >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule_all ctor_actual_bytestring_labels_run >> strip_tac >>
 qexists `actual` >> asm_rewrite_tac[]
QED

Theorem ctor_actual_base_run:
 (^C) (BaseT bt) (BaseTV bt)
Proof
 `(?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp) \/
  (?n. type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring n)` by
   (Cases_on `bt` >> simp[type_to_abi_dec_info_def] >>
    rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def])
 >- (irule ctor_actual_primitive_run >> goal_assum (drule_at Any)) >>
 irule ctor_actual_bytes_run >> goal_assum (drule_at Any)
QED

Theorem ctor_actual_flag_run:
 (^C) (FlagT nsid) (FlagTV n)
Proof
 irule ctor_actual_primitive_run >> simp[Once type_to_abi_dec_info_def]
QED

Theorem ctor_actual_coherent_run:
 !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> (^C) ty tv
Proof
 qabbrev_tac `P = \ce env sf. (^C)` >>
 `!ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> P ce env sf ty tv` suffices_by
   simp[Abbr `P`] >>
 ho_match_mp_tac abi_decoder_coherent_ind >>
 conj_tac
 >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
     MATCH_ACCEPT_TAC (BETA_RULE ctor_actual_base_run)) >>
 conj_tac
 >- (rpt gen_tac >> disch_tac >> simp_tac bool_ss [Abbr `P`] >>
     MATCH_ACCEPT_TAC (BETA_RULE ctor_actual_flag_run)) >>
 conj_tac
 >- (rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
     match_mp_tac (BETA_RULE ctor_actual_array_run) >> first_assum ACCEPT_TAC) >>
 conj_tac
 >- (rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
     match_mp_tac (BETA_RULE ctor_actual_tuple) >> first_assum ACCEPT_TAC) >>
 rpt gen_tac >> strip_tac >> FULL_SIMP_TAC bool_ss [Abbr `P`] >>
 match_mp_tac (BETA_RULE ctor_actual_struct) >> asm_rewrite_tac[]
QED
