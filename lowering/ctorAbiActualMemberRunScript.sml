Theory ctorAbiActualMemberRun
Ancestors
  ctorAbiActualMemberInputs ctorAbiActualMemberBoundary ctorAbiActualChildFrame ctorAbiActualMembers
  ctorAbiActualEmpty ctorAbiActualNarrowWord ctorAbiActualNarrow ctorAbiActualFrame
  ctorAbiActualObservations ctorAbiActualLabelMember ctorAbiActualLabelEmpty
  allocaFrontierBound allocaBudgetProps abiDecoderAppend
  abiDecoderCoherence abiDecoderTypedContract abiEncoderProps venomMemDefs venomState pred_set
  abiDecoderMemberCons abiDecoderEmpty abiDecoderEmptyMember abiDecoderContract abiDecoderReentry
  abiEncoderRegisteredEffect abiDecoderLoop fragExec compileEnv valueEncoding
  abiEncoder contractABI words list rich_list arithmetic abiDecoderMemberInfos
  abiDecoderMembers abiDecoderMemberSetup abiDecoderMemberCode exprLowering abiDecodeRanges
  abiDecoderDynamicLoopSetup abiDecoderReentryPointer valueTypingMemoryProps

Theorem ctor_actual_alloca_transport[local]:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  (alloca_inv t = alloca_inv s) /\
  (alloca_frontier_inv ctx func site t = alloca_frontier_inv ctx func site s) /\
  (ctor_actual_scratch func ids D N t = ctor_actual_scratch func ids D N s)
Proof
  strip_tac >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_def, remaining_alloca_budget_def,
       ctor_actual_scratch_def]
QED

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

val M = ``\tys tvs.
 !dst src hi st final ctx func site initial limit_st sb d D N ids
   pretys pretvs preavs prevs avs vs.
 compile_abi_decode_complex_elems dst src DLOAD (Lit 0w) hi (abi_decoder_member_infos sf ce tys)
   (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
   (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),final) /\
 abi_decoder_members ce env sf pretys pretvs preavs prevs /\
 abi_decoder_members ce env sf tys tvs avs vs /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs))) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs)))) initial.vs_data_section =
   enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs)) /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
   sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs))) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st final func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\ unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ tys)) <= D+N /\
 D+N <= initial.vs_alloca_next /\ frag_ids st final SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final))
   [(d + SUM (MAP (type_memory_bytes ce) pretys), SUM (MAP (type_memory_bytes ce) tys))] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels``;

Theorem ctor_actual_members_run_nil[local]:
  (^M) [] []
Proof
  BETA_TAC >> rpt gen_tac >>
  simp[abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def,
    comp_return_def, Excl "enc_def"] >> strip_tac >>
  drule abi_decoder_members_lengths >> strip_tac >> gvs[Excl "enc_def"] >>
  qexists `initial` >>
  simp[val_in_memory_def, abi_encoder_registered_effect_refl, abi_decode_sim_refl]
QED

Theorem ctor_actual_members_run_cons[local]:
  (^C) ty tv /\ (^M) tys tvs ==> (^M) (ty::tys) (tv::tvs)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (mk_asm "tail")) >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_members_lengths >> strip_tac >>
  Cases_on `avs` >- gvs[] >> Cases_on `vs` >- gvs[] >>
  rename1 `abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs') (v::vs')` >>
  drule abi_decoder_member_cons_trace >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule_all abi_decoder_members_child_phi >> disch_then assume_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     Cases_on `src` >> Cases_on `dst` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `fn_has_code st middle func` by
    (mp_tac (Q.SPECL [`st`, `middle`, `final`, `func`] fn_has_code_split) >>
     simp[]) >>
  drule_all ctor_actual_member_setup_labels_narrow >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[Excl "enc_def"] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial prepared` >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` kall_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var hi` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     Cases_on `hi` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `fn_has_code middle end_st func` by
    (mp_tac (Q.SPECL [`middle`, `end_st`, `final`, `func`] fn_has_code_split) >> simp[]) >>
  `frag_ids middle end_st SUBSET ids` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     gvs[frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> decide_tac) >>
  `alloca_inv prepared /\ alloca_frontier_inv ctx func site prepared /\
   ctor_actual_scratch func ids D N prepared /\ D+N <= prepared.vs_alloca_next` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     drule_all ctor_actual_alloca_transport >> strip_tac >> asm_simp_tac bool_ss []) >>
  `end_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `?after_head. val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) after_head.vs_memory /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle end_st))
      [(d + SUM (MAP (type_memory_bytes ce) pretys),type_memory_bytes ce ty)] prepared after_head /\
    alloca_inv after_head /\ alloca_frontier_inv ctx func site after_head /\
    ctor_actual_scratch func ids D N after_head /\ D+N <= after_head.vs_alloca_next /\
    after_head.vs_data_section = prepared.vs_data_section /\
    after_head.vs_call_ctx = prepared.vs_call_ctx /\
    (!x w. not_fresh_at middle x /\ lookup_var x prepared = SOME w ==>
      lookup_var x after_head = SOME w) /\
    ~after_head.vs_halted /\ after_head.vs_current_bb = end_st.cs_current_bb /\
    after_head.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    abi_decode_sim ctx func prepared after_head /\ fresh_vars_wrt limit_st after_head /\
    after_head.vs_labels = prepared.vs_labels` by
    (qpat_x_assum `prepared.vs_labels = initial.vs_labels` kall_tac >>
     reverse (Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`)
     >- (qpat_x_assum `eval_operand (FST ops) prepared = _` mp_tac >>
         asm_simp_tac bool_ss [] >> disch_then assume_tac >>
         mp_tac (Q.INST [`childsrc` |-> `FST (ops:operand # operand)`,
           `childdst` |-> `SND (ops:operand # operand)`,
           `avs` |-> `avs':abi_value list`, `vs` |-> `vs':value list`] ctor_actual_member_child_inputs) >>
         (impl_tac >- asm_simp_tac bool_ss [MAP_APPEND, MAP]) >>
         disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
         asm "child" (irule o BETA_RULE) >>
         asm_simp_tac bool_ss [LENGTH_APPEND, LENGTH] >>
         qexistsl [`av`, `SND ops`, `hi`,
           `type_to_abi_dec_info ce.ce_struct_fields ce ty`,
           `sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
             (preavs ++ av::avs') (LENGTH pretys)`, `FST ops`] >>
         asm_simp_tac bool_ss [MAP_APPEND, MAP] >>
         asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
         full_simp_tac bool_ss [MAP_APPEND, MAP]) >>
     (mp_tac (Q.INST [`avs` |-> `avs':abi_value list`, `vs` |-> `vs':value list`]
        ctor_actual_member_inline_guard) >>
      (impl_tac >- asm_simp_tac bool_ss []) >> disch_then assume_tac >>
      `abi_decoder_operand_live middle.cs_next_var hi` by
        (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
      qpat_x_assum `compile_abi_decode_to_buf (SND ops) _ _ _ _ _ _ = _` mp_tac >>
      asm_simp_tac bool_ss [] >> disch_then assume_tac >>
      qpat_x_assum `eval_operand (FST ops) prepared = _` mp_tac >>
      asm_simp_tac bool_ss [] >> disch_then assume_tac >>
      `prepared.vs_inst_idx = LENGTH middle.cs_current_insts` by simp[] >>
      drule ctor_actual_empty_complex_labels_reach >>
      disch_then (qspecl_then
        [`sb + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))`,
         `limit_st`, `prepared`, `func`, `ctx`] mp_tac) >>
      (impl_tac >- asm_simp_tac bool_ss [LENGTH_APPEND, LENGTH]) >>
      disch_then (qx_choose_then `empty_end` (MAP_EVERY assume_tac o CONJUNCTS)) >>
      asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
      `abi_decoder_coherent ce env sf ty tv /\
       abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v` by
        (qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
           (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >>
         simp_tac bool_ss [] >> metis_tac[]) >>
      drule_all abi_decoder_empty_metadata_value >> strip_tac >>
      `alloca_inv empty_end /\ alloca_frontier_inv ctx func site empty_end /\
       ctor_actual_scratch func ids D N empty_end` by
        (`empty_end.vs_allocas = prepared.vs_allocas /\
          empty_end.vs_alloca_next = prepared.vs_alloca_next` by
           (qpat_assum `abi_decoder_address_frame _ prepared empty_end`
              (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
            simp_tac bool_ss [] >> metis_tac[]) >>
         drule_all ctor_actual_alloca_transport >> strip_tac >>
         asm_simp_tac bool_ss []) >>
      qexists `empty_end` >>
      asm_simp_tac bool_ss [] >>
      conj_tac
      >- (irule abi_encoder_registered_effect_enlarge >>
          qexistsl [`{}`, `[]`] >> simp[]) >>
      qpat_assum `abi_decoder_address_frame _ prepared empty_end`
        (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      asm_simp_tac bool_ss [] >> rpt strip_tac >>
      first_x_assum (qspec_then `Var x` mp_tac) >>
      qpat_x_assum `lookup_var x prepared = SOME w` mp_tac >>
      qpat_x_assum `not_fresh_at middle x` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
        not_fresh_at_def, eval_operand_def])) >>
  rename1 `abi_decode_sim ctx func prepared after_head` >>
  asm_x "child" kall_tac >>
  `abi_decoder_members ce env sf (pretys ++ [ty]) (pretvs ++ [tv])
     (preavs ++ [av]) (prevs ++ [v]) /\
   abi_decoder_members ce env sf tys tvs avs' vs'` by
    (asm_x "tail" kall_tac >>
     qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >>
     strip_tac >> conj_tac
     >- (irule abi_decoder_members_join >> simp[abi_decoder_members_def]) >>
     first_assum ACCEPT_TAC) >>
  `compile_abi_decode_complex_elems dst src DLOAD (Lit 0w) hi (abi_decoder_member_infos sf ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (pretys ++ [ty]))))
    (SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) end_st = ((),final)` by
    (asm_x "tail" kall_tac >>
     qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >> strip_tac >>
     drule abi_decoder_coherent_header >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
     qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ end_st = _` mp_tac >>
     qpat_x_assum `abi_embedded_static_size _ ty = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0]) >>
  `!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
     lookup_var x after_head = SOME w` by
    (asm_x "tail" kall_tac >> rpt strip_tac >>
     `not_fresh_at middle x` by
       (qpat_x_assum `not_fresh_at st x` mp_tac >>
        simp_tac bool_ss [not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
     `lookup_var x prepared = SOME w` by
       (qpat_assum `abi_decoder_address_frame _ initial prepared`
         (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
        disch_then (mp_tac o CONJUNCT1) >>
        disch_then (qspec_then `Var x` mp_tac) >>
        qpat_x_assum `lookup_var x initial = SOME w` mp_tac >>
        qpat_x_assum `not_fresh_at st x` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          eval_operand_def, not_fresh_at_def]) >>
     metis_tac[]) >>
  `eval_operand src after_head = SOME (n2w sb) /\
   eval_operand dst after_head = SOME (n2w d) /\
   (!h. eval_operand hi initial = SOME (n2w h) ==>
      eval_operand hi after_head = SOME (n2w h))` by
    (asm_x "tail" kall_tac >>
     `after_head.vs_labels = initial.vs_labels` by metis_tac[] >>
     rpt conj_tac >> rpt strip_tac >> irule ctor_actual_old_operand >>
     qexistsl [`initial`, `st`] >> simp[] >> metis_tac[]) >>
  `fn_has_code end_st final func` by
    (mp_tac (Q.SPECL [`middle`, `end_st`, `final`, `func`] fn_has_code_split) >> simp[]) >>
  `frag_ids end_st final SUBSET ids` by
    (qpat_x_assum `frag_ids st final SUBSET ids` mp_tac >>
     qpat_x_assum `st.cs_next_id < middle.cs_next_id` mp_tac >>
     qpat_x_assum `middle.cs_next_id <= end_st.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at end_st x` by
    (asm_x "tail" kall_tac >> rpt strip_tac >>
     `not_fresh_at st x` by metis_tac[] >>
     qpat_x_assum `not_fresh_at st x` mp_tac >>
     simp_tac bool_ss [not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `prepared.vs_data_section = initial.vs_data_section` by
    (qpat_assum `abi_decoder_address_frame _ initial prepared`
      (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     simp_tac bool_ss [] >> metis_tac[]) >>
  drule_all abi_decoder_members_tail_phi >> disch_then assume_tac >>
  asm "tail" (drule o BETA_RULE) >>
  disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_members _ _ _ (_ ++ [_]) _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_members _ _ _ tys _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  (impl_tac >- (asm_x "tail" kall_tac >>
    asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND] >>
    metis_tac[])) >>
  disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  asm_x "tail" kall_tac >>
  `type_memory_size tv = type_memory_bytes ce ty /\ val_wf tv v` by
    (qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >>
     strip_tac >>
     qpat_x_assum `abi_decoder_metadata _ _ ty tv _ av v`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
     strip_tac >> metis_tac[value_has_type_memory_wf]) >>
  `val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory` by
    (irule ctor_actual_child_preserves_value >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`D`, `N`,
       `d + SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))`,
       `frag_ids end_st final`, `func`, `ids`,
       `SUM (MAP (type_memory_bytes ce) tys)`, `after_head`] >>
     asm_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0] >>
     qpat_x_assum `d + SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) <= D+N` mp_tac >>
     qpat_x_assum `D <= d` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[MAP_APPEND, MAP, SUM_APPEND, SUM, venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qexists `actual` >>
  asm_simp_tac bool_ss [] >>
  conj_tac
  >- (asm_simp_tac bool_ss [val_in_memory_def] >>
      qpat_x_assum `tuple_in_memory vs' tvs _ actual.vs_memory` mp_tac >>
      qpat_x_assum `val_in_memory tv v _ actual.vs_memory` mp_tac >>
      qpat_x_assum `type_memory_size tv = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp_tac (srw_ss()) [LET_DEF, pairTheory.UNCURRY_DEF,
        MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC]) >>
  conj_tac
  >- ( `frag_ids middle end_st SUBSET frag_ids st final /\
         frag_ids end_st final SUBSET frag_ids st final` by
         (qpat_x_assum `st.cs_next_id < middle.cs_next_id` mp_tac >>
          qpat_x_assum `middle.cs_next_id <= end_st.cs_next_id` mp_tac >>
          qpat_x_assum `end_st.cs_next_id <= final.cs_next_id` mp_tac >>
          POP_ASSUM_LIST (K ALL_TAC) >>
          simp[frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> decide_tac) >>
       qmatch_goalsub_abbrev_tac `abi_encoder_registered_effect allsites out initial actual` >>
       `abi_encoder_registered_effect allsites out initial prepared` by
         (irule abi_encoder_registered_effect_enlarge >>
          qexistsl [`{}`, `[]`] >> asm_simp_tac (srw_ss()) []) >>
       `abi_encoder_registered_effect allsites out prepared after_head` by
         (simp_tac bool_ss [Abbr `allsites`, Abbr `out`] >>
          irule ctor_actual_child_narrow_effect >>
          goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >> asm_simp_tac bool_ss [] >> decide_tac) >>
       `abi_encoder_registered_effect allsites out after_head actual` by
         (simp_tac bool_ss [Abbr `allsites`, Abbr `out`] >>
          irule ctor_actual_child_narrow_effect >>
          goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
          asm_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0] >> decide_tac) >>
       metis_tac[abi_encoder_registered_effect_trans]) >>
  conj_tac
  >- (qpat_assum `abi_decoder_address_frame _ initial prepared`
        (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
      simp_tac bool_ss [] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at end_st x` by
        (qpat_x_assum `not_fresh_at st x` mp_tac >>
         qpat_x_assum `st.cs_next_var <= middle.cs_next_var` mp_tac >>
         qpat_x_assum `middle.cs_next_var <= end_st.cs_next_var` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[not_fresh_at_def] >> decide_tac) >>
      metis_tac[]) >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem ctor_actual_members_run:
  !tys tvs. LIST_REL (^C) tys tvs ==> (^M) tys tvs
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >>
  simp_tac bool_ss [LIST_REL_def, ctor_actual_members_run_nil] >> strip_tac >>
  rename1 `LIST_REL _ tys rest` >>
  mp_tac (Q.INST [`ty` |-> `h`, `tv` |-> `h'`, `tvs` |-> `rest`]
    ctor_actual_members_run_cons) >>
  (impl_tac >- (conj_tac >- (BETA_TAC >> first_assum ACCEPT_TAC) >>
     first_x_assum irule >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss []
QED
