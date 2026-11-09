(* Same-endpoint head/tail composition of the floor-aware member contract. *)
Theory ctorDeployMemoryRunPtrPrefixMembersCons
Ancestors
  loweringStateRelDefs valueEncodingDefs
  ctorDeployMemoryRunPtrPrefixCanonicalFloor ctorDeployMemoryRunPtrPrefixMembersFloor
  ctorDeployMemoryRunPtrPrefixMemberFloor ctorDeployMemoryRunPtrPrefixEmptyFloor
  ctorDeployMemoryRunPtrPrefixMemberInputs
  ctorDeployMemoryRunPtrPrefixMembers ctorAbiActualMemberRun
  ctorAbiActualComplex abiDecoderComplexExecute abiDecoderComplexHead
  abiDecoderTupleInputs abiDecoderStruct valueEncodingProps vyperABI valueEncodingTyping
  abiStaticDynarrayLayout vyperTyping
  ctorAbiActualMemberInputs ctorAbiActualMemberBoundary ctorAbiActualMemberSetup
  ctorAbiActualChildFrame ctorAbiActualMemory ctorAbiActualSites ctorAbiActualMembers
  abiDecoderMemberCons abiDecoderMemberCode abiDecoderMemberSetup abiDecoderMemberBody
  abiDecoderMembers abiDecoderMemberInfos abiDecoderDynamic abiDecoderOffset
  abiDecoderCoherence abiDecoderContract abiDecoderTypedContract
  abiDecoderReentry abiDecoderDynamicLoopSetup abiEncoderRegisteredEffect
  abiDecoderLoop fragExec compileEnv valueEncoding abiEncoder contractABI
  allocaFrontierBound allocaBudgetProps abiDecoderReentryPointer
  venomState ptrDiscipline ptrSafeRun finite_map pred_set words list rich_list arithmetic

val canonical_pair_floor = ``\ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
   (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb.
    lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
 unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 lo <= initial.vs_alloca_next ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem =
                        mem_bytes_at a 1 actual.vs_memory) ==>
    val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                           op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

val paired_members_floor = ``\tys tvs.
 !dst src st final ctx func site initial limit_st sb d D N ids
   pretys pretvs preavs prevs avs vs G tn b sz Ddead lo PG.
 compile_abi_decode_complex_elems (Var dst) src DLOAD (Lit 0w) (Lit 0w)
   (abi_decoder_member_infos sf ce tys)
   (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
   (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),final) /\
 abi_decoder_members ce env sf pretys pretvs preavs prevs /\
 abi_decoder_members ce env sf tys tvs avs vs /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs))) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs)))) initial.vs_data_section =
   enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs)) /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st final func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\ unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ tys)) <= D+N /\
 D+N <= initial.vs_alloca_next /\ frag_ids st final SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + SUM (MAP (type_memory_bytes ce) (pretys ++ tys)) <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= initial.vs_alloca_next ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final))
   [(d + SUM (MAP (type_memory_bytes ce) pretys), SUM (MAP (type_memory_bytes ce) tys))] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 FINITE B /\ B SUBSET range_bytes
   [(d + SUM (MAP (type_memory_bytes ce) pretys), SUM (MAP (type_memory_bytes ce) tys))] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
   tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                          op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_paired_members_cons_floor:
  (^canonical_pair_floor) ty tv /\ (^paired_members_floor) tys tvs ==>
  (^paired_members_floor) (ty::tys) (tv::tvs)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (mk_asm "tail")) >>
  BETA_TAC >> rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
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
   abi_decoder_operand_live st.cs_next_var (Var dst)` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >> Cases_on `src` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `fn_has_code st middle func` by
    (mp_tac (Q.SPECL [`st`,`middle`,`final`,`func`] fn_has_code_split) >> simp[]) >>
  mp_tac (Q.INST [`avs` |-> `avs':abi_value list`, `vs` |-> `vs':value list`]
    prefix_member_canonical_inputs) >>
  (impl_tac >- asm_rewrite_tac[]) >> disch_tac >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  drule_all prefix_member_setup_pair_floor >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  qpat_x_assum `LET _ _` (strip_assume_tac o SIMP_RULE bool_ss [LET_THM]) >>
  qmatch_asmsub_abbrev_tac `allocas_from lo prepared` >>
  `fn_has_code middle end_st func` by
    (mp_tac (Q.SPECL [`middle`,`end_st`,`final`,`func`] fn_has_code_split) >> simp[]) >>
  `alloca_inv prepared /\ alloca_frontier_inv ctx func site prepared /\
   ctor_actual_scratch func ids D N prepared /\ D+N <= prepared.vs_alloca_next` by
    (drule_all prefix_prepared_alloca_invariants >> simp[]) >>
  `~prepared.vs_halted` by
    (qpat_assum `abi_decoder_address_frame _ initial prepared`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     asm_simp_tac bool_ss []) >>
  `?after_head Hh qh Bh.
    allocas_from lo after_head /\ lo <= after_head.vs_alloca_next /\
    val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) after_head.vs_memory /\
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
    after_head.vs_labels = prepared.vs_labels /\ FINITE Bh /\
    Bh SUBSET range_bytes [(d + SUM (MAP (type_memory_bytes ce) pretys),type_memory_bytes ce ty)] /\
    DISJOINT Bh qh.t_mem /\
    (!mem. (!a. a IN Bh ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 after_head.vs_memory) ==>
      val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) mem) /\
    qh.t_mem SUBSET qt.t_mem /\ qh.t_stor = qt.t_stor /\
    qh.t_trans = qt.t_trans /\ qh.t_imm = qt.t_imm /\
    (!x. not_fresh_at middle x ==> FLOOKUP Hh x = FLOOKUP H x /\
      op_taint qh (Var x) = op_taint qt (Var x)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG Hh qh after_head) ==>
      !fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt prepared)` by
  (Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (qpat_assum `abi_decoder_members ce env sf pretys pretvs preavs prevs`
        (mp_then Any mp_tac abi_decoder_members_child_facts) >>
      disch_then drule >> strip_tac >>
      qpat_x_assum `compile_abi_decode_to_buf (SND ops) _ _ _ _ _ _ = _` mp_tac >>
      asm_simp_tac bool_ss [] >> disch_tac >>
      mp_tac (Q.INST [`initial` |-> `prepared:venom_state`,
        `G` |-> `H:(string, num # num) fmap`, `tn` |-> `qt:taint`,
        `d` |-> `d + SUM (MAP (type_memory_bytes ce) pretys)`,
        `dst` |-> `SND (ops:operand # operand)`, `src` |-> `FST (ops:operand # operand)`,
        `root_di` |-> `type_to_abi_dec_info ce.ce_struct_fields ce ty`]
        prefix_empty_inline_paired_floor) >>
      (impl_tac >- asm_rewrite_tac[]) >>
      strip_tac >> qexistsl [`actual`,`H'`,`qt'`,`B`] >> asm_rewrite_tac[] >> simp[]) >>
  (mp_tac (Q.INST [`avs` |-> `avs':abi_value list`, `vs` |-> `vs':value list`]
        prefix_member_source_offset_agreement) >>
      (impl_tac >- asm_rewrite_tac[]) >> disch_tac >>
      qpat_x_assum `eval_operand (FST ops) prepared = _` mp_tac >>
      asm_simp_tac bool_ss [] >> disch_then assume_tac >>
      mp_tac (Q.INST [`childsrc` |-> `FST (ops:operand # operand)`,
        `childdst` |-> `SND (ops:operand # operand)`, `hi` |-> `Lit (0w:256 word)`,
        `avs` |-> `avs':abi_value list`, `vs` |-> `vs':value list`]
        ctor_actual_member_child_inputs) >>
      (impl_tac >- asm_simp_tac bool_ss [MAP_APPEND, MAP, abi_decoder_operand_live_def, operand_case_def]) >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      qpat_assum `SND ops = Var child_dst` SUBST_ALL_TAC >>
      asm "child" (fn th =>
        qpat_assum `compile_abi_decode_to_buf (Var child_dst) _ _ _ _ _ _ = _`
          (mp_then Any mp_tac (BETA_RULE th))) >>
      disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ prepared`)) >>
      disch_then (drule_at (Pat `fresh_vars_wrt _ prepared`)) >>
      disch_then (drule_at (Pat `FLOOKUP H child_dst = _`)) >>
      disch_then (drule_at (Pat `op_taint qt (FST ops) = _`)) >>
      disch_then (drule_at (Pat `eval_operand (FST ops) prepared = _`)) >>
      disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ prepared`)) >>
      disch_then (qspecl_then [`d + SUM (MAP (type_memory_bytes ce) pretys)`,
        `Ddead`,`lo`,`PG`] mp_tac) >>
      (impl_tac >- (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
        asm_simp_tac bool_ss [] >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- decide_tac >>
        conj_tac >- (qpat_x_assum `frag_ids st final SUBSET ids` mp_tac >>
          simp_tac (srw_ss()) [abiEncoderPropsTheory.frag_ids_def, SUBSET_DEF, IN_DIFF, IN_COUNT] >>
          strip_tac >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
        full_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM] >> decide_tac)) >>
      strip_tac >> qexistsl [`actual`,`H'`,`qt'`,`B`] >>
      asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
      asm_rewrite_tac[] >> metis_tac[])) >>
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
  `compile_abi_decode_complex_elems (Var dst) src DLOAD (Lit 0w) (Lit 0w)
    (abi_decoder_member_infos sf ce tys)
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
  `!x. not_fresh_at st x ==> not_fresh_at middle x` by
    (asm_x "tail" kall_tac >> simp_tac bool_ss [not_fresh_at_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
  `!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
     lookup_var x after_head = SOME w` by
    (asm_x "tail" kall_tac >> rpt strip_tac >>
     `lookup_var x prepared = SOME w` by
       (qpat_assum `abi_decoder_address_frame _ initial prepared`
          (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
        disch_then (mp_tac o CONJUNCT1) >>
        disch_then (qspec_then `Var x` mp_tac) >>
        simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          eval_operand_def, not_fresh_at_def] >>
        metis_tac[not_fresh_at_def]) >>
     metis_tac[]) >>
  `prepared.vs_data_section = initial.vs_data_section` by
    (qpat_assum `abi_decoder_address_frame _ initial prepared`
      (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [] >> metis_tac[]) >>
  `prepared.vs_labels = initial.vs_labels` by
    (asm_x "tail" kall_tac >> simp[Abbr `prepared`] >>
     irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_labels` exprLoweringPropsTheory.run_inst_seq_preserves_field)) >>
     qexists_tac `emitted_insts st middle` >> simp[] >>
     rpt strip_tac >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by fs[EVERY_MEM] >>
     `step_inst 0 ctx i ss1 = OK ss2` by simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
     metis_tac[venomInstPropsTheory.step_preserves_labels]) >>
  `eval_operand src after_head = SOME (n2w sb) /\
   eval_operand (Var dst) after_head = SOME (n2w d)` by
    (asm_x "tail" kall_tac >>
     rpt conj_tac >> irule ctorAbiActualObservationsTheory.ctor_actual_old_operand >>
     qexistsl [`initial`,`st`] >> asm_rewrite_tac[] >> metis_tac[]) >>
  `!x. not_fresh_at st x ==> FLOOKUP Hh x = FLOOKUP G x /\
    op_taint qh (Var x) = op_taint tn (Var x)` by
    (asm_x "tail" kall_tac >> metis_tac[]) >>
  drule_all abi_decoder_members_tail_phi >> disch_then assume_tac >>
  asm "tail" (fn th =>
    qpat_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ end_st = _`
      (mp_then Any mp_tac (BETA_RULE th))) >>
  disch_then (drule_at (Pat `abi_decoder_members _ _ _ (pretys ++ [ty]) _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_members _ _ _ tys tvs avs' vs'`)) >>
  disch_then (drule_at (Pat `eval_operand src after_head = _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ after_head`)) >>
  disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ after_head`)) >>
  disch_then (qspecl_then [`limit_st`,`sb`,`Hh`,`qh`,`b`,`sz`,`Ddead`,`lo`,`PG`] mp_tac) >>
  (impl_tac >- (asm_x "tail" kall_tac >>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC]) >>
    asm_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC,
      GSYM APPEND_ASSOC, APPEND] >>
    conj_tac >- (rpt strip_tac >> fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]) >>
    conj_tac >-
      (qpat_x_assum `frag_ids st final SUBSET ids` mp_tac >>
       simp_tac (srw_ss()) [abiEncoderPropsTheory.frag_ids_def, SUBSET_DEF, IN_DIFF, IN_COUNT] >>
       strip_tac >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
    Cases_on `src` >> fs[op_taint_def] >> metis_tac[])) >>
  disch_then (qx_choose_then `actual` (qx_choose_then `Ht`
    (qx_choose_then `qtail` (qx_choose_then `Bt` strip_assume_tac)))) >>
  asm_x "tail" kall_tac >>
  `!a. a IN Bh ==> mem_bytes_at a 1 actual.vs_memory =
       mem_bytes_at a 1 after_head.vs_memory` by
    (qpat_assum `abi_encoder_registered_effect _ _ after_head actual`
       (mp_then Any mp_tac prefix_member_support_frame) >>
     disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ actual`)) >>
     disch_then (fn th => qpat_assum `Bh SUBSET _` (mp_then Any mp_tac th)) >>
     `frag_ids end_st final SUBSET ids` by
       (qpat_x_assum `frag_ids st final SUBSET ids` mp_tac >>
        simp_tac (srw_ss()) [abiEncoderPropsTheory.frag_ids_def, SUBSET_DEF, IN_DIFF, IN_COUNT] >>
        strip_tac >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     `D <= d + SUM (MAP (type_memory_bytes ce) pretys) /\
      d + SUM (MAP (type_memory_bytes ce) pretys) + type_memory_bytes ce ty <= D+N /\
      regions_disjoint (d + SUM (MAP (type_memory_bytes ce) pretys),type_memory_bytes ce ty)
        (d + SUM (MAP (type_memory_bytes ce) (pretys ++ [ty])),
         SUM (MAP (type_memory_bytes ce) tys))` by
       (fs[MAP_APPEND, MAP, SUM_APPEND, SUM, venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
     simp[]) >>
  `val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory` by
    (qpat_assum `!mem. _ ==> val_in_memory tv v _ mem` irule >> simp[]) >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    (qpat_assum `abi_decoder_members ce env sf pretys pretvs preavs prevs`
      (mp_then Any mp_tac abi_decoder_members_child_facts) >>
     disch_then drule >> simp[]) >>
  qexistsl_tac [`actual`,`Ht`,`qtail`,`Bh UNION Bt`] >>
  asm_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC,
    FINITE_UNION, DISJOINT_UNION, SUBSET_UNION] >>
  conj_tac >-
    (asm_simp_tac bool_ss [val_in_memory_def] >>
     qpat_x_assum `tuple_in_memory vs' tvs _ actual.vs_memory` mp_tac >>
     qpat_x_assum `val_in_memory tv v _ actual.vs_memory` mp_tac >>
     qpat_x_assum `type_memory_size tv = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [LET_DEF, pairTheory.UNCURRY_DEF,
       MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC]) >>
  conj_tac >- suspend "effects" >>
  conj_tac >-
    (qpat_assum `abi_decoder_address_frame _ initial prepared`
      (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     simp_tac bool_ss [] >> metis_tac[]) >>
  conj_tac >-
    (rpt strip_tac >>
     `not_fresh_at end_st x` by (fs[not_fresh_at_def] >> decide_tac) >>
     metis_tac[]) >>
  conj_tac >-
    (`frag_exec ctx st middle (\s. s = initial) (\s. s = prepared) (K F)` by
       (irule frag_exec_run_inst_seq >> simp[Abbr `prepared`] >>
        qpat_x_assum `EVERY _ (emitted_insts st middle)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_CONJ]) >>
     `abi_decode_sim ctx func initial prepared` by
       (drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]) >>
     qpat_assum `abi_decode_sim ctx func initial prepared` mp_tac >>
     qpat_assum `abi_decode_sim ctx func prepared after_head` mp_tac >>
     qpat_assum `abi_decode_sim ctx func after_head actual` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[abi_decode_sim_trans]) >>
  conj_tac >-
    (qpat_assum `Bh SUBSET _` mp_tac >> qpat_assum `Bt SUBSET _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[SUBSET_DEF, IN_UNION, range_bytes_def, MAP_APPEND, MAP, SUM_APPEND, SUM] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  conj_tac >-
    (qpat_assum `DISJOINT Bh qh.t_mem` mp_tac >>
     qpat_assum `qtail.t_mem SUBSET qh.t_mem` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> SET_TAC[]) >>
  conj_tac >- suspend "support" >>
  conj_tac >-
    (qpat_assum `qtail.t_mem SUBSET qh.t_mem` mp_tac >>
     qpat_assum `qh.t_mem SUBSET qt.t_mem` mp_tac >>
     qpat_assum `qt.t_mem = tn.t_mem` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> SET_TAC[]) >>
  rpt strip_tac >>
  `not_fresh_at end_st x` by (fs[not_fresh_at_def] >> decide_tac) >>
  metis_tac[]
QED

Resume prefix_paired_members_cons_floor[effects]:
  `frag_ids middle end_st SUBSET frag_ids st final /\
   frag_ids end_st final SUBSET frag_ids st final` by
    (qpat_x_assum `st.cs_next_id < middle.cs_next_id` mp_tac >>
     qpat_x_assum `middle.cs_next_id <= end_st.cs_next_id` mp_tac >>
     qpat_x_assum `end_st.cs_next_id <= final.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiEncoderPropsTheory.frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> decide_tac) >>
  drule ctor_actual_member_setup_opcodes >> strip_tac >>
  drule_all ctorAbiActualWorldTheory.ctor_actual_sequence_world >> strip_tac >>
  `abi_encoder_registered_effect {} [] initial prepared` by
    (qpat_assum `abi_decoder_address_frame _ initial t` mp_tac >>
     qpat_assum `t.vs_accounts = _` mp_tac >>
     qpat_assum `t.vs_transient = _` mp_tac >>
     qpat_assum `t.vs_logs = _` mp_tac >>
     qpat_assum `t.vs_requests = _` mp_tac >>
     qpat_assum `t.vs_pending_deletions = _` mp_tac >>
     simp_tac bool_ss [Abbr `prepared`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abi_decoder_address_frame_def, abi_encoder_registered_effect_def] >>
     rpt strip_tac >> simp[]) >>
  qmatch_goalsub_abbrev_tac `abi_encoder_registered_effect allsites out initial actual` >>
  `abi_encoder_registered_effect allsites out initial prepared` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`, `[]`] >> asm_simp_tac (srw_ss()) []) >>
  `abi_encoder_registered_effect allsites out prepared after_head` by
    (simp_tac bool_ss [Abbr `allsites`, Abbr `out`] >>
     irule ctor_actual_child_narrow_effect >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_encoder_registered_effect allsites out after_head actual` by
    (simp_tac bool_ss [Abbr `allsites`, Abbr `out`] >>
     irule ctor_actual_child_narrow_effect >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     asm_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0] >> decide_tac) >>
  qpat_assum `abi_encoder_registered_effect allsites out initial prepared` mp_tac >>
  qpat_assum `abi_encoder_registered_effect allsites out prepared after_head` mp_tac >>
  qpat_assum `abi_encoder_registered_effect allsites out after_head actual` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[abi_encoder_registered_effect_trans]
QED

Resume prefix_paired_members_cons_floor[support]:
  qpat_assum `!mem. _ ==> val_in_memory tv v _ mem` mp_tac >>
  qpat_assum `!mem. _ ==> tuple_in_memory vs' tvs _ mem` mp_tac >>
  qpat_assum `!a. a IN Bh ==> mem_bytes_at a 1 actual.vs_memory = _` mp_tac >>
  qpat_assum `type_memory_size tv = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  `val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) mem` by
    (first_x_assum irule >> rpt strip_tac >>
     metis_tac[IN_UNION]) >>
  `tuple_in_memory vs' tvs (d + SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) mem` by
    (first_x_assum irule >> metis_tac[IN_UNION]) >>
  qpat_assum `val_in_memory tv v _ mem` mp_tac >>
  qpat_assum `tuple_in_memory vs' tvs _ mem` mp_tac >>
  qpat_assum `type_memory_size tv = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [val_in_memory_def, LET_DEF, pairTheory.UNCURRY_DEF,
     MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC]
QED

Finalise prefix_paired_members_cons_floor

Theorem prefix_paired_members_floor:
  !tys tvs. LIST_REL (^canonical_pair_floor) tys tvs ==>
    (^paired_members_floor) tys tvs
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >>
  simp_tac bool_ss [LIST_REL_def, prefix_paired_members_nil_floor] >> strip_tac >>
  rename1 `LIST_REL _ tys rest` >>
  mp_tac (Q.INST [`ty` |-> `h`, `tv` |-> `h'`, `tvs` |-> `rest`]
    prefix_paired_members_cons_floor) >>
  (impl_tac >- (conj_tac >- (BETA_TAC >> first_assum ACCEPT_TAC) >>
    first_x_assum irule >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss []
QED

Theorem prefix_paired_tuple_floor:
  LIST_REL (^canonical_pair_floor) tys tvs ==>
    (^canonical_pair_floor) (TupleT tys) (TupleTV tvs)
Proof
  strip_tac >> drule prefix_paired_members_floor >>
  disch_then (mk_asm "members") >>
  qpat_x_assum `LIST_REL _ tys tvs` kall_tac >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_to_vyper env (TupleT tys) av = SOME v` by
    fs[abi_decoder_metadata_def] >>
  drule abi_decoder_tuple_values >> strip_tac >>
  qpat_x_assum `av = ListV _` SUBST_ALL_TAC >>
  qpat_x_assum `v = ArrayV _` SUBST_ALL_TAC >>
  drule_all abi_decoder_tuple_members >> strip_tac >>
  `type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys)` by
    (simp[Once type_memory_bytes_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  `vyper_to_abi_type env (TupleT tys) = Tuple (MAP (vyper_to_abi_type env) tys)` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
  drule abi_decoder_complex_trace >> strip_tac >>
  qpat_x_assum `abi_decode_complex_head_guard _ _ _ _ = _`
    (SUBST_ALL_TAC o SYM o SIMP_RULE (srw_ss()) [abi_decode_complex_head_guard_def, comp_return_def]) >>
  asm_x "members" (mp_tac o SIMP_RULE bool_ss [MAP, SUM, APPEND, ADD_CLAUSES] o
    Q.INST [`final` |-> `st'`, `pretys` |-> `[]`, `pretvs` |-> `[]`,
      `preavs` |-> `[]`, `prevs` |-> `[]`] o SPEC_ALL o BETA_RULE) >>
  (impl_tac >- (asm_simp_tac bool_ss [Once abi_decoder_members_def] >>
    gvs[Excl "enc_def"] >> metis_tac[])) >>
  strip_tac >> qexistsl_tac [`actual`,`H`,`qt`,`B`] >>
  asm_simp_tac bool_ss [val_in_memory_tuple]
QED

val canonical_pair_floor_desc =
  ``(\env sf. ^canonical_pair_floor) (env \\ nsid) (sf \\ nsid_to_string nsid)``;

Theorem prefix_paired_struct_floor:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (^canonical_pair_floor_desc) (MAP SND args) tvs ==>
  (^canonical_pair_floor) (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH tvs = LENGTH args` by (drule LIST_REL_LENGTH >> simp[]) >>
  qpat_x_assum `LIST_REL _ _ _` (assume_tac o BETA_RULE) >>
  drule (Q.INST [`env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`]
    prefix_paired_members_floor) >>
  disch_then (mk_asm "members") >>
  qpat_x_assum `LIST_REL _ _ _` kall_tac >>
  BETA_TAC >> rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_to_vyper env (StructT nsid) av = SOME v` by fs[abi_decoder_metadata_def] >>
  drule abi_decoder_struct_values >> strip_tac >>
  qpat_x_assum `av = ListV _` SUBST_ALL_TAC >>
  qpat_x_assum `v = StructV _` SUBST_ALL_TAC >>
  drule_all abi_decoder_struct_members_at >> strip_tac >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  `type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args))` by
    fs[abi_decoder_metadata_def, Once type_memory_size_def, Excl "enc_def"] >>
  drule_all abi_decoder_struct_field_types >> strip_tac >>
  drule abi_decoder_struct_infos >> strip_tac >>
  `vyper_to_abi_type env (StructT nsid) =
    Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  drule abi_decoder_complex_trace >> strip_tac >>
  qpat_x_assum `abi_decode_complex_head_guard _ _ _ _ = _`
    (SUBST_ALL_TAC o SYM o SIMP_RULE (srw_ss()) [abi_decode_complex_head_guard_def, comp_return_def]) >>
  asm_x "members" (mp_tac o SIMP_RULE bool_ss [MAP, SUM, APPEND, ADD_CLAUSES] o
    Q.INST [`final` |-> `st'`, `pretys` |-> `[]`, `pretvs` |-> `[]`,
      `preavs` |-> `[]`, `prevs` |-> `[]`,
      `vs` |-> `MAP SND (fields:(string # value) list)`] o SPEC_ALL o BETA_RULE) >>
  (impl_tac >- (asm_simp_tac bool_ss [Once abi_decoder_members_def] >>
    gvs[Excl "enc_def"] >> metis_tac[])) >>
  strip_tac >>
  `!mem. tuple_in_memory (MAP SND fields) tvs d mem ==>
     fields_in_memory fields (ZIP (MAP FST args,tvs)) d mem` by
    (rpt strip_tac >> irule static_fields_memory_zip >>
     fs[abi_decoder_metadata_def, Once value_has_type_def]) >>
  qexistsl_tac [`actual`,`H`,`qt`,`B`] >>
  asm_simp_tac bool_ss [val_in_memory_struct] >>
  metis_tac[]
QED
