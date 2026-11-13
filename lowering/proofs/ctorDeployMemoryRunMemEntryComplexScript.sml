Theory ctorDeployMemoryRunMemEntryComplex
Ancestors
  loweringStateRelDefs
  ctorDeployLoweringEntryMember
  ctorDeployMemoryRunMemEntryMembers ctorDeployMemoryRunMemEntryCompositeSetup
  ctorDeployMemoryRunMemEntryWord ctorAbiActualComplex ctorAbiActualObservations
  ctorAbiActualNarrow ctorAbiActualChildFrame ctorAbiActualLabelEmpty
  abiDecoderComplexExecute abiDecoderComplexGuard abiDecoderComplexHead
  abiDecoderReentry abiDecoderDynamicLoopSetup abiDecoderVarSequence
  abiDecoderContract abiDecoderLoop fragExec instIdxIndep compileEnv
  abiEncoderRegisteredEffect venomState venomExecSemantics venomInst words list arithmetic
  abiDecoderMembers abiDecoderMemberInfos abiDecodeRanges contractABI vyperABI
  allocaFrontierBound allocaBudgetProps venomMemDefs pred_set exprLowering ctorAbiActualFrame abiEncoderProps
  abiDecoderTupleInputs abiDecoderTypedContract abiDecoderCoherence valueEncodingProps
  abiDecoderStruct abiStaticDynarrayLayout vyperTyping finite_map valueEncoding valueEncodingTyping
  fragGasPathMem allocaHistory

val C = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH initial.vs_data_section /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\ unit_alloca_budget ctx < dimword (:256) /\
 alloca_history func initial /\
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
 actual.vs_labels = initial.vs_labels /\
 gas_path_mem ctx func initial 0 (OK actual) /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 alloca_history func actual``;

Theorem ctor_checked_complex_alloca_transport[local]:
  abi_decoder_address_frame next s t ==>
  (alloca_inv t = alloca_inv s) /\
  (alloca_frontier_inv ctx func site t = alloca_frontier_inv ctx func site s) /\
  (ctor_actual_scratch func ids D N t = ctor_actual_scratch func ids D N s)
Proof
  simp[abi_decoder_address_frame_def] >> strip_tac >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_def, remaining_alloca_budget_def, ctor_actual_scratch_def]
QED

Theorem ctor_checked_complex_execute:
  LIST_REL (^C) tys tvs /\
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecComplex dyn (abi_decoder_member_infos sf ce tys)) st = ((),final) /\
  abi_decoder_members ce env sf tys tvs avs vs /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) < dimword (:256) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) <= LENGTH initial.vs_data_section /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))) initial.vs_data_section = enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) <= h /\ h < dimword (:256)) /\
  (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\ unit_alloca_budget ctx < dimword (:256) /\
  alloca_history func initial /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) tys) <= D+N /\ D+N <= initial.vs_alloca_next /\
  frag_ids st final SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. tuple_in_memory vs tvs d actual.vs_memory /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final)) [(d,SUM (MAP (type_memory_bytes ce) tys))] initial actual /\
  alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
  ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
  actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
  (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
  ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
  abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\ actual.vs_labels = initial.vs_labels /\
  gas_path_mem ctx func initial 0 (OK actual) /\ actual.vs_gas_readings = initial.vs_gas_readings /\
  alloca_history func actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_complex_trace >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_complex_code >> strip_tac >>
  rename1 `abi_decode_complex_head_guard src hi _ st = ((),middle)` >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var hi` by
    (qpat_x_assum `!x. _ ==> not_fresh_at st x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def] >> metis_tac[]) >>
  `FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys) <=
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))` by
    (qpat_x_assum `LIST_REL _ _ _` kall_tac >>
     drule abi_decoder_members_relations >> strip_tac >>
     drule abi_decoder_member_infos_layout >> strip_tac >>
     `has_types (MAP (vyper_to_abi_type env) tys) avs` by simp[has_types_LIST_REL] >>
     drule canonical_tuple_length >> strip_tac >>
     gvs[Excl "enc_def"] >> decide_tac) >>
  mp_tac (Q.INST [`st'` |-> `middle`, `head_sz` |->
    `FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys)`]
    ctor_checked_complex_guard_labels) >>
  (impl_tac >- (qpat_x_assum `LIST_REL _ _ _` kall_tac >>
    asm_simp_tac bool_ss [] >>
    Cases_on `hi = Lit 0w` >- simp[] >>
    qpat_x_assum `hi = Lit 0w \/ _` mp_tac >>
    asm_simp_tac bool_ss [] >> strip_tac >> qexists `h` >> asm_simp_tac bool_ss [] >> decide_tac)) >>
  disch_then (qx_choose_then `prepared` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all ctor_word_path_sim >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`,
    `next` |-> `st.cs_next_var`] ctor_checked_complex_alloca_transport) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `abi_decoder_address_frame _ initial prepared`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `eval_operand src prepared = SOME (n2w sb) /\
   eval_operand dst prepared = SOME (n2w d)` by
    (qpat_x_assum `LIST_REL _ _ _` kall_tac >>
     conj_tac >> first_x_assum irule >> simp[]) >>
  `!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at middle x` by
    (qpat_x_assum `!x. src = Var x \/ dst = Var x \/ hi = Var x ==> _` mp_tac >>
     qpat_x_assum `st.cs_next_var <= middle.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `frag_ids middle final SUBSET ids` by
    (qpat_x_assum `LIST_REL _ _ _` kall_tac >>
     gvs[frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> decide_tac) >>
  drule ctor_checked_members_run >>
  disch_then (mp_tac o SIMP_RULE bool_ss [MAP, SUM, APPEND, ADD_CLAUSES] o
    Q.INST [`st` |-> `middle`, `initial` |-> `prepared:venom_state`,
      `pretys` |-> `[]`, `pretvs` |-> `[]`, `preavs` |-> `[]`, `prevs` |-> `[]`] o SPEC_ALL o BETA_RULE) >>
  (impl_tac >- (qpat_x_assum `LIST_REL _ _ _` kall_tac >>
    asm_simp_tac (srw_ss()) [Once abi_decoder_members_def, Excl "enc_def"] >> metis_tac[])) >>
  strip_tac >> rename1 `tuple_in_memory vs tvs d actual.vs_memory` >>
  qpat_x_assum `LIST_REL _ _ _` kall_tac >>
  `frag_ids middle final SUBSET frag_ids st final` by
    (qpat_x_assum `st.cs_next_id <= middle.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> decide_tac) >>
  `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final))
    [(d,SUM (MAP (type_memory_bytes ce) tys))] prepared actual` by
    (irule ctor_actual_child_narrow_effect >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >> simp[]) >>
  `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final))
    [(d,SUM (MAP (type_memory_bytes ce) tys))] initial prepared` by
    (irule abi_encoder_registered_effect_enlarge >> qexistsl [`{}`, `[]`] >> simp[]) >>
  qexists `actual` >> asm_simp_tac bool_ss [] >>
  conj_tac >- metis_tac[abi_encoder_registered_effect_trans] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at middle x` by
        (qpat_x_assum `not_fresh_at st x` mp_tac >>
         qpat_x_assum `st.cs_next_var <= middle.cs_next_var` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
      `lookup_var x prepared = SOME w` by
        (qpat_x_assum `!op w. abi_decoder_operand_live _ _ /\ _ ==> _`
          (qspec_then `Var x` mp_tac) >>
         simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
           eval_operand_def, GSYM not_fresh_at_def]) >> metis_tac[]) >>
  conj_tac >- metis_tac[abi_decode_sim_trans] >>
  metis_tac[gas_path_mem_then, ADD_0]
QED

Theorem ctor_checked_tuple_run:
  LIST_REL (^C) tys tvs ==> (^C) (TupleT tys) (TupleTV tvs)
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_to_vyper env (TupleT tys) av = SOME v` by fs[abi_decoder_metadata_def] >>
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
  mp_tac (Q.INST [`final` |-> `st'`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`] ctor_checked_complex_execute) >>
  (impl_tac >- (NO_STRIP_FULL_SIMP_TAC bool_ss [vyper_to_abi_types_MAP] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists `actual` >> asm_simp_tac bool_ss [val_in_memory_tuple]
QED

val Cdesc = ``(\env sf. ^C) (env \\ nsid) (sf \\ nsid_to_string nsid)``;

Theorem ctor_checked_struct_run:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (^Cdesc) (MAP SND args) tvs ==>
  (^C) (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
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
  mp_tac (Q.INST [`final` |-> `st'`,
    `env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
    `tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
    `vs` |-> `MAP SND (fields:(string # value) list)`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields)
      (MAP SND (args:(string # vyperAST$type) list))`] ctor_checked_complex_execute) >>
  (impl_tac >- (NO_STRIP_FULL_SIMP_TAC bool_ss [vyper_to_abi_types_MAP] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `fields_in_memory fields (ZIP (MAP FST args,tvs)) d actual.vs_memory` by
    (irule static_fields_memory_zip >> fs[abi_decoder_metadata_def, Once value_has_type_def]) >>
  qexists `actual` >> asm_simp_tac bool_ss [val_in_memory_struct]
QED
