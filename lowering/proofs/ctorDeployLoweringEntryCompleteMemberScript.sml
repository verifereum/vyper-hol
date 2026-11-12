(* Complete heterogeneous member execution: observations share the run witness. *)
Theory ctorDeployLoweringEntryCompleteMember
Ancestors
  loweringStateRelDefs valueEncodingDefs
  ctorDeployLoweringEntryCompleteMemberBoundary ctorDeployLoweringEntryMember
  ctorAbiActualChildFrame ctorAbiActualMemberInputs abiDecoderMemberBody abiDecoderMemberInfos
  abiDecoderComplexExecute abiDecoderComplexHead abiDecoderEmpty abiDecoderDynamicLoopSetup abiDecoderReentry ctorAbiActualObservations
  abiDecoderMemberCons abiDecoderMemberSetup abiDecoderCoherence abiDecodeRanges abiDecoderMemberCode abiEncoderProps
  abiDecoderMembers abiDecoderContract abiEncoderRegisteredEffect abiEncoder abiDecoderLoop
  ctorDeployLoweringEntryArrayFrame ctorDeployLoweringEntryRegistration
  ctorDeployMemoryFrontier allocaFrontierBound allocaBudgetProps
  valueEncoding contractABI rich_list pred_set
  fragExec compileEnv exprLoweringProps venomExecSemantics venomState
  venomInst words list arithmetic

val Ccomplete = ``\ty tv.
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
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx``;

val Mcomplete = ``\tys tvs.
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
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ tys)) <= D+N /\
 D+N <= initial.vs_alloca_next /\ frag_ids st final SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final))
   [(d + SUM (MAP (type_memory_bytes ce) pretys), SUM (MAP (type_memory_bytes ce) tys))] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx``;

Theorem deploy_ctor_members_run_complete_nil:
  (^Mcomplete) [] []
Proof
  BETA_TAC >> rpt gen_tac >>
  simp[abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def,
    comp_return_def, Excl "enc_def"] >> strip_tac >>
  drule abi_decoder_members_lengths >> strip_tac >> gvs[Excl "enc_def"] >>
  qexists `initial` >>
  simp[val_in_memory_def, abi_encoder_registered_effect_refl, abi_decode_sim_refl]
QED

val Hcomplete = ``\ctx func site ids D N limit_st tv v d sz st st' initial actual.
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,sz)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 actual.vs_code = initial.vs_code /\ actual.vs_outcomes = initial.vs_outcomes /\
 actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx``;

Theorem deploy_ctor_member_child_run_complete:
  (^Ccomplete) ty tv /\
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))) <= h /\ h < dimword (:256)) /\
  abi_decoder_address_frame st.cs_next_var initial prepared /\
  abi_decoder_operand_live st.cs_next_var hi /\ st.cs_next_var <= middle.cs_next_var /\
  eval_operand childsrc prepared = SOME (n2w (sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) (LENGTH pretys))) /\
  eval_operand childdst prepared = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var childdst /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) <= D+N /\
  compile_abi_decode_to_buf childdst childsrc DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st prepared /\
  fn_has_code middle end_st func /\ fn_inst_ids_distinct func /\
  (middle.cs_blocks = end_st.cs_blocks \/ !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv prepared /\ alloca_frontier_inv_from k ctx func site prepared /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D+N <= prepared.vs_alloca_next /\ frag_ids middle end_st SUBSET ids /\
  ctor_actual_scratch func ids D N prepared /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?actual. (^Hcomplete) ctx func site ids D N limit_st tv v
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty)
    middle end_st prepared actual
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all ctor_actual_member_child_inputs >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  BETA_TAC >> asm "child" (drule o BETA_RULE) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then irule >> asm_simp_tac bool_ss [] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
    (preavs ++ av::avs) (LENGTH pretys)` >> asm_simp_tac bool_ss []
QED

Theorem deploy_ctor_member_empty_run_complete:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecComplex T []) st = ((),st') /\
  fn_has_code st st' func /\ eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. (^Hcomplete) ctx func site ids D N limit_st tv v d (type_memory_bytes ce ty)
    st st' initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_empty_metadata_value >> strip_tac >>
  drule_all deploy_ctor_empty_complex_complete_frame_reach >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `actual.vs_allocas = initial.vs_allocas /\
   actual.vs_alloca_next = initial.vs_alloca_next` by
    fs[abi_decoder_address_frame_def] >>
  drule_all deploy_ctor_array_allocation_state >> strip_tac >>
  qexists `actual` >> BETA_TAC >> asm_simp_tac bool_ss [] >>
  conj_tac
  >- (irule abi_encoder_registered_effect_enlarge >>
      qexistsl [`{}`, `[]`] >> simp[]) >>
  qpat_assum `abi_decoder_address_frame _ initial actual`
    (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  first_x_assum (qspec_then `Var x` mp_tac) >>
  qpat_x_assum `lookup_var x initial = SOME w` mp_tac >>
  qpat_x_assum `not_fresh_at st x` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    not_fresh_at_def, eval_operand_def]
QED

Theorem deploy_ctor_member_tail_run_complete:
  (^Mcomplete) tys tvs ==>
  !pretys pretvs preavs prevs ty tv av avs v vs.
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) ==>
  !st initial prepared middle end_st after_head ctx func site ids D N limit_st sb d.
  abi_decoder_address_frame st.cs_next_var initial prepared /\
  prepared.vs_labels = initial.vs_labels /\
  (^Hcomplete) ctx func site ids D N limit_st tv v
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty)
    middle end_st prepared after_head /\
  st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= end_st.cs_next_var ==>
  !dst src hi final.
  compile_abi_decode_complex_elems dst src DLOAD (Lit 0w) hi (abi_decoder_member_infos sf ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (pretys ++ [ty]))))
    (SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) end_st = ((),final) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))) <= h /\ h < dimword (:256)) /\
  (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  fn_has_code end_st final func /\ fn_inst_ids_distinct func /\
  (end_st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) <= D+N /\
  frag_ids end_st final SUBSET ids ==>
  ?actual. tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) actual.vs_memory /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids end_st final))
    [(d + SUM (MAP (type_memory_bytes ce) (pretys ++ [ty])), SUM (MAP (type_memory_bytes ce) tys))]
    after_head actual /\
  alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
  ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
  actual.vs_data_section = after_head.vs_data_section /\ actual.vs_call_ctx = after_head.vs_call_ctx /\
  (!x w. not_fresh_at end_st x /\ lookup_var x after_head = SOME w ==> lookup_var x actual = SOME w) /\
  ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
  actual.vs_inst_idx = LENGTH final.cs_current_insts /\
  abi_decode_sim ctx func after_head actual /\ fresh_vars_wrt limit_st actual /\
  actual.vs_labels = after_head.vs_labels /\ actual.vs_gas_readings = after_head.vs_gas_readings /\
  actual.vs_code = after_head.vs_code /\ actual.vs_outcomes = after_head.vs_outcomes /\
  actual.vs_tx_ctx = after_head.vs_tx_ctx /\ actual.vs_block_ctx = after_head.vs_block_ctx
Proof
  disch_then (mk_asm "tail") >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `(^Hcomplete) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
  `abi_decoder_members ce env sf (pretys ++ [ty]) (pretvs ++ [tv])
    (preavs ++ [av]) (prevs ++ [v]) /\ abi_decoder_members ce env sf tys tvs avs vs` by
    (qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
      (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >> strip_tac >>
     conj_tac >- (irule abi_decoder_members_join >> simp[abi_decoder_members_def]) >>
     first_assum ACCEPT_TAC) >>
  `!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x after_head = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at middle x` by
       (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
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
     qpat_assum `!x w. not_fresh_at middle x /\ lookup_var x prepared = SOME w ==>
       lookup_var x after_head = SOME w` irule >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand src after_head = SOME (n2w sb) /\
   eval_operand dst after_head = SOME (n2w d) /\
   (!h. eval_operand hi initial = SOME (n2w h) ==> eval_operand hi after_head = SOME (n2w h))` by
    (rpt conj_tac >> rpt strip_tac >> irule ctor_actual_old_operand >>
     qexistsl [`initial`, `st`] >> simp[] >> metis_tac[]) >>
  `!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at end_st x` by
    (rpt strip_tac >>
     `not_fresh_at st x` by
       (pop_assum mp_tac >>
        qpat_x_assum `!x. src = Var x \/ _ ==> not_fresh_at st x` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `after_head.vs_data_section = initial.vs_data_section` by
    fs[abi_decoder_address_frame_def] >>
  asm "tail" (drule o BETA_RULE) >>
  disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_members _ _ _ (_ ++ [_]) _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_members _ _ _ tys _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  (impl_tac >- (asm_x "tail" kall_tac >>
    asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND] >> metis_tac[])) >> simp[]
QED

Theorem deploy_ctor_members_cons_layout:
  compile_abi_decode_complex_elems dst src DLOAD (Lit 0w) hi (abi_decoder_member_infos sf ce (ty::tys))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),final) /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  fn_has_code st final func /\ final.cs_next_var <= limit_st.cs_next_var /\
  (st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\ frag_ids st final SUBSET ids ==>
  ?ops middle end_st.
  abi_decode_member_setup dst src DLOAD (Lit 0w) hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) DLOAD (Lit 0w) hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  compile_abi_decode_complex_elems dst src DLOAD (Lit 0w) hi (abi_decoder_member_infos sf ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (pretys ++ [ty]))))
    (SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) end_st = ((),final) /\
  fn_has_code st middle func /\ fn_has_code middle end_st func /\ fn_has_code end_st final func /\
  st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= end_st.cs_next_var /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  st.cs_next_id < middle.cs_next_id /\ middle.cs_next_id <= end_st.cs_next_id /\
  end_st.cs_next_id <= final.cs_next_id /\
  (middle.cs_blocks = end_st.cs_blocks \/ !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  (end_st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  frag_ids middle end_st SUBSET ids /\ frag_ids end_st final SUBSET ids
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_member_cons_trace >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule_all abi_decoder_members_child_phi >> disch_then assume_tac >>
  drule_all abi_decoder_members_tail_phi >> disch_then assume_tac >>
  `fn_has_code st middle func /\ fn_has_code middle end_st func` by
    (conj_tac >> irule (cj 1 fn_has_code_split) >> metis_tac[]) >>
  `compile_abi_decode_complex_elems dst src DLOAD (Lit 0w) hi (abi_decoder_member_infos sf ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (pretys ++ [ty]))))
    (SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) end_st = ((),final)` by
    (qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >> strip_tac >>
     drule abi_decoder_coherent_header >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
     qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ end_st = _` mp_tac >>
     qpat_x_assum `abi_embedded_static_size _ ty = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0]) >>
  `frag_ids middle end_st SUBSET ids /\ frag_ids end_st final SUBSET ids` by
    (qpat_x_assum `frag_ids st final SUBSET ids` mp_tac >>
     qpat_x_assum `st.cs_next_id < middle.cs_next_id` mp_tac >>
     qpat_x_assum `middle.cs_next_id <= end_st.cs_next_id` mp_tac >>
     qpat_x_assum `end_st.cs_next_id <= final.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> decide_tac) >>
  qexistsl [`ops`, `middle`, `end_st`] >> asm_simp_tac arith_ss []
QED

Theorem deploy_ctor_member_child_complete_elim:
  compile_abi_decode_to_buf childdst childsrc DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) middle = ((),end_st) ==>
  !pretys. abi_decoder_members ce env sf pretys pretvs preavs prevs ==>
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) ==>
  abi_decoder_address_frame st.cs_next_var initial prepared ==>
  (^Ccomplete) ty tv ==>
  !sb d ctx func site ids D N limit_st.
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))) <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var hi /\ st.cs_next_var <= middle.cs_next_var /\
  eval_operand childsrc prepared = SOME (n2w (sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) (LENGTH pretys))) /\
  eval_operand childdst prepared = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var childdst /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) <= D+N /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st prepared /\
  fn_has_code middle end_st func /\ fn_inst_ids_distinct func /\
  (middle.cs_blocks = end_st.cs_blocks \/ !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv prepared /\ alloca_frontier_inv_from k ctx func site prepared /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D+N <= prepared.vs_alloca_next /\ frag_ids middle end_st SUBSET ids /\
  ctor_actual_scratch func ids D N prepared /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?actual. (^Hcomplete) ctx func site ids D N limit_st tv v
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty)
    middle end_st prepared actual
Proof
  disch_tac >> gen_tac >> ntac 4 disch_tac >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all deploy_ctor_member_child_run_complete >> simp[]
QED


Theorem deploy_ctor_member_child_encoded_complete:
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) ==>
  compile_abi_decode_to_buf childdst childsrc DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_address_frame st.cs_next_var initial prepared /\ (^Ccomplete) ty tv /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))) <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var hi /\ st.cs_next_var <= middle.cs_next_var /\
  eval_operand childsrc prepared = SOME (n2w (sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) (LENGTH pretys))) /\
  eval_operand childdst prepared = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var childdst /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) <= D+N /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st prepared /\
  fn_has_code middle end_st func /\ fn_inst_ids_distinct func /\
  (middle.cs_blocks = end_st.cs_blocks \/ !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv prepared /\ alloca_frontier_inv_from k ctx func site prepared /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D+N <= prepared.vs_alloca_next /\ frag_ids middle end_st SUBSET ids /\
  ctor_actual_scratch func ids D N prepared /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?actual. (^Hcomplete) ctx func site ids D N limit_st tv v
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty)
    middle end_st prepared actual
Proof
  disch_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all deploy_ctor_member_child_run_complete >> simp[]
QED

Theorem deploy_ctor_member_prepared_complete:
  compile_abi_decode_complex_elems dst src DLOAD (Lit 0w) hi (abi_decoder_member_infos sf ce (ty::tys))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),final) /\
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs))) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs))) <= h /\ h < dimword (:256)) /\
  (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) <= D+N /\
  D+N <= initial.vs_alloca_next /\ frag_ids st final SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (^Ccomplete) ty tv ==>
  ?middle end_st prepared after_head.
  compile_abi_decode_complex_elems dst src DLOAD (Lit 0w) hi (abi_decoder_member_infos sf ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (pretys ++ [ty]))))
    (SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) end_st = ((),final) /\
  abi_decoder_address_frame st.cs_next_var initial prepared /\ prepared.vs_labels = initial.vs_labels /\
  prepared.vs_gas_readings = initial.vs_gas_readings /\ prepared.vs_code = initial.vs_code /\
  prepared.vs_outcomes = initial.vs_outcomes /\ prepared.vs_tx_ctx = initial.vs_tx_ctx /\
  prepared.vs_block_ctx = initial.vs_block_ctx /\
  abi_encoder_registered_effect {} [] initial prepared /\ abi_decode_sim ctx func initial prepared /\
  st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= end_st.cs_next_var /\
  fn_has_code end_st final func /\
  (end_st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  frag_ids end_st final SUBSET ids /\
  frag_ids middle end_st SUBSET frag_ids st final /\
  frag_ids end_st final SUBSET frag_ids st final /\
  (^Hcomplete) ctx func site ids D N limit_st tv v
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty)
    middle end_st prepared after_head
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> disch_then (mk_asm "child") >>
  drule_all deploy_ctor_members_cons_layout >>
  disch_then (qx_choose_then `ops` (qx_choose_then `middle`
    (qx_choose_then `end_st` (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var hi` by
    (qpat_x_assum `!x. src = Var x \/ dst = Var x \/ hi = Var x ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  drule_all deploy_ctor_member_setup_complete_frame_narrow >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[Excl "enc_def"] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial prepared` >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` kall_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  drule_all deploy_ctor_array_allocation_state >> strip_tac >>
  `?after_head. (^Hcomplete) ctx func site ids D N limit_st tv v
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty)
    middle end_st prepared after_head` by
    (reverse (Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`)
     >- (qpat_assum `type_to_abi_dec_info sf ce ty <> DecComplex T []` (fn flag =>
           qpat_x_assum `eval_operand (FST ops) prepared = _`
             (assume_tac o PURE_REWRITE_RULE [flag, COND_CLAUSES])) >>
         asm "child" assume_tac >>
         drule_at (Pat `mem_bytes_at _ _ _ = enc (Tuple _) (ListV _)`)
           deploy_ctor_member_child_encoded_complete >>
         disch_then irule >> asm_x "child" kall_tac >>
         qpat_x_assum `middle.cs_next_var = _` kall_tac >>
         asm_simp_tac bool_ss [] >>
         qexistsl [`SND ops`, `FST ops`, `hi`, `pretvs`, `prevs`, `sf`, `st`, `tvs`, `vs`] >>
         rule_assum_tac BETA_RULE >>
         asm_simp_tac bool_ss [MAP_APPEND, MAP] >> first_assum ACCEPT_TAC) >>
     drule_all ctor_actual_member_inline_guard >> disch_then assume_tac >>
     `abi_decoder_operand_live middle.cs_next_var hi` by
       (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
     qpat_assum `type_to_abi_dec_info sf ce ty = DecComplex T []` (fn flag =>
       qpat_x_assum `compile_abi_decode_to_buf (SND ops) _ _ _ _ _ _ = _`
         (assume_tac o PURE_REWRITE_RULE [flag]) >>
       qpat_x_assum `eval_operand (FST ops) prepared = _`
         (assume_tac o PURE_REWRITE_RULE [flag, COND_CLAUSES])) >>
     `abi_decoder_coherent ce env sf ty tv /\
      abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v` by
       (qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
          (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >>
        simp_tac bool_ss [] >> metis_tac[]) >>
     drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) deploy_ctor_member_empty_run_complete >>
     disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
     BETA_TAC >> disch_then irule >> asm_x "child" kall_tac >>
     asm_simp_tac bool_ss [] >>
     reverse conj_tac >- (qexists `sf` >> asm_simp_tac bool_ss []) >>
     qexists `sb + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))` >>
     asm_simp_tac bool_ss []) >>
  `frag_ids middle end_st SUBSET frag_ids st final /\
   frag_ids end_st final SUBSET frag_ids st final` by
    (simp[frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> decide_tac) >>
  qexistsl [`middle`, `end_st`, `prepared`, `after_head`] >>
  qpat_x_assum `_ ctx func site ids D N limit_st tv v _ _ middle end_st prepared after_head`
    (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
  rule_assum_tac (PURE_REWRITE_RULE [MAP_APPEND, MAP]) >>
  asm_simp_tac bool_ss [MAP_APPEND, MAP]
QED

Theorem deploy_ctor_member_old_lookup_join:
  abi_decoder_address_frame st.cs_next_var initial prepared /\
  st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= end_st.cs_next_var /\
  (!x w. not_fresh_at middle x /\ lookup_var x prepared = SOME w ==>
     lookup_var x after_head = SOME w) /\
  (!x w. not_fresh_at end_st x /\ lookup_var x after_head = SOME w ==>
     lookup_var x actual = SOME w) ==>
  !x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x actual = SOME w
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> rpt strip_tac >>
  `not_fresh_at middle x /\ not_fresh_at end_st x` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
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
  metis_tac[]
QED

Theorem deploy_ctor_members_complete_join:
  abi_decoder_address_frame st.cs_next_var initial prepared /\
  abi_encoder_registered_effect {} [] initial prepared /\
  abi_decode_sim ctx func initial prepared /\ prepared.vs_labels = initial.vs_labels /\
  prepared.vs_gas_readings = initial.vs_gas_readings /\ prepared.vs_code = initial.vs_code /\
  prepared.vs_outcomes = initial.vs_outcomes /\ prepared.vs_tx_ctx = initial.vs_tx_ctx /\
  prepared.vs_block_ctx = initial.vs_block_ctx /\
  (^Hcomplete) ctx func site ids D N limit_st tv v p (type_memory_bytes ce ty)
    middle end_st prepared after_head /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  D <= p /\ p + type_memory_bytes ce ty <= D+N /\
  st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= end_st.cs_next_var /\
  frag_ids middle end_st SUBSET frag_ids st final /\
  frag_ids end_st final SUBSET frag_ids st final /\ frag_ids end_st final SUBSET ids /\
  tuple_in_memory vs tvs (p + type_memory_bytes ce ty) actual.vs_memory /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids end_st final))
    [(p + type_memory_bytes ce ty, SUM (MAP (type_memory_bytes ce) tys))] after_head actual /\
  alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
  ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
  actual.vs_data_section = after_head.vs_data_section /\ actual.vs_call_ctx = after_head.vs_call_ctx /\
  (!x w. not_fresh_at end_st x /\ lookup_var x after_head = SOME w ==> lookup_var x actual = SOME w) /\
  ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
  actual.vs_inst_idx = LENGTH final.cs_current_insts /\
  abi_decode_sim ctx func after_head actual /\ fresh_vars_wrt limit_st actual /\
  actual.vs_labels = after_head.vs_labels /\ actual.vs_gas_readings = after_head.vs_gas_readings /\
  actual.vs_code = after_head.vs_code /\ actual.vs_outcomes = after_head.vs_outcomes /\
  actual.vs_tx_ctx = after_head.vs_tx_ctx /\ actual.vs_block_ctx = after_head.vs_block_ctx ==>
  tuple_in_memory (v::vs) (tv::tvs) p actual.vs_memory /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final))
    [(p, SUM (MAP (type_memory_bytes ce) (ty::tys)))] initial actual /\
  alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
  ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
  actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
  (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
  ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
  actual.vs_inst_idx = LENGTH final.cs_current_insts /\
  abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
  actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\
  actual.vs_code = initial.vs_code /\ actual.vs_outcomes = initial.vs_outcomes /\
  actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `(^Hcomplete) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
  `type_memory_size tv = type_memory_bytes ce ty /\ val_wf tv v` by
    (qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >> strip_tac >>
     qpat_x_assum `abi_decoder_metadata _ _ ty tv _ av v`
       (mp_tac o PURE_REWRITE_RULE [abiDecoderTypedContractTheory.abi_decoder_metadata_def]) >> strip_tac >>
     metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
  conj_tac
  >- (drule_at (Pat `val_in_memory _ _ _ _`) deploy_ctor_member_tuple_join >>
      disch_then (drule_at (Pat `type_memory_size tv = _`)) >>
      disch_then (drule_at (Pat `abi_encoder_registered_effect _ _ after_head actual`)) >>
      disch_then irule >> asm_simp_tac bool_ss [] >>
      qexistsl [`D`, `N`, `ids`] >> asm_simp_tac bool_ss []) >>
  conj_tac
  >- (simp_tac bool_ss [MAP, SUM, ADD_COMM] >>
      drule_at (Pat `abi_encoder_registered_effect {} [] _ _`) deploy_ctor_member_effect_join >>
      disch_then (drule_at (Pat `abi_encoder_registered_effect _ _ prepared after_head`)) >>
      disch_then (drule_at (Pat `abi_encoder_registered_effect _ _ after_head actual`)) >>
      disch_then irule >> asm_simp_tac bool_ss []) >>
  `prepared.vs_data_section = initial.vs_data_section /\
   prepared.vs_call_ctx = initial.vs_call_ctx` by
    (qpat_assum `abi_decoder_address_frame _ initial prepared`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     simp_tac bool_ss [] >> metis_tac[]) >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (mp_tac deploy_ctor_member_old_lookup_join >> asm_simp_tac bool_ss []) >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem deploy_ctor_members_run_complete_cons:
  (^Ccomplete) ty tv /\ (^Mcomplete) tys tvs ==>
  (^Mcomplete) (ty::tys) (tv::tvs)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (mk_asm "tail")) >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH avs = LENGTH (ty::tys) /\ LENGTH vs = LENGTH (ty::tys)` by
    (qpat_assum `abi_decoder_members _ _ _ (ty::tys) _ _ _`
       (mp_tac o MATCH_MP abi_decoder_members_lengths) >> simp[]) >>
  Cases_on `avs` >- fs[] >> Cases_on `vs` >- fs[] >>
  rename1 `abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs)` >>
  drule_at (Pat `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _`)
    deploy_ctor_member_prepared_complete >>
  disch_then (drule_at (Pat `abi_decoder_members _ _ _ (_::_) _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_members _ _ _ pretys _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  asm "child" assume_tac >>
  disch_then drule_all >>
  disch_then (qx_choose_then `middle` (qx_choose_then `end_st`
    (qx_choose_then `prepared` (qx_choose_then `after_head`
      (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  asm "tail" (mp_tac o MATCH_MP deploy_ctor_member_tail_run_complete) >>
  disch_then drule_all >>
  disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists `actual` >> irule deploy_ctor_members_complete_join >>
  asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
  qpat_x_assum `(^Hcomplete) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
  rule_assum_tac (PURE_REWRITE_RULE [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC]) >>
  asm_simp_tac arith_ss [] >>
  conj_tac >- (qexistsl [`av`, `avs`, `env`, `sf`] >> asm_simp_tac bool_ss []) >>
  qexistsl [`after_head`, `end_st`, `middle`, `prepared`] >>
  pure_rewrite_tac [ADD_ASSOC] >> asm_simp_tac bool_ss []
QED


Theorem deploy_ctor_members_run_complete:
  !tys tvs. LIST_REL (^Ccomplete) tys tvs ==> (^Mcomplete) tys tvs
Proof
  BETA_TAC >> ho_match_mp_tac LIST_REL_ind >> conj_tac
  >- ACCEPT_TAC (BETA_RULE deploy_ctor_members_run_complete_nil) >>
  rpt gen_tac >> strip_tac >>
  MATCH_MP_TAC (BETA_RULE deploy_ctor_members_run_complete_cons) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deploy_ctor_members_zero_complete:
  LIST_REL (^Ccomplete) tys tvs ==>
  !dst src hi st final ctx func site initial limit_st sb d D N ids avs vs.
  compile_abi_decode_complex_elems dst src DLOAD (Lit 0w) hi (abi_decoder_member_infos sf ce tys) 0 0 st = ((),final) /\
  abi_decoder_members ce env sf tys tvs avs vs /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))) initial.vs_data_section = enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) <= h /\ h < dimword (:256)) /\
  (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) tys) <= D+N /\ D+N <= initial.vs_alloca_next /\
  frag_ids st final SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. tuple_in_memory vs tvs d actual.vs_memory /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final)) [(d,SUM (MAP (type_memory_bytes ce) tys))] initial actual /\
  alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
  ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
  actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
  (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
  ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
  abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\ actual.vs_labels = initial.vs_labels /\
  actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
  actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx
Proof
  disch_tac >> rpt gen_tac >> drule deploy_ctor_members_run_complete >>
  disch_then (mp_tac o SIMP_RULE bool_ss [MAP, SUM, APPEND, ADD_CLAUSES] o
    Q.INST [`pretys` |-> `[]`, `pretvs` |-> `[]`, `preavs` |-> `[]`, `prevs` |-> `[]`] o SPEC_ALL o BETA_RULE) >>
  simp_tac bool_ss [abi_decoder_members_def, EVERY_DEF, LIST_REL_def]
QED

Theorem deploy_ctor_complete_complex_head_bound[local]:
  abi_decoder_members ce env sf tys tvs avs vs ==>
  FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys) <=
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))
Proof
  strip_tac >> drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `has_types (MAP (vyper_to_abi_type env) tys) avs` by fs[has_types_LIST_REL] >>
  drule canonical_tuple_length >> strip_tac >>
  gvs[Excl "enc_def"] >> decide_tac
QED

Theorem deploy_ctor_complex_execute_complete:
  LIST_REL (^Ccomplete) tys tvs /\
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecComplex dyn (abi_decoder_member_infos sf ce tys)) st = ((),final) /\
  abi_decoder_members ce env sf tys tvs avs vs /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))) initial.vs_data_section = enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) <= h /\ h < dimword (:256)) /\
  (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) tys) <= D+N /\ D+N <= initial.vs_alloca_next /\
  frag_ids st final SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. tuple_in_memory vs tvs d actual.vs_memory /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final)) [(d,SUM (MAP (type_memory_bytes ce) tys))] initial actual /\
  alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
  ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
  actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
  (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
  ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
  abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\ actual.vs_labels = initial.vs_labels /\
  actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
  actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx
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
  drule deploy_ctor_complete_complex_head_bound >> strip_tac >>
  mp_tac (Q.INST [`st'` |-> `middle`, `head_sz` |->
    `FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys)`]
    deploy_ctor_complex_guard_complete_frame_fragment) >>
  (impl_tac >- (qpat_x_assum `LIST_REL _ _ _` kall_tac >>
    asm_simp_tac bool_ss [] >>
    Cases_on `hi = Lit 0w` >- simp[] >>
    qpat_x_assum `hi = Lit 0w \/ _` mp_tac >>
    asm_simp_tac bool_ss [] >> strip_tac >> qexists `h` >> asm_simp_tac bool_ss [] >> decide_tac)) >>
  disch_then assume_tac >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[Excl "enc_def"] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial prepared` >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` kall_tac >>
  qpat_assum `abi_decoder_address_frame _ initial prepared`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  drule_all deploy_ctor_array_allocation_state >> strip_tac >>
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
  drule deploy_ctor_members_zero_complete >>
  disch_then (mp_tac o Q.INST [`st` |-> `middle`, `initial` |-> `prepared:venom_state`] o SPEC_ALL) >>
  (impl_tac >- (qpat_x_assum `LIST_REL _ _ _` kall_tac >>
    asm_simp_tac bool_ss [] >> metis_tac[])) >>
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
  irule abi_decode_sim_trans >> qexists `prepared` >> simp[]
QED
