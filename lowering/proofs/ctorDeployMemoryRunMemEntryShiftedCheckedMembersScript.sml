Theory ctorDeployMemoryRunMemEntryShiftedCheckedMembers
Ancestors
  ctorDeployMemoryRunMemEntryShiftedCheckedBase ctorDeployMemoryRunMemEntryShiftedFrame
  ctorDeployMemoryFrontier ctorDeployMemoryRunMemEntryCompositeSetup ctorAbiActualMemberRun
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
  fragGasPathMem allocaHistory ctorDeployMemoryRunMemEntryWord

val Hk = ``\r ctx func site initial st st' limit_st ids D N tv v d k.
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,k)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from r ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ gas_path_mem ctx func initial 0 (OK actual) /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual``;

val Ck = ``\ty tv.
 !r dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
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
 alloca_inv initial /\ alloca_frontier_inv_from r ctx func site initial /\ r + unit_alloca_budget ctx < dimword (:256) /\
 alloca_history func initial /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 (^Hk) r ctx func site initial st st' limit_st ids D N tv v d (type_memory_bytes ce ty)``;

val Mk = ``\tys tvs.
 !r dst src hi st final ctx func site initial limit_st sb d D N ids
   pretys pretvs preavs prevs avs vs.
 compile_abi_decode_complex_elems dst src DLOAD hi (abi_decoder_member_infos sf ce tys)
   (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
   (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),final) /\
 abi_decoder_members ce env sf pretys pretvs preavs prevs /\
 abi_decoder_members ce env sf tys tvs avs vs /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs))) < dimword (:256) /\
 sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs))) <= LENGTH initial.vs_data_section /\
 mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs)))) initial.vs_data_section =
   enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs)) /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
   sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs))) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st final func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from r ctx func site initial /\ r + unit_alloca_budget ctx < dimword (:256) /\
 alloca_history func initial /\
 D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ tys)) <= D+N /\
 D+N <= initial.vs_alloca_next /\ frag_ids st final SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final))
   [(d + SUM (MAP (type_memory_bytes ce) pretys), SUM (MAP (type_memory_bytes ce) tys))] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from r ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 gas_path_mem ctx func initial 0 (OK actual) /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 alloca_history func actual``;

Theorem ctor_checked_member_alloca_transport_from[local]:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  (alloca_inv t = alloca_inv s) /\
  (alloca_frontier_inv_from r ctx func site t = alloca_frontier_inv_from r ctx func site s) /\
  (ctor_actual_scratch func ids D N t = ctor_actual_scratch func ids D N s)
Proof
  strip_tac >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_from_def, remaining_alloca_budget_def,
       ctor_actual_scratch_def]
QED

Theorem ctor_checked_member_adjacent_value[local]:
  abi_encoder_registered_effect (ctor_actual_sites fn child) [(p+k,n)] s t /\
  child SUBSET ids /\ ctor_actual_scratch fn ids D N t /\
  val_in_memory tv v p s.vs_memory /\ val_wf tv v /\
  type_memory_size tv = k /\ D <= p /\ p+k+n <= D+N ==>
  val_in_memory tv v p t.vs_memory
Proof
  strip_tac >> irule ctor_actual_child_preserves_value >> simp[] >>
  goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ctor_actual_scratch _ _ _ _ _`)) >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem ctor_checked_member_old_vars[local]:
  st.cs_next_var <= middle.cs_next_var /\
  (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
  (!x w. not_fresh_at middle x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) ==>
  !x w. not_fresh_at st x /\ lookup_var x s = SOME w ==> lookup_var x u = SOME w
Proof
  rw[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem ctor_checked_member_effects[local]:
  abi_encoder_registered_effect {} [] s a /\
  abi_encoder_registered_effect (ctor_actual_sites fn headids) [(p,k)] a b /\
  abi_encoder_registered_effect (ctor_actual_sites fn tailids) [(p+k,n)] b t /\
  headids SUBSET ids /\ tailids SUBSET ids ==>
  abi_encoder_registered_effect (ctor_actual_sites fn ids) [(p,k+n)] s t
Proof
  strip_tac >>
  `abi_encoder_registered_effect (ctor_actual_sites fn ids) [(p,k+n)] s a` by
    (irule abi_encoder_registered_effect_enlarge >> qexistsl [`{}`, `[]`] >> simp[]) >>
  `abi_encoder_registered_effect (ctor_actual_sites fn ids) [(p,k+n)] a b` by
    (irule ctor_actual_child_narrow_effect >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >> simp[]) >>
  `abi_encoder_registered_effect (ctor_actual_sites fn ids) [(p,k+n)] b t` by
    (irule ctor_actual_child_narrow_effect >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >> simp[]) >>
  metis_tac[abi_encoder_registered_effect_trans]
QED

