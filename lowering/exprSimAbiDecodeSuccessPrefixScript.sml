Theory exprSimAbiDecodeSuccessPrefix
Ancestors
  exprSimAbiDecodeQuantifiedLift
  exprSimAbiDecodeFreshProbe exprSimAbiDecodeBuiltin abiDecoderReentry
  exprSimAbiDecodeStepLift abiDecoderSiteEffect actualDecoderSites
  exprSimAbiDecodeOutcomeAllocation exprSimAbiDecodeEndpointFrame
  exprSimAbiDecodeObserverReject
  exprSimAbiDecodePathReconstruct exprSimAbiDecodePathLift
  abiEncoderVarTransport exprSimAbiGasBridge abiEncoderObserver
  abiDecoderVarExtend abiDecoderLoop fragExec venomExecSemantics venomState
  venomInst relation

Theorem abi_decode_original_entry_outcome_prefix:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  start.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  eval_operand data s = SOME (n2w p) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
  abi_builtin_decode_site_resources ctx func start final.cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d s /\
  cs_extends start final /\ fn_has_code start final fn /\
  frag_gas_free start final /\ fn_inst_ids_distinct fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (start.cs_blocks = final.cs_blocks \/ final.cs_current_insts <> [] \/
   !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts ==>
  (?t. abi_decode_success_closed ce env ty tv bs out d start final ctx func s t /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ abi_decode_sim ctx fn s t /\
    local_prefix ctx fn (frag_observer_cut final) s t) \/
  ((?e. evaluate_abi_decode env ty bs = INR e) /\
    ?fuel u. run_from fuel ctx fn s = Abort Revert_abort u)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  strip_assume_tac frag_observer_fresh_id >>
  mp_tac abi_decode_pruned_observer_outcome >>
  (impl_tac >- simp[]) >> simp_tac bool_ss [LET_THM] >> strip_tac
  >- (`abi_decoder_vars_extend s.vs_vars
         (abi_decoder_prune_vars start.cs_next_var s) s` by
        simp[abi_decoder_prune_extension] >>
      `?u u'. stop_view u = stop_view t /\
        abi_decoder_vars_extend s.vs_vars u u' /\
        local_prefix ctx fn (frag_observer_cut final) s u' /\
        abi_decode_sim ctx fn s u'` by
        (irule abi_decode_observer_continuation_extend >> simp[] >>
         qexistsl_tac [`id`, `abi_decoder_prune_vars start.cs_next_var s`, `start`] >>
         gvs[abi_decoder_prune_vars_def] >> metis_tac[]) >>
      `abi_decode_allocation_floor
         (abi_decoder_prune_vars start.cs_next_var s).vs_alloca_next
         (abi_decoder_prune_vars start.cs_next_var s).vs_allocas t` by
        (irule abi_decode_observer_continuation_floor >>
         simp[abi_decoder_prune_vars_def] >>
         goal_assum (drule_at (Pat `fn_has_code _ _ _`)) >> simp[] >>
         qexistsl_tac [`ctx`, `id`] >> fs[abi_decoder_prune_vars_def]) >>
      `abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas t` by
        fs[abi_decoder_prune_vars_def] >>
      `FLOOKUP t.vs_allocas (abi_builtin_decode_output_site start
         (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)) =
         SOME (d,type_memory_bytes ce ty)` by
        (irule (cj 2 abi_decode_outcome_allocation) >>
         conj_tac >- (fs[abi_builtin_decode_site_resources_def] >> decide_tac) >>
         goal_assum (drule_at (Pat `lower_abi_decode _ _ _ _ _ _ = _`)) >>
         simp[] >> qexistsl_tac [`ctx`, `fn`, `id`,
           `abi_decoder_prune_vars start.cs_next_var s`] >>
         fs[abi_builtin_decode_site_resources_def, abi_decoder_prune_vars_def]) >>
      drule_all abi_decode_success_closed_transport >> strip_tac >>
      disj1_tac >> qexists_tac `u'` >> simp[]) >>
  `abi_decoder_vars_extend s.vs_vars
     (abi_decoder_prune_vars start.cs_next_var s) s` by
    simp[abi_decoder_prune_extension] >>
  disj2_tac >> simp[] >>
  `?u' fuel'. abi_decoder_vars_extend s.vs_vars u u' /\
     run_from fuel' ctx fn s = Abort Revert_abort u'` by
    (irule abi_decode_observer_reject_transfer_extend >>
     qexistsl_tac [`fuel`, `id`, `abi_decoder_prune_vars start.cs_next_var s`,
                   `start`, `final`] >>
     gvs[abi_decoder_prune_vars_def] >> metis_tac[]) >> metis_tac[]
QED

Theorem abi_decode_original_entry_success_prefix:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  start.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  eval_operand data s = SOME (n2w p) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
  abi_builtin_decode_site_resources ctx func start final.cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d s /\
  cs_extends start final /\ fn_has_code start final fn /\
  frag_gas_free start final /\ fn_inst_ids_distinct fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (start.cs_blocks = final.cs_blocks \/ final.cs_current_insts <> [] \/
   !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  evaluate_abi_decode env ty bs = INL v ==>
  ?t. abi_decode_success_closed ce env ty tv bs out d start final ctx func s t /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ abi_decode_sim ctx fn s t /\
    local_prefix ctx fn (frag_observer_cut final) s t
Proof
  strip_tac >> mp_tac abi_decode_original_entry_outcome_prefix >>
  (impl_tac >- simp[]) >> simp[]
QED
