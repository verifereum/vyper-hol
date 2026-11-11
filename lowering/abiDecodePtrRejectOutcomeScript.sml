Theory abiDecodePtrRejectOutcome
Ancestors
  abiDecodePtrComplexOutcomeAbort abiDecodePtrAbortReentry abiDecodePtrRejectChecks
  abiDecoderReentry abiDecoderVarExtend abiDecodePtrMemberInterface
  abiDecoderCoherence abiDecoderMemberInfos abiEncoder compileEnv fragExec
  fragGasPathPtr venomExecSemantics venomState venomInst list words
  gasSummaryComposePtr gasSummary gasCount exprSimDefs vyperState vyperInterpreter

Theorem abi_decode_complex_reject_reentry_path:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap
    (Lit 0w) 0w hi sa G tn s /\
  EVERY supported_scalar_type tys /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields (TupleT tys) (TupleTV tvs) /\
  cap = SUM (MAP (type_memory_bytes ce) tys) /\
  compile_abi_decode_to_buf (Var dst) (Lit 0w) MLOAD (Var src) hi
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) sa = ((),sb) /\
  fn_has_code sa sb func /\
  abi_decoder_vars_extend extras r s /\
  abi_decode_reject_witness (emitted_insts sa sb) r u ==>
  ?v H tf n j. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort v /\
    vsr_term_frame u = vsr_term_frame v /\
    gas_path_ptr D 0 ctx func PG G tn s n H tf
      (Abort Revert_abort (v with vs_inst_idx := j))
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_reject_witness _ _ _` mp_tac >>
  rewrite_tac[abi_decode_reject_witness_def] >> strip_tac >>
  drule_all abi_decode_rejecting_prefix_reentry >>
  disch_then (qspec_then `post` strip_assume_tac) >>
  `run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort u'` by metis_tac[] >>
  drule_all abi_decode_complex_observed_abort >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  metis_tac[]
QED

Theorem abi_decode_complex_pruned_reject_path:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap
    (Lit 0w) 0w hi sa G tn s /\
  EVERY supported_scalar_type tys /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields (TupleT tys) (TupleTV tvs) /\
  cap = SUM (MAP (type_memory_bytes ce) tys) /\
  compile_abi_decode_to_buf (Var dst) (Lit 0w) MLOAD (Var src) hi
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) sa = ((),sb) /\
  fn_has_code sa sb func /\
  abi_decode_reject_witness (emitted_insts sa sb)
    (abi_decoder_prune_vars sa.cs_next_var s) u ==>
  ?v H tf n j. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort v /\
    vsr_term_frame u = vsr_term_frame v /\
    gas_path_ptr D 0 ctx func PG G tn s n H tf
      (Abort Revert_abort (v with vs_inst_idx := j))
Proof
  strip_tac >> irule abi_decode_complex_reject_reentry_path >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[abi_decoder_prune_extension]
QED

(* Counted rejecting suffixes; exemptions remain whole-expression facts. *)
Theorem ptr_runtime_error_abort_summary:
  (!tail. source (ee with gas_obs := tail) =
    (INR (Error (RuntimeError msg)), ee with gas_obs := tail)) /\
  gas_path_ptr D 0 ctx func PG G tn s n H tk (Abort a t) ==>
  gas_summary_ptr_at D (ctx,func) PG (REPLICATE n F) source
    (ee,s,G,tn) Q (\res ef gt r. expr_exit res r)
Proof
  strip_tac >> rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl [`INR (Error (RuntimeError msg))`, `ee`, `H`, `tk`, `Abort a t`] >>
  simp[exit_result_def, expr_exit_def] >>
  irule gas_marked_exec_ptr_no_source_read >> simp[]
QED

Theorem type_builtin_runtime_error_abort_summary:
  evaluate_type_builtin cx tb typ arg_tys args = INR (RuntimeError msg) /\
  gas_path_ptr D 0 ctx func PG G tn s n H tk (Abort a t) ==>
  gas_summary_ptr_at D (ctx,func) PG (REPLICATE n F)
    (bind (lift_sum (evaluate_type_builtin cx tb typ arg_tys args))
      (\w. return (Value w))) (ee,s,G,tn) Q
    (\res ef gt r. expr_exit res r)
Proof
  strip_tac >> irule ptr_runtime_error_abort_summary >>
  simp[lift_sum_def, bind_def, raise_def] >> metis_tac[]
QED
