Theory abiArgsLabelBoundary
Ancestors compileEnv exprSim exprSimHyps exprSimWordArgs abiArgsLabelObserver
  fragExec venomExecProofs venomExecSemantics

(* Operational steps include returning INVOKE: the caller label map survives. *)
Theorem abi_args_step_labels:
  step_inst fuel ctx inst s = OK t ==> t.vs_labels = s.vs_labels
Proof
  metis_tac[step_inst_preserves_labels_always]
QED

Theorem abi_args_merge_labels:
  (merge_callee_state caller callee).vs_labels = caller.vs_labels
Proof
  simp[merge_callee_state_def]
QED

Theorem abi_args_operand_control_only:
  eval_operand op (s with <|vs_halted := halted; vs_current_bb := bb; vs_inst_idx := idx|>) =
  eval_operand op s
Proof
  Cases_on `op` >> simp[venomStateTheory.eval_operand_def,
    venomStateTheory.lookup_var_def]
QED

(* Control changes are harmless only when the label map is retained. *)
Theorem abi_args_state_rel_control_only:
  stmt_state_rel ctx func ce cx es
    (s with <|vs_halted := halted; vs_current_bb := bb; vs_inst_idx := idx|>) <=>
  stmt_state_rel ctx func ce cx es s
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
       local_ptrs_rel_def, local_region_def, local_backed_def,
       venomStateTheory.lookup_var_def, storage_rel_def, transient_rel_def,
       accounts_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def,
       venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       exprLoweringPropsTheory.alloca_room_def,
       exprLoweringPropsTheory.pending_alloca_size_def,
       exprLoweringPropsTheory.immutable_alloca_sep_def,
       exprLoweringPropsTheory.fmp_room_def, immutable_base_zero_def,
       abi_args_operand_control_only]
QED

Theorem abi_args_immutable_base_kept:
  stmt_state_rel ctx func ce cx es t /\
  stmt_state_rel ctx func ce cx es' u /\
  ce.ce_imm_alloca = SOME op ==>
  eval_operand op t = eval_operand op u
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def, immutable_base_zero_def] >>
  metis_tac[]
QED

Theorem abi_args_state_rel_label_transport:
  immutable_base_zero ce (s with vs_labels := labels) = immutable_base_zero ce s ==>
  (stmt_state_rel ctx func ce cx es (s with vs_labels := labels) <=>
   stmt_state_rel ctx func ce cx es s)
Proof
  strip_tac >>
  simp[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
       local_ptrs_rel_def, local_region_def, local_backed_def,
       venomStateTheory.lookup_var_def, storage_rel_def, transient_rel_def,
       accounts_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def,
       venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       exprLoweringPropsTheory.alloca_room_def,
       exprLoweringPropsTheory.pending_alloca_size_def,
       exprLoweringPropsTheory.immutable_alloca_sep_def,
       exprLoweringPropsTheory.fmp_room_def]
QED

Theorem abi_args_delete_unprotected_label:
  ce.ce_imm_alloca <> SOME (Label l) /\
  (ce.ce_is_ctor ==> l <> "runtime_begin") ==>
  immutable_base_zero ce (s with vs_labels := s.vs_labels \\ l) =
  immutable_base_zero ce s
Proof
  namedCases_on `ce.ce_imm_alloca` ["", "immop"]
  >- (simp[immutable_base_zero_def, finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
      metis_tac[]) >>
  Cases_on `immop` >>
  simp[immutable_base_zero_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  metis_tac[]
QED

Theorem abi_args_success_label_classification:
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (Label l,sm) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 ==>
  ce.ce_imm_alloca = SOME (Label l) \/ (ce.ce_is_ctor /\ l = "runtime_begin")
Proof
  strip_tac >> spose_not_then assume_tac >>
  `ce.ce_imm_alloca <> SOME (Label l) /\
   (ce.ce_is_ctor ==> l <> "runtime_begin")` by metis_tac[] >>
  `immutable_base_zero ce (s0 with vs_labels := s0.vs_labels \\ l) =
   immutable_base_zero ce s0` by metis_tac[abi_args_delete_unprotected_label] >>
  `stmt_state_rel ctx func ce cx es (s0 with vs_labels := s0.vs_labels \\ l)` by
    metis_tac[abi_args_state_rel_label_transport] >>
  qabbrev_tac `z = (s0 with vs_labels := s0.vs_labels \\ l) with
    <|vs_halted := F; vs_current_bb := sa.cs_current_bb;
      vs_inst_idx := LENGTH sa.cs_current_insts|>` >>
  `stmt_state_rel ctx func ce cx es z` by
    simp[Abbr `z`, abi_args_state_rel_control_only] >>
  `expr_res_ok (INL v)` by simp[expr_res_ok_def] >>
  `expr_exit (INL v) = (\r. F)` by simp[FUN_EQ_THM] >>
  drule_all expr_sim_apply >> disch_then (qspec_then `z` mp_tac) >>
  simp[] >> strip_tac >>
  drule_at (Pat `frag_exec`) abi_lower_value_label_observer >>
  simp[Abbr `z`, expr_post_def, expr_val_rel_def,
       venomStateTheory.eval_operand_def, finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  gvs[] >> metis_tac[]
QED

(* Empty typed aggregates exercise the explicit zero-footprint escape. *)
Theorem abi_args_empty_tuple_footprint:
  val_footprint (TupleTV []) (ArrayV (TupleV [])) = 0 /\
  val_wf (TupleTV []) (ArrayV (TupleV [])) /\
  value_has_type (TupleTV []) (ArrayV (TupleV [])) /\
  (!p mem. val_in_memory (TupleTV []) (ArrayV (TupleV [])) p mem)
Proof
  EVAL_TAC >> simp[]
QED

Theorem abi_args_runtime_empty_tuple_location:
  FLOOKUP s.vs_labels "runtime_begin" = SOME w ==>
  expr_val_rel cx (TupleT []) (ArrayV (TupleV [])) (Label "runtime_begin") s /\
  expr_val_at ce cx (TupleT []) sa sb es (ArrayV (TupleV [])) (Label "runtime_begin") s
Proof
  simp[expr_val_rel_def, expr_val_at_def, venomStateTheory.eval_operand_def,
       vyperValueTheory.evaluate_type_def, is_word_type_def,
       abi_args_empty_tuple_footprint, valueEncodingTheory.val_in_memory_def]
QED
