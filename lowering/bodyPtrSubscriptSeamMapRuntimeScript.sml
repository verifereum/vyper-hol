(* Runtime world projections of the mapping hash instruction class. *)
Theory bodyPtrSubscriptSeamMapRuntime
Ancestors
  bodyPtrSubscriptSeamMapSuffix exprLoweringProps venomExecSemantics
  venomState venomInst finite_map pred_set list

Theorem mapping_hash_step_runtime_fields:
  inst.inst_opcode IN {ALLOCA; ADD; MSTORE; SHA3} /\
  step_inst_base inst s = OK t ==>
  (t.vs_accounts,t.vs_transient,t.vs_call_ctx,t.vs_current_bb) =
  (s.vs_accounts,s.vs_transient,s.vs_call_ctx,s.vs_current_bb)
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure2_def, exec_write2_def, exec_alloca_def] >>
  strip_tac >> gvs[AllCaseEqs(), update_var_def, mstore_def]
QED

Theorem mapping_hash_sequence_runtime_fields:
  EVERY (\i. i.inst_opcode IN {ALLOCA; ADD; MSTORE; SHA3}) code /\
  run_inst_seq code s = OK t ==>
  (t.vs_accounts,t.vs_transient,t.vs_call_ctx,t.vs_current_bb) =
  (s.vs_accounts,s.vs_transient,s.vs_call_ctx,s.vs_current_bb)
Proof
  strip_tac >> irule (Q.ISPEC
    `\s:venom_state. (s.vs_accounts,s.vs_transient,s.vs_call_ctx,s.vs_current_bb)`
    run_inst_seq_preserves_field |> BETA_RULE) >>
  qexists `code` >> simp[] >> rpt strip_tac >>
  `i.inst_opcode IN {ALLOCA; ADD; MSTORE; SHA3}` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all mapping_hash_step_runtime_fields >> simp[]
QED

Theorem mapping_slot_hash_runtime_fields:
  compile_mapping_subscript slot key sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >> drule mapping_slot_hash_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode IN {ALLOCA; ADD; MSTORE; SHA3})
     (emitted_insts sa sb)` by simp[mk_inst_def] >>
  drule_all mapping_hash_sequence_runtime_fields >> simp[]
QED
