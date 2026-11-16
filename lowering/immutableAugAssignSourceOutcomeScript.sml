(* Lift the scalar suffix outcome across the source-only immutable prefix. *)
Theory immutableAugAssignSourceOutcome
Ancestors
  immutableAugAssignSourceContinuation bodyImmutableAugAssignExec stmtSimDeclGas
  gasOutcome gasSummary gasExemptCert gasExemptPurePrefix vyperInterpreter vyperState

Theorem immutable_augassign_root_source_outcome:
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables src imms) id = SOME (tv,iv) /\
  ~s0.vs_halted /\
  gas_outcome T tops (ctx,func) cx st0
    (vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
      (\rhs. vyperState$bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop iv rhs)) (write_place cx (ImmutablePlace src id []))))
    (es,s0) Q R ==>
  gas_outcome T tops (ctx,func) cx st0
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (es,s0) Q R
Proof
  strip_tac >>
  drule_all immutable_augassign_source_replay >> strip_tac >>
  drule_all immutable_augassign_root_replay >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks`
  >- (disj1_tac >> fs[gasStorageTheory.gas_bad_storage_at_def] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      fs[gas_summary_at_def,gas_marked_exec_def,gas_explicit_def] >>
      metis_tac[]) >>
  disj2_tac >> disj2_tac >> qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  simp[Once evaluate_def,ignore_bind_def,bind_assoc] >>
  irule gas_exempt_cert_pure_prefix >> simp[] >>
  irule gas_exempt_cert_pure_prefix >> simp[] >>
  irule gas_exempt_cert_pure_prefix >> simp[] >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[ignore_bind_def,bind_assoc]
QED
