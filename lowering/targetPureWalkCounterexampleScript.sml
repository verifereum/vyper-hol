(* A checked counterexample to the exact frozen target_walk_frame formula.
   RawLog is classified nonmutating but appends an observable source log. *)
Theory targetPureWalkCounterexample
Ancestors
  targetPureWalkWitness targetPureWalkSourceWitness targetPureWalkRuntimeWitness
  targetPureWalkOutcomeObstruction

Theorem target_walk_frame_counterexample:
  ?ctx func cenv cx env bt es vt sa sb op s0.
    (~expr_can_mutate cenv (target_to_expr bt) /\
    cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
    (!vis mut nr rr fn args dflts ret body.
       MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops cx) ==>
       function_mutability_ok [(NONE, cx_tops cx)] vis mut nr dflts body) /\
    get_module_code cx NONE = SOME (cx_tops cx) /\
    EVERY (\c. FST c = NONE) (int_calls_target bt) /\
    target_sim ctx func cenv cx env bt es /\
    type_place_target env bt = SOME vt /\
    compile_get_target_ptr compile_expr cenv bt sa = (op, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_base_place cx bt) target_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts) /\
    ~gas_outcome F (cx_tops cx) (ctx, func) (eval_base_place cx bt) (es, s0)
      (\res ee t. ?pv. res = INL pv /\
         target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
         machine_frame es ee /\ ee.scopes = es.scopes /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  qexistsl_tac [`w_ctx`, `w_func`, `w_cenv`, `w_cx`, `w_env`, `w_bt`,
                `w_es`, `Type (BaseT (UintT 256))`, `w_sa`, `w_sb`,
                `w_op`, `w_s0`] >>
  conj_tac
  >- (strip_assume_tac w_source_pins >>
      simp[w_target_sim, w_target_typed, w_compilation,
           w_code, w_reserved, w_gas_admissible, raw_log_witness_entry,
           w_cursor] >> metis_tac[w_code, w_cursor]) >>
  rewrite_tac[w_bt_def] >>
  irule raw_log_target_outcome_obstruction >>
  conj_tac >- (simp[] >> metis_tac[]) >>
  conj_tac >- EVAL_TAC >>
  qexists_tac `<| assignable := T;
    type := ArrayTV (BaseTV (UintT 256)) (Dynamic 1);
    value := ArrayV (DynArrayV [IntV 7]); popped := [] |>` >>
  simp[w_entry_fields, w_cx_def,
       vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.empty_call_txn_def] >>
  metis_tac[]
QED
