(* Readiness-parametric composition of argument evaluation and Log emission. *)
Theory stmtSimLogCompose
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  stmtSimLogArgsRun stmtSimLogArgsGrowth stmtSimLogSuffix stmtSimLogSource   exprSimWordArgs
  stmtSimLogSuffixFrame stmtSimLogSuffixCode stmtSimLogArgs freshWrites
  compileEnv loweringStateRelDefs stmtLowering fragExec loweringSlice exprLoweringProps emitHelperProps
  vyperInterpreter vyperState vyperTyping list stmtSimLogTrace emitHelper context venomInst
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath fragGasSeq rich_list vyperEvalExprPreservesScopesDom
  eventLoweringStructure stmtSimLogTopics logComposeFacts fragGasSeqAbort
Libs
  monadsyntax

Theorem log_ready_values_typed:
  !args es vs es'.
  (!e tail s. R (e::tail) s ==>
     !v s1. (do r <- eval_expr cx e; read_result cx r od) s = (INL v,s1) ==>
       R tail s1 /\ ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) /\
  R args es /\ eval_exprs cx args es = (INL vs,es') ==>
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                        value_has_type tv v) (MAP expr_type args) vs
Proof
  Induct
  >- simp[eval_exprs_nil] >>
  rpt gen_tac >> strip_tac >> drule eval_exprs_cons_cases >> strip_tac
  >- gvs[] >>
  rename1 `eval_exprs cx args es1 = (tail_res,es')` >>
  Cases_on `tail_res` >> gvs[] >> conj_tac
  >- metis_tac[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem log_args_scopes_dom:
  gas_marked_exec memory (ctx,func) (eval_exprs cx args)
    (es,s0) marks res ee r ==>
  MAP FDOM ee.scopes = MAP FDOM es.scopes
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> strip_tac >>
  drule eval_exprs_preserves_scopes_dom >> simp[]
QED

Theorem log_wb_alloca_frame:
  stmt_state_rel H ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  wb_frame cenv es es1 sa s0 t ==>
  alloca_frame cenv es sa s0 cenv ee t
Proof
  strip_tac >> irule alloca_frame_of_mem_frame >>
  goal_assum (drule_at Any) >> gvs[wb_frame_def] >> metis_tac[]
QED

Theorem log_suffix_alloca_frame:
  stmt_state_rel H ctx func cenv cx es s /\
  local_ptrs_reserved cenv sm /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  (!op w. (!z. op = Var z ==> not_fresh_at sm z) /\
    (!l. op <> Label l) /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\
  (!aid a k. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,k) ==>
    mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  alloca_frame cenv es sm s cenv ee t
Proof
  strip_tac >> irule alloca_frame_of_mem_frame >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!op w. _` (qspecl_then [`Var x`, `w`] mp_tac) >>
      simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
  metis_tac[]
QED

val log_cont_frame_tac =
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       vyperStorageTraceTheory.storage_trace_frame_ignore_bind,
       vyperStorageTraceTheory.storage_trace_frame_lifts,
       vyperStorageTraceTheory.storage_trace_frame_checks,
       vyperStorageTraceTheory.storage_trace_frame_check_not_static,
       vyperStorageTraceTheory.storage_trace_frame_state_updates];

val log_out_of_domain_tac =
  qexists_tac `marks` >> disj1_tac >>
  irule gasStorageTheory.gas_bad_storage_at_bind_left >>
  log_cont_frame_tac >>
  irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[];
