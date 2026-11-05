(* Reachability-guarded source eligibility, independent of deferred execution. *)
Theory bodyIntCallArgEligibility
Ancestors
  list bodySim bodyIntCallArgLifetime bodyIntCallSourceFrame exprLoweringProps
  exprSimAggregateSource exprSimHyps supportedExprTraverse
  vyperTypeCallStackSoundness

Theorem body_results_head_vv_sim:
  body_inv tops ctx cenv cx /\ body_results_ok cx (e::rest) /\
  expr_body_pre cenv cx env e ss ==>
  expr_vv_sim ctx func cenv cx (expr_type e) e ss
Proof
  simp[body_results_ok_def, body_expr_ok_def] >> metis_tac[]
QED

Theorem body_results_success_tail:
  body_results_ok cx (e::rest) /\
  eval_expr cx e ss = (INL raw,ss') ==>
  body_results_ok cx rest
Proof
  simp[body_results_ok_def] >> metis_tac[]
QED

Theorem compile_expr_local_ptrs_reserved:
  local_ptrs_reserved cenv sa /\
  compile_expr cenv ty e sa = (vv,sb) ==>
  local_ptrs_reserved cenv sb
Proof
  metis_tac[cj 1 compile_expr_grows, local_ptrs_reserved_next_var]
QED

Theorem expr_body_pre_intcall_arg:
  expr_body_pre cenv cx env (Call ty (IntCall (src,name)) args dflt) ss /\
  MEM e args /\ expr_sim_inv cenv cx env ss' ==>
  expr_body_pre cenv cx env e ss'
Proof
  rw[exprSimHypsTheory.expr_body_pre_def,
     vyperTypeSystemTheory.well_typed_expr_def,
     vyperTypeCallGraphTheory.int_calls_expr_def,
     exprSimHypsTheory.byte_widths_expr_def, allocLimitsTheory.alloc_limits_expr_def] >>
  imp_res_tac exprSimHypsTheory.int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, EXISTS_MEM] >>
  metis_tac[exprSimHypsTheory.well_typed_exprs_member,
    exprSimHypsTheory.byte_widths_exprs_mem,
    exprSimHypsTheory.alloc_limits_exprs_mem,
    exprSimHypsTheory.call_evaluation_safe_exprs_mem,
    vyperTypeCallStackSoundnessTheory.call_evaluation_safe_mono,
    listTheory.MEM]
QED

Theorem expr_body_pre_intcall_args:
  expr_body_pre cenv cx env (Call ty (IntCall (src,name)) args dflt) ss ==>
  EVERY (\e. expr_body_pre cenv cx env e ss) args
Proof
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  drule expr_body_pre_intcall_arg >> disch_then irule >> simp[] >>
  gvs[exprSimHypsTheory.expr_body_pre_def]
QED

val () = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print ("ARG_ELIGIBILITY_AUDIT " ^ name ^ " OK\n")
    else raise Fail (name ^ " has unproved dependencies")
  end)
  [("body_results_head_vv_sim", body_results_head_vv_sim),
   ("body_results_success_tail", body_results_success_tail),
   ("compile_expr_local_ptrs_reserved", compile_expr_local_ptrs_reserved),
   ("expr_body_pre_intcall_arg", expr_body_pre_intcall_arg),
   ("expr_body_pre_intcall_args", expr_body_pre_intcall_args)];
