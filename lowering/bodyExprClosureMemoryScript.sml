(* Reachability-aligned recursive expression memory closure. *)
Theory bodyExprClosureMemory
Ancestors
  bodyMemoryPreds bodyMemoryDefs bodyIfExpMemory exprSimOperators exprSimHyps
  exprLoweringProps vyperInterpreter vyperState

Theorem body_ifexp_word_mem_case:
  !cx t c a b. is_word_type t /\
    (!s tv s'. eval_expr cx c s = (INL tv,s') ==> body_expr_mem_ok cx a) /\
    (!s tv s'. eval_expr cx c s = (INL tv,s') ==> body_expr_mem_ok cx b) /\
    body_expr_mem_ok cx c ==> body_expr_mem_ok cx (IfExp t c a b)
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_ifexp >> strip_tac >>
  `expr_sim_mem ctx func cenv cx (BaseT BoolT) c es` by
    metis_tac[body_expr_mem_ok_def] >>
  `!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = (INL tv,es1) ==>
     expr_sim_mem ctx func cenv cx ty a es1 /\
     expr_sim_mem ctx func cenv cx ty b es1` by
    (rpt gen_tac >> strip_tac >>
     drule_all expr_body_pre_eval >> strip_tac >>
     drule eval_expr_read_INL >> strip_tac >>
     metis_tac[body_expr_mem_ok_def]) >>
  conj_tac
  >- (irule compile_ifexp_word_sim_mem >> simp[] >>
      metis_tac[compile_expr_grows]) >>
  pure_rewrite_tac[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  `expr_read_res_ok cx es' res` by
    metis_tac[expr_body_pre_ifexp_word_readable] >>
  irule fragExecMemTheory.frag_exec_mem_weaken >>
  qexists_tac `\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s` >>
  qexists_tac `\s. (?tv. res = INL tv /\
    vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' tv vv s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s` >>
  qexists_tac `expr_exit res` >> simp[] >>
  irule compile_ifexp_vv_sim_mem >> simp[] >>
  conj_tac >- metis_tac[compile_expr_grows] >> qexists_tac `ty` >>
  simp[] >> metis_tac[compile_expr_grows]
QED

val () =
  let val th = body_ifexp_word_mem_case
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_IFEXP_WORD_CLOSURE_MEMORY_AUDIT OK\n"
     else raise Fail "ifexp word closure memory inherited admission"
  end;
