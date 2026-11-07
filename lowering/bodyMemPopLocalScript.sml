(* Memory case of the body induction, pop on a local dynamic array. *)
Theory bodyMemPopLocal
Ancestors
  bodyMemoryPreds bodyMemPopLocalSim bodyExprForceMemory
  exprSimSource exprSimHypsDefs vyperTypeCallGraph exprLowering

Theorem body_pop_local_mem:
  !cx ann id. body_expr_mem_ok cx (Pop ann (NameTarget id))
Proof
  rpt gen_tac >> (rpt gen_tac >> match_mp_tac body_expr_mem_ok_intro >>
   conj_tac >- (rpt strip_tac >> gvs[])) >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env (Pop ann (NameTarget id)) es` by
    simp[expr_sim_pre_body, int_calls_expr_def] >>
  `expr_vv_sim_mem ctx func cenv cx ty (Pop ann (NameTarget id)) es` by
    metis_tac[compile_pop_name_sim_mem] >>
  simp[] >> irule body_expr_sim_mem_of_vv_sim_mem >>
  simp[] >> conj_tac
  >- (rpt gen_tac >>
      simp[Once compile_expr_def, compile_expr_body_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[])) >>
  qexists_tac `env` >> simp[]
QED
