(* Counted forcing of an allocated nonword memory buffer. *)
Theory exprSimBufferForce
Ancestors
  exprSimMemorySource exprSimUnwrapProps exprSimProps exprSimDefs
  loweringPosts gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasPath fragGasMode exprLowering exprLoweringProps compileEnv
  vyperAST vyperInterpreter vyperState venomState list finite_map
Libs
  monadsyntax

(* Memory-buffer forcing uses only the oracle-clean memory boundary. *)
Theorem expr_sim_of_vv_sim_buffer:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es /\
    (!sa. ?t p sb. compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
      p.ptr_location = LocMemory /\ ~is_word_type t) /\
    (!tv es'. eval_expr cx e es = (INL tv,es') ==> ?v. tv = Value v) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  qpat_x_assum `!tv es'. eval_expr _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!sa. ?t p sb. _` (qspec_then `sa` strip_assume_tac) >>
  gvs[] >> rename1 `compile_expr cenv ty e sa = (LocatedValue t p, sm)` >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw, est)` >>
  qpat_x_assum `(do result <- _; _ od) _ = _` mp_tac >>
  simp[bind_def] >> Cases_on `raw`
  >- (rename1 `eval_expr cx e es = (INL r, est)` >> simp[] >> strip_tac >>
      drule read_result_state >> strip_tac >> gvs[] >>
      `expr_vv_res_ok (INL r)` by
        (Cases_on `r` >> gvs[expr_vv_res_ok_def, read_result_def,
                             raise_def, expr_res_ok_def]) >>
      qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
        (mp_tac o SIMP_RULE std_ss [expr_vv_sim_def]) >>
      disch_then (qspecl_then [`sa`, `sm`, `LocatedValue t p`, `INL r`, `es'`, `s0`] mp_tac) >>
      simp[] >> strip_tac >>
      irule frag_exec_seq >>
      qexistsl_tac [`\s. vv_post ctx func cenv cx e es sa sm s0 es' r (LocatedValue t p) s`, `sm`] >>
      simp[] >> conj_tac
      >- (irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
          simp[FUN_EQ_THM]) >>
      irule unwrap_memory_read_result_sim >> simp[]) >>
  rename1 `eval_expr cx e es = (INR exc, est)` >> strip_tac >> gvs[] >>
  `expr_vv_res_ok (INR exc)` by gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `LocatedValue t p`, `INR exc`, `es'`, `s0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule frag_exec_seq >> qexistsl_tac [`\s. F`, `sm`] >> simp[] >> conj_tac
  >- (irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
      simp[expr_exit_exception_transport]) >>
  simp[fragExecTheory.frag_exec_false_pre]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag expr_sim_of_vv_sim_buffer)
  in
    if null axioms andalso null (Thm.hyp expr_sim_of_vv_sim_buffer) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print "MEMORY_FORCE_AUDIT expr_sim_of_vv_sim_buffer OK\n"
    else raise Fail "expr_sim_of_vv_sim_buffer: admitted proof dependency"
  end;
