(* Counted forcing of a value already located in memory. *)
Theory exprSimMemoryForce
Ancestors
  exprSimUnwrapProps exprSimProps exprSimDefs
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasPath fragGasMode emitHelperProps loweringPosts
  exprLowering exprLoweringProps compileEnv loweringSlice
  list rich_list finite_map pred_set fragExec varsExt freshWrites
  vyperAST vyperInterpreter vyperState vyperTypeSystem valueEncoding
  valueEncodingProofs venomExecSemantics venomInst venomState
Libs
  monadsyntax

Theorem expr_sim_of_vv_sim_memory:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es /\
    (!sa vv sm. compile_expr cenv ty e sa = (vv, sm) ==>
                sm = sa /\
                ?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  qpat_x_assum `!sa vv sm. compile_expr _ _ _ _ = _ ==> _` drule >>
  strip_tac >> gvs[] >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sa func` by
    (irule (cj 1 fn_has_code_split) >> simp[cs_extends_refl] >>
     qexists_tac `sb` >> simp[]) >>
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
      disch_then (qspecl_then [`sa`, `sa`, `LocatedValue t p`, `INL r`, `es'`, `s0`] mp_tac) >>
      simp[] >> strip_tac >>
      irule frag_exec_seq >>
      qexistsl_tac [`\s. vv_post ctx func cenv cx e es sa sa s0 es' r (LocatedValue t p) s`, `sa`] >>
      simp[cs_extends_refl] >> conj_tac
      >- (irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
          simp[FUN_EQ_THM]) >>
      irule unwrap_memory_read_result_sim >> simp[]) >>
  rename1 `eval_expr cx e es = (INR exc, est)` >> strip_tac >> gvs[] >>
  `expr_vv_res_ok (INR exc)` by gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sa`, `LocatedValue t p`, `INR exc`, `es'`, `s0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule frag_exec_seq >> qexistsl_tac [`\s. F`, `sa`] >> simp[cs_extends_refl] >> conj_tac
  >- (irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
      simp[expr_exit_exception_transport]) >>
  simp[fragExecTheory.frag_exec_false_pre]
QED

val () =
  let val (ors,axs) = Tag.dest_tag (Thm.tag expr_sim_of_vv_sim_memory)
  in if null axs andalso null (Thm.hyp expr_sim_of_vv_sim_memory) andalso
        List.all (fn oracle => oracle = "DISK_THM") ors then
       print "MEMORY_FORCE_AUDIT expr_sim_of_vv_sim_memory OK\n"
     else raise Fail "expr_sim_of_vv_sim_memory: admitted proof dependency"
  end;
