(* Reachability-guarded source eligibility for deferred internal arguments. *)
Theory bodyIntCallArgList
Ancestors
  bodyIntCallArgEligibility bodyIntCallSourceFrame list bodySim bodyIntCallArgLifetime exprLoweringProps vyperInterpreter vyperState
  exprSimAggregateSource exprLowering compileEnv fragExec exprSimHyps exprSim
  exprSimUnwrap bodyIntCallCopyProbe bodyIntCallCopyContent bodyIntCallStorageLayout bodyIntCallCodeCopy bodyIntCallForceFrame

(* Runtime forcing without an aggregate copy.  The restriction is explicit:
   the outstanding copy cases are not justified by this boundary. *)
Theorem unwrap_runtime_noncopy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op R.
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ ~cenv.ce_is_ctor /\
    (case vv of StackValue ty operand => T
     | LocatedValue ty p => p.ptr_location = LocMemory \/ is_word_type ty) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >> irule frag_exec_refl >>
      rw[] >> metis_tac[expr_post_of_vv_post_stack]) >>
  rename1 `LocatedValue t p` >>
  Cases_on `p.ptr_location = LocCalldata`
  >- (irule frag_exec_conseq >>
      qexistsl_tac [`\s. F`, `\s. F`, `R`] >>
      gvs[frag_exec_false_pre, vv_post_calldata]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (irule unwrap_memory_sim >> simp[]) >>
  `is_word_type t` by gvs[] >>
  Cases_on `p.ptr_location = LocCode`
  >- (irule unwrap_runtime_immutable_word_sim >>
      gvs[unwrap_value_def, contextTheory.compile_ptr_load_def,
          contextTheory.compile_imm_load_word_def]) >>
  irule unwrap_storage_word_sim >> simp[] >>
  Cases_on `p.ptr_location` >> gvs[]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag unwrap_runtime_noncopy_sim)
  in
    if null axioms andalso null (Thm.hyp unwrap_runtime_noncopy_sim) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print "RUNTIME_NONCOPY_AUDIT unwrap_runtime_noncopy_sim OK\n"
    else raise Fail "unwrap_runtime_noncopy_sim has unproved dependencies"
  end;

(* Source eligibility is exported by bodyIntCallArgEligibility; outcomes-only
   transfer uses the canonical bodyIntCallSourceFrame boundaries directly. *)
Theorem body_results_success_deferred_list:
  !args sa sb start hs raws vvs.
  body_inv tops ctx cenv cx /\ body_results_ok cx args /\
  expr_sim_inv cenv cx env es /\
  EVERY (supported_pure_expr tops) args /\
  EVERY (\e. expr_body_pre cenv cx env e es) args /\
  eval_expr_results cx args es = (INL raws,es) /\
  compile_multi_vvs compile_expr cenv args sa = (vvs,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = start /\ stmt_state_rel ctx func cenv cx es s /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held es s /\
        vv_at cenv cx ty lo sa es raw held s /\
        safe_operand sa (vv_operand held)) hs)
    (\s. stmt_state_rel ctx func cenv cx es s /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held es s /\
        vv_at cenv cx ty lo sb es raw held s /\
        safe_operand sb (vv_operand held)) hs /\
      ?los. LENGTH los = LENGTH args /\ LENGTH raws = LENGTH args /\
        LENGTH vvs = LENGTH args /\
        EVERY (\((e,raw),(held,lo)).
          vv_holds cenv cx (expr_type e) raw held es s /\
          vv_at cenv cx (expr_type e) lo sb es raw held s /\
          safe_operand sb (vv_operand held))
          (ZIP (ZIP (args,raws), ZIP (vvs,los))))
    (\r. F)
Proof
  Induct_on `args`
  >- (rpt gen_tac >>
      simp[compile_multi_vvs_def, comp_return_def, Once evaluate_def,
           return_def] >> rpt strip_tac >> gvs[] >>
      irule frag_exec_refl >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_multi_vvs _ _ _ _ = _` mp_tac >>
  simp[Once compile_multi_vvs_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  suspend "cons"
QED

Resume body_results_success_deferred_list[cons]:
  gvs[] >>
  rename1 `compile_expr cenv (expr_type h) h sa = (vv,sm)` >>
  qpat_x_assum `eval_expr_results _ (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename1 `eval_expr cx h es = (INL raw,esh)` >>
  `esh = es` by metis_tac[supported_pure_eval_expr_state] >> gvs[] >>
  `cs_extends sa sm /\ cs_extends sm cs''` by
    (qspecl_then [`compile_expr`, `cenv`, `args`, `sm`] mp_tac
       ci_mono_compile_multi_vvs >>
     simp[compile_expr_ci_mono] >>
     strip_tac >> fs[ci_mono_def] >>
     metis_tac[cj 1 compile_expr_grows]) >>
  `fn_has_code sa sm func /\ fn_has_code sm cs'' func` by
    metis_tac[fn_has_code_split] >>
  `body_results_ok cx args` by metis_tac[body_results_success_tail] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[compile_expr_local_ptrs_reserved] >>
  `well_typed_expr env h` by gvs[expr_body_pre_def] >>
  `expr_vv_sim ctx func cenv cx (expr_type h) h es` by
    metis_tac[body_results_head_vv_sim] >>
  `expr_vv_res_ok (INL raw)` by metis_tac[aggregate_child_res_ok] >>
  drule_all expr_vv_success_deferred_prefix >>
  disch_then (qspecl_then [`start`, `hs`] mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_then) >>
  disch_then irule >> conj_tac
  >- suspend "tail" >>
  simp[]
QED

Resume body_results_success_deferred_list[tail]:
  rpt strip_tac >>
  first_x_assum (qspecl_then [`sm`, `cs''`, `t`,
    `(expr_type h,raw,vv,sa)::hs`, `rest`] mp_tac) >>
  simp[] >> disch_tac >>
  irule frag_exec_conseq >> first_assum (irule_at Any) >>
  simp[] >> conj_tac
  >- (gvs[vv_post_def]) >>
  rpt strip_tac >> qexists_tac `sa::los` >> simp[]
QED

Finalise body_results_success_deferred_list

Theorem body_results_exception_deferred_list:
  !args sa sb start vvs exc es'.
  body_inv tops ctx cenv cx /\ body_results_ok cx args /\
  expr_sim_inv cenv cx env es /\
  EVERY (supported_pure_expr tops) args /\
  EVERY (\e. expr_body_pre cenv cx env e es) args /\
  eval_expr_results cx args es = (INR exc,es') /\
  compile_multi_vvs compile_expr cenv args sa = (vvs,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = start /\ stmt_state_rel ctx func cenv cx es s)
    (\s. F) (expr_exit (INR exc : eval_result + exception))
Proof
  Induct_on `args`
  >- simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_multi_vvs _ _ _ _ = _` mp_tac >>
  simp[Once compile_multi_vvs_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv (expr_type h) h sa = (vv,sm)` >>
  rename1 `compile_multi_vvs compile_expr cenv args sm = (rest,sb)` >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (qspecl_then [`compile_expr`, `cenv`, `args`, `sm`] mp_tac
       ci_mono_compile_multi_vvs >> simp[compile_expr_ci_mono] >>
     strip_tac >> fs[ci_mono_def] >>
     metis_tac[cj 1 compile_expr_grows]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `expr_vv_sim ctx func cenv cx (expr_type h) h es` by
    metis_tac[body_results_head_vv_sim] >>
  qpat_x_assum `eval_expr_results _ (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >> strip_tac >> gvs[]
  >- suspend "success_head" >>
  suspend "exception_head"
QED

Resume body_results_exception_deferred_list[success_head]:
  rename1 `eval_expr cx h es = (INL raw,esh)` >>
  `esh = es` by metis_tac[supported_pure_eval_expr_state] >> gvs[] >>
  `body_results_ok cx args` by metis_tac[body_results_success_tail] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[compile_expr_local_ptrs_reserved] >>
  `expr_vv_res_ok (INL raw)` by metis_tac[aggregate_child_res_ok] >>
  `frag_exec ctx sa sm
     (\s. s = start /\ stmt_state_rel ctx func cenv cx es s)
     (vv_post ctx func cenv cx h es sa sm start es raw vv)
     (\r. F)` by (irule expr_vv_sim_success_frag >> metis_tac[]) >>
  `frag_exec ctx sa sm
     (\s. s = start /\ stmt_state_rel ctx func cenv cx es s)
     (vv_post ctx func cenv cx h es sa sm start es raw vv)
     (expr_exit (INR exc : eval_result + exception))` by
    (irule frag_exec_conseq >> first_assum (irule_at Any) >> simp[]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ (\r. F)` kall_tac >>
  drule frag_exec_then >> disch_then irule >> simp[] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`sm`, `sb`, `t`, `rest`] mp_tac) >>
  simp[] >> disch_tac >>
  irule frag_exec_conseq >> first_assum (irule_at Any) >>
  gvs[vv_post_def]
QED

Resume body_results_exception_deferred_list[exception_head]:
  `expr_vv_res_ok (INR exc : eval_result + exception)` by
    metis_tac[aggregate_child_res_ok] >>
  irule frag_exec_exit_prefix >> qexists_tac `sm` >> simp[] >>
  irule expr_vv_sim_exception_frag >> metis_tac[]
QED

Finalise body_results_exception_deferred_list
