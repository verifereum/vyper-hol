(* Typed runtime immutable forcing and its actual global-name consumer. *)
Theory bodyToplevelAggregateMemory
Ancestors
  exprSimSource
  bodyImmutableUnwrapMemory bodyToplevelWordMemory bodyToplevelMemory
  bodyMemoryPreds bodyMemoryDefs exprSimHyps exprSimUnwrap exprSimDefs
  exprLowering exprLoweringProps compileEnv context fragExecMem fragExec
  vyperAST vyperValue vyperInterpreter vyperState loweringSlice exprSimLeaves
  accountsRelProps vyperTypeGlobalLookupSoundness vyperTypeSystem vyperTypeCallGraph
  vyperEvalExprPreservesScopesDom

Theorem body_location_code_aggregate_sim_mem:
  expr_body_pre cenv cx env e es /\
  expr_vv_sim_mem ctx func cenv cx ty e es /\
  ~is_word_type (expr_type e) /\ ~cenv.ce_is_ctor /\
  (storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
    !sa. ?p. compile_expr cenv ty e sa = (LocatedValue (expr_type e) p,sa) /\
      p.ptr_location = LocCode /\
      (!x. p.ptr_operand = Var x ==> not_fresh_at sa x)) ==>
  expr_sim_mem ctx func cenv cx ty e es
Proof
  strip_tac >> simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  irule frag_exec_mem_pointwise >> rw[] >> gvs[] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `_ ==> !sa. _` drule_all >>
  disch_then (qspec_then `sa` strip_assume_tac) >> (
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >> strip_tac >>
  `cs_extends sa sb` by metis_tac[unwrap_value_extends] >>
  `fn_has_code sa sa func` by metis_tac[fn_has_code_split, cs_extends_refl] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw,est)` >>
  qpat_x_assum `(do result <- _; _ od) _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `raw`
  >- (rename1 `eval_expr _ _ _ = (INL r,est)` >> simp[] >> strip_tac >>
      drule read_result_state >> strip_tac >> gvs[] >>
      `expr_vv_res_ok (INL r)` by
        (Cases_on `r` >> gvs[expr_vv_res_ok_def, read_result_def,
                             raise_def, expr_res_ok_def]) >>
      `(INL r : eval_result + exception) <>
        INR (Error (RuntimeError "convert empty bytes to signed"))` by simp[] >>
      qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
        (assume_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
      first_x_assum drule_all >> disch_then (qspec_then `s0` assume_tac) >>
      irule frag_exec_mem_seq_pointwise >>
      qexistsl [`\s. vv_post ctx func cenv cx e es sa sa s0 es' r
                    (LocatedValue (expr_type e) p) s /\
                    s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s`, `sa`] >>
      simp[cs_extends_refl] >> reverse conj_tac
      >- (irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >>
          simp[expr_exit_def]) >>
      gen_tac >> strip_tac >> Cases_on `res`
      >- (drule vv_post_read_result >> strip_tac >>
          `MAP FDOM es.scopes = MAP FDOM es'.scopes` by
            (drule eval_expr_preserves_scopes_dom >> simp[]) >>
          irule frag_exec_mem_conseq >>
          qexistsl [`\s. vv_post ctx func cenv cx e es sa sa s0 es' (Value x)
                           (LocatedValue (expr_type e) p) s /\
                         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s`,
                    `\s. expr_post ctx func cenv cx e es sa sb s0 es' x op s /\
                         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s`,
                    `expr_exit (INL x)`] >> simp[] >>
          conj_tac >- metis_tac[] >>
          irule unwrap_runtime_code_copy_sim_mem >> simp[] >>
          metis_tac[expr_body_pre_copy_ok]) >>
      drule vv_post_failed_read >> metis_tac[]) >>
  rename1 `eval_expr _ _ _ = (INR exc,est)` >> strip_tac >> gvs[] >>
  `expr_vv_res_ok (INR exc)` by gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
  `(INR exc : eval_result + exception) <>
   INR (Error (RuntimeError "convert empty bytes to signed"))` by simp[] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (assume_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  first_x_assum drule_all >> disch_then (qspec_then `s0` assume_tac) >>
  `expr_exit (INR exc : eval_result + exception) =
   expr_exit (INR exc : value + exception)` by
    simp[FUN_EQ_THM, expr_exit_exception_transport] >> fs[] >>
  `frag_exec_mem ctx sa sa (\s. s = s0) (\s. F)
     (expr_exit (INR exc : value + exception))` by
    (irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >>
     simp[expr_exit_exception_transport]) >>
  irule frag_exec_mem_exit_prefix >> qexists_tac `sa` >> simp[cs_extends_refl])
QED

Theorem compile_toplevel_immutable_aggregate_runtime_sim_mem:
  !ctx func cenv cx env ty ann src id es ts.
    expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
    ~is_word_type ann /\ ~cenv.ce_is_ctor /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
    expr_sim_mem ctx func cenv cx ty (TopLevelName ann (src,id)) es
Proof
  rpt strip_tac >>
  `env_consistent env cx es /\ state_well_typed es /\
   well_typed_expr env (TopLevelName ann (src,id))` by
    fs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all toplevel_find_NONE_bare_global >> strip_tac >>
  `src = cenv.ce_module /\
   ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
     !tv. evaluate_type (get_tenv cx) ann = SOME tv ==>
          off + type_memory_size tv < dimword (:256)` by
    (fs[expr_sim_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann (src,id)) es` by
    (irule compile_toplevel_name_vv_sim_mem >> metis_tac[]) >>
  irule body_location_code_aggregate_sim_mem >>
  simp[expr_type_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
      simp[compile_expr_def, expr_type_def, contextTheory.mk_ptr_def]) >>
  metis_tac[expr_sim_pre_body_pre]
QED

Theorem body_toplevel_immutable_mem_case:
  !cx ann src id ts.
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
    body_expr_mem_ok cx (TopLevelName ann (src,id))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_word_type ann`
  >- simp[body_toplevel_word_mem_case] >>
  pure_rewrite_tac[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es` by
    simp[expr_sim_pre_body, int_calls_expr_def] >>
  `~cenv.ce_is_ctor` by fs[bodySimTheory.body_inv_def] >>
  metis_tac[compile_toplevel_immutable_aggregate_runtime_sim_mem,
            compile_toplevel_name_vv_sim_mem]
QED

