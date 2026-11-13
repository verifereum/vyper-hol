(*
 * The pointer twins of exprSimUnwrap's expr_sim_of_vv_sim and
 * exprSimStack's expr_vv_sim_stack: an expression's located or stack
 * value gives its lowered value, with the ghost.  The compound
 * expression cases (bodyPtrExprCases) prove one of expr_sim_ptr and
 * expr_vv_sim_ptr and take the other from these.
 *
 * TOP-LEVEL:
 *   expr_sim_ptr_of_vv -- expr_vv_sim_ptr gives expr_sim_ptr
 *   expr_vv_sim_ptr_stack -- expr_sim_ptr gives expr_vv_sim_ptr when
 *     compile_expr leaves a stack value
 *)
Theory exprPtrUnwrap
Ancestors
  bodyPtrDefs fragGasPathPtr exprSimStack exprSimDefs exprSimHyps loweringPosts
  gasExemptCert exprLowering emitHelper compileEnv vyperInterpreter vyperState
  exprPtrUnwrapMarked exprPtrUnwrapIdentity gasOutcomeMarkedPtr exprSimSource exprLoweringProps
  exprOperandVar exprSimUnwrap fragExec pair gasSummaryComposePtr
  fragGasSeqPtr vyperEvalExprPreservesScopesDom
  exprSimAggregateChildren typedMemoryCopy exprSimHypsDefs valueCopyBytes
Libs
  pairLib

(* exprSimStack's expr_stack_outcome with the ghost: a raw value's outcome
   is its forced value's, the post read through Value. *)
Theorem expr_stack_outcome_ptr:
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) /\
  gas_outcome_ptr D tops (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee G tn u. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn u /\
      ptr_val_ok cx (post_value_type cenv e) v op G tn u /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G u) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\res ee gt r. expr_exit res r) ==>
  gas_outcome_ptr D tops (ctx,func) PG (eval_expr cx e) (es,s0,G0,tn0)
    (\res ee G tn u. ?tv. res = INL tv /\
      vv_post ctx func cenv cx e es sa sb s0 ee tv (StackValue t op) u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn u /\
      ptr_vv_ok cx (post_value_type cenv e) tv (StackValue t op) ee G tn u /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G u) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\res ee gt r. expr_exit res r)
Proof
  rw[gas_outcome_ptr_def] >> qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_ptr_at_def]
      >- (qexistsl_tac [`INL (Value v)`, `es_end`, `G`, `tn`, `OK u`] >>
          simp[] >> conj_tac
          >- (gen_tac >> drule eval_expr_force_value >>
              disch_then (qspec_then `es with gas_obs :=
                gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >>
              simp[]) >>
          gvs[expr_post_def, vv_post_def, vv_holds_def, vv_at_def, vv_own_def,
              ptr_vv_ok_def, read_result_def, return_def] >>
          first_assum ACCEPT_TAC) >>
      qexistsl_tac [`case res of INL v => INL (Value v) | INR ex => INR ex`,
                    `es_end`, `G`, `tn`, `r`] >>
      simp[expr_exit_success_map] >> gen_tac >>
      drule eval_expr_force_value >>
      disch_then (qspec_then `es with gas_obs :=
        gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >> simp[]) >>
  disj2_tac >> drule eval_expr_force_ignore >>
  disch_then (fn th => fs[th]) >> metis_tac[]
QED

(* unwrap_value's code takes vv_post and ptr_vv_ok to expr_post and
   ptr_val_ok.  expr_body_pre gives exprSimUnwrap's side condition
   (exprSimHyps' expr_body_pre_copy_ok) and, on success, that the type
   evaluates (exprSimSource's expr_body_pre_runtime_typed), which the
   loaded word's taint needs: ptr_vv_ok's memory clause says nothing about
   a type that doesn't evaluate. *)
Theorem expr_exit_exception_exists[local]:
  (?exc. res = INR exc /\ expr_exit (INR exc : 'b + exception) r) <=>
  expr_exit (res : 'a + exception) r
Proof
  Cases_on `res` >- simp[] >> simp[] >>
  qspecl_then [`(\x:'a. ARB:'b)`, `INR y : 'a + exception`]
    mp_tac expr_exit_success_map >> simp[FUN_EQ_THM]
QED

Theorem expr_sim_ptr_of_vv:
  !d ctx PG func cenv cx env ty e es.
    expr_body_pre cenv cx env e es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es ==>
    expr_sim_ptr d ctx PG func cenv cx ty e es
Proof
  rpt gen_tac >> strip_tac >> simp[expr_sim_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_expr cenv ty e sa = (vv,sm)` >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[compile_expr_ci_mono, compiler_ci_mono_reserved, SND] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_tac >>
  irule gas_outcome_ptr_bind >> conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[]) >>
  suspend "prefix"
QED

Resume expr_sim_ptr_of_vv[prefix]:
  simp[expr_exit_exception_exists] >>
  irule gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at Any) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  suspend "normal"
QED
Resume expr_sim_ptr_of_vv[normal]:
  `eval_expr cx e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL tv,mid with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `~t.vs_halted` by
    (fs[gas_marked_exec_ptr_def] >> metis_tac[gas_path_ptr_ok_not_halted]) >>
  `?v H tf z.
     gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
       (mid with gas_obs := [],t,G,tn) [] (INL v) (mid with gas_obs := []) H tf (OK z) /\
     expr_post ctx func cenv cx e es sa sb s0 (mid with gas_obs := []) v op z /\
     z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
     ghost_inv d cenv cx (mid with gas_obs := []) H tf z /\
     ptr_val_ok cx (post_value_type cenv e) v op H tf z /\
     (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op H z) /\
     ghost_kept cenv es sa G0 tn0 s0 H tf` by
    (Cases_on `post_value_type cenv e = expr_type e`
     >- (qpat_assum `post_value_type cenv e = expr_type e`
           (fn th => fs[th] >> assume_tac th) >>
         irule unwrap_value_marked_read_ptr >> simp[] >>
     conj_tac >- (strip_tac >>
       drule_all expr_body_pre_copy_ok >> simp[]) >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     qexists `ty` >> simp[]) >>
     `type_widens_to env.type_defs (post_value_type cenv e) (expr_type e)` by
       (irule post_value_type_widens >>
        fs[expr_body_pre_def] >> qexistsl_tac [`cx`, `es`] >> simp[]) >>
     `~is_word_type (post_value_type cenv e)` by
       metis_tac[return_source_word_widens_eq] >>
     Cases_on `vv`
     >- (irule exprPtrUnwrapIdentityTheory.unwrap_stack_marked_read_ptr >> simp[] >>
         goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
     rename1 `LocatedValue tag p` >>
     `p.ptr_location = LocMemory` by
       metis_tac[aggregate_unequal_post_result_location] >>
     `~is_word_type tag` by
       (fs[vv_post_def, vv_holds_def] >> metis_tac[is_bytestring_word_type]) >>
     irule exprPtrUnwrapIdentityTheory.unwrap_memory_marked_read_ptr >> simp[] >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  pop_assum strip_assume_tac >>
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  qexists `[]` >> disj1_tac >>
  qexistsl [`INL v`, `mid with gas_obs := []`, `H`, `tf`, `OK z`] >> simp[]
QED
Finalise expr_sim_ptr_of_vv

Theorem expr_vv_sim_ptr_stack:
  !d ctx PG func cenv cx ty e es.
    expr_sim_ptr d ctx PG func cenv cx ty e es /\
    (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op, sb)) /\
    (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es
Proof
  rw[expr_vv_sim_ptr_def] >>
  qpat_x_assum `!sa. ?t op sb. _` (qspec_then `sa` strip_assume_tac) >> gvs[] >>
  `lower_value compile_expr cenv ty e sa = (op, sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[eval_expr_force_admissible] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule expr_stack_outcome_ptr >> conj_tac >> first_assum ACCEPT_TAC
QED
