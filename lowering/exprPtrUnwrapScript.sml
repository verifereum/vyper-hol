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
  fragGasSeqPtr vyperEvalExprPreservesScopesDom gasSummaryComposePtrAll
  exprSimAggregateChildren typedMemoryCopy exprSimHypsDefs valueCopyBytes
Libs
  pairLib

(* exprSimStack's expr_stack_outcome with the ghost: a raw value's outcome
   is its forced value's, the post read through Value. *)
Theorem expr_stack_outcome_ptr:
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) /\
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn u. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sb s0 ee v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv H d cenv cx ee G tn u /\
      ptr_val_ok cx (post_value_type cenv e) v op G tn u /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G u) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r) ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0 (eval_expr cx e) (es,s0,G0,tn0)
    (\H res ee G tn u. ?tv. res = INL tv /\
      vv_post H ctx func cenv cx e es sa sb s0 ee tv (StackValue t op) u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv H d cenv cx ee G tn u /\
      ptr_vv_ok cx (post_value_type cenv e) tv (StackValue t op) ee G tn u /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G u) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> gvs[gasStorageTheory.gas_bad_storage_at_def] >> gen_tac >>
      Cases_on `bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail)` >>
      drule_all eval_expr_force_value >> strip_tac >> gvs[] >>
      first_x_assum (qspec_then `tail` mp_tac) >> simp[])
  >- (disj2_tac >> disj1_tac >> gvs[gas_summary_ptr_at_def] >>
      qexistsl_tac [`case res of INL v => INL (Value v) | INR ex => INR ex`,
                    `es_end`, `G`, `tn`, `r`] >>
      conj_tac
      >- (gen_tac >> qpat_x_assum `!tail. _` (qspec_then `tail` assume_tac) >>
          drule_all eval_expr_force_value >> simp[]) >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[expr_exit_success_map] >>
      gvs[expr_post_def, vv_post_def, vv_holds_def, vv_at_def, vv_own_def,
          ptr_vv_ok_def, read_result_def, return_def] >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> disj2_tac >> drule eval_expr_force_ignore >>
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

(* The unwrap lemmas take any horizon family P, polymorphic in the horizon
   type; here P is every valid horizon at the expression's endpoint. *)
fun horizon_family th =
  qpat_assum `valid_horizon _ _ _ _` (fn hv =>
    let
      val tm = concl hv
      val f = mk_abs (el 3 (snd (strip_comb tm)), tm)
      val P = Lib.first (fn v => fst (dest_var v) = "P") (free_vars (concl th))
      val th' = INST_TYPE (match_type (type_of P) (type_of f)) th
    in
      irule (BETA_RULE (INST [mk_var ("P", type_of f) |-> f] th'))
    end)

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
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `vv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_tac >>
  irule gas_outcome_ptr_bind_all >>
  first_assum (irule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> rpt conj_tac >> rpt strip_tac
  >~ [`gas_exempt_cert F _ _ _ _ (left ++ right) _ _`]
  >- (irule gas_exempt_cert_bind_result >> goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert F _ _ _ _ marks _ _`]
  >- (irule gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame _`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]
  >~ [`gas_outcome_ptr _ _ _ _ _ _ (read_result cx _) _ _ _`]
  >- suspend "read" >>
  gvs[expr_exit_exception_exists]
QED

Resume expr_sim_ptr_of_vv[read]:
  rename1 `gas_marked_exec F _ (eval_expr cx e) _ left (INL tv) mid (OK t)` >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `eval_expr cx e
     (es with gas_obs := gas_explicit left s0.vs_gas_readings) =
     (INL tv,mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec F _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit left s0.vs_gas_readings)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `~t.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `?rv HG tf z.
     (!D. gas_marked_exec_ptr D (ctx,func) PG (read_result cx tv)
            (mid with gas_obs := [],t,G,tn) [] (INL rv) (mid with gas_obs := [])
            HG tf (OK z)) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
        expr_post H ctx func cenv cx e es sa sb s0 (mid with gas_obs := []) rv op z /\
        ghost_inv H d cenv cx (mid with gas_obs := []) HG tf z) /\
     z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
     ptr_val_ok cx (post_value_type cenv e) rv op HG tf z /\
     (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op HG z) /\
     ghost_kept cenv es sa G0 tn0 s0 HG tf` by suspend "unwrap" >>
  pop_assum strip_assume_tac >>
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  qexists `[]` >> disj2_tac >> disj1_tac >>
  qexistsl [`INL rv`, `mid with gas_obs := []`, `HG`, `tf`, `OK z`] >>
  conj_tac
  >- (qpat_assum `!D. gas_marked_exec_ptr D _ _ _ _ _ _ _ _ _ _`
        (qspec_then `ARB` mp_tac) >>
      rewrite_tac[gas_marked_exec_ptr_def] >>
      disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  gen_tac >> disch_then (assume_tac o SIMP_RULE (srw_ss()) []) >> simp[]
QED

Resume expr_sim_ptr_of_vv[unwrap]:
  Cases_on `post_value_type cenv e = expr_type e`
  >- (qpat_assum `post_value_type cenv e = expr_type e`
        (fn th => fs[th] >> assume_tac th) >>
      horizon_family unwrap_value_marked_read_ptr >> simp[] >>
      conj_tac >- (strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
      conj_tac >- (qexists_tac `H` >> first_assum ACCEPT_TAC) >>
      goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[]) >>
  `type_widens_to env.type_defs (post_value_type cenv e) (expr_type e)` by
    (irule post_value_type_widens >>
     fs[expr_body_pre_def] >> qexistsl_tac [`cx`, `es`] >> simp[]) >>
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[return_source_word_widens_eq] >>
  Cases_on `vv`
  >- (horizon_family unwrap_stack_marked_read_ptr_horizons >> simp[] >>
      goal_assum (drule_at (Pat `unwrap_value _ _ _ = _`)) >> simp[]) >>
  rename1 `LocatedValue tag p` >>
  `p.ptr_location = LocMemory` by
    metis_tac[aggregate_unequal_post_result_location] >>
  `~is_word_type tag` by
    (qpat_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [vv_post_def, vv_holds_def]) >>
     metis_tac[is_bytestring_word_type]) >>
  horizon_family unwrap_memory_marked_read_ptr_horizons >> simp[] >>
  conj_tac >- (qexists_tac `H` >> first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `unwrap_value _ _ _ = _`)) >> simp[]
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
  disch_then (qspecl_then [`st0`, `sa`, `sb`, `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule expr_stack_outcome_ptr >> conj_tac >> first_assum ACCEPT_TAC
QED
