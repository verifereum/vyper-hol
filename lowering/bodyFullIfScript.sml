(* The conditional statement over the finite-horizon joint judgment: the
   condition's source prefix, the JNZ, the selected branch, its scope
   cleanup and the optional exit jump share one origin/memory/pointer
   witness. *)
Theory bodyFullIf
Ancestors
  bodyFullShared bodyFullPreds bodySimFull gasOutcomeFullStmts gasOutcomeFullCompose
  gasOutcomeFull fragGasEmitCtrl fragGasOriginPtrExec fragGasOriginPtr
  fragGasOrigin gasShadowState gasShadowUnit gasShadow bodyDeclMemoryCompose
  bodyPtrDefs bodyMemoryDefs stmtSimIfProps stmtSimProps
  stmtSimDefs exprSimDefs loweringPosts gasExemptCert gasSummary
  gasSummaryCompose fragGasPathPtr fragGasPathMem fragGasMode fragExec
  ptrSafeRun ptrDiscipline codegenRel contextCodegenRel
  memSafeRun instMemFrontier gasEvents gasCount gasContext
  emitHelper emitHelperProps exprLoweringProps freshWrites
  stmtLowering exprLowering compileEnv valueEncoding allocaHistory
  vyperStorageTrace vyperStorageFootprint vyperStorageBackend
  vyperInterpreter vyperState vyperValue
  venomExecSemantics venomExecProofs venomInst venomState
  list rich_list finite_map pred_set pair

(* ----- The If's compiled layout, paired with its shadow ----- *)

Theorem compile_if_chain[local]:
  !cenv lctx ty c ss1 ss2 st st'.
    compile_stmt cenv lctx ty (If c ss1 ss2) st = ((), st') ==>
    ?op s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 tl el xl x5 x8.
      lower_value compile_expr cenv (BaseT BoolT) c st = (op, s1) /\
      fresh_label "then" s1 = (tl, s2) /\
      fresh_label "else" s2 = (el, s3) /\
      fresh_label "if_exit" s3 = (xl, s4) /\
      emit_inst JNZ [op; Label tl; Label el] [] s4 = ((), s5) /\
      new_block tl s5 = (x5, s6) /\
      compile_stmts cenv lctx ty ss1 s6 = ((), s7) /\
      (if block_is_terminated s7 then s8 = s7
       else emit_inst JMP [Label xl] [] s7 = ((), s8)) /\
      new_block el s8 = (x8, s9) /\
      compile_stmts cenv lctx ty ss2 s9 = ((), s10) /\
      (if block_is_terminated s10 then s11 = s10
       else emit_inst JMP [Label xl] [] s10 = ((), s11)) /\
      (~block_is_terminated s7 \/ ~block_is_terminated s10 ==>
       ?x11. new_block xl s11 = (x11, st')) /\
      (block_is_terminated s7 /\ block_is_terminated s10 ==> st' = s11)
Proof
  rpt gen_tac >>
  simp[compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_get_def,
       emit_jmp_if_not_terminated_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  (fn (asl, w) =>
     MAP_EVERY (fn v => Cases_on `^v`)
       (filter (fn v => type_of v = oneSyntax.one_ty)
          (free_varsl (w :: asl))) (asl, w)) >>
  strip_tac >>
  rename1 `compile_stmts _ _ _ ss1 _ = ((), s7)` >>
  rename1 `new_block else_lbl s8 = (x8, s9)` >>
  rename1 `compile_stmts _ _ _ ss2 _ = ((), s10)` >>
  rename1 `(if block_is_terminated s10 then _ else _) s10 = ((), s11)` >>
  qexistsl_tac [`s8`, `s9`, `s10`, `s11`, `x8`] >>
  Cases_on `block_is_terminated s7` >> Cases_on `block_is_terminated s10` >>
  gvs[comp_return_def, comp_bind_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem compile_if_chain_frontiers[local]:
  !cenv lctx ty c ss1 ss2 sa sb func.
    compile_stmt cenv lctx ty (If c ss1 ss2) sa = ((), sb) /\
    fn_has_code sa sb func /\
    (!sx op sy. lower_value compile_expr cenv (BaseT BoolT) c sx = (op, sy) ==>
       cs_extends sx sy /\ sx.cs_next_var <= sy.cs_next_var) /\
    cs_mono (stmts_env cenv lctx ty ss1) /\
    cs_mono (stmts_env cenv lctx ty ss2) ==>
    ?op s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 tl el xl x5 x8.
      lower_value compile_expr cenv (BaseT BoolT) c sa = (op, s1) /\
      fresh_label "then" s1 = (tl, s2) /\
      fresh_label "else" s2 = (el, s3) /\
      fresh_label "if_exit" s3 = (xl, s4) /\
      emit_inst JNZ [op; Label tl; Label el] [] s4 = ((), s5) /\
      new_block tl s5 = (x5, s6) /\
      compile_stmts cenv lctx ty ss1 s6 = ((), s7) /\
      (if block_is_terminated s7 then s8 = s7
       else emit_inst JMP [Label xl] [] s7 = ((), s8)) /\
      new_block el s8 = (x8, s9) /\
      compile_stmts cenv lctx ty ss2 s9 = ((), s10) /\
      (if block_is_terminated s10 then s11 = s10
       else emit_inst JMP [Label xl] [] s10 = ((), s11)) /\
      fn_has_code sa s1 func /\ cs_extends sa s1 /\
      sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
      s4.cs_current_bb = s1.cs_current_bb /\
      s4.cs_current_insts = s1.cs_current_insts /\
      fn_has_code s4 s5 func /\
      s6.cs_current_bb = tl /\ s6.cs_current_insts = [] /\
      cs_extends sa s6 /\ sa.cs_next_var <= s6.cs_next_var /\
      cs_extends s6 s7 /\ cs_extends s7 sb /\
      s7.cs_next_var <= sb.cs_next_var /\
      fn_has_code s6 s7 func /\ fn_has_code s7 s8 func /\
      (~block_is_terminated s7 ==>
       sb.cs_current_bb = xl /\ sb.cs_current_insts = []) /\
      s9.cs_current_bb = el /\ s9.cs_current_insts = [] /\
      cs_extends sa s9 /\ sa.cs_next_var <= s9.cs_next_var /\
      cs_extends s9 s10 /\ cs_extends s10 sb /\
      s10.cs_next_var <= sb.cs_next_var /\
      fn_has_code s9 s10 func /\ fn_has_code s10 s11 func /\
      (~block_is_terminated s10 ==>
       sb.cs_current_bb = xl /\ sb.cs_current_insts = [])
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_if_chain >> strip_tac >>
  qpat_assum `!sx op sy. _` (drule_then strip_assume_tac) >>
  imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
  imp_res_tac if_branch_compiler_mono >>
  imp_res_tac if_optional_jump_extends >>
  imp_res_tac emit_inst_extends >>
  imp_res_tac cs_extends_fresh_label >> imp_res_tac cs_extends_new_block >>
  `cs_extends s4 s5` by
    (qpat_x_assum `emit_inst JNZ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[cs_appends_emit_helpers, cs_appends_def]) >>
  `cs_extends s11 sb /\ s11.cs_next_var = sb.cs_next_var /\
   (~block_is_terminated s7 \/ ~block_is_terminated s10 ==>
    sb.cs_current_bb = xl /\ sb.cs_current_insts = [])` by
    (Cases_on `block_is_terminated s7` >> Cases_on `block_is_terminated s10` >>
     gvs[cs_extends_refl] >>
     imp_res_tac new_block_props >> imp_res_tac cs_extends_new_block >>
     simp[]) >>
  `cs_extends sa s2` by
    (irule cs_extends_trans >> qexists_tac `s1` >> simp[]) >>
  `cs_extends sa s3` by
    (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  `cs_extends sa s4` by
    (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends sa s5` by
    (irule cs_extends_trans >> qexists_tac `s4` >> simp[]) >>
  `cs_extends sa s6` by
    (irule cs_extends_trans >> qexists_tac `s5` >> simp[]) >>
  `cs_extends sa s7` by
    (irule cs_extends_trans >> qexists_tac `s6` >> simp[]) >>
  `cs_extends sa s8` by
    (irule cs_extends_trans >> qexists_tac `s7` >> simp[]) >>
  `cs_extends sa s9` by
    (irule cs_extends_trans >> qexists_tac `s8` >> simp[]) >>
  `cs_extends sa s10` by
    (irule cs_extends_trans >> qexists_tac `s9` >> simp[]) >>
  `cs_extends sa s11` by
    (irule cs_extends_trans >> qexists_tac `s10` >> simp[]) >>
  `cs_extends sa sb` by
    (irule cs_extends_trans >> qexists_tac `s11` >> simp[]) >>
  `cs_extends s10 sb` by
    (irule cs_extends_trans >> qexists_tac `s11` >> simp[]) >>
  `cs_extends s9 sb` by
    (irule cs_extends_trans >> qexists_tac `s10` >> simp[]) >>
  `cs_extends s8 sb` by
    (irule cs_extends_trans >> qexists_tac `s9` >> simp[]) >>
  `cs_extends s7 sb` by
    (irule cs_extends_trans >> qexists_tac `s8` >> simp[]) >>
  `cs_extends s6 sb` by
    (irule cs_extends_trans >> qexists_tac `s7` >> simp[]) >>
  `cs_extends s5 sb` by
    (irule cs_extends_trans >> qexists_tac `s6` >> simp[]) >>
  `cs_extends s4 sb` by
    (irule cs_extends_trans >> qexists_tac `s5` >> simp[]) >>
  `cs_extends s3 sb` by
    (irule cs_extends_trans >> qexists_tac `s4` >> simp[]) >>
  `cs_extends s2 sb` by
    (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends s1 sb` by
    (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\
   sa.cs_next_var <= s6.cs_next_var /\ sa.cs_next_var <= s9.cs_next_var /\
   s7.cs_next_var <= sb.cs_next_var /\ s10.cs_next_var <= sb.cs_next_var` by
    decide_tac >>
  `fn_has_code sa s1 func` by
    (qspecl_then [`sa`, `sa`, `s1`, `sb`, `func`] mp_tac fn_has_code_mid >>
     simp[cs_extends_refl]) >>
  `fn_has_code s4 s5 func` by
    (qspecl_then [`sa`, `s4`, `s5`, `sb`, `func`] mp_tac fn_has_code_mid >>
     simp[cs_extends_refl]) >>
  `fn_has_code s6 s7 func` by
    (qspecl_then [`sa`, `s6`, `s7`, `sb`, `func`] mp_tac fn_has_code_mid >>
     simp[cs_extends_refl]) >>
  `fn_has_code s7 s8 func` by
    (qspecl_then [`sa`, `s7`, `s8`, `sb`, `func`] mp_tac fn_has_code_mid >>
     simp[cs_extends_refl]) >>
  `fn_has_code s9 s10 func` by
    (qspecl_then [`sa`, `s9`, `s10`, `sb`, `func`] mp_tac fn_has_code_mid >>
     simp[cs_extends_refl]) >>
  `fn_has_code s10 s11 func` by
    (qspecl_then [`sa`, `s10`, `s11`, `sb`, `func`] mp_tac fn_has_code_mid >>
     simp[cs_extends_refl]) >>
  qexistsl_tac [`op`, `s1`, `s2`, `s3`, `s4`, `s5`, `s6`, `s7`, `s8`, `s9`,
                `s10`, `s11`, `tl`, `el`, `xl`, `x5`, `x8`] >>
  simp[]
QED

Theorem compile_if_layout_shadow:
  !cenv lctx ty c ss1 ss2 c' ss1' ss2' sa sb ta tb func sfunc.
  compile_stmt cenv lctx ty (If c ss1 ss2) sa = ((), sb) /\
  compile_stmt cenv lctx ty (If c' ss1' ss2') ta = ((), tb) /\
  gas_shadow_state sa ta /\
  fn_has_code sa sb func /\ fn_has_code ta tb sfunc /\
  (!sx op sy. lower_value compile_expr cenv (BaseT BoolT) c sx = (op, sy) ==>
     cs_extends sx sy /\ sx.cs_next_var <= sy.cs_next_var) /\
  (!sx op sy. lower_value compile_expr cenv (BaseT BoolT) c' sx = (op, sy) ==>
     cs_extends sx sy /\ sx.cs_next_var <= sy.cs_next_var) /\
  cs_mono (stmts_env cenv lctx ty ss1) /\
  cs_mono (stmts_env cenv lctx ty ss2) /\
  cs_mono (stmts_env cenv lctx ty ss1') /\
  cs_mono (stmts_env cenv lctx ty ss2') /\
  gas_shadow_compiles (lower_value compile_expr cenv (BaseT BoolT) c)
    (lower_value compile_expr cenv (BaseT BoolT) c') /\
  gas_shadow_compiles (stmts_env cenv lctx ty ss1)
    (stmts_env cenv lctx ty ss1') /\
  gas_shadow_compiles (stmts_env cenv lctx ty ss2)
    (stmts_env cenv lctx ty ss2') ==>
  ?op cond scond pre post tl el xl.
    lower_value compile_expr cenv (BaseT BoolT) c sa = (op, cond) /\
    lower_value compile_expr cenv (BaseT BoolT) c' ta = (op, scond) /\
    gas_shadow_state cond scond /\
    fn_has_code sa cond func /\ fn_has_code ta scond sfunc /\
    cs_extends sa cond /\ sa.cs_next_var <= cond.cs_next_var /\
    sa.cs_next_var <= sb.cs_next_var /\
    pre.cs_current_bb = cond.cs_current_bb /\
    pre.cs_current_insts = cond.cs_current_insts /\
    emit_inst JNZ [op; Label tl; Label el] [] pre = ((), post) /\
    fn_has_code pre post func /\
    !b. ?entry last after sentry slast cenvb.
      stmts_env cenv lctx ty (if b then ss1 else ss2) entry =
        (cenvb, last) /\
      stmts_env cenv lctx ty (if b then ss1' else ss2') sentry =
        (cenvb, slast) /\
      gas_shadow_state entry sentry /\ gas_shadow_state last slast /\
      fn_has_code sentry slast sfunc /\
      entry.cs_current_bb = (if b then tl else el) /\
      entry.cs_current_insts = [] /\
      cs_extends sa entry /\ sa.cs_next_var <= entry.cs_next_var /\
      cs_extends entry last /\ cs_extends last sb /\
      last.cs_next_var <= sb.cs_next_var /\
      fn_has_code entry last func /\ fn_has_code last after func /\
      (if block_is_terminated last then after = last
       else emit_inst JMP [Label xl] [] last = ((), after)) /\
      (~block_is_terminated last ==>
       sb.cs_current_bb = xl /\ sb.cs_current_insts = [])
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cenv`, `lctx`, `ty`, `c`, `ss1`, `ss2`, `sa`, `sb`, `func`]
    mp_tac compile_if_chain_frontiers >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`op`, `s1`, `s2`, `s3`, `s4`, `s5`, `s6`,
    `s7`, `s8`, `s9`, `s10`, `s11`, `tl`, `el`, `xl`, `x5`, `x8`]
    strip_assume_tac) >>
  qspecl_then [`cenv`, `lctx`, `ty`, `c'`, `ss1'`, `ss2'`, `ta`, `tb`, `sfunc`]
    mp_tac compile_if_chain_frontiers >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`op'`, `t1`, `t2`, `t3`, `t4`, `t5`, `t6`,
    `t7`, `t8`, `t9`, `t10`, `t11`, `tl'`, `el'`, `xl'`, `y5`, `y8`]
    strip_assume_tac) >>
  `op' = op /\ gas_shadow_state s1 t1` by metis_tac[gas_shadow_step] >>
  `tl' = tl /\ gas_shadow_state s2 t2` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_fresh_label] >>
  `el' = el /\ gas_shadow_state s3 t3` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_fresh_label] >>
  `xl' = xl /\ gas_shadow_state s4 t4` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_fresh_label] >>
  qpat_x_assum `op' = op` SUBST_ALL_TAC >>
  qpat_x_assum `tl' = tl` SUBST_ALL_TAC >>
  qpat_x_assum `el' = el` SUBST_ALL_TAC >>
  qpat_x_assum `xl' = xl` SUBST_ALL_TAC >>
  `gas_shadow_state s5 t5` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_emit_inst] >>
  `gas_shadow_state s6 t6` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_new_block] >>
  `stmts_env cenv lctx ty ss1 s6 =
     (FST (stmts_env cenv lctx ty ss1 s6), s7) /\
   stmts_env cenv lctx ty ss1' t6 =
     (FST (stmts_env cenv lctx ty ss1' t6), t7) /\
   stmts_env cenv lctx ty ss2 s9 =
     (FST (stmts_env cenv lctx ty ss2 s9), s10) /\
   stmts_env cenv lctx ty ss2' t9 =
     (FST (stmts_env cenv lctx ty ss2' t9), t10)` by
    (fs[compile_stmts_env] >> metis_tac[PAIR]) >>
  qabbrev_tac `e1 = FST (stmts_env cenv lctx ty ss1 s6)` >>
  qabbrev_tac `e1' = FST (stmts_env cenv lctx ty ss1' t6)` >>
  qabbrev_tac `e2 = FST (stmts_env cenv lctx ty ss2 s9)` >>
  qabbrev_tac `e2' = FST (stmts_env cenv lctx ty ss2' t9)` >>
  `e1' = e1 /\ gas_shadow_state s7 t7` by metis_tac[gas_shadow_step] >>
  qpat_x_assum `e1' = e1` SUBST_ALL_TAC >>
  `block_is_terminated t7 = block_is_terminated s7` by
    metis_tac[gas_shadow_terminated] >>
  `gas_shadow_state s8 t8` by
    (Cases_on `block_is_terminated s7` >> gvs[] >>
     metis_tac[gas_shadow_step, gas_shadow_compiles_emit_inst]) >>
  `gas_shadow_state s9 t9` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_new_block] >>
  `e2' = e2 /\ gas_shadow_state s10 t10` by metis_tac[gas_shadow_step] >>
  qpat_x_assum `e2' = e2` SUBST_ALL_TAC >>
  `block_is_terminated t10 = block_is_terminated s10` by
    metis_tac[gas_shadow_terminated] >>
  qexistsl_tac [`op`, `s1`, `t1`, `s4`, `s5`, `tl`, `el`, `xl`] >>
  simp[] >> gen_tac >> Cases_on `b` >> simp[]
  >- (qexistsl_tac [`s6`, `s7`, `s8`, `t6`, `t7`, `e1`] >> simp[]) >>
  qexistsl_tac [`s9`, `s10`, `s11`, `t9`, `t10`, `e2`] >> simp[]
QED

(* ----- The selected branch ----- *)

Theorem if_full_condition_bool[local]:
  gas_admissible (eval_stmt cx (If c ss1 ss2)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := xs ++ tail) = (INL v, mid with gas_obs := tail)) ==>
  ?b. v = BoolV b
Proof
  strip_tac >> spose_not_then assume_tac >>
  `v <> BoolV T /\ v <> BoolV F` by metis_tac[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  rewrite_tac[gas_admissible_def] >>
  disch_then (qspecl_then [`xs`,
    `INR (Error (TypeError "not BoolV"))`, `mid with gas_obs := []`] mp_tac) >>
  simp[stmt_res_ok_def] >>
  first_x_assum (qspec_then `[]` assume_tac) >> fs[] >>
  rewrite_tac[eval_stmt_if_forced] >>
  pure_once_rewrite_tac[bind_def] >> simp[raise_def]
QED

Theorem if_next_selected[local]:
  (if BoolV b = BoolV T then
     ignore_bind push_scope (finally (eval_stmts cx ss1) pop_scope)
   else if BoolV b = BoolV F then
     ignore_bind push_scope (finally (eval_stmts cx ss2) pop_scope)
   else raise (Error (TypeError "not BoolV"))) =
  ignore_bind push_scope
    (finally (eval_stmts cx (if b then ss1 else ss2)) pop_scope)
Proof
  Cases_on `b` >> simp[]
QED

(* The optional exit jump, and the condition's frame before the branch,
   at one horizon; the endpoint does not depend on the horizon. *)
Theorem if_full_post_finish[local]:
  !D lo d explicit ctx func PG cx lctx cenv H es sa sb s0 G0 tn0 t G1 tn1
   lbl entry last after xl res ee u G tn.
  (?cenv''.
     stmt_lands lctx last res u /\ ~u.vs_halted /\
     (res = INL () ==> ~block_is_terminated last /\ cenv'' = cenv) /\
     cenv_top_ext cenv cenv'' ee.scopes /\
     stmt_state_rel H ctx func cenv'' cx ee u /\
     storage_well_formed_on cx ee (FST H) /\
     return_buf_frame d cenv'' last u /\ alloca_history func u /\
     (jump_to lbl t).vs_alloca_next <= u.vs_alloca_next /\
     ghost_inv_at D lo d cenv'' cx ee G tn u /\
     (!x w. not_fresh_at entry x /\ lookup_var x (jump_to lbl t) = SOME w ==>
            lookup_var x u = SOME w) /\
     (!aid b. FLOOKUP (jump_to lbl t).vs_allocas aid = SOME b ==>
              FLOOKUP u.vs_allocas aid = SOME b) /\
     (!x. not_fresh_at entry x ==>
          FLOOKUP G x = FLOOKUP G1 x /\
          op_taint tn (Var x) = op_taint tn1 (Var x))) /\
  ~ctx_has_dalloca ctx /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP t.vs_allocas aid = SOME b) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  sa.cs_next_var <= entry.cs_next_var /\
  last.cs_next_var <= sb.cs_next_var /\
  (~block_is_terminated last ==>
     emit_inst JMP [Label xl] [] last = ((), after) /\
     fn_has_code last after func /\
     sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (u, G, tn) [] (OK (if res = INL () then jump_to xl u else u), G, tn) /\
  ?cenv''.
    stmt_lands lctx sb res (if res = INL () then jump_to xl u else u) /\
    ~(if res = INL () then jump_to xl u else u).vs_halted /\
    (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
    cenv_top_ext cenv cenv'' ee.scopes /\
    stmt_state_rel H ctx func cenv'' cx ee
      (if res = INL () then jump_to xl u else u) /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv'' sb (if res = INL () then jump_to xl u else u) /\
    alloca_history func (if res = INL () then jump_to xl u else u) /\
    s0.vs_alloca_next <=
      (if res = INL () then jump_to xl u else u).vs_alloca_next /\
    ghost_inv_at D lo d cenv'' cx ee G tn
      (if res = INL () then jump_to xl u else u) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x (if res = INL () then jump_to xl u else u) = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP (if res = INL () then jump_to xl u else u).vs_allocas aid =
               SOME b) /\
    (!x. not_fresh_at sa x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x u = SOME w` by
    (rpt strip_tac >>
     `lookup_var x t = SOME w` by metis_tac[] >>
     `not_fresh_at entry x` by metis_tac[not_fresh_at_mono] >>
     fs[lookup_var_def, jump_to_def]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b` by
    (rpt strip_tac >> fs[jump_to_def]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by fs[jump_to_def] >>
  `!x. not_fresh_at sa x ==>
       FLOOKUP G x = FLOOKUP G0 x /\
       op_taint tn (Var x) = op_taint tn0 (Var x)` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at entry x` by metis_tac[not_fresh_at_mono] >>
     fs[ghost_kept_at_def]) >>
  `return_buf_frame d cenv'' sb u` by
    (qspecl_then [`d`, `cenv''`, `cenv''`, `last`, `sb`, `u`, `u`] mp_tac
       return_buf_frame_frame >> simp[]) >>
  Cases_on `res = INL ()`
  >- (qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
      `~block_is_terminated last` by fs[] >>
      `cenv'' = cenv` by fs[] >> pop_assum SUBST_ALL_TAC >>
      `emit_inst JMP [Label xl] [] last = ((), after) /\
       fn_has_code last after func /\
       sb.cs_current_bb = xl /\ sb.cs_current_insts = []` by fs[] >>
      `u.vs_current_bb = last.cs_current_bb /\
       u.vs_inst_idx = LENGTH last.cs_current_insts` by
        (qpat_x_assum `stmt_lands _ _ _ _` mp_tac >> simp[stmt_lands_def]) >>
      `allocas_from lo u` by fs[ghost_inv_at_def] >>
      `gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
         (u, G, tn) [] (OK (jump_to xl u), G, tn)` by
        (qpat_assum `emit_inst JMP _ _ _ = _`
           (irule o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                emit_jmp_origin_ptr)) >>
         simp[]) >>
      `alloca_history func (jump_to xl u)` by
        (irule alloca_history_jump >> conj_tac >- simp[jump_to_def] >>
         qexists_tac `u` >> simp[jump_to_def]) >>
      `!x. lookup_var x (jump_to xl u) = lookup_var x u` by
        simp[lookup_var_def, jump_to_def] >>
      conj_tac >- simp[] >> qexists_tac `cenv` >>
      simp[stmt_lands_def, stmt_state_rel_jump_to, block_is_terminated_def,
           return_buf_frame_jump_to, ghost_inv_at_jump] >>
      simp[jump_to_def]) >>
  `stmt_lands lctx sb res u` by
    (qpat_x_assum `stmt_lands _ _ _ _` mp_tac >> simp[stmt_lands_def]) >>
  asm_simp_tac std_ss [] >>
  conj_tac >- (irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  qexists_tac `cenv''` >> simp[]
QED

(* ----- The If fragment ----- *)

Theorem stmt_env_if[local]:
  stmt_env cenv lctx ty (If c ss1 ss2) st = (cenv', st') <=>
  cenv' = cenv /\ compile_stmt cenv lctx ty (If c ss1 ss2) st = ((), st')
Proof
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty (If c ss1 ss2) st` >>
  rename1 `(u, st1)` >> Cases_on `u` >> simp[] >> metis_tac[]
QED

Theorem compile_if_stmt_frag_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty c ss1 ss2
   es.
    expr_type c = BaseT BoolT /\
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (BaseT BoolT) c es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    (!sa op sb.
       lower_value compile_expr cenv (BaseT BoolT) (gas_shadow_expr c) sa =
         (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    cs_mono (stmts_env cenv lctx ty ss1) /\
    cs_mono (stmts_env cenv lctx ty ss2) /\
    cs_mono (stmts_env cenv lctx ty (MAP gas_shadow_stmt ss1)) /\
    cs_mono (stmts_env cenv lctx ty (MAP gas_shadow_stmt ss2)) /\
    gas_shadow_compiles (lower_value compile_expr cenv (BaseT BoolT) c)
      (lower_value compile_expr cenv (BaseT BoolT) (gas_shadow_expr c)) /\
    gas_shadow_compiles (stmts_env cenv lctx ty ss1)
      (stmts_env cenv lctx ty (MAP gas_shadow_stmt ss1)) /\
    gas_shadow_compiles (stmts_env cenv lctx ty ss2)
      (stmts_env cenv lctx ty (MAP gas_shadow_stmt ss2)) /\
    (!gs b es1.
       bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
         (INL (BoolV b), es1) ==>
       stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (stmts_env cenv lctx ty
            (if b then MAP gas_shadow_stmt ss1 else MAP gas_shadow_stmt ss2))
         (eval_stmts cx (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (If c ss1 ss2))
      (stmt_env cenv lctx ty
         (If (gas_shadow_expr c) (MAP gas_shadow_stmt ss1)
            (MAP gas_shadow_stmt ss2)))
      (eval_stmt cx (If c ss1 ss2)) es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[stmt_frag_full_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (If c _ _) _ = _`
    (strip_assume_tac o REWRITE_RULE [stmt_env_if]) >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  qpat_x_assum `stmt_env _ _ _ (If (gas_shadow_expr c) _ _) _ = _`
    (strip_assume_tac o SIMP_RULE std_ss [stmt_env_if]) >>
  qspecl_then [`cenv`, `lctx`, `ty`, `c`, `ss1`, `ss2`, `gas_shadow_expr c`,
    `MAP gas_shadow_stmt ss1`, `MAP gas_shadow_stmt ss2`, `sa`, `sb`,
    `shadow_sa`, `shadow_sb`, `func`, `shadow_func`]
    mp_tac compile_if_layout_shadow >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  `gas_admissible (bind (eval_expr cx c) (read_result cx)) expr_res_ok es` by
    (irule if_condition_admissible >> metis_tac[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  (* the condition, on the If's own input block *)
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `cond`, `shadow_sa`, `scond`, `op`,
    `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ condQ condR` >>
  rewrite_tac[eval_stmt_if_forced] >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (rw[storage_trace_frame_raise] >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates] >>
      irule storage_trace_frame_finally >>
      simp[storage_trace_frame_pop_scope, evaluate_storage_trace_frame]) >>
  qexists_tac `\H res ee G' tn' t. condQ H res ee G' tn' t /\ ~t.vs_halted /\
                 ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "selected" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `condR`] >> rpt strip_tac >>
  Cases_on `res` >- fs[expr_exit_def] >>
  simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_if_stmt_frag_full[selected]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `condQ` >> RULE_ASSUM_TAC BETA_RULE >>
  (* the condition's H-free facts, at the trace's own horizon *)
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  `(!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
          lookup_var x t = SOME w) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
            FLOOKUP t.vs_allocas aid = SOME b)` by fs[expr_post_def] >>
  drule_all if_full_condition_bool >> strip_tac >>
  qpat_x_assum `v = BoolV _` SUBST_ALL_TAC >>
  qexists_tac `BoolV b` >> conj_tac >- simp[] >>
  rewrite_tac[if_next_selected] >>
  qpat_x_assum `!b. ?entry last after sentry slast cenvb. _`
    (qspec_then `b` strip_assume_tac) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    (drule_all if_condition_operand >>
     simp[valueEncodingTheory.val_to_w256_def]) >>
  `op_taint tn1 op = {} /\ allocas_from lo t` by
    metis_tac[ptr_val_ok_def, ghost_inv_at_def] >>
  (* the JNZ into the selected branch *)
  `!H. gas_origin_ptr_path
         (DF H, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
         (t, G1, tn1) [] (OK (jump_to (if b then tl else el) t), G1, tn1)` by
    (gen_tac >>
     qpat_assum `emit_inst JNZ _ _ _ = _`
       (irule o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                            emit_jnz_origin_ptr)) >>
     fs[]) >>
  pop_assum (irule o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                 gas_outcome_full_zero_prefix)) >>
  `bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL (BoolV b), mid)` by
    (`mid with gas_obs := [] = mid` by
       fs[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pop_assum (fn th => rewrite_tac [th, APPEND_NIL])) >>
  `gas_admissible (eval_stmts cx (if b then ss1 else ss2)) (stmt_res_ok lctx)
     (mid with scopes := FEMPTY :: mid.scopes)` by
    (drule_all if_branch_admissible >> simp[]) >>
  (* the selected branch, on the condition's posts *)
  qpat_x_assum `!gs b es1. _`
    (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `b`, `mid`]
       mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  rewrite_tac[stmt_frag_full_def] >>
  disch_then (qspecl_then [`st0`, `entry`, `last`, `sentry`, `slast`,
    `jump_to (if b then tl else el) t`, `G1`, `tn1`, `cenvb`] mp_tac) >>
  (impl_tac >- suspend "entry") >>
  strip_tac >>
  `~(jump_to (if b then tl else el) t).vs_halted` by simp[jump_to_def] >>
  drule gas_outcome_full_scope_cleanup >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (ignore_bind _ _) _ _ _`
    (mp_then Any irule gas_outcome_full_zero_suffix_mono) >>
  conj_tac
  >~ [`gas_origin_ptr_path _ _ _ _`] >- suspend "finish" >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> gen_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  `(ee with scopes := sc :: ee.scopes) with gas_obs := tail =
   (ee with gas_obs := tail) with scopes := sc :: ee.scopes` by
    simp[evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >> simp[stmt_exit_ptr_def]
QED

Resume compile_if_stmt_frag_full[entry]:
  `!H. valid_horizon cx st0 H
         (mid with scopes := FEMPTY :: mid.scopes).storage_trace ==>
       stmt_state_rel H ctx func cenv cx
         (mid with scopes := FEMPTY :: mid.scopes)
         (jump_to (if b then tl else el) t) /\
       storage_well_formed_on cx (mid with scopes := FEMPTY :: mid.scopes)
         (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx
         (mid with scopes := FEMPTY :: mid.scopes) G1 tn1
         (jump_to (if b then tl else el) t)` by
    (gen_tac >> simp[] >> strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[] >>
     `stmt_state_rel H ctx func cenv cx mid t /\
      storage_well_formed_on cx mid (FST H)` by fs[expr_post_def] >>
     simp[stmt_state_rel_jump_to, stmt_state_rel_push_scope,
          ghost_inv_at_jump] >>
     conj_tac >- fs[storage_well_formed_on_def, get_storage_scopes] >>
     irule ghost_inv_at_push >> first_assum ACCEPT_TAC) >>
  `alloca_history func (jump_to (if b then tl else el) t)` by
    (irule alloca_history_jump >> conj_tac >- simp[jump_to_def] >>
     qexists_tac `t` >> simp[jump_to_def]) >>
  `ret_pc_ok cenv entry t` by
    (qspecl_then [`cenv`, `cenv`, `sa`, `entry`, `s0`, `t`] mp_tac
       ret_pc_ok_frame >> impl_tac >- fs[] >> simp[]) >>
  `return_buf_frame d cenv entry t` by
    (qspecl_then [`d`, `cenv`, `cenv`, `sa`, `entry`, `s0`, `t`] mp_tac
       return_buf_frame_frame >> impl_tac >- fs[] >> simp[]) >>
  `local_ptrs_reserved cenv entry` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at entry x` by metis_tac[not_fresh_at_mono] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[ret_pc_ok_jump_to, return_buf_frame_jump_to, block_is_terminated_def,
       jump_to_def]
QED

Resume compile_if_stmt_frag_full[finish]:
  qx_genl_tac [`res`, `ee`, `G`, `tn`, `u`] >> strip_tac >>
  qexistsl_tac [`if res = INL () then jump_to xl u else u`, `G`, `tn`] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> BETA_TAC >>
  disch_then (qx_choose_then `sc` (CONJUNCTS_THEN2
    (assume_tac o BETA_RULE) assume_tac)) >>
  `(ee with scopes := sc::ee.scopes).scopes = sc::ee.scopes` by simp[] >>
  pop_assum (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  drule_all full_post_scope_pop >> disch_then assume_tac >>
  `~block_is_terminated last ==>
   emit_inst JMP [Label xl] [] last = ((), after) /\
   fn_has_code last after func /\
   sb.cs_current_bb = xl /\ sb.cs_current_insts = []` by
    (strip_tac >> fs[]) >>
  qspecl_then [`DF H`, `lo`, `d`, `gas_explicit_sites ctx shadow_ctx`, `ctx`,
    `func`, `PG`, `cx`, `lctx`, `cenv`, `H`, `es`, `sa`, `sb`, `s0`, `G0`,
    `tn0`, `t`, `G1`, `tn1`, `if b then tl else el`, `entry`, `last`,
    `after`, `xl`, `res`, `ee`, `u`, `G`, `tn`] mp_tac if_full_post_finish >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  BETA_TAC >> disch_then ACCEPT_TAC
QED

Finalise compile_if_stmt_frag_full
