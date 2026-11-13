(* Compiler slices and preservation of an owned RHS through target evaluation. *)
Theory placeAssignSourceTransport
Ancestors
  bodyMemoryDefs exprSimProps exprSimMemoryPath stmtSimAssign
  exprLoweringProps stmtLowering loweringPosts targetPlaceSimDefs
  valueEncodingProofs freshWrites compileEnv emitHelper context venomState arithmetic fragExec stmtLoweringMono
  exprSimUnwrapProps vyperEvalExprPreservesScopesDom
Libs
  monadsyntax

Theorem assign_place_relayout_code_parts:
  compile_stmt ce lctx ty (Assign (BaseTarget bt) e) a = ((),sb) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
  ?vv sv r sa src su.
    compile_expr ce (expr_type e) e a = (vv,sv) /\
    compile_get_target_ptr compile_expr ce bt sv = (r,sa) /\
    unwrap_value ce vv sa = (src,su) /\
    (case FST (SND r) of
       SOME loc => compile_assign_value ce (FST r) loc src
         (is_word_type (case SND (SND r) of SOME (ValPT dt) => dt
                       | _ => lowered_value_type ce e))
         (vv_location vv)
         (case SND (SND r) of SOME (ValPT dt) => dt
          | _ => lowered_value_type ce e) (lowered_value_type ce e)
         (case (case SND (SND r) of SOME (ValPT dt) => dt
                | _ => lowered_value_type ce e) of
            ArrayT et (Dynamic _) =>
              SOME ((type_memory_bytes ce et + 31) DIV 32,
                    type_memory_bytes ce et) | _ => NONE)
         (type_memory_bytes ce (case SND (SND r) of SOME (ValPT dt) => dt
                               | _ => lowered_value_type ce e)) su
     | NONE => emit_void INVALID [] su) = ((),sb)
Proof
  strip_tac >> qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  Cases_on `FST (SND tgt_result)` >> gvs[]
QED

Theorem assign_place_memory_relayout_suffix:
  compile_stmt ce lctx ty (Assign (BaseTarget bt) e) a = ((),sb) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  compile_expr ce (expr_type e) e a = (LocatedValue sty sp,sv) /\
  compile_get_target_ptr compile_expr ce bt sv =
    ((dst,SOME loc,SOME (ValPT dty)),sa) /\
  sp.ptr_location = LocMemory /\ ~is_word_type sty ==>
  compile_assign_value ce dst loc sp.ptr_operand (is_word_type dty)
    (SOME LocMemory) dty (lowered_value_type ce e)
    (case dty of ArrayT et (Dynamic _) =>
      SOME ((type_memory_bytes ce et + 31) DIV 32,
            type_memory_bytes ce et) | _ => NONE)
    (type_memory_bytes ce dty) sa = ((),sb)
Proof
  strip_tac >> drule_all assign_place_relayout_code_parts >>
  simp[unwrap_memory_compile, comp_return_def, vv_location_def] >>
  strip_tac >> gvs[]
QED

Theorem assign_source_own_target[local]:
  expr_val_own ce cx sty a sv es v src s /\
  sv.cs_next_id <= sa.cs_next_id /\
  target_post ctx func ce cx es sv sa s ee pv vt r t /\
  local_ptrs_reserved ce sv /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  stmt_state_rel ctx func ce cx es s /\ t.vs_labels = s.vs_labels /\
  (!x. src = Var x ==> not_fresh_at sv x) ==>
  expr_val_own ce cx sty a sa ee v src t
Proof
  strip_tac >>
  `!w. eval_operand src s = SOME w ==> eval_operand src t = SOME w` by
    (Cases_on `src` >> fs[eval_operand_def, target_post_def]) >>
  `!n b sz. local_region ce ee.scopes t n b sz ==>
             local_region ce es.scopes s n b sz` by
    (rpt strip_tac >> irule local_region_frame >>
     fs[stmt_state_rel_def, state_rel_def, target_post_def] >>
     metis_tac[]) >>
  fs[expr_val_own_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `w` >> simp[] >>
  disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >>
  fs[target_post_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem assign_source_owned_bytes_target[local]:
  expr_val_own ce cx sty a sv es v src s /\
  target_post ctx func ce cx es sv sa s ee pv vt r t /\
  evaluate_type (get_tenv cx) sty = SOME tv /\ ~is_word_type sty /\
  eval_operand src s = SOME w ==>
  mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >> Cases_on `val_footprint tv v = 0`
  >- simp[valueEncodingTheory.mem_bytes_at_def] >>
  fs[expr_val_own_def] >> gvs[] >>
  `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (fs[target_post_def] >> metis_tac[]) >>
  drule (cj 1 mem_bytes_at_agree_window) >>
  disch_then (qspecl_then [`w2n w`,`val_footprint tv v`] mp_tac) >> simp[]
QED

Theorem assign_source_value_target:
  expr_val_rel cx sty v src s /\
  expr_val_at ce cx sty a sv es v src s /\
  expr_val_own ce cx sty a sv es v src s /\
  sv.cs_next_id <= sa.cs_next_id /\
  target_post ctx func ce cx es sv sa s ee pv vt r t /\
  local_ptrs_reserved ce sv /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  stmt_state_rel ctx func ce cx es s /\ t.vs_labels = s.vs_labels /\
  (!x. src = Var x ==> not_fresh_at sv x) /\
  evaluate_type (get_tenv cx) sty = SOME tv /\ ~is_word_type sty ==>
  expr_val_rel cx sty v src t /\
  expr_val_at ce cx sty a sa ee v src t /\
  expr_val_own ce cx sty a sa ee v src t
Proof
  strip_tac >>
  `expr_val_own ce cx sty a sa ee v src t` by
    (irule assign_source_own_target >> metis_tac[]) >>
  `val_wf tv v /\ ?w. eval_operand src s = SOME w` by
    (fs[expr_val_at_def] >> metis_tac[]) >>
  `eval_operand src t = SOME w` by
    (Cases_on `src` >> fs[eval_operand_def, target_post_def]) >>
  `mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory` by
    (irule assign_source_owned_bytes_target >> metis_tac[]) >>
  conj_tac
  >- (irule expr_val_rel_footprint_agree >> metis_tac[]) >>
  simp[] >> fs[expr_val_at_def, expr_val_own_def] >> metis_tac[]
QED

Theorem assign_place_code_slices:
  compile_expr ce (expr_type e) e a = (vv,sv) /\
  compile_get_target_ptr compile_expr ce bt sv = (r,sa) /\
  compile_assign_value ce dst loc src prim sl dty sty info bytes sa = ((),sb) /\
  fn_has_code a sb func ==>
  fn_has_code a sv func /\ fn_has_code sv sa func /\
  fn_has_code a sa func /\ fn_has_code sa sb func /\
  ci_mono a sv /\ ci_mono sv sa /\ ci_mono sa sb
Proof
  strip_tac >>
  `ci_mono a sv` by
    (fs[ci_mono_def] >> metis_tac[compile_expr_grows]) >>
  `ci_mono sv sa` by
    (mp_tac (Q.SPECL [`bt`,`ce`,`sv`] ci_mono_compile_get_target_ptr) >>
     simp[]) >>
  `ci_mono sa sb` by
    metis_tac[cj 1 ci_mono_stmt_helpers, pairTheory.SND] >>
  fs[ci_mono_def] >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem assign_vv_source_target:
  vv_post ctx func ce cx e es a sv s0 es1 tv (LocatedValue sty sp) s /\
  read_result cx tv es1 = (INL v,es1) /\
  sp.ptr_location = LocMemory /\ ~is_word_type sty /\
  sty = post_value_type ce e /\ sty <> expr_type e /\
  sv.cs_next_id <= sa.cs_next_id /\
  sv.cs_next_var <= sa.cs_next_var /\
  target_post ctx func ce cx es1 sv sa s ee pv vt r t /\
  local_ptrs_reserved ce sv /\
  eval_base_place cx bt es1 = (INL pv,ee) /\
  t.vs_labels = s.vs_labels /\
  (!x. sp.ptr_operand = Var x ==> not_fresh_at sv x) /\
  evaluate_type (get_tenv cx) sty = SOME stv ==>
  expr_val_rel cx sty v sp.ptr_operand t /\
  expr_val_at ce cx sty a sa ee v sp.ptr_operand t /\
  expr_val_own ce cx sty a sa ee v sp.ptr_operand t /\
  (!x. sp.ptr_operand = Var x ==> not_fresh_at sa x)
Proof
  strip_tac >>
  drule_all vv_post_read_result >> disch_then (fn th => fs[th]) >>
  drule_all expr_post_of_vv_post_memory >> strip_tac >>
  `MAP FDOM es1.scopes = MAP FDOM ee.scopes` by
    metis_tac[eval_base_place_preserves_scopes_dom] >>
  `expr_val_rel cx sty v sp.ptr_operand t /\
   expr_val_at ce cx sty a sa ee v sp.ptr_operand t /\
   expr_val_own ce cx sty a sa ee v sp.ptr_operand t` by
    (irule assign_source_value_target >>
     fs[expr_post_def, vv_post_def] >> metis_tac[]) >>
  simp[] >> metis_tac[not_fresh_at_mono]
QED

Theorem assign_return_buf_frame_target:
  return_buf_frame d ce a s0 /\
  vv_post ctx func ce cx e es a sv s0 es1 tv vv s /\
  target_post ctx func ce cx es1 sv sa s ee pv vt r t /\
  a.cs_next_var <= sv.cs_next_var /\
  sv.cs_next_var <= sa.cs_next_var /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  s.vs_alloca_next <= t.vs_alloca_next ==>
  return_buf_frame d ce sa t
Proof
  strip_tac >>
  `return_buf_frame d ce sv s` by
    (irule return_buf_frame_frame >>
     fs[vv_post_def] >> metis_tac[]) >>
  irule return_buf_frame_frame >> fs[target_post_def] >> metis_tac[]
QED
