Theory bodyPtrSubscriptSeamArrayMemoryAfterIndex
Ancestors
  bodyPtrSubscriptSeamArrayMemoryRepresented
  bodyPtrSubscriptSeamArrayMemoryFrame bodyPtrSubscriptSeamArrayMemoryPrepare
  exprSimSubscriptArrayCompose bodyPtrEnvBuiltinsGhostCompose
  bodyPtrEnvBuiltinsEntryFrame vyperState exprSimSubscriptArraySource
  exprSimSource vyperEvalExprPreservesScopesDom

Theorem marked_index_source_frame:
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx idx) (read_result cx))
    (mid with gas_obs := [],u,Gb,tnb) marks (INL iv) raw Gi tni (OK q) /\
  (!t r t'. eval_expr cx idx t = (INL r,t') ==>
    t'.scopes = t.scopes /\ t'.immutables = t.immutables) ==>
  ?ir t. eval_expr cx idx
      (mid with gas_obs := gas_explicit marks u.vs_gas_readings) = (INL ir,t) /\
    read_result cx ir t = (INL iv,t) /\
    (raw with gas_obs := []).scopes = mid.scopes /\
    (raw with gas_obs := []).immutables = mid.immutables
Proof
  strip_tac >>
  `bind (eval_expr cx idx) (read_result cx)
     (mid with gas_obs := gas_explicit marks u.vs_gas_readings) =
     (INL iv,raw with gas_obs := [])` by
    (gvs[gasSummaryComposePtrTheory.gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  gvs[bind_def, AllCaseEqs()] >>
  drule read_result_state >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem marked_array_base_source_view:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  gas_marked_exec_ptr D (ctx,func) PG (eval_expr cx obj)
    (es,s0,G0,tn0) marks (INL r) mid Gb tnb (OK u) ==>
  eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL r,mid with gas_obs := []) /\
  expr_body_pre cenv cx env idx (mid with gas_obs := []) /\
  expr_sim_inv cenv cx env (mid with gas_obs := []) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL r,mid with gas_obs := [])` by
    (gvs[gasSummaryComposePtrTheory.gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env (Subscript ann obj idx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  `expr_body_pre cenv cx env obj
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[expr_body_pre_array_subscript_base] >>
  drule_all expr_body_pre_array_subscript_index_after_base >> strip_tac >>
  drule_all exprSimSourceTheory.expr_body_pre_eval_result >> strip_tac >>
  drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
  simp[]
QED

Theorem vv_post_ghost_kept_compose:
  vv_post ctx func cenv cx obj es sa sb s0 mid r vv u /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ ci_mono sa sb /\
  ghost_kept cenv es sa G0 tn0 s0 Gb tnb /\
  ghost_kept cenv mid sb Gb tnb u Gi tni ==>
  ghost_kept cenv es sa G0 tn0 s0 Gi tni
Proof
  strip_tac >> irule ghost_kept_locals_trans >>
  goal_assum (drule_at Any) >>
  conj_tac
  >- (qexists_tac `func` >>
      gvs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
  qexistsl_tac [`Gb`,`mid`,`u`,`sb`,`tnb`] >>
  gvs[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.ci_mono_def,
      loweringPostsTheory.wb_frame_def,
      exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem marked_array_index_post_view:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  expr_body_pre cenv cx env idx (mid with gas_obs := []) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx idx) (read_result cx))
    (mid with gas_obs := [],u,Gb,tnb) marks (INL iv) raw Gi tni (OK q) /\
  expr_post ctx func cenv cx idx (mid with gas_obs := []) sb sc u
    (raw with gas_obs := []) iv iop q ==>
  ?i iw. iv = IntV i /\ eval_operand iop q = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw))
Proof
  strip_tac >>
  `bind (eval_expr cx idx) (read_result cx)
     (mid with gas_obs := gas_explicit marks u.vs_gas_readings) =
     (INL iv,raw with gas_obs := [])` by
    (gvs[gasSummaryComposePtrTheory.gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env idx
     (mid with gas_obs := gas_explicit marks u.vs_gas_readings)` by
    metis_tac[expr_body_pre_gas_obs] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[bind_def, AllCaseEqs()] >> strip_tac >>
  drule read_result_state >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env idx
     (mid with gas_obs := gas_explicit marks u.vs_gas_readings)` by
    simp[expr_body_pre_gas_obs] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `value_has_type tvt iv` by metis_tac[] >>
  metis_tac[exprSimSubscriptArraySuffixTheory.framed_array_index_post_view]
QED

Theorem fixed_array_after_index_summary_ptr:
  expr_body_pre cenv cx env (Subscript et obj idx) es /\
  expr_type obj = ArrayT et (Fixed n) /\ post_value_type cenv obj = expr_type obj /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (eval_expr cx obj)
    (es,s0,G0,tn0) bmarks (INL r) mid Gb tnb (OK u) /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (bind (eval_expr cx idx) (read_result cx))
    (mid with gas_obs := [],u,Gb,tnb) imarks (INL iv) raw Gi tni (OK q) /\
  vv_post ctx func cenv cx obj es sa sb s0 (mid with gas_obs := []) r
    (LocatedValue (ArrayT et (Fixed n)) p) u /\
  ptr_vv_ok cx (ArrayT et (Fixed n)) r (LocatedValue (ArrayT et (Fixed n)) p)
    (mid with gas_obs := []) Gb tnb u /\
  ptr_buf_ok cenv obj p.ptr_operand Gb u /\
  ghost_kept cenv es sa G0 tn0 s0 Gb tnb /\
  expr_post ctx func cenv cx idx (mid with gas_obs := []) sb sc u
    (raw with gas_obs := []) iv iop q /\
  ghost_inv d cenv cx (raw with gas_obs := []) Gi tni q /\
  ptr_val_ok cx (expr_type idx) iv iop Gi tni q /\
  ghost_kept cenv (mid with gas_obs := []) sb Gb tnb u Gi tni /\
  (!t ir t'. eval_expr cx idx t = (INL ir,t') ==>
    t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
  (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
  (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
  p.ptr_location = LocMemory /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\ (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  compile_array_subscript p.ptr_operand iop F n ws (elem_size_in_location cenv LocMemory et)
    (is_signed_type (expr_type idx)) loader sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~ctx_has_dalloca ctx /\ ~q.vs_halted /\
  q.vs_current_bb = sc.cs_current_bb /\ q.vs_inst_idx = LENGTH sc.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\ local_ptrs_reserved cenv sc /\
  ci_mono sa sb /\ ci_mono sb sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (select_result cx (ArrayT et (Fixed n)) r (ValueSubscript iv))
    (raw with gas_obs := [],q,Gi,tni)
    (\res ee' H tm z. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst LocMemory)) z /\
      z.vs_current_bb = sd.cs_current_bb /\ z.vs_inst_idx = LENGTH sd.cs_current_insts /\
      ghost_inv d cenv cx ee' H tm z /\
      ptr_vv_ok cx et child (LocatedValue et (mk_ptr dst LocMemory)) ee' H tm z /\
      ptr_buf_ok cenv (Subscript et obj idx) dst H z /\
      ghost_kept cenv es sa G0 tn0 s0 H tm)
    (\res ee' gt outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all marked_array_base_source_view >> strip_tac >>
  drule_all marked_index_source_frame >> strip_tac >>
  `!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)` by metis_tac[] >>
  drule_all marked_array_index_post_view >> strip_tac >>
  `is_word_type (expr_type idx)` by
    (drule_all bodyPtrSubscriptSeamArrayMemoryTypingTheory.array_subscript_index_type >>
     strip_tac >> Cases_on `expr_type idx` >>
     gvs[vyperTypeSystemTheory.is_int_type_def] >>
     Cases_on `b` >> gvs[vyperTypeSystemTheory.is_int_type_def, compileEnvTheory.is_word_type_def]) >>
  suspend "frame"
QED

Resume fixed_array_after_index_summary_ptr[frame]:
  `vv_post ctx func cenv cx (Subscript (ArrayT et (Fixed n)) obj idx) es sa sc s0
     (raw with gas_obs := []) r (LocatedValue (ArrayT et (Fixed n)) p) q` by
    (irule exprSimSubscriptArrayEndpointTheory.framed_array_base_endpoint >>
     simp[] >>
     conj_tac >- gvs[loweringPostsTheory.expr_post_def] >>
     qexistsl_tac [`env`,`iop`,`iv`,`sb`,`sc`,`mid with gas_obs := []`,`u`,`q`] >>
     gvs[exprLoweringPropsTheory.ci_mono_def]) >>
  suspend "ptr_frame"
QED

Resume fixed_array_after_index_summary_ptr[ptr_frame]:
  `expr_body_pre cenv cx env obj
     (es with gas_obs := gas_explicit bmarks s0.vs_gas_readings)` by
    (simp[expr_body_pre_gas_obs] >>
     metis_tac[expr_body_pre_array_subscript_base]) >>
  `?etv. evaluate_type (get_tenv cx) et = SOME etv /\
     evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
     ?w. eval_operand p.ptr_operand u = SOME w` by
    (`IS_SOME (evaluate_type (get_tenv cx) (expr_type obj))` by
       metis_tac[exprSimHypsTheory.expr_body_pre_type_evaluates] >>
     `?etv. evaluate_type (get_tenv cx) et = SOME etv /\
        evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n))` by
       (qpat_x_assum `IS_SOME _` mp_tac >>
        qpat_x_assum `expr_type obj = _` mp_tac >>
        rpt (pop_assum kall_tac) >> rpt strip_tac >>
        Cases_on `evaluate_type (get_tenv cx) et` >>
        gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
     qexists_tac `etv` >> simp[] >>
     qpat_x_assum `vv_post _ _ _ _ _ _ sa sb _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def] >>
     metis_tac[]) >>
  `vv_at cenv cx (ArrayT et (Fixed n)) sa sb (mid with gas_obs := []) r
     (LocatedValue (ArrayT et (Fixed n)) p) u` by
    gvs[loweringPostsTheory.vv_post_def] >>
  `dynarray_free (ArrayTV etv (Fixed n))` by
    metis_tac[exprSimPropsTheory.dynarray_free_fixed] >>
  `(raw with gas_obs := []).scopes = (mid with gas_obs := []).scopes /\
   (raw with gas_obs := []).immutables = (mid with gas_obs := []).immutables` by simp[] >>
  drule_all captured_memory_ptr_index_frame >> strip_tac >>
  `ghost_kept cenv es sa G0 tn0 s0 Gi tni` by
    (irule vv_post_ghost_kept_compose >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  suspend "represented"
QED

Resume fixed_array_after_index_summary_ptr[represented]:
  `ci_mono sa sc` by
    (gvs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[compileEnvTheory.cs_extends_trans, arithmeticTheory.LE_TRANS]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, exprLoweringPropsTheory.ci_mono_def] >>
  `op_taint tni iop = {}` by gvs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  qpat_x_assum `iv = IntV i` SUBST_ALL_TAC >>
  irule (fixed_array_represented_summary_ptr
    |> Q.INST [`es` |-> `es with gas_obs := obs`]
    |> PURE_REWRITE_RULE [exprSimPropsTheory.vv_post_initial_gas,
              ghost_kept_entry_gas_obs, expr_body_pre_gas_obs]) >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`gas_explicit bmarks s0.vs_gas_readings`,`mid with gas_obs := []`] >> simp[]) >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`iop`,`iw`,`loader`,`p`,`sc`,`ws`] >> simp[]
QED
Finalise fixed_array_after_index_summary_ptr
