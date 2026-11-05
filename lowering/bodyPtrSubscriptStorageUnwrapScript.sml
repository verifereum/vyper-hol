(* Storage word suffixes construct ordinary and ghost posts on one path. *)
Theory bodyPtrSubscriptStorageUnwrap
Ancestors
  bodyPtrSubscriptStoragePost bodyPtrSubscriptWordStorage bodyPtrSubscriptReadFrame
  bodyPtrSubscriptStorageLoad bodyPtrSubscriptNamedScalar exprSimUnwrapProps exprLoweringProps bodyPtrDefs
  loweringPosts gasSummaryComposePtr fragGasPathPtr exprSimProps
  emitHelper compileEnv venomState venomInst valueEncodingProps finite_map
  vyperInterpreter vyperState exprSimMemorySource

Theorem located_word_storage_prepare[local]:
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty ==>
  ?w:bytes32. eval_operand p.ptr_operand s = SOME w /\
    t = expr_type e /\ op_taint tn p.ptr_operand = {} /\
    key_taint (if tr then tn.t_trans else tn.t_stor) w = {}
Proof
  strip_tac >>
  `?w. eval_operand p.ptr_operand s = SOME w /\ t = expr_type e` by
    gvs[vv_post_def, vv_holds_def] >>
  qexists_tac `w` >> simp[] >> conj_tac
  >- gvs[ptr_vv_ok_def] >>
  `key_taint (if p.ptr_location = LocTransient then tn.t_trans else tn.t_stor) w = {}` by
    (irule located_word_key_taint_empty >> simp[] >>
     metis_tac[]) >>
  Cases_on `tr` >> gvs[]
QED

Theorem unwrap_storage_word_marked_ptr:
  emit_op (if tr then TLOAD else SLOAD) [p.ptr_operand] sm = (op,sb) /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  is_word_type (expr_type e) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s /\
  read_result cx tv ee = (INL v,ee) /\ ee.gas_obs = [] /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\ value_has_type ty v /\
  ghost_inv d cenv cx ee G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  fn_has_code sm sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u Gf tnf.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee Gf tnf (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee Gf tnf u /\
    ptr_val_ok cx (expr_type e) v op Gf tnf u /\
    ghost_kept cenv es sa G0 tn0 s0 Gf tnf /\ op_prov Gf op = NONE
Proof
  strip_tac >> drule_all located_word_storage_prepare >> strip_tac >>
  `?out. op = Var out` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def] >> metis_tac[]) >>
  gvs[] >> drule_all emit_storage_load_counted_scalar >>
  disch_then (qspecl_then [`PG`, `G`, `cx_dead cx`] strip_assume_tac) >>
  `expr_post ctx func cenv cx e es sa sb s0 ee v (Var out) sf` by
    (irule storage_load_unwrap_ordinary_post >> simp[] >>
     qexistsl_tac [`p`, `s`, `sm`, `expr_type e`, `tr`, `w`] >>
     drule vv_post_read_result >> disch_then (fn th => rewrite_tac[GSYM th]) >>
     simp[] >> metis_tac[]) >>
  `ghost_inv d cenv cx (ee with gas_obs := []) Gf tnf sf` by
    (irule (cj 1 named_read_ghost_frame) >> simp[] >> metis_tac[]) >>
  `ghost_kept cenv es sa G0 tn0 s0 Gf tnf` by
    (irule ghost_kept_read_suffix >> simp[] >> metis_tac[]) >>
  `(ee with gas_obs := []) = ee` by
    simp[evaluation_state_component_equality] >>
  qexistsl_tac [`sf`, `Gf`, `tnf`] >>
  simp[ptr_val_ok_def] >>
  simp[gas_marked_exec_ptr_def] >> metis_tac[read_result_gas_obs]
QED

Theorem unwrap_storage_word_prefix_ptr:
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG source
    (ei,si,Gi,tni) left (INL tv) ee G tn (OK s) /\
  emit_op (if tr then TLOAD else SLOAD) [p.ptr_operand] sm = (op,sb) /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  is_word_type (expr_type e) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s /\
  read_result cx tv ee = (INL v,ee) /\ ee.gas_obs = [] /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\ value_has_type ty v /\
  ghost_inv d cenv cx ee G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  fn_has_code sm sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u Gf tnf.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
      (vyperState$bind source (read_result cx)) (ei,si,Gi,tni) left
      (INL v) ee Gf tnf (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee Gf tnf u /\
    ptr_val_ok cx (expr_type e) v op Gf tnf u /\
    ghost_kept cenv es sa G0 tn0 s0 Gf tnf /\ op_prov Gf op = NONE
Proof
  strip_tac >> drule_all unwrap_storage_word_marked_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`u`, `Gf`, `tnf`] >> simp[] >>
  `(ee with gas_obs := []) = ee` by
    simp[evaluation_state_component_equality] >>
  metis_tac[gas_marked_exec_ptr_bind_normal, listTheory.APPEND_NIL]
QED
