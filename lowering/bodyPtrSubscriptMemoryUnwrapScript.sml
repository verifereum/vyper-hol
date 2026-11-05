(* Constructive word unwrap: ordinary and pointer posts share one load. *)
Theory bodyPtrSubscriptMemoryUnwrap
Ancestors
  bodyPtrSubscriptWordMemory bodyPtrSubscriptReadFrame bodyPtrSubscriptScalarLoad
  exprSimUnwrapProps exprLoweringProps bodyPtrDefs loweringPosts
  gasSummaryComposePtr fragGasPathPtr exprSimProps
  emitHelper compileEnv venomState venomInst valueEncodingProps finite_map
  vyperInterpreter vyperState exprSimMemorySource

Theorem mload_unwrap_ordinary_post:
  emit_op MLOAD [p.ptr_operand] sm = (Var out,sb) /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
  is_word_type (expr_type e) /\ sa.cs_next_var <= sm.cs_next_var /\
  local_ptrs_reserved cenv sm /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  mload (w2n (a:bytes32)) s = typed_val_to_w256 ty v /\
  sf = (update_var out (mload (w2n (a:bytes32)) s) s with
          vs_inst_idx := SUC s.vs_inst_idx) /\
  (!x. not_fresh_at sm x ==> lookup_var x sf = lookup_var x s) ==>
  expr_post ctx func cenv cx e es sa sb s0 ee v (Var out) sf
Proof
  strip_tac >>
  `not_local_ptr cenv ee.scopes out` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >>
     irule local_ptrs_reserved_fresh >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `stmt_state_rel ctx func cenv cx ee sf` by
    (simp[stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> gvs[vv_post_def]) >>
  irule expr_post_of_vv_post_load >>
  simp[] >> conj_tac
  >- simp[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >> gvs[update_var_def] >> metis_tac[]
QED

Theorem unwrap_memory_word_marked_ptr:
  emit_op MLOAD [p.ptr_operand] sm = (op,sb) /\
  p.ptr_location = LocMemory /\ is_word_type (expr_type e) /\
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
  strip_tac >> drule_all located_word_memory_prepare >> strip_tac >>
  `?out. op = Var out` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def] >> metis_tac[]) >>
  gvs[] >> drule_all emit_mload_counted_scalar >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `expr_post ctx func cenv cx e es sa sb s0 ee v (Var out) sf` by
    (irule mload_unwrap_ordinary_post >> simp[] >>
     qexistsl_tac [`w`, `p`, `s`, `sm`, `t`] >>
     drule vv_post_read_result >> disch_then (fn th => rewrite_tac[GSYM th]) >>
     simp[] >> metis_tac[]) >>
  `ghost_inv d cenv cx (ee with gas_obs := []) Gf tnf sf /\
   ghost_kept cenv es sa G0 tn0 s0 Gf tnf` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] mload_read_suffix_frame) >>
     qexistsl_tac [`G`, `w`, `out`, `s`, `sm`, `src`, `tn`] >> simp[]) >>
  `(ee with gas_obs := []) = ee` by
    simp[evaluation_state_component_equality] >>
  qexistsl_tac [`sf`, `Gf`, `tnf`] >>
  simp[ptr_val_ok_def] >>
  simp[gas_marked_exec_ptr_def] >> metis_tac[read_result_gas_obs]
QED

Theorem unwrap_memory_word_prefix_ptr:
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG source
    (ei,si,Gi,tni) left (INL tv) ee G tn (OK s) /\
  emit_op MLOAD [p.ptr_operand] sm = (op,sb) /\
  p.ptr_location = LocMemory /\ is_word_type (expr_type e) /\
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
  strip_tac >> drule_all unwrap_memory_word_marked_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`u`, `Gf`, `tnf`] >> simp[] >>
  `(ee with gas_obs := []) = ee` by
    simp[evaluation_state_component_equality] >>
  metis_tac[gas_marked_exec_ptr_bind_normal, listTheory.APPEND_NIL]
QED
