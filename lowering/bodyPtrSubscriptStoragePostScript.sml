(* Ordinary typed storage reads at the same explicit endpoint as the ptr path. *)
Theory bodyPtrSubscriptStoragePost
Ancestors
  bodyPtrSubscriptStorageLoad exprSimUnwrap exprSimUnwrapProps
  exprLoweringProps loweringPosts exprSimProps emitHelper compileEnv
  venomState venomInst finite_map

Theorem storage_load_unwrap_ordinary_post:
  emit_op (if tr then TLOAD else SLOAD) [p.ptr_operand] sm = (Var out,sb) /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
  is_word_type t /\ p.ptr_location = (if tr then LocTransient else LocStorage) /\
  eval_operand p.ptr_operand s = SOME (w:bytes32) /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sm /\
  sf = (update_var out (if tr then tload w s else sload w s) s with
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
  `t = expr_type e /\ storage_holds cx tr t (Value v) w ee s` by
    (Cases_on `tr` >> gvs[vv_post_def, vv_holds_def]) >>
  `!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
     (if tr then tload w s else sload w s) = typed_val_to_w256 tvt v` by
    (rpt strip_tac >> irule storage_holds_load >> simp[] >> metis_tac[]) >>
  `is_word_type (expr_type e)` by metis_tac[] >>
  irule expr_post_of_vv_post_load >>
  simp[] >> conj_tac
  >- simp[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >> gvs[update_var_def] >> metis_tac[]
QED
