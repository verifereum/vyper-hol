(* Private endpoint transports for local-array For callbacks. No run is selected. *)
Theory bodyFullForArrayLocalRecovery
Ancestors
  stmtSimForArrayFrame
  bodyFullShared stmtSimProps vyperEvalPreservesScopes
  vyperInterpreter vyperState compileEnv bodyPtrDefs
  vyperStorageTrace vyperStorageBackend vyperStorageFootprint loweringPosts
  list finite_map

Theorem for_array_local_snapshot_after_pop:
  supported_stmts tops bindings stmts /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty stmts = SOME env' /\
  iterator_unmodified (Array (Name aty name)) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  es.scopes = tmp :: outer /\
  finally (try (ignore_bind (eval_stmts cx stmts) (return F))
    handle_loop_exception) pop_scope es = (res,ee) /\
  lookup_scopes name outer = SOME snapshot ==>
  lookup_scopes name ee.scopes = SOME snapshot
Proof
  strip_tac >>
  `?raw. finally (eval_stmts cx stmts) pop_scope es = (raw,ee)` by
    (qpat_x_assum `finally _ _ _ = _` mp_tac >>
     Cases_on `eval_stmts cx stmts es` >> rename1 `_ = (outcome,after)` >>
     Cases_on `outcome`
     >- (simp[finally_def, try_def, ignore_bind_def, bind_def, return_def] >>
         Cases_on `pop_scope after` >> simp[ignore_bind_def, bind_def, return_def] >>
         Cases_on `q` >> simp[]) >>
     rename1 `INR exc` >> Cases_on `exc` >>
     simp[finally_def, try_def, ignore_bind_def, bind_def, return_def,
          raise_def, handle_loop_exception_def] >>
     Cases_on `pop_scope after` >> simp[ignore_bind_def, bind_def, return_def, raise_def] >>
     Cases_on `q` >> simp[]) >>
  drule_all array_body_pop_snapshot >> simp[]
QED

Theorem for_array_local_reserved_slot_recovery:
  not_fresh_at sb0 p /\ ptr_covers G0 tn0 p s0 sz /\
  lookup_var p s0 = SOME w /\
  FLOOKUP s0.vs_allocas aid = SOME region /\
  (!x v. not_fresh_at sb0 x /\ lookup_var x s0 = SOME v ==>
    lookup_var x t = SOME v) /\
  (!x. not_fresh_at sb0 x ==>
    FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  (!a b. FLOOKUP s0.vs_allocas a = SOME b ==>
    FLOOKUP t.vs_allocas a = SOME b) ==>
  ptr_covers G tn p t sz /\ lookup_var p t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME region
Proof
  strip_tac >>
  `lookup_var p t = SOME w` by metis_tac[] >>
  `FLOOKUP G p = FLOOKUP G0 p /\
   op_taint tn (Var p) = op_taint tn0 (Var p)` by metis_tac[] >>
  gvs[ptr_covers_def] >> metis_tac[]
QED

(* This is the normal post of the full callback, projected through its actual
   scope pop. The target endpoint, ghost pair and arbitrary lower frontier
   are unchanged; the conditional allocation obligation is not discarded. *)
Theorem for_array_local_callback_pop_full:
  (mid.gas_obs = [] /\ ?c3.
    stmt_lands lctx sb1 res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb1 /\ c3 = bc_out) /\
    cenv_top_ext bc c3 mid.scopes /\
    stmt_state_rel H ctx func c3 cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    return_buf_frame d c3 sb1 t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    sstart.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d c3 cx mid G tn t /\
    (!x w. not_fresh_at sb0 x /\ lookup_var x sstart = SOME w ==>
      lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP sstart.vs_allocas aid = SOME b ==>
      FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sb0 x ==>
      FLOOKUP G x = FLOOKUP Gstart x /\
      op_taint tn (Var x) = op_taint tnstart (Var x))) /\
  cenv_top_ext cenv bc ei.scopes /\
  eval_stmts cx stmts ei = (res,mid) /\
  mid.scopes = sc :: rest /\
  (!name. name IN FDOM sc ==> lookup_scopes name rest = NONE) ==>
  (mid with scopes := TL mid.scopes).gas_obs = [] /\
  stmt_lands lctx sb1 res t /\ ~t.vs_halted /\
  (res = INL () ==> ~block_is_terminated sb1) /\
  stmt_state_rel H ctx func cenv cx (mid with scopes := TL mid.scopes) t /\
  storage_well_formed_on cx (mid with scopes := TL mid.scopes) (FST H) /\
  return_buf_frame d cenv sb1 t /\ alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  sstart.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at (DF H) lo d cenv cx (mid with scopes := TL mid.scopes) G tn t /\
  (!x w. not_fresh_at sb0 x /\ lookup_var x sstart = SOME w ==>
    lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP sstart.vs_allocas aid = SOME b ==>
    FLOOKUP t.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sb0 x ==>
    FLOOKUP G x = FLOOKUP Gstart x /\
    op_taint tn (Var x) = op_taint tnstart (Var x))
Proof
  strip_tac >>
  `cenv_top_ext cenv c3 mid.scopes` by
    (drule eval_stmts_preserves_scopes_dom >>
     simp[preserves_scopes_dom_def] >> strip_tac >>
     irule cenv_top_ext_trans >> qexistsl_tac [`bc`,`ei.scopes`] >> gvs[]) >>
  `stmt_state_rel H ctx func cenv cx (mid with scopes := rest) t` by
    metis_tac[stmt_state_rel_pop_top_ext] >>
  `ghost_inv_at (DF H) lo d cenv cx (mid with scopes := rest) G tn t` by
    metis_tac[ghost_inv_at_pop] >>
  `storage_well_formed_on cx (mid with scopes := rest) (FST H)` by
    fs[storage_well_formed_on_def, get_storage_scopes] >>
  `c3.ce_return_buf = cenv.ce_return_buf` by
    fs[cenv_top_ext_def, compile_env_component_equality] >>
  `return_buf_frame d cenv sb1 t` by
    (qpat_x_assum `return_buf_frame _ _ _ _` mp_tac >>
     Cases_on `d` >> simp[return_buf_frame_def] >>
     rename1 `SOME dd` >> PairCases_on `dd` >> simp[return_buf_frame_def]) >>
  simp[]
QED
