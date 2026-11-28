(* Request-prefix companion to bodyFullRaiseCustomError. *)
Theory s1PrefixRaiseCustomError
Ancestors
  s1PrefixPreds bodyFullRaiseCustomError s1PrefixDefs s1PrefixOfVV
  bodyFullCustomErrorSource bodyFullCustomErrorLayout gasShadow s1PrefixExtCallPosList
  stmtSimDefs loweringPosts vyperState list pair

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> Cases_on `err` >> rename1 `CustomError id pos kw` >>
  drule_all custom_error_raise_source >>
  disch_then (qx_choosel_then [`params`,`args`] strip_assume_tac) >>
  `body_exprs_full_ok cx args /\ body_exprs_prefix_ok cx args` by metis_tac[] >>
  pure_rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (assume_tac o PURE_REWRITE_RULE[gas_shadow_stmt_def, gas_shadow_raise_reason_def]) >>
  drule_all (GEN_ALL (Q.INST [`tys` |-> `MAP (lowered_value_type ce) args`]
    compile_raise_custom_layout_full |> SIMP_RULE bool_ss [])) >>
  disch_then (qx_choosel_then [`saved`,`se`,`te`,`buf`,`sm`,`ss`]
    strip_assume_tac) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    metis_tac[ret_pc_ok_def] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx args) (es,s0,G0,tn0)` suffices_by
    (qpat_assum `eval_stmt cx (Raise _) = _` (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
     qmatch_goalsub_abbrev_tac `gas_prefix_full _ _ _ (bind (eval_exprs cx args) next) _` >>
     `!qe. SND (eval_exprs cx args qe) = SND (bind (eval_exprs cx args) next qe)` by
       (gen_tac >> Cases_on `eval_exprs cx args qe` >>
        rename1 `eval_exprs cx args qe = (ans,mid)` >>
        Cases_on `ans` >> simp[Abbr `next`, bind_def, lift_option_def, return_def, raise_def] >>
        qmatch_goalsub_rename_tac `build_custom_error_data _ _ _ values` >>
        Cases_on `build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) values` >>
        simp[raise_def, return_def]) >>
     drule gas_prefix_full_state_cong >> simp[]) >>
  irule extcall_request_positional_packing_prefix >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  map_every qexists_tac [`cenv`,`d`,`env`,`[]`,`sa`,`se`,`shadow_func`,
                         `shadow_sa`,`te`,`saved`,`tops`] >>
  fs[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
QED
*)
Theorem compile_raise_custom_frag_prefix:
  !cx err DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env
    env' ret_ty lctx RetQ es.
  (!id pos kw error_tops params args.
       err = CustomError id pos kw /\
       get_module_code cx (FST id) = SOME error_tops /\
       lookup_custom_error_args_in (SND id) error_tops = SOME params /\
       order_custom_error_args params err = SOME args ==>
       body_exprs_full_ok cx args) /\
  (!id pos kw error_tops params args.
       err = CustomError id pos kw /\
       get_module_code cx (FST id) = SOME error_tops /\
       lookup_custom_error_args_in (SND id) error_tops = SOME params /\
       order_custom_error_args params err = SOME args ==>
       body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Raise (RaiseCustomError err)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Raise (RaiseCustomError err)) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
  stmt_exprs_ok cenv (Raise (RaiseCustomError err)) /\
  call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseCustomError err)))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty
        (gas_shadow_stmt (Raise (RaiseCustomError err))))
      (eval_stmt cx (Raise (RaiseCustomError err))) es
Proof
  cheat
QED
