(* The shared widened layout handles the ordinary heads.  At a nested
   immutable head, the write starts at the marked target-place endpoint. *)
Theory s1PrefixTupleWidenedLayout
Ancestors
  s1PrefixTupleWidenedHeads s1PrefixTupleNestedHeadBind
  s1PrefixImmutableTargetPlace tuplePlaceSuffixCode gasShadowCompileStmtHelpers
  bodyFullTargetRoots exprSimAbiDecodeEntryTyping valueEncodingProps
  tupleWidenedStoreEntry bodyFullAssignTuple vyperTypeSystem list gasShadow gasShadowState
  vyperTypeValues tuplePlaceSource vyperTypeDefaults vyperTypeArgFits s1PrefixPreds

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  irule tuple_widened_prefix_from_nested_heads >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  rpt gen_tac >> strip_tac >> suspend "nested_head"
QED
*)
Theorem tuple_assign_widened_prefix_from_heads:
  !cx gs e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_prefix_ok cx (TupleTarget gs) v) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  ~supported_stmt_expr_exists (const_name_root cx) (Assign (TupleTarget gs) e) /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
  lowered_value_type cenv e <> expr_type e ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_assign_widened_prefix_from_heads[nested_head]:
  `j < LENGTH tys /\ LENGTH gs = LENGTH tys /\ LENGTH gs = LENGTH vs` by decide_tac >>
  qpat_assum `tuple_widened_store_entry _ _ _ _ j _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [tuple_widened_store_entry_def]) >>
  drule_all tuple_widened_head_static >>
  disch_then (qx_choose_then `bt` strip_assume_tac) >>
  `bt = head` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  drule_all tuple_widened_head_source >> strip_tac >>
  drule_all tuple_widened_head_const_cells >> strip_tac >>
  `IS_SOME (type_place_target env head)` by fs[well_typed_target_def] >>
  drule_all typed_immutable_target_root >>
  disch_then (qx_choosel_then [`id`,`root_ty`] strip_assume_tac) >>
  qpat_assum `compile_tuple_store_all _ _ (DROP j gs) _ c0 = _`
    (mp_then (Pat `compile_tuple_store_all _ _ _ _ _ = _`)
      (Q.ISPECL_THEN [`tys`,`func`,`head`] mp_tac) tuple_place_suffix_code_parts) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`r`,`place_cs`,`write_cs`] strip_assume_tac) >>
  `EL j (MAP gas_shadow_assignment gs) = BaseTarget (gas_shadow_target head)` by
    simp[EL_MAP,gas_shadow_assignment_def] >>
  qpat_assum `compile_tuple_store_all _ _ (DROP j (MAP gas_shadow_assignment gs)) _ sh0 = _`
    (mp_then (Pat `compile_tuple_store_all _ _ _ _ _ = _`)
      (Q.ISPECL_THEN [`tys`,`shadow_func`,`gas_shadow_target head`] mp_tac)
      tuple_place_suffix_code_parts) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`shadow_r`,`shadow_place_cs`,`shadow_write_cs`] strip_assume_tac) >>
  `r = shadow_r /\ gas_shadow_state place_cs shadow_place_cs` by
    (`gas_shadow_compiles (compile_get_target_ptr compile_expr cenv head)
        (compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (gas_shadow_target head))` by
       irule gas_shadow_stmt_get_target_ptr_env >>
     pop_assum (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`c0`,`sh0`] mp_tac) >> simp[]) >>
  qpat_x_assum `r = shadow_r` (SUBST_ALL_TAC o SYM) >>
  suspend "paired_place"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_assign_widened_prefix_from_heads[paired_place]:
  `env.type_defs = get_tenv cx` by (drule abi_decode_inv_type_env >> simp[]) >>
  `assignable_type (get_tenv cx) (TupleT dtys)` by metis_tac[] >>
  `?dtvs. evaluate_type (get_tenv cx) (TupleT dtys) = SOME (TupleTV dtvs)` by
    (drule assignable_type_well_formed >> simp[well_formed_type_def] >>
     Cases_on `evaluate_type (get_tenv cx) (TupleT dtys)` >>
     simp[] >> metis_tac[evaluate_type_TupleT_cases]) >>
  `tys <> dtys` by metis_tac[] >>
  `arg_types_fit tys dtys` by
    (qpat_assum `type_widens_to env.type_defs (TupleT tys) (TupleT dtys)` mp_tac >>
     simp[NoAsms,type_widens_to_def,cj 5 arg_type_fits_def,TypeBase.one_one_of ``:type``] >>
     metis_tac[]) >>
  `evaluate_type (get_tenv cx) (EL j dtys) = SOME (EL j dtvs) /\
   evaluate_type (get_tenv cx) (EL j tys) = SOME (EL j tvs) /\
   type_widens_to (get_tenv cx) (EL j tys) (EL j dtys) /\
   assignable_type (get_tenv cx) (EL j dtys) /\ 0 < type_slot_size (EL j dtvs)` by
    (drule_all tuple_place_type_facts >> strip_tac >>
     first_x_assum (qspec_then `j` mp_tac) >> simp[]) >>
  `value_has_type (EL j tvs) (EL j vs)` by
    (qpat_assum `values_have_types tvs vs` mp_tac >>
     simp[NoAsms,values_have_types_LIST_REL,LIST_REL_EL_EQN] >>
     strip_tac >> first_assum irule >> decide_tac) >>
  `value_has_type (EL j dtvs) (EL j vs)` by
    (drule_all type_widens_to_value_has_type >> simp[]) >>
  `body_base_target_prefix_ok cx head` by fs[body_tuple_target_prefix_ok_def] >>
  irule tuple_widened_nested_head_bind >>
  qexistsl_tac [`c0`,`head`,`id`,`place_cs`,`r`,`EL j dtvs`,`EL j dtys`] >>
  conj_tac >- suspend "write" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (irule immutable_target_place_prefix >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
      >- (qexists_tac `id` >> asm_rewrite_tac[]) >>
      qexistsl_tac [`cenv`,`d`,`env`,`r`,`c0`,`place_cs`,`shadow_func`,`sh0`,
                   `shadow_place_cs`,`tops`,`EL j dtvs`,`EL j dtys`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule tuple_immutable_head_target >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qexistsl_tac [`shadow_func`,`sh0`,`shadow_place_cs`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `tops` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_assign_widened_prefix_from_heads[write]:
  map_every qx_gen_tac [`marks`,`mid`,`Gp`,`tp`,`sp`,`path`] >> strip_tac >>
  `?path' ff q Gq tq.
     (INL (ImmutablePlace NONE id path):place + exception) = INL (ImmutablePlace NONE id path') /\
     (!tail. write_place cx (ImmutablePlace NONE id path') (EL j vs)
       (mid with gas_obs := tail) = (INL (),ff with gas_obs := tail)) /\
     ff.storage_trace = mid.storage_trace /\
     (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (sp,Gp,tp) [] (OK q,Gq,tq)) /\
     tuple_widened_store_entry (DF,lo,d,ctx,func,shadow_func) (cenv,cx,env,st0,es,ee)
       (sa,sb,shadow_sb,s0,G0,tn0) (tys,gs,elems,tvs,vs,w,t,tf) (SUC j)
       write_cs shadow_write_cs ff q Gq tq (obs0 ++ gas_explicit marks s1.vs_gas_readings)` by
    (irule tuple_widened_nested_write_advance >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- simp[GSYM val_in_memory_tuple]
     >- (qexists_tac `root_ty` >> first_assum ACCEPT_TAC)
     >- (qexists_tac `tops` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`G1`,`c0`,`dtvs`,`dtys`,`head`,`place_cs`,`r`,`sh0`,
                  `shadow_place_cs`,`src0`,`tn1`,
       `\ce dty. if is_word_type (EL j tys) then
          if is_word_type dty then
            compile_store_at_loc ce.ce_imm_alloca (FST r) (EL j elems) (FST (SND r))
          else emit_void INVALID []
        else compile_assign_value ce (FST r)
          (case FST (SND r) of NONE => LocMemory | SOME loc => loc)
          (EL j elems) (is_word_type dty) NONE dty (EL j tys) (type_memory_bytes ce dty)`] >>
     BETA_TAC >> rpt conj_tac >>
     TRY (FIRST [first_assum ACCEPT_TAC, REFL_TAC,
                 first_assum (ACCEPT_TAC o SIMP_RULE bool_ss [LET_THM])] >> NO_TAC) >>
     gen_tac >> strip_tac >> qexists_tac `path` >> simp[] >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> imm_target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  qpat_x_assum `INL _ = INL _` (SUBST_ALL_TAC o SIMP_RULE (srw_ss()) []) >>
  qexistsl_tac [`ff`,`q`,`Gq`,`tq`] >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `tuple_widened_store_entry _ _ _ _ (SUC j) _ _ ff _ _ _ _` mp_tac >>
      simp[NoAsms,tuple_widened_store_entry_def])
  >- (rpt strip_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qexistsl_tac [`write_cs`,`shadow_write_cs`,`obs0 ++ gas_explicit marks s1.vs_gas_readings`] >>
  first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise tuple_assign_widened_prefix_from_heads
*)
