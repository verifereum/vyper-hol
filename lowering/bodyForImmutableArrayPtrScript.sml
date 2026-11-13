Theory bodyForImmutableArrayPtr
Ancestors bodyPtrPreds bodyPtrDefs bodySimDeclCases
  stmtSimForArray exprSimHypsDefs exprSimHyps bodySim bodyExprPreFacts
  vyperAST vyperInterpreter vyperState vyperValue vyperTyping
  vyperTypeSystem vyperTypeInvariants vyperTypeValues
  supportedStmts supportedStmtTraverse allocLimits compileVyper
  vyperTypeCallGraph exprLoweringProps finite_map list vyperTypeCallStackSoundness
  whitelistForIterImmSource whitelistForIterImmFrame
  bodyStorageMetadata exprSimTopLevelProps valueEncodingProps valueEncodingTyping
  vyperTypeEnv arithmetic valueEncoding stmtSimProps stmtLoweringMono loweringPosts
  forPtrArraySemantic exprSimWordArgs vyperBareGlobalName
  whitelistForIterImmCopy exprSimCopy vyperValueOperation compileEnv
  bodyImmEntryPtr whitelistForIterImmFrag forPtrArraySource
  gasSummaryComposePtr stmtLoweringProps stmtLowering
  localPtrsProps emitHelperProps context emitHelper venomInst
  fragExec loweringStateRelDefs stmtFragPtr gasContext whitelistForIterImmLoop
  ptrDiscipline stmtSimForArrayLoop forPtrArrayEntry
Libs monadsyntax

val _ = Parse.hide "body";

Theorem body_for_immutable_array_ptr:
  (!tenv s'' tyv t s3 vs t' s4 x t''.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
     eval_iterator cx (Array (TopLevelName (ArrayT typ bd) (src,name))) s3 = (INL vs,t') /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s4 = (INL x,t'') ==>
     body_for_ptr_ok cx tyv id body vs) /\
  (!tenv s'' tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) ==>
     body_iterator_ptr_ok cx (Array (TopLevelName (ArrayT typ bd) (src,name)))) ==>
  body_stmt_ptr_ok cx (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n body)
Proof
  strip_tac >> rewrite_tac[body_stmt_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env (TopLevelName (ArrayT typ bd) (src,name)) /\
   id NOTIN FDOM env.var_types /\
   iterator_unmodified (Array (TopLevelName (ArrayT typ bd) (src,name))) body /\
   ?env_b. type_stmts (extend_local env id typ F) ret_ty body = SOME env_b` by
    gvs[type_stmt_def, well_typed_iterator_def, expr_type_def,
        optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   IS_SOME (supported_immutable_type tops (src,name)) /\ bound_length bd <= n` by
    fs[body_inv_def, supported_stmt_def, supported_iterator_def] >>
  `?t. supported_immutable_type tops (src,name) = SOME t` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  drule_all supported_immutable_type_find_NONE >> strip_tac >> gvs[] >>
  `FLOOKUP env.bare_globals (NONE,name) = SOME (ArrayT typ bd)` by
    (irule toplevel_find_NONE_bare_global >> fs[expr_sim_inv_def] >> metis_tac[]) >>
  drule_all immutable_array_source_ready >> strip_tac >>
  drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _` drule >>
     simp[FLOOKUP_DEF]) >>
  qmatch_asmsub_abbrev_tac `INL (MAP Value vs)` >>
  `LENGTH vs <= bound_length bd /\ bound_length bd < dimword (:256) /\
   (case bd of Fixed cap => LENGTH vs = cap | Dynamic cap => T)` by
    suspend "bounds" >>
  `LENGTH vs <= n` by decide_tac >>
  `eval_iterator cx (Array (TopLevelName (ArrayT typ bd) (cenv.ce_module,name)))
      es = (INL (MAP Value vs),es)` by
    (`es with gas_obs := es.gas_obs = es` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     qpat_x_assum `!gs. eval_iterator _ _ _ = (INL (MAP Value vs),_)`
       (qspec_then `es.gas_obs` mp_tac) >> asm_rewrite_tac[]) >>
  `body_for_ptr_ok cx tv id body (MAP Value vs)` by
    (qpat_x_assum `!s3 vs t' s4 t''. _` mp_tac >>
     simp[lift_option_type_def, return_def, check_def, assert_def, compatible_bound_def] >>
     disch_then irule >> simp[] >> qexistsl_tac [`es`, `es`] >> gvs[]) >>
  suspend "static"
QED

Resume body_for_immutable_array_ptr[static]:
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `supported_stmts tops bindings body /\
   ~supported_stmts_expr_exists expr_internal_call_root body` by
    fs[supported_stmt_def, supported_iterator_def] >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       alloc_limits_stmt_def, stmt_valued_return_def] >>
  `type_memory_bytes cenv typ = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `elem_size_in_location cenv LocCode typ = type_memory_size tv` by
    simp[elem_size_in_location_def, is_slot_addressed_def] >>
  `0 < type_memory_size tv` by metis_tac[immutable_array_element_size_positive] >>
  `type_memory_bytes cenv typ + 64 < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  `!k. k < LENGTH vs ==> value_has_type tv (EL k vs)` by suspend "typed" >>
  suspend "callbacks"
QED

Resume body_for_immutable_array_ptr[callbacks]:
  `stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) body` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_thm, alloc_limits_stmt_def, stmt_valued_return_def] >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  qabbrev_tac `P = \ei. expr_sim_inv cenv cx env ei /\
    lookup_immutable cx ei cenv.ce_module name = lookup_immutable cx es cenv.ce_module name` >>
  `!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    (case bd of Fixed cap => T | Dynamic cap =>
       ?av. immutable_holds cenv cx (ArrayT typ (Dynamic cap))
               (Value (ArrayV av)) (n2w off) ei s /\
            value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
            LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
    (!k. k < LENGTH vs ==> immutable_holds cenv cx typ (Value (EL k vs))
      (n2w off + n2w ((case bd of Fixed cap => 0 | Dynamic cap => 32) +
                      k * type_memory_size tv)) ei s)` by suspend "source" >>
  `!st0 bc sd ex inc ei k.
    declare_local cenv id typ st0 = (bc,sd) /\ P ei /\
    lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag_ptr d ctx PG func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ret_ty body) (eval_stmts cx body)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>)` by suspend "body" >>
  `!ei k gs r es2. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx body (ei with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
      gas_obs := gs|>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)` by suspend "scope" >>
  `P (es with gas_obs := [])` by
    simp[Abbr `P`, expr_sim_inv_gas_obs, lookup_immutable_def] >>
  suspend "loop"
QED

Resume body_for_immutable_array_ptr[bounds]:
  `bound_length bd < dimword (:256)` by
    (qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs(), type_slot_size_def] >>
     rpt strip_tac >> Cases_on `bd` >> fs[type_slot_size_def, bound_length_def] >>
     `n' <= n' * type_slot_size tv` by
       (irule LESS_EQ_TRANS >> qexists_tac `n' * 1` >> simp[]) >> decide_tac) >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, array_elements_def, bound_length_def, Abbr `vs`]
QED

Resume body_for_immutable_array_ptr[typed]:
  gen_tac >> strip_tac >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, Abbr `vs`]
  >- (irule (cj 1 fixed_array_elements_typed) >> simp[value_has_type_def] >> metis_tac[]) >>
  gvs[array_elements_def, all_have_type_EVERY, EVERY_EL]
QED

Resume body_for_immutable_array_ptr[source]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `P ei` mp_tac >> simp[Abbr `P`] >> strip_tac >>
  `lookup_immutable cx ei cenv.ce_module name = SOME (ArrayTV tv bd,ArrayV av)` by
    gvs[lookup_immutable_def] >>
  `immutable_holds cenv cx (ArrayT typ bd) (Value (ArrayV av)) (n2w off) ei s` by
    (simp[immutable_holds_def, read_result_def, return_def] >>
     qexistsl_tac [`name`, `off`, `ArrayTV tv bd`, `ArrayV av`, `0`] >>
     simp[sub_layout_def] >>
     qpat_x_assum `lookup_immutable cx ei _ name = SOME _` mp_tac >>
     Cases_on `ALOOKUP ei.immutables cx.txn.target` >> simp[lookup_immutable_def]) >>
  conj_tac
  >- (Cases_on `bd` >> simp[] >> qexists_tac `av` >>
      Cases_on `av` >> gvs[value_has_type_def, array_elements_def, array_length_def, Abbr `vs`]) >>
  rpt strip_tac >> once_rewrite_tac[ADD_COMM] >>
  irule (cj 1 immutable_iter_element_ready) >> simp[] >>
  qexistsl_tac [`av`, `Value (ArrayV av)`] >>
  simp[read_result_def, return_def, Abbr `vs`] >>
  metis_tac[value_has_type_val_wf]
QED

Resume body_for_immutable_array_ptr[body]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `P ei` mp_tac >> simp[Abbr `P`] >> strip_tac >>
  `vs <> []` by (Cases_on `vs` >> fs[]) >>
  `body_stmts_ptr_ok cx body` by
    (fs[body_for_ptr_ok_def] >> Cases_on `vs` >> gvs[read_result_def, return_def]) >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
    occurs_abi_decode_target target tops` by fs[supported_stmt_expr_exists_def] >>
  `value_has_type tv (EL k vs)` by simp[] >>
  `expr_sim_inv cenv cx env (ei with gas_obs := [])` by simp[expr_sim_inv_gas_obs] >>
  `lookup_scopes id (ei with gas_obs := []).scopes = NONE` by simp[] >>
  drule_all for_array_body_fragment_ptr >>
  disch_then (qspecl_then [`inc`, `ex`] mp_tac) >> simp[]
QED

Resume body_for_immutable_array_ptr[scope]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `P ei` mp_tac >> simp[Abbr `P`] >> strip_tac >>
  `expr_sim_inv cenv cx env (ei with gas_obs := gs)` by simp[expr_sim_inv_gas_obs] >>
  `value_has_type tv (EL k vs)` by simp[] >>
  `lookup_scopes id (ei with gas_obs := gs).scopes = NONE` by simp[] >>
  `eval_stmts cx body
    ((ei with gas_obs := gs) with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) ::
        (ei with gas_obs := gs).scopes) = (r,es2)` by simp[] >>
  conj_tac >- (drule_all array_body_result_ok >> simp[]) >>
  drule_all array_body_scope_shape >> strip_tac >>
  qexistsl_tac [`sc`, `rest`] >> simp[] >> strip_tac >>
  `expr_sim_inv cenv cx env (es2 with scopes := rest)` by
    (irule expr_sim_inv_for_pop >> metis_tac[]) >>
  `lookup_scopes id rest = NONE` by
    (Cases_on `lookup_scopes id rest` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _` drule >> simp[FLOOKUP_DEF]) >>
  simp[] >>
  `env_context_consistent (extend_local env id typ F) cx` by
    (fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def,
        extend_local_def] >> metis_tac[]) >>
  `FLOOKUP (extend_local env id typ F).bare_globals (NONE,name) =
     SOME (ArrayT typ bd)` by simp[extend_local_def] >>
  drule_all immutable_array_body_observation >>
  gvs[lookup_immutable_def, extend_local_def]
QED

Resume body_for_immutable_array_ptr[loop]:
  simp[stmt_frag_ptr_def] >>
  map_every qx_gen_tac [`st`, `st'`, `s0`, `G0`, `tn0`, `cenv'`] >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> Cases_on `_0` >>
  qpat_x_assum `cs' = st'` SUBST_ALL_TAC >>
  qpat_x_assum `cenv = cenv'` (SUBST_ALL_TAC o SYM) >>
  `!c lc sa sb. compile_stmts c lc ret_ty body sa = ((),sb) ==>
    cs_extends sa sb` by
    (rpt gen_tac >> strip_tac >>
     drule (SIMP_RULE std_ss [cs_mono_def] (cj 2 compile_stmt_cs_mono)) >> simp[]) >>
  drule_all compile_for_immutable_entry_code_normalized >> strip_tac >>
  drule_all immutable_optional_load_ready >> strip_tac >>
  `sb0.cs_next_var <= sb1.cs_next_var` by
    (mp_tac (cj 2 compile_stmt_cs_mono) >>
     simp[cs_mono_def] >> disch_then drule >> simp[]) >>
  `sa.cs_next_var <= sj.cs_next_var` by decide_tac >>
  qabbrev_tac `tot = STRING #"%" (toString (st1.cs_next_var + 6))` >>
  `tot = STRING #"%" (toString (st1.cs_next_var + 6))` by simp[Abbr `tot`] >>
  drule_all immutable_register_frame >> strip_tac >>
  `fn_has_code st st1 func` by
    (irule (cj 1 fn_has_code_split) >> asm_rewrite_tac[] >>
     qexists_tac `st'` >> asm_rewrite_tac[] >> metis_tac[cs_extends_trans]) >>
  qabbrev_tac `ainst = mk_inst st1.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes cenv typ))] [p]` >>
  `MEM ainst (fn_insts func)` by
    (irule lookup_block_fn_insts >>
     qpat_assum `lookup_block st1.cs_current_bb _ = _` (irule_at Any) >>
     simp[Abbr `ainst`]) >>
  qabbrev_tac `g = STRING #"%" (toString (st1.cs_next_var + 2))` >>
  qabbrev_tac `vld = STRING #"%" (toString (st1.cs_next_var + 3))` >>
  `ALL_DISTINCT [p;idx;g;vld] /\
   (!scopes. not_local_ptr cenv scopes g /\ not_local_ptr cenv scopes vld) /\
   (!x. not_fresh_at st1 x ==> ~MEM x [p;idx;g;vld])` by
    (simp[Abbr `g`, Abbr `vld`, not_fresh_at_def] >>
     rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
     irule local_ptrs_reserved_fresh >> qexists_tac `st1` >> simp[]) >>
  `!x. lvo = Var x ==> ~MEM x [p;idx;g;vld]` by metis_tac[] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) \/
    cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x` by
    (qpat_assum `ret_pc_ok cenv st s0` mp_tac >>
     qpat_assum `!x sz. cenv.ce_return_buf = _ ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ret_pc_ok_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0 /\
   ghost_inv d cenv cx (es with gas_obs := []) G0 tn0 s0` by
    simp[ghost_inv_gas_obs] >>
  `lookup_scopes id (es with gas_obs := []).scopes = NONE` by simp[] >>
  `type_memory_bytes cenv typ < dimword (:256)` by decide_tac >>
  `gas_admissible (eval_for cx tv id body (MAP Value vs)) (stmt_res_ok lctx)
    (es with gas_obs := [])` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, Once evaluate_def, lift_option_type_def,
       lift_option_def, bind_return, bind_def, compatible_bound_def,
       check_def, vyperStateTheory.assert_def, ignore_bind_def, return_def]) >>
  suspend "initialize"
QED

Resume body_for_immutable_array_ptr[initialize]:
  qpat_assum `!ei s. P ei /\ stmt_state_rel _ _ _ _ _ _ ==> _` drule_all >>
  strip_tac >>
  `?iav. (dyn ==>
    immutable_holds cenv cx (ArrayT typ (Dynamic (bound_length bd)))
      (Value (ArrayV iav)) (n2w off) (es with gas_obs := []) s0 /\
    evaluate_type (get_tenv cx) typ = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic (bound_length bd))) (ArrayV iav) /\
    LENGTH vs = array_length (ArrayTV tv (Dynamic (bound_length bd))) iav) /\
    (~dyn ==> LENGTH vs = bound_length bd)` by
    (qpat_x_assum `case bd of Fixed cap => T | Dynamic cap => _` mp_tac >>
     qpat_x_assum `case bd of Fixed cap => LENGTH vs = cap | Dynamic cap => T` mp_tac >>
     qpat_assum `dyn = _` mp_tac >>
     qpat_assum `evaluate_type _ typ = SOME tv` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `bd` >>
     simp[bound_length_def] >> metis_tac[]) >>
  `?dst cc H tm.
    array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst (type_memory_bytes cenv typ) ainst cond st 0
      (es with gas_obs := []) cc /\
    ghost_inv d cenv cx (es with gas_obs := []) H tm cc /\
    ptr_covers H tm p cc (type_memory_bytes cenv typ) /\
    eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\
    FLOOKUP H idx = NONE /\ op_taint tm (Var idx) = {} /\
    op_prov H lvo = NONE /\ op_taint tm lvo = {} /\
    array_caller_frame st s0 cc /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 H tm (OK cc) /\
    (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G0 x /\
      op_taint tm (Var x) = op_taint tn0 (Var x))` by
    (mp_tac (Q.INST [`es` |-> `es with gas_obs := []`, `sa` |-> `st`,
       `sb` |-> `st1`, `cap` |-> `bound_length bd`, `sz` |-> `type_memory_bytes cenv typ`,
       `et` |-> `typ`, `av` |-> `iav`, `s` |-> `s0`, `G` |-> `G0`, `tn` |-> `tn0`,
       `lbl` |-> `st1.cs_current_bb`, `aid` |-> `st1.cs_next_id`,
       `j` |-> `st1.cs_next_id + 1`, `e1` |-> `st1.cs_next_id + 2`,
       `e2` |-> `st1.cs_next_id + 3`, `e3` |-> `st1.cs_next_id + 4`,
       `e4` |-> `st1.cs_next_id + 5`, `e5` |-> `h - 3`, `cond_lbl` |-> `cond`,
       `D` |-> `cx_dead cx`]
       (SPEC_ALL (INST_TYPE [alpha |-> ``:value``] immutable_entry_initialize_ptr))) >>
     impl_tac >- (simp[Abbr `ainst`, Abbr `g`, Abbr `vld`] >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >>
     qpat_assum `op_prov H (Var idx) = NONE`
       (assume_tac o SIMP_RULE (srw_ss()) [op_prov_def]) >>
     qexistsl_tac [`dst`, `cc`, `H`, `tm`] >> simp[Abbr `ainst`]) >>
  `copy_old_operand st1 lvo` by simp[copy_old_operand_def] >>
  `LENGTH vs < dimword (:256)` by decide_tac >>
  `!ei t j. P ei /\ stmt_state_rel ctx func cenv cx ei t /\ j < LENGTH vs ==>
    immutable_holds cenv cx typ (Value (EL j vs))
      (n2w off + n2w ((if dyn then 32 else 0) + j * type_memory_size tv)) ei t` by
    (qpat_x_assum `!ei s. P ei /\ stmt_state_rel _ _ _ _ _ _ ==> _` mp_tac >>
     qpat_x_assum `dyn = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `bd` >> simp[] >> metis_tac[]) >>
  suspend "counted"
QED

Resume body_for_immutable_array_ptr[counted]:
  FAIL_TAC "immutable pointer counted loop bridge"
QED

Finalise body_for_immutable_array_ptr
