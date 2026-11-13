(* Memory case of the body induction, for loop (bodyMemFor's dispatch):
   iteration over a fixed array (S1's body_for_array), from
   stmtForArrayMemory's compile_for_array_frag_mem with expr_sim_inv and the
   array's unchanged binding as the loop invariant. *)
Theory bodyMemForArray
Ancestors
  vyperTypeContract
  bodyMemoryPreds bodySeqMemory stmtForArrayMemory bodySimDeclCases
  stmtSimForArray stmtSimForArrayFrame venomState exprLoweringProps
  exprSimSource bodyExprPreFacts stmtSimProps exprSimHypsDefs
  vyperTypeStoragePreservation list finite_map bodySim bodySimStmtCases
  allocLimits exprSimHyps exprLoweringProps stmtLowering stmtLoweringMono
  stmtSimForParts vyperTyping fragExec compileEnv loweringStateRelDefs valueEncoding
  supportedStmts supportedStmtTraverse supportedExprs vyperAST
  vyperInterpreter vyperState vyperValue vyperTypeSystem
  vyperTypeInvariants vyperTypeCallGraph gasContext stmtSimReturn
  vyperTypeCallStackSoundness vyperTypeValues compileVyper targetPlaceSim exprSimTopLevelProps
  bodyStorageMetadata bodyDynArraySource stmtForDynArrayMemory
  bodyImmFragMemory whitelistForIterImmSource
  whitelistForIterImmFrame whitelistForIterImmCopy valueEncodingTyping
  valueEncodingProps vyperTypeEnv supportedExprTraverse allocLimitsProps arithmetic vyperValueOperation loweringPosts
Libs
  monadsyntax

val _ = Parse.hide "body";

(* S1's array_for_source_ready with the memory body judgment. *)
Theorem array_for_source_ready_mem[local]:
  (!tenv s tyv t s3 vs t3 s4 x t4.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tyv,t) /\
    eval_iterator cx (Array e) s3 = (INL vs,t3) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s4 = (INL x,t4)
    ==> body_for_mem_ok cx tyv id stmts vs) /\
  supported_stmt tops bindings (For id typ (Array e) n stmts) /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  type_stmt env ret_ty (For id typ (Array e) n stmts) = SOME env' /\
  e = Name (ArrayT typ (Fixed n)) arr ==>
  ?name env_b entry tv ptr sz al vs.
    e = Name (ArrayT typ (Fixed n)) name /\ env' = env /\
    well_typed_expr env (Name (ArrayT typ (Fixed n)) name) /\
    id NOTIN FDOM env.var_types /\
    iterator_unmodified (Array (Name (ArrayT typ (Fixed n)) name)) stmts /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    supported_stmts tops bindings stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    lookup_scopes name es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) typ = SOME tv /\
    entry.type = ArrayTV tv (Fixed n) /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
    cenv.ce_var_type name = SOME (ArrayT typ (Fixed n)) /\
    0 < n /\ n < dimword (:256) /\ entry.value = ArrayV (SArrayV al) /\
    vs = array_elements (ArrayTV tv (Fixed n)) (SArrayV al) /\ LENGTH vs = n /\
    (!gs. eval_iterator cx (Array (Name (ArrayT typ (Fixed n)) name))
            (es with gas_obs := gs) = (INL (MAP Value vs), es with gas_obs := gs)) /\
    body_stmts_mem_ok cx stmts /\
    FLOOKUP cenv.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE
Proof
  strip_tac >> drule_all array_for_hypotheses >> strip_tac >> gvs[] >>
  drule_all array_name_local_binding >> strip_tac >>
  rename1 `lookup_scopes name es.scopes = SOME entry` >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  `?al. entry.value = ArrayV (SArrayV al)` by
    (Cases_on `entry.value` >> gvs[value_has_type_def] >>
     rename1 `value_has_type _ (ArrayV av)` >> Cases_on `av` >>
     gvs[value_has_type_def]) >>
  `evaluate_type (get_tenv cx) (ArrayT typ (Fixed n)) =
     SOME (ArrayTV tv (Fixed n))` by
    (fs[expr_sim_inv_def, well_typed_expr_def, env_consistent_def,
        env_scopes_consistent_def] >> metis_tac[]) >>
  `!gs. eval_iterator cx (Array (Name (ArrayT typ (Fixed n)) name))
          (es with gas_obs := gs) =
        (INL (MAP Value (array_elements (ArrayTV tv (Fixed n)) (SArrayV al))),
         es with gas_obs := gs)` by
    (gen_tac >> irule eval_iterator_fixed_name >> simp[]) >>
  drule_all eval_iterator_fixed_name >> strip_tac >>
  qmatch_asmsub_abbrev_tac `INL (MAP Value vs)` >>
  `LENGTH vs = n` by simp[Abbr `vs`, fixed_array_elements_length] >>
  `body_for_mem_ok cx tv id stmts (MAP Value vs)` by
    (qpat_x_assum `!s tyv t s3 vs t3 s4 t4. _` mp_tac >>
     simp[lift_option_type_def, return_def, check_def, assert_def,
          compatible_bound_def] >> disch_then irule >> simp[] >>
     qexistsl_tac [`es`, `es`] >> simp[]) >>
  `body_stmts_mem_ok cx stmts` by
    (fs[body_for_mem_ok_def] >> `vs <> []` by (strip_tac >> gvs[]) >>
     Cases_on `vs` >> gvs[read_result_def, return_def]) >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  qexistsl_tac [`entry`, `tv`] >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `al` >> fs[Abbr `vs`]
QED

(* The array local's region, n elements long, lies below the frontier
   (local_ptrs_rel): what the loop's element reads need beyond
   array_snapshot_memory. *)
Theorem array_snapshot_frontier[local]:
  !H name ei entry tv n cenv ptr sz ctx func cx s.
    lookup_scopes name ei.scopes = SOME entry /\
    entry.type = ArrayTV tv (Fixed n) /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
    stmt_state_rel H ctx func cenv cx ei s ==>
    ?base. eval_operand (Var ptr) s = SOME base /\
      w2n base + n * type_memory_size tv <= s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func cenv ei.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `w` >> simp[eval_operand_def] >>
  gvs[valueEncodingTheory.type_memory_size_def]
QED

(* S1's array_body_fragment_callback with the memory body judgment. *)
Theorem array_body_fragment_callback_mem[local]:
  !cx stmts tops ctx cenv bindings env ei id typ tv v env_b ret_ty
   d func RetQ st0 bc sd ex inc.
    body_stmts_safe tops stmts /\
    body_stmts_mem_ok cx stmts /\ body_inv tops ctx cenv cx /\
    supported_stmts tops bindings stmts /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) stmts ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env ei /\
    ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
    id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) stmts /\
    type_memory_bytes cenv typ < 2 ** 64 /\
    call_evaluation_safe cx (int_calls_stmts stmts) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    declare_local cenv id typ st0 = (bc,sd) ==>
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ret_ty stmts)
      (eval_stmts cx stmts)
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                          popped := []|>)) :: ei.scopes)
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (Cases_on `FLOOKUP cenv.ce_vars id` >> gvs[ce_locals_declared_def] >>
     metis_tac[]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `same_frame cenv bc` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `body_inv tops ctx bc cx` by metis_tac[body_inv_same_frame] >>
  `body_stmts_safe tops stmts` by
    metis_tac[body_stmt_safe_for_body] >>
  qpat_x_assum `body_stmts_mem_ok _ _`
    (irule o REWRITE_RULE [body_stmts_mem_ok_def]) >>
  simp[] >> rpt conj_tac
  >- metis_tac[for_declare_stmts_exprs_ok]
  >- (qexistsl_tac [`bindings`, `tops`] >> simp[])
  >- (qexistsl_tac [`extend_local env id typ F`, `env_b`] >> simp[] >>
      `bc.ce_struct_fields = cenv.ce_struct_fields` by
        metis_tac[same_frame_struct_fields] >>
      conj_tac >- metis_tac[ce_locals_declared_declare_local] >>
      conj_tac >- metis_tac[locals_alloc_ok_extend] >>
      irule expr_sim_inv_for_scope >> metis_tac[]) >>
  metis_tac[frame_ret_ok_mem_same_frame]
QED

(* Local DynArray memory For: preserve the source binding and certify
   the length header and payload snapshot at every live iteration. *)
Theorem body_for_dynarray_name_mem:
  !cx id typ it n body d tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es.
    body_stmt_safe tops (For id typ it n body) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_mem_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_mem_ok cx it) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    (?c name. it = Array (Name (ArrayT typ (Dynamic c)) name) /\ c <= n) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  imp_res_tac body_stmt_safe_for_body >>
  drule_all dynarray_name_source_ready >> strip_tac >> gvs[] >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  rename1 `lookup_scopes name es.scopes = SOME entry` >>
  rename1 `entry.value = ArrayV (DynArrayV vs)` >>
  `body_for_mem_ok cx tv id body (MAP Value vs)` by
    (qpat_x_assum `!s3 vs t3 s4 t4. _` mp_tac >>
     simp[check_def, assert_def, compatible_bound_def, return_def] >>
     disch_then irule >>
     conj_tac >- simp[] >>
     qexistsl_tac [`es with gas_obs := es.gas_obs`, `es with gas_obs := es.gas_obs`] >> simp[]) >>
  `supported_stmts tops bindings body /\
   ~supported_stmts_expr_exists expr_internal_call_root body` by
    fs[supported_stmt_def] >>
  `!target. supported_stmts_expr_exists
      (expr_abi_decode_target_root target) body ==>
      occurs_abi_decode_target target tops` by
    fs[supported_stmt_expr_exists_def] >>
  drule_all array_for_layout_ready >> strip_tac >>
  `name <> id` by metis_tac[optionTheory.NOT_NONE_SOME] >>
  `cenv.ce_alloca_locals /\ supported_program tops /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) body /\ type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_thm, alloc_limits_stmt_def, stmt_valued_return_def] >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  MATCH_MP_TAC
    (Q.GENL [`arr_ptr`, `arr_sz`, `tv`, `vs`]
      (BETA_RULE (Q.SPEC `\ei. expr_sim_inv cenv cx env ei /\
                              lookup_scopes name ei.scopes = SOME entry`
                   (Q.GEN `P` (SPEC_ALL compile_for_dynarray_frag_mem))))) >>
  qexistsl_tac [`dp`, `sz`, `tv`, `vs`] >>
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule (SIMP_RULE std_ss [cs_mono_def] (cj 2 compile_stmt_cs_mono)) >> simp[])
  >- (gen_tac >> strip_tac >> irule dynarray_elements_typed >>
      simp[] >> qexists_tac `c` >> gvs[])
  >- (rpt strip_tac >>
      `value_has_type entry.type entry.value` by simp[] >>
      drule_all dynarray_snapshot_memory >> strip_tac >>
      drule_all dynarray_snapshot_frontier >> strip_tac >>
      gvs[] >> goal_assum (drule_at Any) >> simp[arithmeticTheory.ADD_ASSOC])
  >- (rpt strip_tac >>
      `body_stmts_mem_ok cx body` by
        (fs[body_for_mem_ok_def] >> Cases_on `vs` >>
         gvs[read_result_def, return_def]) >>
      irule array_body_fragment_callback_mem >>
      metis_tac[dynarray_elements_typed]) >>
  rpt gen_tac >> strip_tac >>
  drule_all dynarray_elements_typed >> strip_tac >>
  `expr_sim_inv cenv cx env (ei with gas_obs := gs) /\
   lookup_scopes name (ei with gas_obs := gs).scopes = SOME entry /\
   lookup_scopes id (ei with gas_obs := gs).scopes = NONE` by simp[] >>
  `eval_stmts cx body
     ((ei with gas_obs := gs) with scopes :=
       (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs;
                         popped := []|>)) :: (ei with gas_obs := gs).scopes) =
     (r, es2)` by simp[] >>
  drule_at (Pat `eval_stmts`) array_body_scope_callback >>
  disch_then drule_all >> simp[] >> metis_tac[]
QED

(* Immutable-array memory iteration: instantiate the memory fragment with
   the expression invariant and an unchanged immutable lookup snapshot. *)
Theorem body_for_immutable_array_mem:
  !cx id typ it n body d tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es.
    body_stmt_safe tops (For id typ it n body) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_mem_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_mem_ok cx it) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    (?bd src name. it = Array (TopLevelName (ArrayT typ bd) (src,name)) /\
       FLOOKUP env.bare_globals (src,name) = SOME (ArrayT typ bd) /\
       bound_length bd <= n) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `id NOTIN FDOM env.var_types /\
   iterator_unmodified (Array (TopLevelName (ArrayT typ bd) (src,name))) body /\
   ?env_b. type_stmts (extend_local env id typ F) ret_ty body = SOME env_b` by
    gvs[type_stmt_def, well_typed_iterator_def, expr_type_def,
        optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
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
    (`es = es with gas_obs := es.gas_obs` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     pop_assum SUBST1_TAC >>
     qpat_assum `!gs. eval_iterator _ _ _ = (INL (MAP Value vs),_)` (fn th => rewrite_tac [th])) >>
  `body_for_mem_ok cx tv id body (MAP Value vs)` by
    (qpat_x_assum `!s3 vs t' s4 t''. _` mp_tac >>
     simp[lift_option_type_def, return_def, check_def, assert_def, compatible_bound_def] >>
     disch_then irule >> simp[] >> qexistsl_tac [`es`, `es`] >> simp[]) >>
  `cenv.ce_alloca_locals /\ supported_program tops /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
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
  suspend "assemble"
QED
Resume body_for_immutable_array_mem[assemble]:
  match_mp_tac compile_for_immutable_frag_mem >>
  qexistsl_tac [`off`, `tv`, `vs`,
    `\ei. expr_sim_inv cenv cx env ei /\
       lookup_immutable cx ei cenv.ce_module name = lookup_immutable cx es cenv.ce_module name`] >>
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule (SIMP_RULE std_ss [cs_mono_def] (cj 2 compile_stmt_cs_mono)) >> simp[])
  >- suspend "source"
  >- suspend "body"
  >- suspend "scope" >>
  simp[expr_sim_inv_gas_obs, vyperBareGlobalNameTheory.lookup_immutable_def]
QED
Resume body_for_immutable_array_mem[bounds]:
  `bound_length bd < dimword (:256)` by
    (qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs(), type_slot_size_def] >>
     rpt strip_tac >> Cases_on `bd` >> fs[type_slot_size_def, bound_length_def] >>
     `n' <= n' * type_slot_size tv` by
       (irule LESS_EQ_TRANS >> qexists_tac `n' * 1` >> simp[]) >> decide_tac) >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, array_elements_def, bound_length_def, Abbr `vs`]
QED
Resume body_for_immutable_array_mem[typed]:
  gen_tac >> strip_tac >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, Abbr `vs`]
  >- (irule (cj 1 fixed_array_elements_typed) >> simp[value_has_type_def] >> metis_tac[]) >>
  gvs[array_elements_def, all_have_type_EVERY, EVERY_EL]
QED
Resume body_for_immutable_array_mem[source]:
  rpt gen_tac >> strip_tac >>
  `lookup_immutable cx ei cenv.ce_module name = SOME (ArrayTV tv bd,ArrayV av)` by
    gvs[vyperBareGlobalNameTheory.lookup_immutable_def] >>
  drule_all immutable_array_source_ready >> strip_tac >>
  gvs[vyperBareGlobalNameTheory.lookup_immutable_def] >>
  `immutable_holds cenv cx (ArrayT typ bd) (Value (ArrayV av)) (n2w off) ei s` by
    (simp[immutable_holds_def, read_result_def, return_def] >>
     qexistsl_tac [`name`, `off`, `ArrayTV tv bd`, `ArrayV av`, `0`] >>
     simp[sub_layout_def]) >>
  conj_tac
  >- (Cases_on `bd` >> simp[] >> qexists_tac `av` >>
      Cases_on `av` >> gvs[value_has_type_def, array_elements_def, array_length_def, Abbr `vs`]) >>
  rpt strip_tac >> once_rewrite_tac[ADD_COMM] >>
  irule (cj 1 immutable_iter_element_ready) >> simp[] >>
  qexistsl_tac [`av`, `Value (ArrayV av)`] >>
  simp[read_result_def, return_def, Abbr `vs`] >>
  metis_tac[value_has_type_val_wf]
QED
Resume body_for_immutable_array_mem[body]:
  rpt gen_tac >> strip_tac >>
  `vs <> []` by (Cases_on `vs` >> fs[]) >>
  `body_stmts_mem_ok cx body` by
    (fs[body_for_mem_ok_def] >> Cases_on `vs` >>
     gvs[read_result_def, return_def]) >>
  `body_stmts_safe tops body` by metis_tac[body_stmt_safe_for_body] >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
    occurs_abi_decode_target target tops` by fs[supported_stmt_expr_exists_def] >>
  `stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) body` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_thm, alloc_limits_stmt_def, stmt_valued_return_def] >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  irule array_body_fragment_callback_mem >> metis_tac[]
QED
Resume body_for_immutable_array_mem[scope]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  `expr_sim_inv cenv cx env (ei with gas_obs := gs)` by
    simp[expr_sim_inv_gas_obs] >>
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
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _` drule >>
     simp[FLOOKUP_DEF]) >>
  simp[] >>
  `env_context_consistent (extend_local env id typ F) cx` by
    (fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def,
        extend_local_def] >> metis_tac[]) >>
  `FLOOKUP (extend_local env id typ F).bare_globals (cenv.ce_module,name) =
     SOME (ArrayT typ bd)` by simp[extend_local_def] >>
  drule_all immutable_array_body_observation >>
  gvs[vyperBareGlobalNameTheory.lookup_immutable_def, extend_local_def]
QED
Finalise body_for_immutable_array_mem

(* ADMITTED (packet A2-mem, memory iterable): a For over an array that is
   neither a name nor a top-level name, nor a place rooted at a storage
   declaration, with no ternary in it: a temporary (literal, call result) or
   a projection of a local.  A ternary of same-layout arms lowers to a pointer
   into one arm, which could alias a local the body writes (#1254); the
   lowered value has the annotated type, so a widened internal call result
   (#767) is out. *)
Theorem body_for_memory_iterable_mem:
  !cx id typ it n body d tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es.
    body_stmt_safe tops (For id typ it n body) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_mem_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_mem_ok cx it) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    (?e. it = Array e /\ ~(?t v. e = Name t v) /\ ~(?t nid. e = TopLevelName t nid) /\
       ~supported_expr_exists (\x. ?t c l r. x = IfExp t c l r) e /\
       post_value_type cenv e = expr_type e /\
       ~(?tgt nid. loop_iterator_place e = SOME tgt /\
                   target_root tgt = TopLevelNameTarget nid /\ ~immutable_root cx tgt) /\
       ?bd. expr_type e = ArrayT typ bd /\ bound_length bd <= n) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  cheat
QED

Theorem body_for_fixed_array_mem[local]:
  !cx id typ it n body d tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es e m arr.
    body_stmt_safe tops (For id typ it n body) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_mem_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_mem_ok cx it) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    it = Array e /\ e = Name (ArrayT typ (Fixed n)) arr ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac body_stmt_safe_for_body >> qpat_x_assum `it = Array _` SUBST_ALL_TAC >>
  drule_all array_for_source_ready_mem >> strip_tac >> gvs[] >>
  rename1 `lookup_scopes name es.scopes = SOME entry` >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  rename1 `body_stmts_mem_ok cx stmts` >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target)
              stmts ==> occurs_abi_decode_target target tops` by
    fs[supported_stmt_expr_exists_def] >>
  drule_all array_for_layout_ready >> strip_tac >>
  `name <> id` by metis_tac[optionTheory.NOT_NONE_SOME] >>
  `FLOOKUP env.var_types name = SOME (ArrayT typ (Fixed n))` by
    fs[well_typed_expr_def, expr_type_def] >>
  `cenv.ce_alloca_locals /\ supported_program tops /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) stmts /\
   type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_thm, alloc_limits_stmt_def, stmt_valued_return_def] >>
  `call_evaluation_safe cx (int_calls_stmts stmts)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ap) az)` >>
  MATCH_MP_TAC
    (Q.GENL [`arr_ptr`, `arr_sz`, `tv`, `vs`]
      (BETA_RULE (Q.SPEC `\ei. expr_sim_inv cenv cx env ei /\
                              lookup_scopes name ei.scopes = SOME entry`
                   (Q.GEN `P` (SPEC_ALL compile_for_array_frag_mem))))) >>
  qexistsl_tac [`ap`, `az`, `tv`,
    `array_elements (ArrayTV tv (Fixed n)) (SArrayV al)`] >>
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule (SIMP_RULE std_ss [cs_mono_def] (cj 2 compile_stmt_cs_mono)) >>
      simp[])
  >- (rpt strip_tac >> metis_tac[fixed_array_elements_typed])
  >- (rpt strip_tac >>
      qspecl_then [`H`, `name`, `ei`, `entry`, `tv`, `n`, `al`, `cenv`, `ap`, `az`,
                   `ctx`, `func`, `cx`, `s`] mp_tac array_snapshot_memory >>
      qspecl_then [`H`, `name`, `ei`, `entry`, `tv`, `n`, `cenv`, `ap`, `az`,
                   `ctx`, `func`, `cx`, `s`] mp_tac array_snapshot_frontier >>
      simp[] >> rpt strip_tac >> gvs[])
  >- (rpt strip_tac >> irule array_body_fragment_callback_mem >>
      metis_tac[fixed_array_elements_typed]) >>
  rpt gen_tac >> strip_tac >>
  drule_all fixed_array_elements_typed >> strip_tac >>
  `expr_sim_inv cenv cx env (ei with gas_obs := gs) /\
   lookup_scopes name (ei with gas_obs := gs).scopes = SOME entry /\
   lookup_scopes id (ei with gas_obs := gs).scopes = NONE` by simp[] >>
  `eval_stmts cx stmts
     ((ei with gas_obs := gs) with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv;
                          value := EL k (array_elements (ArrayTV tv (Fixed n))
                                                        (SArrayV al));
                          popped := []|>)) :: (ei with gas_obs := gs).scopes) =
     (r, es2)` by simp[] >>
  drule_at (Pat `eval_stmts`) array_body_scope_callback >>
  disch_then drule_all >> simp[] >> metis_tac[]
QED

Theorem body_for_array_mem:
  !cx id typ it n body d tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es.
    body_stmt_safe tops (For id typ it n body) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_mem_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_mem_ok cx it) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    (?e. it = Array e) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `supported_iterator tops typ (Array e) n` by fs[supported_stmt_def] >>
  `well_typed_expr env e /\ ?bd. expr_type e = ArrayT typ bd` by
    gvs[type_stmt_def, well_typed_iterator_def, AllCaseEqs()] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   cenv.ce_func_return_type = build_func_return_type tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops))` by
    fs[bodySimTheory.body_inv_def] >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_declared_return >> qexists_tac `tops` >>
     simp[] >> rpt strip_tac >>
     gvs[supported_iterator_def]) >>
  Cases_on `e` >>
  gvs[supported_iterator_def, expr_type_def, place_access_root]
  >~ [`Name (ArrayT _ bd) arr`]
  >- (Cases_on `bd` >> gvs[]
      >- (irule body_for_fixed_array_mem >> simp[] >> metis_tac[]) >>
      irule body_for_dynarray_name_mem >> simp[] >> metis_tac[])
  >~ [`TopLevelName (ArrayT _ bd) nid`]
  >- (PairCases_on `nid` >> gvs[optionTheory.IS_SOME_EXISTS] >>
      drule_all supported_immutable_type_find_NONE >> strip_tac >> gvs[] >>
      `FLOOKUP env.bare_globals (NONE,nid1) = SOME (ArrayT typ bd)` by
        (irule toplevel_find_NONE_bare_global >>
         fs[expr_sim_inv_def] >> metis_tac[]) >>
      irule body_for_immutable_array_mem >> simp[] >> metis_tac[]) >>
  irule body_for_memory_iterable_mem >> simp[expr_type_def] >> metis_tac[]
QED
