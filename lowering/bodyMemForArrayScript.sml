(* Memory case of the body induction, for loop (bodyMemFor's dispatch):
   iteration over a fixed array (S1's body_for_array), from
   stmtForArrayMemory's compile_for_array_frag_mem with expr_sim_inv and the
   array's unchanged binding as the loop invariant. *)
Theory bodyMemForArray
Ancestors
  bodyMemoryPreds bodySeqMemory stmtForArrayMemory bodySimDeclCases
  stmtSimForArray stmtSimForArrayFrame venomState exprLoweringProps
  exprSimSource bodyExprPreFacts stmtSimProps exprSimHypsDefs
  vyperTypeStoragePreservation list finite_map bodySim bodySimStmtCases
  allocLimits exprSimHyps exprLoweringProps stmtLowering stmtLoweringMono
  stmtSimForParts vyperTyping fragExec compileEnv valueEncoding
  supportedStmts supportedStmtTraverse supportedExprs vyperAST
  vyperInterpreter vyperState vyperValue vyperTypeSystem
  vyperTypeInvariants vyperTypeCallGraph gasContext stmtSimReturn
  vyperTypeCallStackSoundness vyperTypeValues compileVyper
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
  type_stmt env ret_ty (For id typ (Array e) n stmts) = SOME env' ==>
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
            (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) /\
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
        (INL (array_elements (ArrayTV tv (Fixed n)) (SArrayV al)),
         es with gas_obs := gs)` by
    (gen_tac >> irule eval_iterator_fixed_name >> simp[]) >>
  drule_all eval_iterator_fixed_name >> strip_tac >>
  qmatch_asmsub_abbrev_tac `INL vs` >>
  `LENGTH vs = n` by simp[Abbr `vs`, fixed_array_elements_length] >>
  `body_for_mem_ok cx tv id stmts vs` by
    (qpat_x_assum `!s tyv t s3 vs t3 s4 t4. _` mp_tac >>
     simp[lift_option_type_def, return_def, check_def, assert_def,
          compatible_bound_def] >> disch_then irule >> simp[] >>
     qexistsl_tac [`es`, `es`] >> simp[]) >>
  `body_stmts_mem_ok cx stmts` by
    (fs[body_for_mem_ok_def] >> `vs <> []` by (strip_tac >> gvs[]) >>
     metis_tac[]) >>
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
  !name ei entry tv n cenv ptr sz ctx func cx s.
    lookup_scopes name ei.scopes = SOME entry /\
    entry.type = ArrayTV tv (Fixed n) /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
    stmt_state_rel ctx func cenv cx ei s ==>
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
    EVERY (stmt_exprs_ok cenv) stmts /\
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
  qpat_x_assum `body_stmts_mem_ok _ _`
    (irule o REWRITE_RULE [body_stmts_mem_ok_def]) >>
  simp[] >> rpt conj_tac
  >- metis_tac[stmt_exprs_ok_same_frame]
  >- (qexistsl_tac [`bindings`, `tops`] >> simp[])
  >- (qexistsl_tac [`extend_local env id typ F`, `env_b`] >> simp[] >>
      `bc.ce_struct_fields = cenv.ce_struct_fields` by
        metis_tac[same_frame_struct_fields] >>
      conj_tac >- metis_tac[ce_locals_declared_declare_local] >>
      conj_tac >- metis_tac[locals_alloc_ok_extend] >>
      irule expr_sim_inv_for_scope >> metis_tac[]) >>
  metis_tac[frame_ret_ok_mem_same_frame]
QED

Theorem body_for_array_mem:
  !cx id typ it n body d tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es.
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
  rpt gen_tac >> strip_tac >> qpat_x_assum `it = Array _` SUBST_ALL_TAC >>
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
  `EVERY (stmt_exprs_ok cenv) stmts /\ type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_EVERY, alloc_limits_stmt_def, stmt_valued_return_def] >>
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
      qspecl_then [`name`, `ei`, `entry`, `tv`, `n`, `al`, `cenv`, `ap`, `az`,
                   `ctx`, `func`, `cx`, `s`] mp_tac array_snapshot_memory >>
      qspecl_then [`name`, `ei`, `entry`, `tv`, `n`, `cenv`, `ap`, `az`,
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
