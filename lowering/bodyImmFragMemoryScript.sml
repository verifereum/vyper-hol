Theory bodyImmFragMemory
Ancestors
  bodyImmCompiledMemory
  whitelistForIterImmFrag stmtForArrayMemorySupport stmtSimDefs
  stmtSimProps stmtSimForArrayLoop stmtLowering loweringPosts
  compileEnv context emitHelper exprLoweringProps loweringStateRelDefs
  vyperInterpreter vyperState vyperValue vyperAST gasSummary gasOutcome
  gasContext gasExemptCert fragGasMode fragGasPathMem exprSimMemDefs
  list finite_map words arithmetic
Libs
  monadsyntax

Theorem compile_for_immutable_frag_mem_from_outcome:
  (!d ctx func cx cenv lctx RetQ ty id et bd n src name off stmts tv vs es P st st' s.
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  elem_size_in_location cenv LocCode et = type_memory_size tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_bytes cenv et + 64 < dimword (:256) /\
  LENGTH vs <= bound_length bd /\ bound_length bd < dimword (:256) /\
  (case bd of Fixed cap => LENGTH vs = cap | Dynamic cap => T) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==> cs_extends sa sb) /\
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    (case bd of Fixed cap => T | Dynamic cap =>
       ?av. immutable_holds cenv cx (ArrayT et (Dynamic cap))
               (Value (ArrayV av)) (n2w off) ei s /\
            value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
            LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
    (!k. k < LENGTH vs ==> immutable_holds cenv cx et (Value (EL k vs))
      (n2w off + n2w ((case bd of Fixed cap => 0 | Dynamic cap => 32) +
                      k * type_memory_size tv)) ei s)) /\
  (!st0 bc sd ex inc ei k.
    declare_local cenv id et st0 = (bc,sd) /\ P ei /\
    lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes)) /\
  (!ei k gs r es2. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
      gas_obs := gs|>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) /\
  compile_stmt cenv lctx ty
    (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts) st = ((),st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\ ret_pc_ok cenv st s /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  P es /\ lookup_scopes id es.scopes = NONE /\
  gas_admissible (eval_for cx tv id stmts vs) (stmt_res_ok lctx) es /\
  alloca_history func s /\ return_buf_frame d cenv st s ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (eval_for cx tv id stmts vs) (es,s)
    (\res ee t. res = INL () /\
       t.vs_current_bb = st'.cs_current_bb /\
       t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
       stmt_state_rel ctx func cenv cx ee t /\ array_caller_frame st s t /\
       (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
       return_buf_frame d cenv st' t /\ alloca_history func t /\
       s.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. ?ex. res = INR ex /\
       !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)) ==>
  !d ctx func cx cenv lctx RetQ ty id et bd n src name off stmts tv vs es P.
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  elem_size_in_location cenv LocCode et = type_memory_size tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_bytes cenv et + 64 < dimword (:256) /\
  LENGTH vs <= bound_length bd /\ bound_length bd < dimword (:256) /\
  (case bd of Fixed cap => LENGTH vs = cap | Dynamic cap => T) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==> cs_extends sa sb) /\
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    (case bd of Fixed cap => T | Dynamic cap =>
       ?av. immutable_holds cenv cx (ArrayT et (Dynamic cap))
               (Value (ArrayV av)) (n2w off) ei s /\
            value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
            LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
    (!k. k < LENGTH vs ==> immutable_holds cenv cx et (Value (EL k vs))
      (n2w off + n2w ((case bd of Fixed cap => 0 | Dynamic cap => 32) +
                      k * type_memory_size tv)) ei s)) /\
  (!st0 bc sd ex inc ei k.
    declare_local cenv id et st0 = (bc,sd) /\ P ei /\
    lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes)) /\
  (!ei k gs r es2. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
      gas_obs := gs|>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) /\
  bound_length bd <= n /\ lookup_scopes id es.scopes = NONE /\
  P (es with gas_obs := []) /\
  (!gs. eval_iterator cx (Array (TopLevelName (ArrayT et bd) (src,name)))
    (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty
      (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts))
    (eval_stmt cx
      (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts)) es
Proof
  disch_then (mk_asm "compiled") >>
  rpt gen_tac >> strip_tac >> simp[stmt_frag_mem_def] >>
  map_every qx_gen_tac [`st`, `st'`, `s0`, `cenv'`] >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def, NoAsms] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `lookup_scopes id (es with gas_obs := []).scopes = NONE` by simp[] >>
  `LENGTH vs <= n` by decide_tac >>
  `gas_admissible (eval_for cx tv id stmts vs) (stmt_res_ok lctx)
     (es with gas_obs := [])` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, Once evaluate_def, lift_option_type_def,
       lift_option_def, bind_return, bind_def, compatible_bound_def,
       check_def, vyperStateTheory.assert_def, ignore_bind_def, return_def]) >>
  asm_x "compiled" (mp_tac o Q.INST
    [`es` |-> `es with gas_obs := []`, `st'` |-> `cs'`, `s` |-> `s0`] o SPEC_ALL) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  suspend "source_prefix"
QED
Resume compile_for_immutable_frag_mem_from_outcome[source_prefix]:
  qmatch_asmsub_abbrev_tac `gas_outcome T _ _ _ _ Q R` >>
  `gas_outcome T (cx_tops cx) (ctx,func)
     (eval_stmt cx (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts))
     (es,s0) Q R` by
    (qpat_x_assum `gas_outcome T _ _ _ _ Q R` mp_tac >>
     rewrite_tac[gas_outcome_def] >> strip_tac >> qexists `marks`
     >- (disj1_tac >>
         qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
         simp[gas_summary_at_def, gas_marked_exec_def, Once evaluate_def,
           bind_def, lift_option_type_def, ignore_bind_def, check_def,
           compatible_bound_def, vyperStateTheory.assert_def, return_def]) >>
     disj2_tac >>
     `assert T (Error (RuntimeError "For too long")) = return ()` by
       simp[FUN_EQ_THM, vyperStateTheory.assert_def, return_def] >>
     rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target)` >>
     qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
     simp[Once evaluate_def, lift_option_type_def, bind_return,
       ignore_bind_def, bind_assoc] >>
     `gas_marked_exec T (ctx,func)
       (eval_iterator cx (Array (TopLevelName (ArrayT et bd) (src,name)))) (es,s0)
       [] (INL vs) es (OK s0)` by
       (simp[gas_marked_exec_def, gas_marked_path_def] >>
        irule (cj 1 gas_path_mem_rules) >> simp[]) >>
     drule gas_exempt_cert_bind_values >>
     simp[] >> disch_then irule >>
     simp[check_def, compatible_bound_def, vyperStateTheory.assert_def, bind_return,
       GSYM ignore_bind_def] >>
     gvs[ignore_bind_def, vyperStateTheory.assert_def, bind_return]) >>
  suspend "post"
QED
Resume compile_for_immutable_frag_mem_from_outcome[post]:
  `cs'.cs_current_insts = []` by
    (drule_all whitelistForIterImmLoopTheory.compile_for_immutable_entry_code_normalized >>
     strip_tac >> asm_rewrite_tac[]) >>
  irule exprSimSubscriptMapTheory.gas_outcome_conseq >>
  qpat_assum `gas_outcome T _ _ (eval_stmt _ _) _ Q R` (irule_at Any) >>
  conj_tac
  >- (rpt gen_tac >> simp[Abbr `R`] >> metis_tac[]) >>
  rpt gen_tac >> BETA_TAC >> simp[Abbr `Q`] >> strip_tac >>
  simp[stmt_lands_def, block_is_terminated_def, cenv_top_ext_refl] >>
  qpat_x_assum `array_caller_frame _ _ _` mp_tac >>
  simp[array_caller_frame_def]
QED
Finalise compile_for_immutable_frag_mem_from_outcome

(* TOP-LEVEL: full memory fragment for immutable-array iteration. *)
Theorem compile_for_immutable_frag_mem:
  !d ctx func cx cenv lctx RetQ ty id et bd n src name off stmts tv vs es P.
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  elem_size_in_location cenv LocCode et = type_memory_size tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_bytes cenv et + 64 < dimword (:256) /\
  LENGTH vs <= bound_length bd /\ bound_length bd < dimword (:256) /\
  (case bd of Fixed cap => LENGTH vs = cap | Dynamic cap => T) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==> cs_extends sa sb) /\
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    (case bd of Fixed cap => T | Dynamic cap =>
       ?av. immutable_holds cenv cx (ArrayT et (Dynamic cap))
               (Value (ArrayV av)) (n2w off) ei s /\
            value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
            LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
    (!k. k < LENGTH vs ==> immutable_holds cenv cx et (Value (EL k vs))
      (n2w off + n2w ((case bd of Fixed cap => 0 | Dynamic cap => 32) +
                      k * type_memory_size tv)) ei s)) /\
  (!st0 bc sd ex inc ei k.
    declare_local cenv id et st0 = (bc,sd) /\ P ei /\
    lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes)) /\
  (!ei k gs r es2. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
      gas_obs := gs|>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) /\
  bound_length bd <= n /\ lookup_scopes id es.scopes = NONE /\
  P (es with gas_obs := []) /\
  (!gs. eval_iterator cx (Array (TopLevelName (ArrayT et bd) (src,name)))
    (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty
      (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts))
    (eval_stmt cx
      (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts)) es
Proof
  mp_tac compile_for_immutable_frag_mem_from_outcome >>
  (impl_tac >- ACCEPT_TAC immutable_compiled_loop_outcome_mem) >>
  disch_then ACCEPT_TAC
QED
