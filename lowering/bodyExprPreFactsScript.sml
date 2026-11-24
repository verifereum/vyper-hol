(* Shared expression-call and body-precondition boundaries. *)
Theory bodyExprPreFacts
Ancestors
  bodyStorageCases bodyInvariantFrameProps bodyInvCodeProps bodyInvMetadataProps
  bodyMainModuleProps bodyInvExecutionProps alist compileUnit
  exprSimSource bodySim allocLimitsProps stmtLowering stmtLoweringMono
  fragExec stmtSimProps
  loweringPosts supportedStmtTraverse vyperCallOutcomeStorage vyperTypeExprSoundness
  vyperTypeSystem vyperTypeEnvPreservation vyperTypeContractStaticMaps
  vyperTypeEvalSoundness vyperTypeInvariants vyperTypeAssignContext
  vyperTypeValues vyperTypeScopePop vyperTypeEnvExtension
  vyperTypeStoragePreservation vyperStorageLayoutSafety vyperStorageBackend
  vyperEvalOutcomeSuffix stmtPoppedKeys placeTypingProps
  finite_map list exprLoweringProps compileVyper
  exprSimHypsDefs gasContext vyperABI
  bodyLinkedCallResolution bodyCallSupport bodyInvSplit bodySingletonCallSupport whitelistCheckerDecls
  vyperTypeContract
  supportedExprTraverse supportedExprs supportedDecls supportedStmts
  vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperInterpreter vyperState compileEnv allocLimits
  vyperTypeEvalProofs
Libs
  monadsyntax

(* stmt_expr_body_pre's const-name premise, discharged from body_inv. *)
val irule_body_pre = bodyConstNameLib.irule_body_pre;

(* An expression with no internal call in it has no internal calls to
   make.  Reasons and conditions are pure (supported_pure_no_internal_call). *)
Theorem no_internal_call_int_calls:
  (!e. ~supported_expr_exists expr_internal_call_root e ==>
       int_calls_expr e = []) /\
  (!t. ~supported_target_exists expr_internal_call_root t ==>
       int_calls_target t = []) /\
  (!es. ~supported_exprs_exists expr_internal_call_root es ==>
        int_calls_exprs es = []) /\
  (!eo. ~supported_opt_exists expr_internal_call_root eo ==>
        int_calls_opt eo = []) /\
  (!kes. ~supported_fields_exists expr_internal_call_root kes ==>
         int_calls_named_exprs kes = [])
Proof
  ho_match_mp_tac int_calls_expr_ind >>
  rw[int_calls_expr_def, supported_expr_exists_def,
     expr_internal_call_root_def]
QED


Theorem supported_pure_int_calls:
  !tops e. supported_effect_free_expr tops e ==> int_calls_expr e = []
Proof
  metis_tac[supported_pure_no_internal_call, expr_has_internal_call_def,
            no_internal_call_int_calls]
QED

(* All EVM-running roots are handled by the body simulation. *)
Theorem stmt_no_evm_run[local]:
  (!s. ~supported_stmt_expr_exists expr_evm_run_root s) /\
  (!ss. ~supported_stmts_expr_exists expr_evm_run_root ss)
Proof
  `!p e. p = expr_evm_run_root ==> ~supported_expr_exists p e` by
    (sg `(!p e. p = expr_evm_run_root ==> ~supported_expr_exists p e) /\
         (!p t. p = expr_evm_run_root ==> ~supported_target_exists p t) /\
         (!p es. p = expr_evm_run_root ==> ~supported_exprs_exists p es) /\
         (!p eo. p = expr_evm_run_root ==> ~supported_opt_exists p eo) /\
         (!p fes. p = expr_evm_run_root ==> ~supported_fields_exists p fes)`
     >- (ho_match_mp_tac supported_expr_exists_ind >>
         rw[supported_expr_exists_def, expr_evm_run_root_def]) >> simp[]) >>
  `(!p t. p = expr_evm_run_root ==> ~supported_assignment_exists p t) /\
   (!p ts. p = expr_evm_run_root ==> ~supported_assignments_exists p ts)` by
    (ho_match_mp_tac supported_assignment_exists_ind >>
     simp[supported_assignment_exists_def, supported_target_exists_indices] >>
     fs[EVERY_MEM, combinTheory.o_DEF]) >>
  `!es. ~supported_exprs_exists expr_evm_run_root es` by
    (Induct >> simp[supported_expr_exists_def]) >>
  `!eo. ~supported_opt_exists expr_evm_run_root eo` by
    (Cases >> simp[supported_expr_exists_def]) >>
  `!r. ~supported_assert_exists expr_evm_run_root r` by
    (Cases >> simp[supported_assert_exists_def, EXISTS_MEM]) >>
  `!r. ~supported_raise_exists expr_evm_run_root r` by
    (Cases >> simp[supported_raise_exists_def, EXISTS_MEM]) >>
  `!i. ~supported_iterator_exists expr_evm_run_root i` by
    (Cases >> simp[supported_iterator_exists_def]) >>
  sg `(!p s. p = expr_evm_run_root ==> ~supported_stmt_expr_exists p s) /\
       (!p ss. p = expr_evm_run_root ==> ~supported_stmts_expr_exists p ss)`
  >- (ho_match_mp_tac supported_stmt_expr_exists_ind >>
      simp[supported_stmt_expr_exists_def, supported_target_exists_indices,
           EVERY_MEM, combinTheory.o_DEF, EXISTS_MEM]) >> simp[]
QED

Theorem supported_string_reason_expr[local]:
  supported_string_reason tops e ==> supported_expr tops e
Proof
  Cases_on `e` >>
  gvs[supported_string_reason_def, supportedExprsTheory.supported_expr_def] >>
  rename1 `Literal _ lit` >> Cases_on `lit` >>
  gvs[supported_string_reason_def, supported_pure_expr_def]
QED

Theorem supported_base_target_main_calls[local]:
  (supported_target tops bindings t \/ supported_aug_target tops bindings t) ==>
  EVERY (\c. FST c = NONE ==>
             IS_SOME (supported_function_decl tops c Internal)) (int_calls_target t)
Proof
  Cases_on `t` >>
  simp[supported_target_def, supported_aug_target_def, int_calls_expr_def] >>
  strip_tac >> drule supported_target_info_main_calls >>
  simp[int_calls_expr_def, EVERY_APPEND]
QED

Theorem supported_assignment_main_calls[local]:
  supported_assignment tops bindings target e ==>
  EVERY (\c. FST c = NONE ==>
             IS_SOME (supported_function_decl tops c Internal)) (int_calls_atarget target)
Proof
  Cases_on `target` >>
  simp[supported_assignment_def, int_calls_atarget_def]
  >- metis_tac[supported_base_target_main_calls] >>
  strip_tac >> qpat_x_assum `EVERY _ _` mp_tac >>
  qmatch_goalsub_rename_tac `int_calls_atargets ts` >>
  Induct_on `ts` >> simp[int_calls_atarget_def] >>
  Cases_on `h` >> simp[int_calls_atarget_def, EVERY_APPEND] >>
  metis_tac[supported_base_target_main_calls]
QED

Theorem supported_append_target_main_calls[local]:
  supported_append_target tops t ==>
  EVERY (\c. FST c = NONE ==>
             IS_SOME (supported_function_decl tops c Internal)) (int_calls_target t)
Proof
  `!t. int_calls_target t = FLAT (MAP int_calls_expr (target_indices t))` by
    (measureInduct_on `base_assignment_target_size t` >>
     Cases_on `t` >> simp[int_calls_expr_def, target_indices_def] >>
     gvs[vyperASTTheory.expr_size_def]) >>
  strip_tac >>
  `EVERY (supported_pure_expr tops) (target_indices t)` by
    (Cases_on `t` >> gvs[supported_append_target_def, target_indices_def]) >>
  qpat_x_assum `!t. int_calls_target t = _`
    (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  simp[EVERY_FLAT, EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
  rpt strip_tac >> fs[EVERY_MEM] >>
  `supported_pure_expr tops x` by (first_x_assum irule >> simp[]) >>
  drule (cj 1 supported_pure_main_calls) >>
  simp[EVERY_MEM] >> disch_then (qspec_then `c` mp_tac) >> simp[]
QED

Theorem supported_iterator_main_calls[local]:
  supported_iterator tops ty it bound ==>
  EVERY (\c. FST c = NONE ==>
             IS_SOME (supported_function_decl tops c Internal)) (int_calls_iterator it)
Proof
  Cases_on `it`
  >- (simp[int_calls_iterator_def] >>
      qmatch_goalsub_rename_tac `int_calls_expr arr` >> Cases_on `arr`
      >~ [`Name _ _`]
      >- simp[int_calls_expr_def]
      >~ [`TopLevelName _ _`]
      >- simp[int_calls_expr_def]
      >> simp[supported_iterator_def] >> metis_tac[supported_expr_main_calls])
  >> simp[supported_iterator_def, int_calls_iterator_def, EVERY_APPEND] >>
  qmatch_goalsub_rename_tac
    `EVERY _ (int_calls_expr lo) /\ EVERY _ (int_calls_expr hi)` >>
  strip_tac >>
  `supported_pure_expr tops lo /\ supported_pure_expr tops hi` suffices_by
    metis_tac[supported_pure_main_calls] >>
  Cases_on `lo` >> gvs[supported_pure_expr_def] >>
  rename1 `Literal _ lit` >> Cases_on `lit` >> gvs[supported_pure_expr_def] >>
  Cases_on `hi` >> gvs[supported_pure_expr_def]
QED

Theorem supported_reasons_main_calls[local]:
  (!tops r. supported_assert_reason tops r ==>
    EVERY (\c. FST c = NONE ==>
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_assert_reason r)) /\
  (!tops r. supported_raise_reason tops r ==>
    EVERY (\c. FST c = NONE ==>
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_raise_reason r))
Proof
  conj_tac >> rpt gen_tac >> Cases_on `r` >>
  simp[supported_assert_reason_def, supported_raise_reason_def,
       int_calls_assert_reason_def, int_calls_raise_reason_def,
       GSYM supported_pure_exprs_every] >>
  metis_tac[supported_pure_main_calls, supported_expr_main_calls,
            supported_string_reason_expr]
QED

Theorem supported_stmts_main_calls[local]:
  (!tops bindings s. supported_stmt tops bindings s ==>
    EVERY (\c. FST c = NONE ==>
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmt s)) /\
  (!tops bindings ss. supported_stmts tops bindings ss ==>
    EVERY (\c. FST c = NONE ==>
               IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts ss))
Proof
  ho_match_mp_tac supported_stmt_ind >>
  simp[supported_stmt_def, int_calls_stmt_def, int_calls_expr_def, EVERY_APPEND] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  imp_res_tac supported_assignment_def >>
  imp_res_tac supported_log_def >>
  imp_res_tac supported_pure_main_calls >>
  imp_res_tac supported_expr_main_calls >>
  imp_res_tac supported_assignment_main_calls >>
  imp_res_tac supported_base_target_main_calls >>
  imp_res_tac supported_append_target_main_calls >>
  imp_res_tac supported_iterator_main_calls >>
  imp_res_tac supported_reasons_main_calls >> gvs[]
QED

Theorem supported_stmt_body_safe:
  supported_stmt tops bindings s ==> body_stmt_safe tops s
Proof
  simp[body_stmt_safe_def, stmt_no_evm_run] >>
  metis_tac[supported_stmts_main_calls]
QED

Theorem supported_stmts_body_safe:
  supported_stmts tops bindings ss ==> body_stmts_safe tops ss
Proof
  simp[body_stmts_safe_iff, stmt_no_evm_run] >>
  metis_tac[supported_stmts_main_calls]
QED

(* The body expression precondition permits effects in call operands. *)
Theorem supported_expr_body_calls:
  !tops e. supported_expr tops e /\ EVERY (\c. FST c = NONE) (int_calls_expr e) ==>
    ~expr_has_evm_run e /\
    EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    EVERY (\c. IS_SOME (supported_function_decl tops c Internal))
      (int_calls_expr e)
Proof
  rpt strip_tac >>
  imp_res_tac supported_expr_no_evm_run >>
  drule supported_expr_main_calls >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem supported_string_reason_body_calls:
  !tops e. supported_string_reason tops e /\ EVERY (\c. FST c = NONE) (int_calls_expr e) ==>
    ~expr_has_evm_run e /\
    EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    EVERY (\c. IS_SOME (supported_function_decl tops c Internal))
      (int_calls_expr e)
Proof
  metis_tac[supported_string_reason_expr, supported_expr_body_calls]
QED

Theorem supported_stmts_main_calls_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es ==>
  (!bindings s ret env'. supported_stmt (main_module mods) bindings s /\
     type_stmt env ret s = SOME env' ==>
     EVERY (source_body_call_supported cx) (int_calls_stmt s)) /\
  (!bindings ss ret env'. supported_stmts (main_module mods) bindings ss /\
     type_stmts env ret ss = SOME env' ==>
     EVERY (source_body_call_supported cx) (int_calls_stmts ss))
Proof
  strip_tac >> conj_tac >> rpt strip_tac >>
  imp_res_tac supported_stmts_main_calls >>
  imp_res_tac type_stmt_int_calls_fn_sigs >>
  metis_tac[supported_body_calls_resolve]
QED

Theorem supported_expr_body_calls_mods:
  contract_inv mods exps ctx cenv cx /\ supported_expr (main_module mods) e /\
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e ==>
  ~expr_has_evm_run e /\ EVERY (source_body_call_supported cx) (int_calls_expr e)
Proof
  strip_tac >> drule_then assume_tac supported_expr_no_evm_run >>
  drule_then assume_tac supported_expr_main_calls >>
  drule_then assume_tac (cj 1 well_typed_int_calls_fn_sigs) >>
  simp[] >> metis_tac[supported_body_calls_resolve]
QED

(* A statement's expression meets the linked precondition. *)
Theorem stmt_expr_body_pre_mods:
  !mods cenv cx env e es calls.
    expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
    ~supported_expr_exists
       (\e. ~is_extcode e /\
             ~(byte_widths_expr e /\
                (array_slot_base cenv e \/ alloc_limits_expr cenv e))) e /\
    ~is_extcode e /\
    (~array_slot_base cenv e \/ alloc_limits_expr cenv e) /\
    ~supported_expr_exists (const_name_root_mods mods) e /\
    ~supported_expr_exists (unallocated_bare_global_root cenv env) e /\
    call_evaluation_safe cx (int_calls_expr e ++ calls) /\
    ~expr_has_evm_run e /\
    EVERY (source_body_call_supported cx)
      (int_calls_expr e) /\
    (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
       EXISTS (occurs_abi_decode_target target o SND) mods) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env_all_modules mods) target)) ==>
    expr_body_pre_mods mods cenv cx env e es
Proof
  rpt gen_tac >> strip_tac >>
  `byte_widths_expr e /\ (array_slot_base cenv e \/ alloc_limits_expr cenv e)` by
    (CCONTR_TAC >>
     qpat_x_assum `~supported_expr_exists (\e. ~is_extcode e /\ _) _` mp_tac >>
     simp[] >> irule supported_expr_exists_root >> metis_tac[]) >>
  `alloc_limits_expr cenv e` by metis_tac[] >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[call_evaluation_safe_append_left] >>
  simp[expr_body_pre_mods_def]
QED

Theorem stmt_expr_body_pre_main_mods:
  contract_inv mods exps ctx cenv cx /\
  supported_expr (main_module mods) e /\
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  ~supported_expr_exists
     (\e. ~is_extcode e /\
           ~(byte_widths_expr e /\
                (array_slot_base cenv e \/ alloc_limits_expr cenv e))) e /\
  ~is_extcode e /\
  (~array_slot_base cenv e \/ alloc_limits_expr cenv e) /\
  ~supported_expr_exists (const_name_root_mods mods) e /\
  ~supported_expr_exists (unallocated_bare_global_root cenv env) e /\
  call_evaluation_safe cx (int_calls_expr e ++ calls) /\
  (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
     occurs_abi_decode_target target (main_module mods)) ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac supported_expr_body_calls_mods >>
  drule_then assume_tac contract_inv_main_module >>
  drule_then assume_tac contract_inv_type_env >>
  qspecl_then [`mods`,`cenv`,`cx`,`env`,`e`,`es`,`calls`] mp_tac
    stmt_expr_body_pre_mods >>
  impl_tac
  >- (simp[EXISTS_MEM] >> rpt strip_tac >>
      qexists_tac `(NONE,main_module mods)` >> simp[] >>
      metis_tac[ALOOKUP_MEM]) >>
  simp[]
QED

(* A statement's expression meets expr_body_pre. *)
Theorem stmt_expr_body_pre:
  !cenv cx env e es calls.
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    ~supported_expr_exists
       (\e. ~is_extcode e /\
             ~(byte_widths_expr e /\
                (array_slot_base cenv e \/ alloc_limits_expr cenv e))) e /\
    ~is_extcode e /\
    (~array_slot_base cenv e \/ alloc_limits_expr cenv e) /\
    ~supported_expr_exists (const_name_root cx) e /\
    call_evaluation_safe cx (int_calls_expr e ++ calls) /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    (int_calls_expr e <> [] ==>
     ?tops. supported_program tops /\ get_module_code cx NONE = SOME tops /\
            EVERY (\c. IS_SOME (supported_function_decl tops c Internal))
              (int_calls_expr e)) /\
    (!target. supported_expr_exists
       (expr_abi_decode_target_root target) e ==>
       occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)) ==>
    expr_body_pre cenv cx env e es
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (source_body_call_supported cx)
     (int_calls_expr e)` by
    (Cases_on `int_calls_expr e` >- simp[] >>
     PairCases_on `h` >> gvs[EVERY_MEM, pairTheory.FORALL_PROD] >>
     rpt gen_tac >> strip_tac >> res_tac >>
     gvs[source_body_call_supported_def, supported_linked_callee_def] >>
     metis_tac[supported_program_module_headers]) >>
  simp[expr_body_pre_split_def] >>
  drule_all_then assume_tac expr_sim_inv_no_unallocated_bare_globals >>
  qspecl_then [`[(NONE,cx_tops cx)]`,`cenv`,`cx`,`env`,`e`,`es`,`calls`] mp_tac
    stmt_expr_body_pre_mods >>
  fs[expr_sim_inv_split_def, const_name_root_mods_singleton,
     vyperContextTheory.type_env_all_modules_def, vyperContextTheory.type_env_def,
     FUNION_FEMPTY_2]
QED

(* The same, from byte_widths_expr of every node and alloc_limits_expr of
   the root, as alloc_limits_stmt gives a declaration's value. *)
Theorem stmt_expr_body_pre_alloc:
  !cenv cx env e es calls.
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    ~supported_expr_exists (\e. ~is_extcode e /\ ~byte_widths_expr e) e /\
    alloc_limits_expr cenv e /\
    ~is_extcode e /\
    ~supported_expr_exists (const_name_root cx) e /\
    call_evaluation_safe cx (int_calls_expr e ++ calls) /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    (int_calls_expr e <> [] ==>
     ?tops. supported_program tops /\ get_module_code cx NONE = SOME tops /\
            EVERY (\c. IS_SOME (supported_function_decl tops c Internal))
              (int_calls_expr e)) /\
    (!target. supported_expr_exists
       (expr_abi_decode_target_root target) e ==>
       occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)) ==>
    expr_body_pre cenv cx env e es
Proof
  rpt gen_tac >> strip_tac >> irule_body_pre stmt_expr_body_pre >> simp[] >>
  reverse conj_tac >- (qexists_tac `calls` >> simp[]) >>
  `(\e. ~is_extcode e /\
         (~byte_widths_expr e \/ ~array_slot_base cenv e /\ ~alloc_limits_expr cenv e)) =
   (\e. (~is_extcode e /\ ~byte_widths_expr e) \/
        (~is_extcode e /\ ~array_slot_base cenv e /\ ~alloc_limits_expr cenv e))` by
    (simp[FUN_EQ_THM] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >> simp[supported_expr_exists_disj] >>
  imp_res_tac alloc_limits_expr_exists >> simp[]
QED

Theorem stmts_env_cs_mono:
  !cenv lctx ty ss. cs_mono (stmts_env cenv lctx ty ss)
Proof
  rw[cs_mono_def] >>
  `compile_stmts cenv lctx ty ss sa = ((), sb)` by simp[compile_stmts_env] >>
  qspecl_then [`cenv`, `lctx`, `ty`, `ss`] mp_tac (cj 2 compile_stmt_cs_mono) >>
  simp[cs_mono_def] >> disch_then drule >> simp[]
QED

Theorem stmt_env_declare:
  !cenv lctx ty s sa c sm.
    stmt_env cenv lctx ty s sa = (c, sm) ==>
    ?sm0. declare_stmt_local cenv s sa = (c, sm0)
Proof
  simp[stmt_env_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]
QED

Theorem declare_stmt_local_other:
  !cenv s sa c sm.
    ~(?id typ e. s = AnnAssign id typ e) /\
    declare_stmt_local cenv s sa = (c, sm) ==> c = cenv
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, comp_return_def]
QED

Theorem type_stmt_other:
  !env ret_ty s env'.
    ~(?id typ e. s = AnnAssign id typ e) /\
    type_stmt env ret_ty s = SOME env' ==> env' = env
Proof
  rpt gen_tac >> Cases_on `s` >> simp[] >>
  TRY (rename1 `Raise rs` >> Cases_on `rs`) >>
  TRY (rename1 `Assert _ ak` >> Cases_on `ak`) >>
  TRY (rename1 `Return eo` >> Cases_on `eo`) >>
  rw[type_stmt_def, AllCaseEqs()]
QED

Theorem same_frame_trans:
  !c1 c2 c3. same_frame c1 c2 /\ same_frame c2 c3 ==> same_frame c1 c3
Proof
  rw[same_frame_def] >> fs[compile_env_component_equality] >>
  Cases_on `FLOOKUP c2.ce_vars n = FLOOKUP c1.ce_vars n` >> gvs[] >>
  metis_tac[]
QED

Theorem same_frame_struct_fields:
  !cenv c. same_frame cenv c ==> c.ce_struct_fields = cenv.ce_struct_fields
Proof
  rw[same_frame_def] >> qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem body_inv_same_frame_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  same_frame cenv c ==>
  contract_inv mods exps ctx c cx /\ module_body_inv mods src tops c cx
Proof
  strip_tac >> drule_then (fn th => simp[th]) body_invariants_same_frame
QED

Theorem body_inv_same_frame:
  !tops ctx cenv c cx.
    body_inv tops ctx cenv cx /\ same_frame cenv c ==>
    body_inv tops ctx c cx
Proof
  simp[body_inv_split_def] >> rpt gen_tac >> strip_tac >>
  drule_then (fn th => simp[th]) body_invariants_same_frame
QED

Theorem frame_ret_ok_same_frame:
  !ctx func cx RetQ cenv c ret_ty.
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\ same_frame cenv c ==>
    frame_ret_ok ctx func cx RetQ c ret_ty
Proof
  rw[frame_ret_ok_def] >> first_x_assum irule >>
  metis_tac[same_frame_trans]
QED

Theorem stmt_exprs_ok_same_frame:
  !cenv c. same_frame cenv c /\ c.ce_var_type = cenv.ce_var_type ==>
           stmt_exprs_ok c = stmt_exprs_ok cenv
Proof
  rw[same_frame_def] >>
  `c.ce_struct_fields = cenv.ce_struct_fields /\
   c.ce_func_return_type = cenv.ce_func_return_type /\
   c.ce_modules = cenv.ce_modules /\
   c.ce_hashmap_info = cenv.ce_hashmap_info /\
   c.ce_module_var_type = cenv.ce_module_var_type /\
   c.ce_module_vars = cenv.ce_module_vars` by
    (qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  `alloc_limits_expr c = alloc_limits_expr cenv` by
    (rw[FUN_EQ_THM] >> irule (cj 1 alloc_limits_struct_fields) >> simp[]) >>
  `alloc_env_agree cenv c` by
    (qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >>
     simp[alloc_env_agree_def]) >>
  `alloc_limits_stmt c = alloc_limits_stmt cenv` by
    (rw[FUN_EQ_THM] >> irule (cj 1 alloc_limits_stmt_struct_fields) >>
     simp[]) >>
  `c.ce_is_external = cenv.ce_is_external /\
   c.ce_raw_return = cenv.ce_raw_return /\
   return_buffer_ok c = return_buffer_ok cenv` by
    (qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >>
     simp[return_buffer_ok_def]) >>
  simp[FUN_EQ_THM, stmt_exprs_ok_def]
QED

(* A statement's checks read the fields alloc_limits_stmt reads
   (alloc_env_agree) and the return buffer's. *)
Theorem stmt_exprs_ok_agree:
  !cenv c.
    alloc_env_agree cenv c /\ c.ce_is_external = cenv.ce_is_external /\
    c.ce_raw_return = cenv.ce_raw_return /\
    return_buffer_ok c = return_buffer_ok cenv ==>
    stmt_exprs_ok c = stmt_exprs_ok cenv
Proof
  rpt strip_tac >> simp[FUN_EQ_THM, stmt_exprs_ok_def] >>
  drule (cj 1 alloc_limits_stmt_struct_fields) >> fs[alloc_env_agree_def]
QED

Theorem return_buffer_ok_var_type[simp]:
  !cenv f.
    return_buffer_ok (cenv with ce_var_type updated_by f) = return_buffer_ok cenv
Proof
  simp[return_buffer_ok_def]
QED

Theorem decl_var_type_return_fields[simp]:
  !cenv s.
    (decl_var_type cenv s).ce_modules = cenv.ce_modules /\
    (decl_var_type cenv s).ce_is_external = cenv.ce_is_external /\
    (decl_var_type cenv s).ce_raw_return = cenv.ce_raw_return /\
    return_buffer_ok (decl_var_type cenv s) = return_buffer_ok cenv
Proof
  gen_tac >> Cases >> simp[decl_var_type_def, return_buffer_ok_def]
QED

Theorem stmts_exprs_ok_agree:
  !ss cenv c.
    alloc_env_agree cenv c /\ c.ce_is_external = cenv.ce_is_external /\
    c.ce_raw_return = cenv.ce_raw_return /\
    return_buffer_ok c = return_buffer_ok cenv ==>
    stmts_exprs_ok c ss = stmts_exprs_ok cenv ss
Proof
  Induct >> simp[stmts_exprs_ok_def] >> rpt strip_tac >>
  `stmt_exprs_ok c h = stmt_exprs_ok cenv h` by
    metis_tac[stmt_exprs_ok_agree] >>
  `stmts_exprs_ok (decl_var_type c h) ss =
   stmts_exprs_ok (decl_var_type cenv h) ss` by
    (first_x_assum irule >> gvs[alloc_env_agree_decl_var_type]) >>
  simp[]
QED

Theorem same_frame_alloc_env_agree:
  !cenv c.
    same_frame cenv c /\ c.ce_var_type = cenv.ce_var_type ==>
    alloc_env_agree cenv c /\ c.ce_is_external = cenv.ce_is_external /\
    c.ce_raw_return = cenv.ce_raw_return /\
    return_buffer_ok c = return_buffer_ok cenv
Proof
  rw[same_frame_def] >> qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >>
  simp[alloc_env_agree_def, return_buffer_ok_def]
QED

Theorem stmts_exprs_ok_same_frame:
  !cenv c. same_frame cenv c /\ c.ce_var_type = cenv.ce_var_type ==>
           stmts_exprs_ok c = stmts_exprs_ok cenv
Proof
  rpt strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  irule stmts_exprs_ok_agree >> metis_tac[same_frame_alloc_env_agree]
QED

Theorem same_frame_var_type:
  !cenv c f. same_frame cenv c ==>
             same_frame (cenv with ce_var_type updated_by f) c
Proof
  rw[same_frame_def] >> fs[compile_env_component_equality] >> metis_tac[]
QED

Theorem same_frame_decl_var_type:
  !cenv c s. same_frame cenv c ==> same_frame (decl_var_type cenv s) c
Proof
  ntac 2 gen_tac >> Cases >> simp[decl_var_type_def, same_frame_var_type]
QED

Theorem declare_local_var_type:
  !cenv id ty st c st1.
    declare_local cenv id ty st = (c, st1) ==>
    c.ce_var_type = (id =+ SOME ty) cenv.ce_var_type
Proof
  rw[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def,
     LET_THM] >> gvs[]
QED

(* A for body is checked under the loop variable's type, which the env
   declaring the loop variable has. *)
Theorem for_declare_stmts_exprs_ok:
  !cenv id ty st c st1 ss.
    declare_local cenv id ty st = (c, st1) /\ same_frame cenv c /\
    stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME ty)) ss ==>
    stmts_exprs_ok c ss
Proof
  rpt strip_tac >> drule declare_local_var_type >> strip_tac >>
  `stmts_exprs_ok c =
   stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME ty))` by
    (irule stmts_exprs_ok_same_frame >> simp[same_frame_var_type]) >>
  gvs[]
QED

(* A declaration's checks carry over to the env that declares its local:
   that env reads the value as the declared check does. *)
Theorem annassign_declare_exprs_ok:
  !cenv id ty e st c st1.
    declare_local cenv id ty st = (c, st1) /\ same_frame cenv c /\
    stmt_exprs_ok cenv (AnnAssign id ty e) ==>
    stmt_exprs_ok c (AnnAssign id ty e)
Proof
  rpt strip_tac >> drule declare_local_var_type >> strip_tac >>
  `c.ce_struct_fields = cenv.ce_struct_fields /\
   c.ce_func_return_type = cenv.ce_func_return_type /\
   c.ce_modules = cenv.ce_modules /\
   c.ce_hashmap_info = cenv.ce_hashmap_info /\
   c.ce_module_var_type = cenv.ce_module_var_type /\
   c.ce_module_vars = cenv.ce_module_vars` by
    (gvs[same_frame_def] >> qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >>
     simp[]) >>
  qabbrev_tac `X = cenv with ce_var_type updated_by (id =+ SOME ty)` >>
  `type_memory_bytes c = type_memory_bytes X /\
   alloc_limits_expr c = alloc_limits_expr X` by
    (qspecl_then [`X`, `c`] mp_tac alloc_limits_frame >>
     impl_tac >- gvs[Abbr`X`] >> simp[]) >>
  `alloc_limits_expr (c with ce_var_type updated_by (id =+ SOME ty)) =
   alloc_limits_expr X` by
    (qspecl_then [`X`, `c with ce_var_type updated_by (id =+ SOME ty)`]
       mp_tac alloc_limits_frame >>
     impl_tac >- gvs[Abbr`X`, combinTheory.UPDATE_EQ] >> simp[]) >>
  `type_memory_bytes X = type_memory_bytes cenv` by
    (irule type_memory_bytes_frame >> simp[Abbr`X`]) >>
  gvs[stmt_exprs_ok_def, alloc_limits_stmt_def, stmt_valued_return_def]
QED

(* After a statement the compile env has the local types decl_var_type
   gives, as compile_stmts threads them. *)
Theorem stmt_env_var_type:
  !cenv lctx ty s sa c sb.
    stmt_env cenv lctx ty s sa = (c, sb) ==>
    c.ce_var_type = (decl_var_type cenv s).ce_var_type
Proof
  rpt gen_tac >>
  simp[stmt_env_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `declare_stmt_local cenv s sa` >> rename1 `_ = (c0, sm)` >>
  simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `s` >>
  gvs[declare_stmt_local_def, comp_return_def, decl_var_type_def] >>
  metis_tac[declare_local_var_type]
QED

(* The rest of a block is checked under the local types the statement
   before it leaves. *)
Theorem stmt_env_stmts_exprs_ok:
  !cenv lctx ty s sa c sb.
    stmt_env cenv lctx ty s sa = (c, sb) /\ same_frame cenv c ==>
    stmts_exprs_ok c = stmts_exprs_ok (decl_var_type cenv s)
Proof
  rpt strip_tac >> irule stmts_exprs_ok_same_frame >>
  conj_tac >- metis_tac[stmt_env_var_type] >>
  metis_tac[same_frame_decl_var_type]
QED

(* A statement that holds no block checks every expression under cenv
   itself (alloc_limits_stmt_exists). *)
Theorem stmt_exprs_ok_flat:
  !cenv s.
    (!c ss1 ss2. s <> If c ss1 ss2) /\
    (!id ty it n body. s <> For id ty it n body) ==>
    (stmt_exprs_ok cenv s <=>
     ~supported_stmt_expr_exists
        (\e. ~is_extcode e /\
              ~(byte_widths_expr e /\
                (array_slot_base cenv e \/ alloc_limits_expr cenv e))) s /\
     alloc_limits_stmt cenv s /\
     (stmt_valued_return s /\ cenv.ce_is_external /\ ~cenv.ce_raw_return ==>
        return_buffer_ok cenv) /\
     ~supported_stmt_expr_exists (const_name_root_mods cenv.ce_modules) s /\
     qualified_stmt_decls_ok cenv.ce_modules s)
Proof
  rpt strip_tac >>
  `(\e. ~is_extcode e /\ ~(byte_widths_expr e /\
                (array_slot_base cenv e \/ alloc_limits_expr cenv e))) =
   (\e. (~is_extcode e /\ ~byte_widths_expr e) \/
        (~is_extcode e /\ ~array_slot_base cenv e /\ ~alloc_limits_expr cenv e))` by
    (simp[FUN_EQ_THM] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  simp[stmt_exprs_ok_def, supported_stmt_expr_exists_disj] >>
  metis_tac[alloc_limits_stmt_exists]
QED

Theorem stmts_exprs_ok_thm:
  !ss cenv.
    stmts_exprs_ok cenv ss <=>
    ~supported_stmts_expr_exists
       (\e. ~is_extcode e /\ ~byte_widths_expr e) ss /\
    alloc_limits_stmts cenv ss /\
    (stmts_valued_return ss /\ cenv.ce_is_external /\ ~cenv.ce_raw_return ==>
       return_buffer_ok cenv) /\
    ~supported_stmts_expr_exists (const_name_root_mods cenv.ce_modules) ss /\
    qualified_stmts_decls_ok cenv.ce_modules ss
Proof
  Induct >>
  simp[stmts_exprs_ok_def, supported_stmt_expr_exists_def, stmt_exprs_ok_def,
       alloc_limits_stmt_def, stmt_valued_return_def] >>
  metis_tac[]
QED

(* ===== The source state after a statement ===== *)

(* Evaluating a statement keeps popped_keys_indexed, as
   eval_expr_popped_keys_indexed shows for an expression: stmtPoppedKeys. *)
Theorem eval_stmts_popped_keys_indexed:
  (!cx s env ret_ty env' es res es'.
     type_stmt env ret_ty s = SOME env' /\
     runtime_consistent env cx es /\ functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmt s) /\
     eval_stmt cx s es = (res, es') /\
     popped_keys_indexed es.scopes ==>
     popped_keys_indexed es'.scopes) /\
  (!cx ss env ret_ty env' es res es'.
     type_stmts env ret_ty ss = SOME env' /\
     runtime_consistent env cx es /\ functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmts ss) /\
     eval_stmts cx ss es = (res, es') /\
     popped_keys_indexed es.scopes ==>
     popped_keys_indexed es'.scopes)
Proof
  metis_tac[cj 1 eval_statement_loop_popped_keys_indexed,
            cj 2 eval_statement_loop_popped_keys_indexed]
QED

(* The storage conjuncts of expr_sim_inv do not look at the scopes. *)
Theorem storage_conjs_scopes:
  !cx es f.
    contract_storage_well_formed cx es /\ oracle_storage_ok cx es ==>
    contract_storage_well_formed cx (es with scopes updated_by f) /\
    oracle_storage_ok cx (es with scopes updated_by f)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule vyperStorageLayoutSafetyTheory.contract_storage_well_formed_storage_frame >>
      qexists_tac `es` >> rw[] >> Cases_on `b` >>
      simp[vyperStorageBackendTheory.get_storage_def]) >>
  `(es with scopes updated_by f).outcomes = es.outcomes` by simp[] >>
  metis_tac[vyperTypeStoragePreservationTheory.oracle_storage_ok_outcomes]
QED

(* The scope of a loop's iteration: the loop variable, declared in the
   compile env and added to the type environment. *)
Theorem for_pushed_state_well_typed:
  !st tyv v id.
    state_well_typed st /\ value_has_type tyv v /\
    well_formed_type_value tyv ==>
    state_well_typed
      (st with scopes updated_by
         CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                                popped := []|>)))
Proof
  rw[state_well_typed_def, scope_well_typed_def, FLOOKUP_UPDATE]
QED

Theorem for_pushed_popped_keys[local]:
  !scs id tyv v.
    popped_keys_indexed scs ==>
    popped_keys_indexed
      (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                        popped := []|>) :: scs)
Proof
  rw[popped_keys_indexed_def, FLOOKUP_UPDATE] >> gvs[]
QED

Theorem scopes_CONS_updated:
  !es x. es with scopes := x :: es.scopes = es with scopes updated_by CONS x
Proof
  simp[evaluation_state_component_equality]
QED

Theorem expr_sim_inv_for_scope:
  !cenv cx env es id fty tyv v st c st1.
    expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ value_has_type tyv v /\
    declare_local cenv id fty st = (c, st1) /\ cenv.ce_alloca_locals ==>
    expr_sim_inv c cx (extend_local env id fty F)
      (es with scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                           popped := []|>)) :: es.scopes)
Proof
  rpt strip_tac >> REWRITE_TAC [scopes_CONS_updated] >>
  `env_consistent (extend_local env id fty F) cx
     (es with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                               popped := []|>)))` by
    (irule push_scope_with_var_env_consistent >> fs[expr_sim_inv_def]) >>
  `well_formed_type_value tyv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  qpat_x_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  drule_all for_pushed_state_well_typed >>
  disch_then (qspec_then `id` assume_tac) >>
  `popped_keys_indexed
     (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                       popped := []|>) :: es.scopes)` by
    simp[for_pushed_popped_keys] >>
  drule_all declare_local_ptr >> strip_tac >>
  `c.ce_var_type = (id =+ SOME fty) cenv.ce_var_type` by
    (qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >>
     simp[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def,
          LET_THM] >> strip_tac >> gvs[]) >>
  `!n ty. FLOOKUP (extend_local env id fty F).var_types n = SOME ty ==>
          ?p sz. FLOOKUP c.ce_vars n = SOME (PtrVar (Var p) sz)` by
    (rpt gen_tac >> Cases_on `n = id` >>
     simp[extend_local_def, FLOOKUP_UPDATE, combinTheory.C_THM] >>
     metis_tac[]) >>
  `!n ty. FLOOKUP (extend_local env id fty F).var_types n = SOME ty ==>
          c.ce_var_type n = SOME ty` by
    (rpt gen_tac >> Cases_on `n = id` >>
     simp[extend_local_def, FLOOKUP_UPDATE, combinTheory.C_THM,
          combinTheory.APPLY_UPDATE_THM]) >>
  qpat_x_assum
    `_ with <| ce_vars := _; ce_var_type := _;
               ce_dynarray_capacity := _ |> = cenv`
    (strip_assume_tac o
     SIMP_RULE (srw_ss()) [compile_env_component_equality]) >>
  `(place_map_tables_agree_on_defined c (extend_local env id fty F) <=>
    place_map_tables_agree_on_defined cenv env) /\
   (extend_local env id fty F).bare_globals = env.bare_globals` by
    (conj_tac >- (irule placeTypingPropsTheory.place_map_tables_agree_on_defined_cong >> fs[extend_local_def]) >>
     simp[extend_local_def]) >>
  ASM_REWRITE_TAC [expr_sim_inv_def] >> simp[] >>
  gvs[extend_local_def] >> first_assum ACCEPT_TAC
QED

(* After an iteration that goes on (a normal end or a continue), with the
   loop variable's scope popped, expr_sim_inv holds again at the loop's
   compile and type environments: the type soundness of the body, and
   vyperTypeEvalSoundness's for_body_env_consistent_after_pop. *)
Theorem expr_sim_inv_for_pop:
  !cenv cx env es id fty tyv v ret_ty body env_b r2 es2 sc rest tops
   bindings.
    expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ value_has_type tyv v /\
    type_stmts (extend_local env id fty F) ret_ty body = SOME env_b /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    eval_stmts cx body
      (es with scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                           popped := []|>)) :: es.scopes) = (r2, es2) /\
    (r2 = INL () \/ r2 = INR ContinueException) /\
    es2.scopes = sc :: rest /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    supported_stmts tops bindings body ==>
    expr_sim_inv cenv cx env (es2 with scopes := rest)
Proof
  rpt gen_tac >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  RULE_ASSUM_TAC (REWRITE_RULE [scopes_CONS_updated]) >>
  `env_consistent (extend_local env id fty F) cx
     (es with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                               popped := []|>)))` by
    (irule push_scope_with_var_env_consistent >> fs[expr_sim_inv_def]) >>
  `well_formed_type_value tyv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  qpat_x_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  drule_all for_pushed_state_well_typed >>
  disch_then (qspec_then `id` assume_tac) >>
  `accounts_well_typed
     (es with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                               popped := []|>))).accounts` by simp[] >>
  drule_all (cj 2 eval_scc_type_sound_mutual) >> strip_tac >>
  `env_maps_wf env` by metis_tac[env_consistent_env_maps_wf] >>
  `env_consistent env cx (es2 with scopes := TL es2.scopes)` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC >>
     qpat_x_assum `sum_CASE _ _ _` mp_tac >> simp_tac (srw_ss()) [] >>
     strip_tac
     >- (irule for_body_env_consistent_after_pop >> metis_tac[]) >>
     irule for_body_env_extends_consistent_after_pop >> metis_tac[]) >>
  `state_well_typed (es2 with scopes := TL es2.scopes)` by
    (irule scope_bracket_preserves_swt >> metis_tac[]) >>
  `outcomes_accounts_typed es2.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 2 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >>
     gvs[outcomes_accounts_typed_def]) >>
  `popped_keys_indexed es2.scopes` by
    (`runtime_consistent (extend_local env id fty F) cx
        (es with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                                 popped := []|>)))` by
       simp[runtime_consistent_def] >>
     `popped_keys_indexed
        (es with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                                 popped := []|>))).scopes` by
       simp[for_pushed_popped_keys] >>
     drule_all (cj 2 eval_stmts_popped_keys_indexed) >> simp[]) >>
  `popped_keys_indexed rest` by gvs[popped_keys_indexed_def] >>
  `IS_SOME es2.outcomes` by
    (drule (cj 2 eval_outcome_suffix_mutual) >>
     rw[outcome_suffix_def] >> gvs[]) >>
  qpat_x_assum `es2.scopes = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  RULE_ASSUM_TAC (REWRITE_RULE [TL]) >>
  ASM_REWRITE_TAC [expr_sim_inv_def] >> simp[]
QED

Theorem expr_sim_inv_push_scope:
  !cenv cx env es.
    expr_sim_inv cenv cx env es ==>
    expr_sim_inv cenv cx env (es with scopes := FEMPTY :: es.scopes)
Proof
  rpt strip_tac >>
  `es with scopes := FEMPTY :: es.scopes =
   es with scopes updated_by CONS FEMPTY` by
    simp[evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  `env_consistent env cx (es with scopes updated_by CONS FEMPTY)` by
    (irule push_scope_env_consistent >> simp[]) >>
  `state_well_typed (es with scopes updated_by CONS FEMPTY)` by
    fs[state_well_typed_def, scope_well_typed_def] >>
  `popped_keys_indexed (es with scopes updated_by CONS FEMPTY).scopes` by
    fs[popped_keys_indexed_def] >>
  ASM_REWRITE_TAC [expr_sim_inv_def] >> simp[]
QED

(* After a statement that completes, expr_sim_inv holds at the type
   environment its typing gives and the compile environment its
   declaration gives. *)
Theorem expr_sim_inv_stmt:
  !tops bindings cenv cx env ret_ty s env' es es1 lctx sa c sm.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    supported_stmt tops bindings s /\
    expr_sim_inv cenv cx env es /\ cenv.ce_alloca_locals /\
    type_stmt env ret_ty s = SOME env' /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    eval_stmt cx s es = (INL (), es1) /\
    stmt_env cenv lctx ret_ty s sa = (c, sm) ==>
    expr_sim_inv c cx env' es1
Proof
  rpt strip_tac >>
  `IS_SOME es1.outcomes` by
    (drule (cj 1 eval_outcome_suffix_mutual) >>
     rw[outcome_suffix_def] >> fs[expr_sim_inv_def]) >>
  drule stmt_env_declare >> strip_tac >>
  qspecl_then [`cx`, `s`, `env`, `ret_ty`, `env'`, `es`, `INL ()`, `es1`]
    mp_tac (cj 1 eval_scc_type_sound_mutual) >>
  impl_tac >- fs[expr_sim_inv_def] >> simp[] >> strip_tac >>
  `outcomes_accounts_typed es1.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 1 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >>
     gvs[expr_sim_inv_def, outcomes_accounts_typed_def]) >>
  `popped_keys_indexed es1.scopes` by
    (`runtime_consistent env cx es` by
       fs[expr_sim_inv_def, runtime_consistent_def] >>
     fs[expr_sim_inv_def] >>
     drule_all (cj 1 eval_stmts_popped_keys_indexed) >> simp[]) >>
  Cases_on `?id typ e. s = AnnAssign id typ e`
  >- (gvs[type_stmt_def, declare_stmt_local_def] >>
      drule_all declare_local_ptr >> strip_tac >>
      `c.ce_var_type = (id =+ SOME typ) cenv.ce_var_type` by
        (qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >> strip_tac >>
         gvs[declare_local_def, fresh_var_def, comp_bind_def,
             comp_return_def, LET_THM]) >>
      `!n ty. FLOOKUP (extend_local env id typ T).var_types n = SOME ty ==>
              ?p sz. FLOOKUP c.ce_vars n = SOME (PtrVar (Var p) sz)` by
        (rpt gen_tac >> Cases_on `n = id` >>
         simp[extend_local_def, FLOOKUP_UPDATE, combinTheory.C_THM] >>
         strip_tac >> fs[expr_sim_inv_def] >> metis_tac[]) >>
      `!n ty. FLOOKUP (extend_local env id typ T).var_types n = SOME ty ==>
              c.ce_var_type n = SOME ty` by
        (rpt gen_tac >> Cases_on `n = id` >>
         simp[extend_local_def, FLOOKUP_UPDATE, combinTheory.C_THM,
              combinTheory.APPLY_UPDATE_THM] >>
         fs[expr_sim_inv_def]) >>
      qpat_x_assum
        `_ with <| ce_vars := _; ce_var_type := _;
                   ce_dynarray_capacity := _ |> = cenv`
        (strip_assume_tac o
         SIMP_RULE (srw_ss()) [compile_env_component_equality]) >>
      `(place_map_tables_agree_on_defined c (extend_local env id typ T) <=>
        place_map_tables_agree_on_defined cenv env) /\
       (extend_local env id typ T).bare_globals = env.bare_globals /\
       (extend_local env id typ T).fn_sigs = env.fn_sigs` by
        (conj_tac >- (irule placeTypingPropsTheory.place_map_tables_agree_on_defined_cong >> fs[extend_local_def]) >>
         simp[extend_local_def]) >>
      qpat_x_assum `expr_sim_inv _ _ _ es`
        (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
      ASM_REWRITE_TAC [expr_sim_inv_def, extend_local_bare_globals]) >>
  drule_all declare_stmt_local_other >> strip_tac >>
  drule_all type_stmt_other >> strip_tac >> gvs[] >>
  qpat_x_assum `expr_sim_inv _ _ _ es`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  ASM_REWRITE_TAC [expr_sim_inv_def]
QED

(* A declaration keeps ce_locals_declared: it binds its name as the typing
   adds it. *)
Theorem ce_locals_declared_declare_local:
  !cenv env id ty st c st1 a.
    ce_locals_declared cenv env /\ declare_local cenv id ty st = (c, st1) ==>
    ce_locals_declared c (extend_local env id ty a)
Proof
  rpt gen_tac >> strip_tac >>
  `!n. n <> id ==> FLOOKUP c.ce_vars n = FLOOKUP cenv.ce_vars n` by
    (qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >>
     rw[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def,
        LET_THM] >> simp[FLOOKUP_UPDATE]) >>
  fs[ce_locals_declared_def, extend_local_def, combinTheory.C_THM] >>
  rpt strip_tac >> Cases_on `n = id` >> simp[] >> metis_tac[]
QED

(* After a statement, ce_locals_declared holds at the type environment its
   typing gives and the compile environment its declaration gives. *)
Theorem ce_locals_declared_stmt:
  !cenv env ret_ty s env' lctx sa c sm.
    ce_locals_declared cenv env /\ type_stmt env ret_ty s = SOME env' /\
    stmt_env cenv lctx ret_ty s sa = (c, sm) ==>
    ce_locals_declared c env'
Proof
  rpt strip_tac >> drule stmt_env_declare >> strip_tac >>
  Cases_on `?id typ e. s = AnnAssign id typ e`
  >- (gvs[type_stmt_def, declare_stmt_local_def] >>
      irule ce_locals_declared_declare_local >> metis_tac[]) >>
  drule_all declare_stmt_local_other >> strip_tac >>
  drule_all type_stmt_other >> strip_tac >> gvs[]
QED

(* A local declared at a type below the limit keeps locals_alloc_ok, in a
   compile env with the same struct sizes. *)
Theorem locals_alloc_ok_extend:
  !cenv c env id ty a.
    locals_alloc_ok cenv env /\ type_memory_bytes cenv ty < 2 ** 64 /\
    c.ce_struct_fields = cenv.ce_struct_fields ==>
    locals_alloc_ok c (extend_local env id ty a)
Proof
  rw[locals_alloc_ok_def, extend_local_def, combinTheory.C_THM,
     FLOOKUP_UPDATE] >>
  drule_then assume_tac type_memory_bytes_frame >>
  gvs[locals_alloc_ok_def, AllCaseEqs()] >> metis_tac[]
QED

(* After a statement, locals_alloc_ok holds at the type environment its
   typing gives and the compile environment its declaration gives: a
   declaration's type is below the limit by alloc_limits_stmt. *)
Theorem locals_alloc_ok_stmt:
  !cenv env ret_ty s env' lctx sa c sm.
    locals_alloc_ok cenv env /\ stmt_exprs_ok cenv s /\
    type_stmt env ret_ty s = SOME env' /\
    stmt_env cenv lctx ret_ty s sa = (c, sm) ==>
    locals_alloc_ok c env'
Proof
  rpt strip_tac >> drule stmt_env_declare >> strip_tac >>
  Cases_on `?id typ e. s = AnnAssign id typ e`
  >- (gvs[type_stmt_def, declare_stmt_local_def, AllCaseEqs()] >>
      `c.ce_struct_fields = cenv.ce_struct_fields` by
        (qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >>
         rw[declare_local_def, fresh_var_def, comp_bind_def,
            comp_return_def, LET_THM] >> simp[]) >>
      irule locals_alloc_ok_extend >> qexists_tac `cenv` >>
      gvs[stmt_exprs_ok_def, alloc_limits_stmt_def]) >>
  drule_all declare_stmt_local_other >> strip_tac >>
  drule_all type_stmt_other >> strip_tac >> gvs[]
QED
