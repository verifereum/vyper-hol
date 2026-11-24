(* Static and compiler boundaries for the full Range body case. *)
Theory bodyFullForRange
Ancestors exprSimWordArgs[qualified,ignore_grammar] vyperLookup[qualified,ignore_grammar] vyperTypeEnvPreservation[qualified,ignore_grammar] vyperPlaceResultTyping[qualified,ignore_grammar]
  bodyFullShadowBodyInv bodyInvSplit bodyInvExecutionProps bodyInvCodeProps forConsBodyGas[qualified,ignore_grammar]
  bodyFullPreds bodyFullForFacts bodySimDeclCases bodySim bodyExprPreFacts
  stmtSimForParts stmtSimForRange exprLoweringProps freshWrites
  loweringStateRelDefs loweringPosts stmtLowering compileEnv
  supportedStmts supportedStmtTraverse supportedExprTraverse
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperInterpreter vyperState vyperAST gasShadow
  ASCIInumbers integer list finite_map pred_set
  stmtSimDefs venomMemDefs valueEncodingProps ptrDiscipline
  venomState words stateRelProj
  augAssignPtrScalarCertificate fragExecMem instMemFrontier memSafeRun
  venomInst venomExecSemantics emitHelperProps slotCopyExecution
  stmtSimDeclStore localPtrsProps wordLoadStorePtr bodyPtrDefs
  loweringSlice valueEncoding bodyPtrEnvBuiltinsSelectorBuffer
  decoderNavigationPtr fragGasSeqPtr fragGasOriginPtrLoop bodyFullGhostFrame
  venomInstProps venomExecProofs acBaseProofs augAssignPtrScalarSafety
  unitTransformDefs contextCodegenRel codegenRel
  stmtSimForLoop fragGasOriginPtr fragGasOrigin fragGasPathPtr
  ptrSafeRun exprPtrUnwrapCopyEdges venomExecProps venomInstProofs
  memLocDefs integer_word
  bodyPtrBopInLoopSearch bodyMemAssignTopCopyPaths fragExec
  rich_list ghostPcTransportPtr instIdxIndep
  gasOutcomeFullCompose gasOutcomeFull gasExemptCert gasSummary
  vyperStorageTrace vyperStorageFootprint
  fragGasPathMem exprPtrUnwrapCondition bodyMemoryDefs
  gasCount gasEvents stmtSimProps gasShadowStmtEnv gasShadowState
  augAssignPtrScalarRun fragGasCopyLoop fragGasCopySeqLiftProps
  vyperEvalPreservesScopes[qualified,ignore_grammar]
  stmtSimForArrayLoop[qualified,ignore_grammar]
  bodyFullShared[qualified,ignore_grammar]
  bodyFullPathHistory[qualified,ignore_grammar]
  bodyFullBuiltinWordPowCompose[qualified,ignore_grammar]
  bodyFullIfExpReach[qualified,ignore_grammar]
  stmtSimDeclCompose[qualified,ignore_grammar] bodyFullForRounds

val _ = Parse.hide "body";

(* Declaration transports the three static body inputs at the pushed scope. *)
Theorem range_declared_scope_inputs:
  !cenv cx env es id typ e1 e2 n body ret_ty env' tyv v st bc st1.
    type_stmt env ret_ty (For id typ (Range e1 e2) n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ (Range e1 e2) n body) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
    cenv.ce_alloca_locals /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\ value_has_type tyv v /\
    declare_local cenv id typ st = (bc,st1) ==>
    expr_sim_inv bc cx (extend_local env id typ F)
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                          popped := []|>)) :: es.scopes) /\
    ce_locals_declared bc (extend_local env id typ F) /\
    locals_alloc_ok bc (extend_local env id typ F)
Proof
  rpt gen_tac >> strip_tac >>
  drule type_stmt_for_projection >> strip_tac >>
  conj_tac >- (drule_all expr_sim_inv_for_scope >> simp[]) >>
  conj_tac >- (drule_all ce_locals_declared_declare_local >> simp[]) >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    (qpat_x_assum `stmt_exprs_ok _ _` mp_tac >>
     simp[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def]) >>
  `bc.ce_struct_fields = cenv.ce_struct_fields` by
    (drule_all declare_local_ptr >> strip_tac >>
     qpat_x_assum `bc with <|ce_vars := _; ce_var_type := _;
                            ce_dynarray_capacity := _|> = cenv` mp_tac >>
     disch_then (mp_tac o AP_TERM ``\c. c.ce_struct_fields``) >> simp[]) >>
  drule_all locals_alloc_ok_extend >> simp[]
QED

(* Static contracts follow the actual declared environment; admissibility
   of old loop-name bindings follows from enclosing typing freshness. *)
Theorem range_body_static_transport_mods:
  !mods exps src tops ctx cenv cx bc id typ st st1 body env ret_ty
    DF lo d shadow_ctx PG func shadow_func RetQ.
    declare_local cenv id typ st = (bc,st1) /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) body /\
    IS_SOME (type_stmts (extend_local env id typ F) ret_ty body) /\
    frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx RetQ cenv ret_ty ==>
    same_frame cenv bc /\
    contract_inv mods exps ctx bc cx /\
    module_body_inv mods src tops bc cx /\
    stmts_exprs_ok bc body /\
    frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx RetQ bc ret_ty /\
    ?body_env'. type_stmts (extend_local env id typ F) ret_ty body = SOME body_env'
Proof
  rpt gen_tac >> strip_tac >>
  `cenv.ce_alloca_locals` by (drule contract_inv_alloca_locals >> simp[]) >>
  `same_frame cenv bc` by
    (drule declare_local_same_frame >> simp[]) >>
  drule_all body_inv_same_frame_mods >> strip_tac >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (drule_all for_declare_stmts_exprs_ok >> simp[]) >>
  reverse conj_tac >- gvs[optionTheory.IS_SOME_EXISTS] >>
  qpat_x_assum `frame_ret_ok_full _ _ _ _ _` mp_tac >>
  simp[bodySimFullTheory.frame_ret_ok_full_def] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[same_frame_trans]
QED

Theorem range_body_static_transport:
  !tops ctx cenv cx bc id typ st st1 body env ret_ty
    DF lo d shadow_ctx PG func shadow_func RetQ.
    declare_local cenv id typ st = (bc,st1) /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    body_inv tops ctx cenv cx /\
    stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) body /\
    IS_SOME (type_stmts (extend_local env id typ F) ret_ty body) /\
    frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx RetQ cenv ret_ty ==>
    same_frame cenv bc /\
    body_inv tops ctx bc cx /\
    stmts_exprs_ok bc body /\
    frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx RetQ bc ret_ty /\
    ?body_env'. type_stmts (extend_local env id typ F) ret_ty body = SOME body_env'
Proof
  rpt gen_tac >> strip_tac >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac body_inv_module >>
  drule_all range_body_static_transport_mods >> strip_tac >>
  drule_all body_inv_same_frame >> simp[]
QED

Theorem range_full_body_ih:
  !cx tyv id body n1 N.
    body_for_full_ok cx tyv id body
      (GENLIST (\j. Value (IntV (n1 + &j))) N) /\ 0 < N ==>
    body_stmts_full_ok cx body
Proof
  rpt gen_tac >> Cases_on `N` >> simp[GENLIST_CONS, body_for_full_ok_def,
    read_result_def, return_def]
QED

Theorem range_full_outer_env:
  (stmt_env cenv lctx ret_ty (For id typ (Range e1 e2) n body) sa =
     (cenv', sb) <=>
   cenv' = cenv /\
   compile_stmt cenv lctx ret_ty (For id typ (Range e1 e2) n body) sa =
     ((), sb)) /\
  (stmt_env (gas_shadow_env T cenv) lctx ret_ty
     (gas_shadow_stmt (For id typ (Range e1 e2) n body)) ssa = (scenv', ssb) <=>
   scenv' = gas_shadow_env T cenv /\
   compile_stmt (gas_shadow_env T cenv) lctx ret_ty
     (For id typ (Range (gas_shadow_expr e1) (gas_shadow_expr e2)) n
       (MAP gas_shadow_stmt body)) ssa = ((), ssb))
Proof
  simp[stmt_env_def, declare_stmt_local_def, gas_shadow_stmt_def,
       gas_shadow_iterator_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt conj_tac >> pairarg_tac >> simp[EQ_SYM_EQ]
QED

(* Finite projections at exactly the enclosing For; no source invariant is
   strengthened here. Endpoint support remains in its literal/checked gate. *)
Theorem range_full_static_pre:
  supported_stmt tops bindings (For id typ (Range e1 e2) n body) /\
  type_stmt env ret_ty (For id typ (Range e1 e2) n body) = SOME env' /\
  stmt_exprs_ok cenv (For id typ (Range e1 e2) n body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (For id typ (Range e1 e2) n body) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Range e1 e2) n body)) ==>
  env' = env /\ assignable_type env.type_defs typ /\ is_int_type typ /\
  well_typed_expr env e1 /\ well_typed_expr env e2 /\
  expr_type e1 = typ /\ expr_type e2 = typ /\
  expr_writes_ok (\_. F) e1 /\ expr_writes_ok (\_. F) e2 /\
  expr_static_calls e1 /\ expr_static_calls e2 /\
  id NOTIN FDOM env.var_types /\
  IS_SOME (type_stmts (extend_local env id typ F) ret_ty body) /\
  supported_type_namespace typ /\ supported_iterator tops typ (Range e1 e2) n /\
  supported_stmts tops bindings body /\
  stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) body /\
  type_memory_bytes cenv typ < 2 ** 64 /\
  alloc_limits_expr cenv e1 /\ alloc_limits_expr cenv e2 /\
  ~supported_expr_exists (\e. ~is_extcode e /\ ~byte_widths_expr e) e1 /\
  ~supported_expr_exists (\e. ~is_extcode e /\ ~byte_widths_expr e) e2 /\
  (!target. supported_expr_exists (expr_abi_decode_target_root target) e1 ==>
      occurs_abi_decode_target target tops) /\
  (!target. supported_expr_exists (expr_abi_decode_target_root target) e2 ==>
      occurs_abi_decode_target target tops) /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
      occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_expr e1) /\
  call_evaluation_safe cx (int_calls_expr e2) /\
  call_evaluation_safe cx (int_calls_stmts body)
Proof
  strip_tac >>
  drule type_stmt_for_projection >> strip_tac >>
  drule supported_stmt_for_projection >> strip_tac >>
  drule supported_loop_body_contract >> strip_tac >>
  drule body_for_exprs_ok >> strip_tac >>
  gvs[well_typed_iterator_def] >>
  qpat_x_assum `stmt_exprs_ok _ _` mp_tac >>
  simp[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       supported_iterator_exists_def, allocLimitsTheory.alloc_limits_stmt_def,
       allocLimitsTheory.alloc_limits_iterator_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[int_calls_stmt_def, int_calls_iterator_def] >> strip_tac >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  gvs[supported_stmt_expr_exists_def, supported_iterator_exists_def] >>
  `supported_type_namespace (expr_type e1)` by
    (qpat_assum `is_int_type (expr_type e1)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `expr_type e1` >>
     simp[is_int_type_def, supported_type_namespace_def]) >>
  metis_tac[call_evaluation_safe_append_left]
QED

(* The original iterator supplies the body IH; the current cons call supplies
   admissibility at this iteration's actual source scope. *)
Theorem range_cons_source_pre:
  !cx id typ e1 e2 bound body tops bindings cenv env env' ret_ty
    tyv n1 N k a rs es lctx exit_lbl incr_lbl.
    supported_stmt tops bindings (For id typ (Range e1 e2) bound body) /\
    type_stmt env ret_ty (For id typ (Range e1 e2) bound body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ (Range e1 e2) bound body) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (For id typ (Range e1 e2) bound body) ==>
       occurs_abi_decode_target target tops) /\
    call_evaluation_safe cx
      (int_calls_stmt (For id typ (Range e1 e2) bound body)) /\
    body_for_full_ok cx tyv id body
      (GENLIST (\j. Value (IntV (n1 + &j))) N) /\
    k + LENGTH (a::rs) = N /\
    a::rs = GENLIST (\j. Value (IntV (n1 + &(k+j)))) (LENGTH (a::rs)) /\
    lookup_scopes id es.scopes = NONE /\
    gas_admissible (eval_for cx tyv id body (a::rs)) (stmt_res_ok lctx) es
    ==>
    a = Value (IntV (n1 + &k)) /\ k < N /\
    body_stmts_full_ok cx body /\
    (?body_env'. type_stmts (extend_local env id typ F) ret_ty body =
                  SOME body_env') /\
    id NOTIN FDOM env.var_types /\
    supported_stmts tops bindings body /\
    stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) body /\
    (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target)
       body ==> occurs_abi_decode_target target tops) /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    gas_admissible (eval_stmts cx body)
      (stmt_res_ok (InLoop exit_lbl incr_lbl))
      (es with <|scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tyv;
                            value := IntV (n1 + &k); popped := []|>)) :: es.scopes;
                  gas_obs := []|>)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all range_full_static_pre >> strip_tac >>
  `a = Value (IntV (n1 + &k))` by
    (qpat_x_assum `a::rs = _` mp_tac >> simp[GENLIST_CONS]) >>
  `k < N /\ 0 < N` by gvs[] >>
  drule_all range_full_body_ih >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  irule forConsBodyGasTheory.captured_storage_body_admissible >>
  simp[] >> qexistsl [`Value (IntV (n1 + &k))`, `lctx`, `stmt_res_ok lctx`, `rs`] >>
  simp[read_result_def, return_def]
QED

(* Enriched elimination interfaces for the two actual compiler shapes. The
   original code equations are retained, together with ages at body entry.
   Source and shadow compiler states are deliberately independent. *)
Theorem range_full_compiler_geometry:
  (!cenv lctx ty id fty a1 n1 a2 n2 bound stmts sa cenv' sb
       ssa scenv' ssb func.
    stmt_env cenv lctx ty
      (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
        bound stmts) sa = (cenv', sb) /\
    stmt_env (gas_shadow_env T cenv) lctx ty
      (gas_shadow_stmt
        (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
          bound stmts)) ssa = (scenv', ssb) /\
    cenv.ce_alloca_locals /\ fn_has_code sa sb func /\
    (!c lc s t. compile_stmts c lc ty stmts s = ((), t) ==> cs_extends s t) ==>
    cenv' = cenv /\ scenv' = gas_shadow_env T cenv /\
    compile_stmt (gas_shadow_env T cenv) lctx ty
      (For id fty
        (Range (gas_shadow_expr (Literal a1 (IntL n1)))
               (gas_shadow_expr (Literal a2 (IntL n2))))
        bound (MAP gas_shadow_stmt stmts)) ssa = ((), ssb) /\
    ?p cv ev dv entry_lbl cond_lbl body_lbl incr_lbl exit_lbl bc sb0 sb1 sj nv.
      p = STRING #"%" (toString sa.cs_next_var) /\
      cv = STRING #"%" (toString (sa.cs_next_var + 1)) /\
      ev = STRING #"%" (toString (sa.cs_next_var + 2)) /\
      dv = STRING #"%" (toString (sa.cs_next_var + 3)) /\
      entry_lbl = fresh_label_output "for_entry" sa.cs_next_label /\
      cond_lbl = fresh_label_output "for_cond" (sa.cs_next_label + 1) /\
      body_lbl = fresh_label_output "for_body" (sa.cs_next_label + 2) /\
      incr_lbl = fresh_label_output "for_incr" (sa.cs_next_label + 3) /\
      exit_lbl = fresh_label_output "for_exit" (sa.cs_next_label + 4) /\
      declare_local cenv id fty sa =
        (bc, sa with cs_next_var := sa.cs_next_var + 1) /\
      sb0.cs_current_bb = body_lbl /\
      sb0.cs_current_insts =
        [mk_inst (sa.cs_next_id + 7) MSTORE [Var p; Var cv] []] /\
      sb0.cs_next_var = sa.cs_next_var + 4 /\ cs_extends sa sb0 /\
      sa.cs_next_id <= sb0.cs_next_id /\
      compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((), sb1) /\
      fn_has_code sb0 sb1 func /\
      lookup_block sa.cs_current_bb func.fn_blocks =
        SOME <|bb_label := sa.cs_current_bb; bb_instructions :=
          sa.cs_current_insts ++
          [mk_inst sa.cs_next_id ALLOCA
             [Lit (n2w (type_memory_bytes cenv fty))] [p];
           mk_inst (sa.cs_next_id + 1) JMP [Label entry_lbl] []]|> /\
      lookup_block entry_lbl func.fn_blocks =
        SOME <|bb_label := entry_lbl; bb_instructions :=
          [mk_inst (sa.cs_next_id + 2) ASSIGN [Lit (i2w n1)] [cv];
           mk_inst (sa.cs_next_id + 3) ADD
             [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev];
           mk_inst (sa.cs_next_id + 4) JMP [Label cond_lbl] []]|> /\
      lookup_block cond_lbl func.fn_blocks =
        SOME <|bb_label := cond_lbl; bb_instructions :=
          [mk_inst (sa.cs_next_id + 5) EQ [Var cv; Var ev] [dv];
           mk_inst (sa.cs_next_id + 6) JNZ
             [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
      (?bbb. lookup_block body_lbl func.fn_blocks = SOME bbb /\
        get_instruction bbb 0 =
          SOME (mk_inst (sa.cs_next_id + 7) MSTORE [Var p; Var cv] [])) /\
      (~block_is_terminated sb1 ==>
        sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
        sj.cs_current_insts = sb1.cs_current_insts ++
          [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
        fn_has_code sb1 sj func) /\
      sj.cs_next_var = sb1.cs_next_var /\
      nv = STRING #"%" (toString sj.cs_next_var) /\
      lookup_block incr_lbl func.fn_blocks =
        SOME <|bb_label := incr_lbl; bb_instructions :=
          [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
           mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [cv];
           mk_inst (sj.cs_next_id + 2) JMP [Label cond_lbl] []]|> /\
      sb.cs_current_bb = exit_lbl /\ sb.cs_current_insts = [] /\
      not_fresh_at sb0 p /\ not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\
      sa.cs_next_var <= sb0.cs_next_var /\
      (!x. not_fresh_at sa x ==> not_fresh_at sb0 x)) /\
  (!cenv lctx ty id fty e1 e2 bound stmts sa cenv' sb ssa scenv' ssb
       op1 s1 op2 st func.
    stmt_env cenv lctx ty (For id fty (Range e1 e2) bound stmts) sa = (cenv', sb) /\
    stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (For id fty (Range e1 e2) bound stmts))
      ssa = (scenv', ssb) /\
    lower_value compile_expr cenv fty e1 sa = (op1, s1) /\
    lower_value compile_expr cenv fty e2 s1 = (op2, st) /\
    ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) /\
    cenv.ce_alloca_locals /\ fn_has_code sa sb func /\
    (!c lc s t. compile_stmts c lc ty stmts s = ((), t) ==> cs_extends s t) ==>
    cenv' = cenv /\ scenv' = gas_shadow_env T cenv /\
    compile_stmt (gas_shadow_env T cenv) lctx ty
      (For id fty (Range (gas_shadow_expr e1) (gas_shadow_expr e2)) bound
        (MAP gas_shadow_stmt stmts)) ssa = ((), ssb) /\
    ?p cv rv g1 z1 g2 z2 ev dv entry_lbl cond_lbl body_lbl incr_lbl exit_lbl
       bc sb0 sb1 sj nv.
      p = STRING #"%" (toString st.cs_next_var) /\
      cv = STRING #"%" (toString (st.cs_next_var + 1)) /\
      rv = STRING #"%" (toString (st.cs_next_var + 2)) /\
      g1 = STRING #"%" (toString (st.cs_next_var + 3)) /\
      z1 = STRING #"%" (toString (st.cs_next_var + 4)) /\
      g2 = STRING #"%" (toString (st.cs_next_var + 5)) /\
      z2 = STRING #"%" (toString (st.cs_next_var + 6)) /\
      ev = STRING #"%" (toString (st.cs_next_var + 7)) /\
      dv = STRING #"%" (toString (st.cs_next_var + 8)) /\
      entry_lbl = fresh_label_output "for_entry" st.cs_next_label /\
      cond_lbl = fresh_label_output "for_cond" (st.cs_next_label + 1) /\
      body_lbl = fresh_label_output "for_body" (st.cs_next_label + 2) /\
      incr_lbl = fresh_label_output "for_incr" (st.cs_next_label + 3) /\
      exit_lbl = fresh_label_output "for_exit" (st.cs_next_label + 4) /\
      declare_local cenv id fty st =
        (bc, st with cs_next_var := st.cs_next_var + 1) /\
      sb0.cs_current_bb = body_lbl /\
      sb0.cs_current_insts =
        [mk_inst (st.cs_next_id + 14) MSTORE [Var p; Var cv] []] /\
      sb0.cs_next_var = st.cs_next_var + 9 /\ cs_extends st sb0 /\
      st.cs_next_id <= sb0.cs_next_id /\
      compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((), sb1) /\
      fn_has_code sb0 sb1 func /\
      lookup_block st.cs_current_bb func.fn_blocks =
        SOME <|bb_label := st.cs_current_bb; bb_instructions :=
          st.cs_current_insts ++
          [mk_inst st.cs_next_id ALLOCA
             [Lit (n2w (type_memory_bytes cenv fty))] [p];
           mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] []]|> /\
      lookup_block entry_lbl func.fn_blocks =
        SOME <|bb_label := entry_lbl; bb_instructions :=
          [mk_inst (st.cs_next_id + 2) ASSIGN [op1] [cv];
           mk_inst (st.cs_next_id + 3) SUB [op2; op1] [rv];
           mk_inst (st.cs_next_id + 4)
             (if is_signed_type fty then SGT else GT) [op1; op2] [g1];
           mk_inst (st.cs_next_id + 5) ISZERO [Var g1] [z1];
           mk_inst (st.cs_next_id + 6) ASSERT [Var z1] [];
           mk_inst (st.cs_next_id + 7) GT [Var rv; Lit (n2w bound)] [g2];
           mk_inst (st.cs_next_id + 8) ISZERO [Var g2] [z2];
           mk_inst (st.cs_next_id + 9) ASSERT [Var z2] [];
           mk_inst (st.cs_next_id + 10) ADD [op1; Var rv] [ev];
           mk_inst (st.cs_next_id + 11) JMP [Label cond_lbl] []]|> /\
      lookup_block cond_lbl func.fn_blocks =
        SOME <|bb_label := cond_lbl; bb_instructions :=
          [mk_inst (st.cs_next_id + 12) EQ [Var cv; Var ev] [dv];
           mk_inst (st.cs_next_id + 13) JNZ
             [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
      (?bbb. lookup_block body_lbl func.fn_blocks = SOME bbb /\
        get_instruction bbb 0 =
          SOME (mk_inst (st.cs_next_id + 14) MSTORE [Var p; Var cv] [])) /\
      (~block_is_terminated sb1 ==>
        sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
        sj.cs_current_insts = sb1.cs_current_insts ++
          [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
        fn_has_code sb1 sj func) /\
      sj.cs_next_var = sb1.cs_next_var /\
      nv = STRING #"%" (toString sj.cs_next_var) /\
      lookup_block incr_lbl func.fn_blocks =
        SOME <|bb_label := incr_lbl; bb_instructions :=
          [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
           mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [cv];
           mk_inst (sj.cs_next_id + 2) JMP [Label cond_lbl] []]|> /\
      sb.cs_current_bb = exit_lbl /\ sb.cs_current_insts = [] /\ cs_extends st sb /\
      not_fresh_at sb0 p /\ not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\
      sa.cs_next_var <= sb0.cs_next_var /\ sa.cs_next_id <= sb0.cs_next_id /\
      (!x. not_fresh_at sa x ==> not_fresh_at sb0 x))
Proof
  conj_tac
  >- (rpt gen_tac >> simp[range_full_outer_env] >> strip_tac >>
      drule_all compile_for_range_lit_parts >>
      disch_then (qx_choosel_then
        [`p`, `cv`, `ev`, `dv`, `entry_lbl`, `cond_lbl`, `body_lbl`, `incr_lbl`,
         `exit_lbl`, `bc`, `sb0`, `sb1`, `sj`, `nv`] strip_assume_tac) >>
      simp[] >>
      qexistsl_tac [`sb0`, `sb1`, `sj`] >>
      gvs[not_fresh_at_def]) >>
  rpt gen_tac >> simp[range_full_outer_env] >> strip_tac >>
  imp_res_tac (cj 2 compile_expr_grows) >>
  `cs_extends sa st` by metis_tac[cs_extends_trans] >>
  drule_all (SRULE [] compile_stmt_for_range_checked) >> strip_tac >>
  `for_range_checked_code cenv lctx ty id fty bound stmts op1 op2 st = ((), sb)` by
    metis_tac[] >>
  drule_all for_range_checked_parts >>
  disch_then (qx_choosel_then
    [`p`, `cv`, `rv`, `g1`, `z1`, `g2`, `z2`, `ev`, `dv`, `entry_lbl`,
     `cond_lbl`, `body_lbl`, `incr_lbl`, `exit_lbl`, `bc`, `sb0`, `sb1`, `sj`, `nv`]
    strip_assume_tac) >>
  simp[] >>
  qexistsl_tac [`sb0`, `sb1`, `sj`] >>
  gvs[not_fresh_at_def] >> decide_tac
QED

(* ===== Joint finite round control ===== *)
Theorem range_full_increment_path:
  !ctx s lo func bb i1 cv nv i2 i3 cond_lbl w G tn D explicit PG.
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\ allocas_from lo s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst i1 ADD [Var cv;Lit 1w] [nv]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst i2 ASSIGN [Var nv] [cv]) /\
    get_instruction bb (SUC (SUC s.vs_inst_idx)) =
      SOME (mk_inst i3 JMP [Label cond_lbl] []) /\
    lookup_var cv s = SOME w /\ op_prov G (Var cv) = NONE /\
    op_taint tn (Var cv) = {} ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to cond_lbl (update_var cv (w+1w) (update_var nv (w+1w) s))),
       DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}),
       tn with t_var := tn.t_var |+ (nv,{}) |+ (cv,{}))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `a = mk_inst i1 ADD [Var cv;Lit 1w] [nv]` >>
  qabbrev_tac `b = mk_inst i2 ASSIGN [Var nv] [cv]` >>
  qabbrev_tac `u = update_var nv (w+1w) s` >>
  qabbrev_tac `v = update_var cv (w+1w) u` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {nv})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (nv,{})` >>
  qabbrev_tac `G2 = DRESTRICT G1 (COMPL {cv})` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (cv,{})` >>
  `step_inst_base a s = OK u /\ step_inst_base b u = OK v` by
    (simp[Abbr `a`, Abbr `b`, Abbr `u`, Abbr `v`,
      step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     gvs[lookup_var_def]) >>
  `isPREFIX [a;b] (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule topcopy_instruction_prefix >>
     simp[Abbr `a`, Abbr `b`] >>
     rpt strip_tac >> Cases_on `j` >> gvs[] >>
     Cases_on `n` >> gvs[arithmeticTheory.ADD1]) >>
  `inst_seq_ptr D 0 ctx func PG G tn [a;b] s G2 tn2` by
    suspend "checks" >>
  `run_inst_seq_mem_ok [a;b] s` by
    (simp[run_inst_seq_mem_ok_def] >>
     simp[Abbr `a`, Abbr `b`, mk_inst_def,
      inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_write_ranges_def, source_memory_read_ranges_def]) >>
  `run_inst_seq [a;b] s = OK v` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) [a;b]` by
    simp[Abbr `a`, Abbr `b`, mk_inst_def, is_terminator_def] >>
  `(ctx_has_dalloca ctx ==> !pre i post u'.
      [a;b] = pre ++ i::post /\ run_inst_seq pre s = OK u' ==>
      dalloca_no_wrap i u')` by
    (rpt strip_tac >>
     `MEM i [a;b]` by metis_tac[MEM_APPEND, MEM] >>
     fs[Abbr `a`, Abbr `b`, mk_inst_def]) >>
  drule_all run_inst_seq_origin_ptr_lift >>
  disch_then (qspecl_then [`explicit`] strip_assume_tac) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (v with vs_inst_idx := s.vs_inst_idx + 2,G2,tn2) []
     (OK (jump_to cond_lbl (v with vs_inst_idx := s.vs_inst_idx + 2)),G2,tn2)` by
    (`allocas_below_fmp (v with vs_inst_idx := s.vs_inst_idx + 2) = allocas_below_fmp s` by
       simp[Abbr `v`, Abbr `u`, update_var_def, allocas_below_fmp_def] >>
     irule jmp_origin_ptr_path >>
     gvs[Abbr `v`, Abbr `u`, update_var_def, allocas_from_def,
       arithmeticTheory.ADD1] >>
     metis_tac[]) >>
  fs[] >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >> simp[] >>
  disch_then drule >>
  simp[Abbr `v`, Abbr `u`, Abbr `G2`, Abbr `G1`, Abbr `tn2`, Abbr `tn1`,
    jump_to_def]
QED

Resume range_full_increment_path[checks]:
  simp[inst_seq_ptr_def] >>
  `ptr_inst_ok D 0 0 ctx func G tn a s` by
    (simp[Abbr `a`] >> irule membership_increment_check >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> gvs[op_taint_def, op_prov_def]) >>
     qexists_tac `w+1w` >> simp[Abbr `u`]) >>
  `step_prov PG G a u = G1 /\ step_taint a s u tn = tn1` by
    (simp[Abbr `a`, Abbr `u`, Abbr `G1`, Abbr `tn1`] >>
     irule membership_increment_ghost >> simp[]) >>
  `op_prov G1 (Var nv) = NONE /\ op_taint tn1 (Var nv) = {}` by
    simp[Abbr `G1`, Abbr `tn1`, op_prov_def, op_taint_def,
      FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  `step_inst_base b (u with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (`~is_terminator b.inst_opcode` by
       simp[Abbr `b`, mk_inst_def, is_terminator_def] >>
     simp[step_inst_inst_idx_indep, exec_result_map_def]) >>
  `allocas_below_fmp (u with vs_inst_idx := SUC s.vs_inst_idx) = allocas_below_fmp s` by
    simp[Abbr `u`, update_var_def, allocas_below_fmp_def] >>
  simp[] >> conj_tac
  >- (simp[Abbr `b`] >> irule membership_increment_check >>
      simp[] >> qexists_tac `w+1w` >> simp[Abbr `v`, update_var_def]) >>
  `step_prov PG G1 b v = G2 /\ step_taint b u v tn1 = tn2` by
    (simp[Abbr `b`, Abbr `v`, Abbr `G2`, Abbr `tn2`] >>
     irule membership_increment_ghost >> simp[]) >> simp[]
QED

Finalise range_full_increment_path

(* The increment writes only fresh registers; the original frame anchor stays
   fixed, including the separation from every live final local. *)
Theorem range_full_increment_frame:
  !H D lo d ctx func cenv cx e sa sb0 es0 s0 G0 tn0 s G tn cv nv ev p sz w endw
      cond_lbl.
    stmt_state_rel H ctx func cenv cx e s /\
    ghost_inv_at D lo d cenv cx e G tn s /\ local_ptrs_reserved cenv sa /\
    (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
    (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
    ~not_fresh_at sa cv /\ ~not_fresh_at sa nv /\ cv <> nv /\ p <> cv /\
    p <> nv /\ ev <> cv /\ ev <> nv /\ ~s.vs_halted /\ ret_pc_ok cenv sa s /\
    return_buf_frame d cenv sb0 s /\ lookup_var cv s = SOME w /\
    lookup_var ev s = SOME endw /\ op_prov G (Var ev) = NONE /\
    op_taint tn (Var ev) = {} /\ ptr_covers G tn p s sz /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x v.
       not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
       lookup_var x s = SOME v) /\
    (!aid b.
       FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es0 sa s0 cenv e s /\
    (!aid off z i.
       FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
       (!nm b z'.
          local_region cenv es0.scopes s0 nm b z' ==>
          off + z <= b \/ b + z' <= off) /\ off <= i /\ i < off + z /\
       i IN tn.t_mem ==>
       i IN tn0.t_mem) ==>
    stmt_state_rel H ctx func cenv cx e
      (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))) /\
    ghost_inv_at D lo d cenv cx e
      (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}))
      (tn with t_var := fmupdate cv {} (fmupdate nv {} tn.t_var))
      (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))) /\
    ret_pc_ok cenv sa
      (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))) /\
    return_buf_frame d cenv sb0
      (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))) /\
    (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))).
    vs_current_bb = cond_lbl /\
    (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))).
    vs_inst_idx = 0 /\
    ~(jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))).
    vs_halted /\
    lookup_var cv
      (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))) =
    SOME (w + 1w) /\
    lookup_var nv
      (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))) =
    SOME (w + 1w) /\
    lookup_var ev
      (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))) =
    SOME endw /\
    lookup_var p
      (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))) =
    lookup_var p s /\
    op_prov (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv})) (Var cv) = NONE /\
    op_taint (tn with t_var := fmupdate cv {} (fmupdate nv {} tn.t_var))
      (Var cv) = {} /\
    op_prov (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv})) (Var ev) = NONE /\
    op_taint (tn with t_var := fmupdate cv {} (fmupdate nv {} tn.t_var))
      (Var ev) = {} /\
    ptr_covers (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}))
      (tn with t_var := fmupdate cv {} (fmupdate nv {} tn.t_var)) p
      (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))) sz /\
    (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))).
    vs_memory = s.vs_memory /\
    (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))).
    vs_allocas = s.vs_allocas /\
    (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))).
    vs_alloca_next = s.vs_alloca_next /\
    (tn with t_var := fmupdate cv {} (fmupdate nv {} tn.t_var)).t_mem =
    tn.t_mem /\
    alloca_history func
      (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))) /\
    (ctx_has_dalloca ctx ==>
     allocas_below_fmp
       (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s)))) /\
    s0.vs_alloca_next <=
    (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))).
    vs_alloca_next /\
    (!x v.
       not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
       lookup_var x
         (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))) =
       SOME v) /\
    (!aid b.
       FLOOKUP s0.vs_allocas aid = SOME b ==>
       FLOOKUP
         (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))).
         vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
         FLOOKUP (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv})) x =
         FLOOKUP G0 x /\
         op_taint (tn with t_var := fmupdate cv {} (fmupdate nv {} tn.t_var))
           (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es0 sa s0 cenv e
      (jump_to cond_lbl (update_var cv (w + 1w) (update_var nv (w + 1w) s))) /\
    !aid off z i.
      FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
      (!nm b z'.
         local_region cenv es0.scopes s0 nm b z' ==>
         off + z <= b \/ b + z' <= off) /\ off <= i /\ i < off + z /\
      i IN (tn with t_var := fmupdate cv {} (fmupdate nv {} tn.t_var)).t_mem ==>
      i IN tn0.t_mem
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `ghost_inv_at _ _ _ _ _ _ G1 tn1 t` >>
  `not_local_ptr cenv e.scopes cv /\ not_local_ptr cenv e.scopes nv` by
    metis_tac[exprSimOperandsTheory.fresh_not_local_ptr] >>
  `!x. x <> cv /\ x <> nv ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
    op_taint tn1 (Var x) = op_taint tn (Var x)` by
    simp[Abbr `t`, Abbr `G1`, Abbr `tn1`, jump_to_def, update_var_def,
      lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
  `!x. not_fresh_at sa x ==> x <> cv /\ x <> nv` by metis_tac[] >>
  conj_tac >- suspend "relation" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "pc" >>
  conj_tac >- suspend "buffer" >>
  suspend "remaining"
QED

Resume range_full_increment_frame[remaining]:
  `ptr_covers G1 tn1 p t sz` by
    (fs[ptr_covers_def] >>
     simp[Abbr `t`, Abbr `G1`, Abbr `tn1`, jump_to_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]) >>
  `alloca_history func t` by
    (irule allocaHistoryTheory.alloca_history_jump >>
     simp[Abbr `t`, jump_to_def, update_var_def] >> qexists_tac `s` >> simp[]) >>
  `alloca_frame cenv es0 sa s0 cenv e t` by
    (simp[Abbr `t`] >> irule alloca_frame_same_state >>
     qexists_tac `update_var cv (w+1w) (update_var nv (w+1w) s)` >>
     simp[jump_to_def] >>
     irule alloca_frame_update_var >> simp[] >>
     irule alloca_frame_update_var >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G1 x = FLOOKUP G x /\
       op_taint tn1 (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  simp[Abbr `t`, Abbr `G1`, Abbr `tn1`, jump_to_def, update_var_def,
    lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_prov_def, op_taint_def] >>
  fs[op_prov_def, lookup_var_def, allocas_below_fmp_def] >> metis_tac[]
QED

Resume range_full_increment_frame[relation]:
  simp[Abbr `t`, stmt_state_rel_jump_to] >>
  irule stmt_state_rel_update_var >> simp[] >>
  irule stmt_state_rel_update_var >> simp[]
QED
Resume range_full_increment_frame[ghost]:
  irule ghost_inv_at_exterior_frame >>
  qexistsl_tac [`G`, `e`, `s`, `sa`, `tn`] >>
  simp[Abbr `t`, Abbr `tn1`, jump_to_def, update_var_def] >> metis_tac[]
QED
Resume range_full_increment_frame[pc]:
  fs[ret_pc_ok_def] >> rpt strip_tac >>
  `x <> cv /\ x <> nv` by metis_tac[] >> metis_tac[]
QED
Resume range_full_increment_frame[buffer]:
  Cases_on `d` >- fs[return_buf_frame_def] >>
  PairCases_on `x` >> fs[return_buf_frame_def] >>
  simp[Abbr `t`, jump_to_def, update_var_def]
QED
Finalise range_full_increment_frame

Theorem range_full_body_lands_path:
  !ctx func sb sj s res exit_lbl incr_lbl lo D explicit PG G tn.
    stmt_lands (InLoop exit_lbl incr_lbl) sb res s /\ ~s.vs_halted /\
    (res = INL () \/ res = INR BreakException \/ res = INR ContinueException) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
    (res = INL () ==> ~block_is_terminated sb) /\
    (~block_is_terminated sb ==>
      sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
      sj.cs_current_insts = sb.cs_current_insts ++
        [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\
      fn_has_code sb sj func) ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (if res = INL () then jump_to incr_lbl s else s),G,tn) /\
    (if res = INL () then jump_to incr_lbl s else s).vs_inst_idx = 0 /\
    (res = INR BreakException ==> s.vs_current_bb = exit_lbl) /\
    (res <> INR BreakException ==>
      (if res = INL () then jump_to incr_lbl s else s).vs_current_bb = incr_lbl)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `res = INL ()`
  >- (gvs[stmt_lands_def] >>
      reverse conj_tac >- simp[jump_to_def] >>
      drule_all fn_has_code_same_block >> strip_tac >>
      irule jmp_origin_ptr_path >> simp[] >>
      qexists_tac `sb.cs_next_id` >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[stmt_lands_def] >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED
(* The nil test uses the same concrete endpoint for every horizon. *)
Theorem range_full_nil_path[local]:
  eval_operand (Var cv) s = SOME w /\ eval_operand (Var ev) s = SOME w /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
  op_prov G (Var cv) = NONE /\ op_prov G (Var ev) = NONE /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst eid EQ [Var cv; Var ev] [dv]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst jid JNZ [Var dv; Label yes; Label no] []) /\
  u = update_var dv 1w s /\ v = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  G1 = step_prov PG G (mk_inst eid EQ [Var cv; Var ev] [dv]) u /\
  tn1 = step_taint (mk_inst eid EQ [Var cv; Var ev] [dv]) s u tn ==>
  gas_origin_ptr_path (D,lo,d,ctx,func,PG) (s,G,tn) []
    (OK (jump_to yes u),G1,tn1)
Proof
  strip_tac >>
  `step_inst_base (mk_inst eid EQ [Var cv; Var ev] [dv]) s = OK u` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, bool_to_word_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn (mk_inst eid EQ [Var cv; Var ev] [dv]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     conj_tac
     >- (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
     conj_tac >- metis_tac[] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     asm_rewrite_tac[update_var_def]) >>
  `gas_origin_ptr_edge (D,lo,d,ctx,func,PG) (s,G,tn) [] (OK v,G1,tn1)` by
    (drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`) straight_line_origin_ptr_edge >>
     simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def]) >>
  `gas_path_ptr_edge D lo ctx func PG G1 tn1 v 0 G1 tn1
    (OK (jump_to yes v))` by
    suspend "branch" >>
  `gas_origin_ptr_edge (D,lo,d,ctx,func,PG) (v,G1,tn1) []
    (OK (jump_to yes v),G1,tn1)` by suspend "origin" >>
  `jump_to yes v = jump_to yes u /\ ~(jump_to yes v).vs_halted` by
    simp[jump_to_def, update_var_def] >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Resume range_full_nil_path[branch]:
  `eval_operand (Var dv) v = SOME 1w /\ op_taint tn1 (Var dv) = {} /\
   allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
   ~v.vs_halted /\ v.vs_current_bb = s.vs_current_bb /\
   v.vs_inst_idx = SUC s.vs_inst_idx` by
    (fs[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
          allocas_from_def, allocas_below_fmp_def, step_taint_def,
          set_var_taint_def, out_taint_def, op_taint_def, mk_inst_def] >>
     metis_tac[]) >>
  irule (SRULE [] (copy_jnz_counted_edge |> Q.INST [`b` |-> `T`])) >>
  simp[] >> qexistsl [`jid`, `no`, `Var dv`] >>
  fs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
     step_taint_def, set_var_taint_def, out_taint_def, op_taint_def, mk_inst_def]
QED

Resume range_full_nil_path[origin]:
  pure_rewrite_tac[gas_origin_ptr_edge_def] >>
  reverse conj_tac >- (pure_rewrite_tac[LENGTH] >> first_assum ACCEPT_TAC) >>
  irule gas_path_mem_edge_zero_origin >>
  `!fuel. mem_safe_step fuel ctx (mk_inst jid JNZ [Var dv; Label yes; Label no] []) v` by
    simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
      inst_dload_in_section_def, source_memory_read_ranges_def,
      source_memory_write_ranges_def, mk_inst_def] >>
  qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  gvs[update_var_def] >>
  simp[gas_path_ptr_edge_def, gas_path_mem_edge_def, is_terminator_def, mk_inst_def] >>
  fs[mk_inst_def] >> metis_tac[]
QED

Finalise range_full_nil_path

(* The fixed condition/body-prefix path. All endpoints are chosen before any
   horizon: EQ, the false JNZ arm, then the clean counter store. *)
Theorem range_entry_joint_path:
  !func cenv bc ty body id tyv p sz ainst cv ev dv nv cond_lbl exit_lbl
      body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj s n1 n2 k w G tn lo
      ctx D explicit PG.
    for_code func cenv bc ty body id tyv p sz ainst cv ev dv nv cond_lbl
      exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
    lookup_var cv s = SOME (i2w (n1 + &k)) /\
    lookup_var ev s = SOME (i2w n2) /\ lookup_var p s = SOME w /\
    ptr_covers G tn p s sz /\ op_taint tn (Var cv) = {} /\
    op_prov G (Var cv) = NONE /\ op_taint tn (Var ev) = {} /\
    op_prov G (Var ev) = NONE /\ lo <= w2n w /\ allocas_from lo s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    w2n w + 32 <= s.vs_alloca_next ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK
         (mstore (w2n w) (i2w (n1 + &k))
            (jump_to body_lbl
               (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
          vs_inst_idx := 1),
       step_prov PG
         (step_prov PG
            (step_prov PG G (mk_inst j1 EQ [Var cv; Var ev] [dv])
               (update_var dv (bool_to_word F) s))
            (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
            (jump_to body_lbl
               (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
         (mk_inst j3 MSTORE [Var p; Var cv] [])
         (mstore (w2n w) (i2w (n1 + &k))
            (jump_to body_lbl
               (update_var dv (bool_to_word F) s with vs_inst_idx := 1))),
       step_taint (mk_inst j3 MSTORE [Var p; Var cv] [])
         (jump_to body_lbl
            (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
         (mstore (w2n w) (i2w (n1 + &k))
            (jump_to body_lbl
               (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
         (step_taint
            (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
            (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
            (jump_to body_lbl
               (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
            (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
               (update_var dv (bool_to_word F) s) tn))) /\
    (mstore (w2n w) (i2w (n1 + &k))
       (jump_to body_lbl
          (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
     vs_inst_idx := 1).vs_current_bb = body_lbl /\
    (mstore (w2n w) (i2w (n1 + &k))
       (jump_to body_lbl
          (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
     vs_inst_idx := 1).vs_inst_idx = 1 /\
    ~(mstore (w2n w) (i2w (n1 + &k))
       (jump_to body_lbl
          (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
     vs_inst_idx := 1).vs_halted /\
    (!x. x <> dv ==>
         lookup_var x
           (mstore (w2n w) (i2w (n1 + &k))
              (jump_to body_lbl
                 (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
            vs_inst_idx := 1) = lookup_var x s) /\
    (mstore (w2n w) (i2w (n1 + &k))
       (jump_to body_lbl
          (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
     vs_inst_idx := 1).vs_allocas = s.vs_allocas /\
    (mstore (w2n w) (i2w (n1 + &k))
       (jump_to body_lbl
          (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
     vs_inst_idx := 1).vs_alloca_next = s.vs_alloca_next /\
    (!x. x <> dv ==>
         FLOOKUP
           (step_prov PG
              (step_prov PG
                 (step_prov PG G (mk_inst j1 EQ [Var cv; Var ev] [dv])
                    (update_var dv (bool_to_word F) s))
                 (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
              (mk_inst j3 MSTORE [Var p; Var cv] [])
              (mstore (w2n w) (i2w (n1 + &k))
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with vs_inst_idx := 1))))
           x = FLOOKUP G x /\
         op_taint
           (step_taint (mk_inst j3 MSTORE [Var p; Var cv] [])
              (jump_to body_lbl
                 (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
              (mstore (w2n w) (i2w (n1 + &k))
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
              (step_taint
                 (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
                 (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
                 (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
                    (update_var dv (bool_to_word F) s) tn))) (Var x) =
         op_taint tn (Var x)) /\
    (step_taint (mk_inst j3 MSTORE [Var p; Var cv] [])
       (jump_to body_lbl
          (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
       (mstore (w2n w) (i2w (n1 + &k))
          (jump_to body_lbl
             (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
       (step_taint (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
          (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
          (jump_to body_lbl
             (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
          (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
             (update_var dv (bool_to_word F) s) tn))).t_mem =
    tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32} /\
    (step_taint (mk_inst j3 MSTORE [Var p; Var cv] [])
       (jump_to body_lbl
          (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
       (mstore (w2n w) (i2w (n1 + &k))
          (jump_to body_lbl
             (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
       (step_taint (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
          (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
          (jump_to body_lbl
             (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
          (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
             (update_var dv (bool_to_word F) s) tn))).t_stor = tn.t_stor /\
    (step_taint (mk_inst j3 MSTORE [Var p; Var cv] [])
       (jump_to body_lbl
          (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
       (mstore (w2n w) (i2w (n1 + &k))
          (jump_to body_lbl
             (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
       (step_taint (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
          (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
          (jump_to body_lbl
             (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
          (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
             (update_var dv (bool_to_word F) s) tn))).t_trans = tn.t_trans /\
    (step_taint (mk_inst j3 MSTORE [Var p; Var cv] [])
       (jump_to body_lbl
          (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
       (mstore (w2n w) (i2w (n1 + &k))
          (jump_to body_lbl
             (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
       (step_taint (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
          (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
          (jump_to body_lbl
             (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
          (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
             (update_var dv (bool_to_word F) s) tn))).t_imm = tn.t_imm
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac [LET_THM] >>
  map_every qabbrev_tac
    [`z = n1 + &k`, `ie = mk_inst j1 EQ [Var cv;Var ev] [dv]`,
     `ij = mk_inst j2 JNZ [Var dv;Label exit_lbl;Label body_lbl] []`,
     `im = mk_inst j3 MSTORE [Var p;Var cv] []`,
     `ue = update_var dv (bool_to_word F) s`, `se = ue with vs_inst_idx := 1`,
     `b = jump_to body_lbl se`, `u = mstore (w2n w) (i2w z) b`,
     `t = u with vs_inst_idx := 1`, `Ge = step_prov PG G ie ue`,
     `te = step_taint ie s ue tn`, `Gb = step_prov PG Ge ij b`,
     `tb = step_taint ij se b te`, `Gf = step_prov PG Gb im u`,
     `tt = step_taint im b u tb`] >>
  `i2w z <> (i2w n2 : bytes32)` by
    (simp[Abbr `z`] >> irule i2w_counter_ne >> simp[]) >>
  fs[for_code_def] >>
  `step_inst_base ie s = OK ue` by
    simp[Abbr `ie`, Abbr `ue`, step_inst_base_opcode_eqs,
         exec_pure2_def, eval_operand_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn ie s` by
    (simp[Abbr `ie`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def] >>
     fs[op_prov_def, FLOOKUP_DEF] >>
     conj_tac >- metis_tac[] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[Abbr `ue`, update_var_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK se,Ge,te)` by
    (drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`) straight_line_origin_ptr_edge >>
     simp[Abbr `ie`, Abbr `se`, Abbr `Ge`, Abbr `te`,
          get_instruction_def, mk_inst_def, is_terminator_def,
          inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >> simp[]) >>
  `allocas_from lo se /\ (ctx_has_dalloca ctx ==> allocas_below_fmp se) /\
   ~se.vs_halted /\ se.vs_current_bb = cond_lbl /\ se.vs_inst_idx = 1 /\
   eval_operand (Var dv) se = SOME 0w` by
    (fs[Abbr `se`, Abbr `ue`, allocas_from_def, allocas_below_fmp_def,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
    metis_tac[]) >>
  `op_taint te (Var dv) = {}` by
    simp[Abbr `te`, Abbr `ie`, step_taint_def, set_var_taint_def,
         out_taint_def, op_taint_def, mk_inst_def, FLOOKUP_UPDATE,
         eval_operand_def] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (se,Ge,te) [] (OK b,Ge,te)` by
    (simp[Abbr `b`] >>
     irule (SRULE [] (Q.INST [`v` |-> `0w`] decoderNavigationPtrTheory.jnz_origin_ptr_path)) >>
     simp[] >> qexistsl_tac [`j2`, `Var dv`, `exit_lbl`] >>
     simp[get_instruction_def, Abbr `ij`]) >>
  `Ge = DRESTRICT G (COMPL {dv}) /\
   te = tn with t_var := tn.t_var |+ (dv,{})` by
    (simp[Abbr `Ge`, Abbr `te`, Abbr `ie`, Abbr `ue`, step_prov_def,
          set_prov_def, out_prov_def, step_taint_def, set_var_taint_def,
          out_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
          source_memory_write_ranges_def, range_bytes_def, written_taint_def,
          store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
          update_var_def, eval_operand_def, taint_component_equality,
          FLOOKUP_DEF, EXTENSION] >> metis_tac[]) >>
  `Gb = Ge /\ tb = te /\ step_taint ij ue b te = te` by
    (simp[Abbr `Gb`, Abbr `tb`, Abbr `ij`, Abbr `b`, Abbr `se`,
          step_prov_def, set_prov_def, out_prov_def, step_taint_def,
          set_var_taint_def, mem_taint_def, new_site_bytes_def,
          step_writes_def, source_memory_write_ranges_def, range_bytes_def,
          written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
          mk_inst_def, jump_to_def, taint_component_equality, FLOOKUP_DEF,
          DRESTRICT_UNIV, EXTENSION, SF CONJ_ss]) >>
  `lookup_var p b = SOME w /\ eval_operand (Var cv) b = SOME (i2w z) /\
   ~b.vs_halted /\ b.vs_current_bb = body_lbl /\ b.vs_inst_idx = 0 /\
   b.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo b /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp b)` by
    (fs[Abbr `b`, Abbr `se`, Abbr `ue`, jump_to_def, update_var_def,
        eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
        allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `ptr_covers Ge te p b 32 /\ op_taint te (Var cv) = {}` by
    (fs[ptr_covers_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
     gvs[] >> decide_tac) >>
  `step_inst_base im b = OK u` by
    simp[Abbr `im`, Abbr `u`, step_inst_base_opcode_eqs,
         exec_write2_def, eval_operand_def] >>
  `ptr_inst_ok D lo 0 ctx func Ge te im b` by
    (simp[Abbr `im`] >> irule ptr_inst_ok_mstore_tainted >>
     fs[] >> metis_tac[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
      (b,Ge,te) [] (OK t,Gf,tt)` by
    (drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`) straight_line_origin_ptr_edge >>
     simp[Abbr `im`, Abbr `t`, Abbr `Gf`, Abbr `tt`,
          mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, fixed_source_write_range_def,
          eval_operand_def] >>
     disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >> simp[]) >>
  fs[Abbr `tt`] >>
  conj_tac
  >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`Ge`, `se`, `te`] >> conj_tac
      >- (irule (SRULE [] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
                (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)))) >>
          qexistsl_tac [`Ge`, `se`, `te`] >> fs[] >>
          irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
      irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`Ge`, `b`, `te`] >> fs[] >>
      irule (SRULE [] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
        (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)))) >>
      qexistsl_tac [`Gf`, `t`, `step_taint im b u tb`] >> fs[] >>
      conj_tac >- metis_tac[] >>
      irule (cj 1 gas_origin_ptr_path_rules) >>
      simp[Abbr `t`, Abbr `u`, mstore_def]) >>
  `Gf = Ge /\
   (step_taint im b u te).t_var = te.t_var /\
   (step_taint im b u te).t_mem =
       te.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32} /\
   (step_taint im b u te).t_stor = te.t_stor /\
   (step_taint im b u te).t_trans = te.t_trans` by
    (drule_all wordLoadStorePtrTheory.mstore_ghost_frame >>
     disch_then (qspecl_then [`PG`, `Ge`, `j3`] mp_tac) >>
     simp[Abbr `Gf`, Abbr `im`, Abbr `u`] >> metis_tac[]) >>
  `(step_taint im b u te).t_imm = te.t_imm` by
    simp[Abbr `im`, copy_mk_immutable_taint] >>
  gvs[] >>
  simp[Abbr `u`, Abbr `t`, Abbr `b`, Abbr `se`, Abbr `ue`,
     mstore_def, jump_to_def, update_var_def, lookup_var_def,
     FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]
QED

(* Store while the loop id is inactive; only then expose its live scope. *)
Theorem range_entry_store_scope:
  !H ctx func cenv cx e b D lo d G tn id bc p sz w ainst tyv z.
    stmt_state_rel H ctx func cenv cx e b /\
    ghost_inv_at D lo d cenv cx e G tn b /\ lookup_scopes id e.scopes = NONE /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!nm. nm <> id ==> FLOOKUP bc.ce_vars nm = FLOOKUP cenv.ce_vars nm) /\
    bc with
    <|ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
      ce_dynarray_capacity := cenv.ce_dynarray_capacity|> = cenv /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z'. l = PtrVar q z') /\
    not_local_ptr cenv e.scopes p /\ not_local_ptr bc (FEMPTY::e.scopes) p /\
    lookup_var p b = SOME w /\ ptr_covers G tn p b sz /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
    FLOOKUP b.vs_allocas ainst.inst_id = SOME (w2n w,sz) /\ 32 <= sz /\
    type_memory_size tyv = 32 /\ word_memory_type tyv /\ val_wf tyv (IntV z) /\
    lo <= w2n w ==>
    stmt_state_rel H ctx func bc cx
      (e with
       scopes :=
         fmupdate id
           <|assignable := F; type := tyv; value := IntV z; popped := []|>
           FEMPTY::e.scopes) (mstore (w2n w) (i2w z) b) /\
    ghost_inv_at D lo d bc cx
      (e with
       scopes :=
         fmupdate id
           <|assignable := F; type := tyv; value := IntV z; popped := []|>
           FEMPTY::e.scopes) G
      (tn with t_mem := tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32})
      (mstore (w2n w) (i2w z) b)
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac [LET_THM] >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `!name off nb. local_region cenv e.scopes b name off nb ==>
      off + nb <= w2n w \/ w2n w + 32 <= off` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) sz off nb` by
       (irule local_ptrs_rel_alloca_disjoint >>
        qexistsl_tac [`cenv`, `func`, `ainst`, `name`, `p`, `e.scopes`, `b`] >>
        simp[]) >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  fs[compile_env_component_equality] >>
  conj_tac >- suspend "declare" >>
  `ghost_inv_at D lo d cenv cx e G
     (tn with t_mem := tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32})
     (mstore (w2n w) (i2w z) b)` by
    (irule ghost_inv_at_mstore_clean >> simp[] >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule >> decide_tac) >>
     conj_tac >- (qexists_tac `func` >> simp[]) >>
     qexists_tac `tn` >> simp[]) >>
  `return_buf_ptr d bc G
      (tn with t_mem := tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32})
      (mstore (w2n w) (i2w z) b) =
   return_buf_ptr d cenv G
      (tn with t_mem := tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32})
      (mstore (w2n w) (i2w z) b)` by
    (Cases_on `d` >- simp[return_buf_ptr_def] >>
     PairCases_on `x` >> simp[return_buf_ptr_def]) >>
  fs[ghost_inv_at_def] >>
  simp[ghost_inv_at_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `name = id` >- suspend "new_local" >>
  gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
  first_x_assum irule >> simp[] >> qexists_tac `name` >> simp[]
QED

Resume range_entry_store_scope[declare]:
  `stmt_state_rel H ctx func bc cx (e with scopes := FEMPTY :: e.scopes) b` by
    (simp[stmt_state_rel_push_scope] >> irule stmt_state_rel_cenv_cong >>
     qexists_tac `cenv` >> simp[] >> rpt strip_tac >>
     Cases_on `n = id` >> gvs[]) >>
  qpat_x_assum `stmt_state_rel _ _ _ bc _ (_ with scopes := _) _`
    (mp_then Any mp_tac stmt_state_rel_declare_store) >>
  disch_then (irule o SRULE []) >>
  simp[lookup_scopes_def] >>
  conj_tac >- (qexists_tac `ainst` >> simp[]) >>
  simp[GSYM val_to_w256_def, word_value_memory_rel, word_value_def]
QED

Resume range_entry_store_scope[new_local]:
  gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- gvs[ptr_covers_def, op_taint_def, lookup_var_def, mstore_def] >>
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at (w2n w) 32 mem =
   mem_bytes_at (w2n w) 32 (mstore (w2n w) (i2w z) b).vs_memory` by
    (irule clean_memory_window >>
     qexists_tac `tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32}` >>
     simp[]) >>
  irule val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`32`, `(mstore (w2n w) (i2w z) b).vs_memory`] >>
  simp[valueEncodingDefsTheory.val_in_memory_def, mstore_mem_word_at_same,
       val_to_w256_def]
QED

Finalise range_entry_store_scope

(* ===== Initialization: virtual allocation cut ===== *)

Theorem range_alloc_buffer_code:
  compile_alloc_buffer n st = (buf,cut) /\
  lookup_block st.cs_current_bb func.fn_blocks =
    SOME <|bb_label := st.cs_current_bb; bb_instructions :=
      st.cs_current_insts ++
      [mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString st.cs_next_var)]] ++ tail|> ==>
  fn_has_code st cut func
Proof
  strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def]
QED

(* The counter allocation is newer than every protected original allocation. *)
Theorem range_entry_anchor_frame:
  !c0 e0 sa0 s00 cenv e s counter w sz id bc p dv t value tn1 tn tn00 entry.
    alloca_frame c0 e0 sa0 s00 cenv e s /\
    (!aid block. FLOOKUP s00.vs_allocas aid = SOME block ==>
                 FLOOKUP s.vs_allocas aid = SOME block) /\
    alloca_inv s /\ FLOOKUP s.vs_allocas counter = SOME (w2n w,sz) /\
    sa0.cs_next_id <= counter /\ 32 <= sz /\
    lookup_scopes id e.scopes = NONE /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!nm. nm <> id ==> FLOOKUP bc.ce_vars nm = FLOOKUP cenv.ce_vars nm) /\
    not_local_ptr cenv e.scopes dv /\ p <> dv /\ lookup_var p s = SOME w /\
    (!q. q <> dv ==> lookup_var q t = lookup_var q s) /\
    t.vs_memory = (mstore (w2n w) value s).vs_memory /\
    tn1.t_mem SUBSET tn.t_mem /\
    (!aid off z i.
       FLOOKUP s00.vs_allocas aid = SOME (off,z) /\ aid < sa0.cs_next_id /\
       (!nm b0 z0. local_region c0 e0.scopes s00 nm b0 z0 ==>
                    off+z <= b0 \/ b0+z0 <= off) /\
       off <= i /\ i < off+z /\ i IN tn.t_mem ==> i IN tn00.t_mem) ==>
    alloca_frame c0 e0 sa0 s00 bc
      (e with scopes := (FEMPTY |+ (id,entry)) :: e.scopes) t /\
    (!aid off z i.
       FLOOKUP s00.vs_allocas aid = SOME (off,z) /\ aid < sa0.cs_next_id /\
       (!nm b0 z0. local_region c0 e0.scopes s00 nm b0 z0 ==>
                    off+z <= b0 \/ b0+z0 <= off) /\
       off <= i /\ i < off+z /\ i IN tn1.t_mem ==> i IN tn00.t_mem)
Proof
  rpt gen_tac >> strip_tac >> reverse conj_tac
  >- (fs[SUBSET_DEF] >> metis_tac[]) >>
  rewrite_tac[alloca_frame_def] >>
  map_every qx_gen_tac [`aid`, `off`, `oldsz`] >> strip_tac >>
  `aid <> counter` by decide_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,oldsz)` by metis_tac[] >>
  Q.SUBGOAL_THEN `off + oldsz <= w2n w \/ w2n w + sz <= off` assume_tac
  >- (fs[alloca_inv_def, allocas_non_overlapping_def] >>
      qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
        (qspec_then `aid` mp_tac) >>
      disch_then (qspec_then `counter` mp_tac) >> simp[]) >>
  `mem_bytes_at off oldsz s.vs_memory = mem_bytes_at off oldsz s00.vs_memory /\
   (!nm b z. local_region cenv e.scopes s nm b z ==>
              off + oldsz <= b \/ b + z <= off)` by
    (qpat_assum `alloca_frame _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [alloca_frame_def] >>
     disch_then (qspecl_then [`aid`, `off`, `oldsz`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  conj_tac
  >- (`mem_bytes_at off oldsz (mstore (w2n w) value s).vs_memory =
        mem_bytes_at off oldsz s.vs_memory` by
        (irule mstore_mem_bytes_at_disjoint >> decide_tac) >> simp[]) >>
  map_every qx_gen_tac [`nm`, `b`, `localsz`] >> strip_tac >> Cases_on `nm = id`
  >- (gvs[local_region_def, lookup_scopes_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `local_region cenv e.scopes s nm b localsz` suffices_by metis_tac[] >>
  gvs[local_region_def, lookup_scopes_def, FLOOKUP_UPDATE] >>
  rename1 `lookup_var lp t = SOME lw` >>
  `lp <> dv` by (fs[not_local_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED

(* Literal machine suffix; source range checks remain at the initialization join. *)
Theorem range_literal_entry_full:
  !ctx func lo s G tn bb entry_lbl cond_lbl cv ev n1 n2 j0 j1 j2 j3.
    ~s.vs_halted /\ allocas_from lo s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ cv <> ev /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst j0 JMP [Label entry_lbl] []) /\
    lookup_block entry_lbl func.fn_blocks =
      SOME <|bb_label := entry_lbl; bb_instructions :=
        [mk_inst j1 ASSIGN [Lit (i2w n1)] [cv];
         mk_inst j2 ADD [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev];
         mk_inst j3 JMP [Label cond_lbl] []]|> ==>
    ?t G' tn'.
      t = jump_to cond_lbl
        (update_var ev (i2w n2)
          (update_var cv (i2w n1) (jump_to entry_lbl s))) /\
      G' = DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {ev}) /\
      tn' = (tn with t_var :=
        set_var_taint (set_var_taint tn.t_var [cv] {}) [ev] {}) /\
      (!D explicit PG.
        gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
          (OK t,G',tn')) /\
      ~t.vs_halted /\ t.vs_current_bb = cond_lbl /\ t.vs_inst_idx = 0 /\
      lookup_var cv t = SOME (i2w n1) /\ lookup_var ev t = SOME (i2w n2) /\
      FLOOKUP G' cv = NONE /\ FLOOKUP G' ev = NONE /\
      op_taint tn' (Var cv) = {} /\ op_taint tn' (Var ev) = {} /\
      (!x. x <> cv /\ x <> ev ==>
        lookup_var x t = lookup_var x s /\
        FLOOKUP G' x = FLOOKUP G x /\
        op_taint tn' (Var x) = op_taint tn (Var x)) /\
      (!H cenv cx es.
        stmt_state_rel H ctx func cenv cx es s /\
        not_local_ptr cenv es.scopes cv /\ not_local_ptr cenv es.scopes ev ==>
        stmt_state_rel H ctx func cenv cx es t) /\
      (!D d cenv cx es sa.
        ghost_inv_at D lo d cenv cx es G tn s /\
        local_ptrs_reserved cenv sa /\
        (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
        (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
        (!x. not_fresh_at sa x ==> x <> cv /\ x <> ev) ==>
        ghost_inv_at D lo d cenv cx es G' tn' t) /\
      (!c0 e0 sa0 s00 cenv es.
        alloca_frame c0 e0 sa0 s00 cenv es s /\
        not_local_ptr cenv es.scopes cv /\ not_local_ptr cenv es.scopes ev ==>
        alloca_frame c0 e0 sa0 s00 cenv es t)
Proof
  rpt gen_tac >> strip_tac >>
  qexistsl_tac [`jump_to cond_lbl (update_var ev (i2w n2)
      (update_var cv (i2w n1) (jump_to entry_lbl s)))`,
    `DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {ev})`,
    `tn with t_var := set_var_taint (set_var_taint tn.t_var [cv] {}) [ev] {}`] >>
  pure_rewrite_tac [REFL_CLAUSE, boolTheory.AND_CLAUSES] >>
  conj_tac >- suspend "literal_path" >>
  simp[lookup_var_def, update_var_def, jump_to_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE, set_var_taint_def, op_taint_def] >>
  conj_tac >- suspend "literal_relation" >>
  conj_tac >- suspend "literal_ghost" >>
  suspend "literal_frame"
QED

Resume range_literal_entry_full[literal_path]:
  rpt gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (jump_to entry_lbl s),G,tn)` by
    (irule decoderNavigationPtrTheory.jump_origin_ptr_path >> metis_tac[]) >>
  qabbrev_tac `u = jump_to entry_lbl s` >>
  qabbrev_tac `code = [mk_inst j1 ASSIGN [Lit (i2w n1)] [cv];
    mk_inst j2 ADD [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev]]` >>
  qabbrev_tac `v = update_var ev (i2w n2) (update_var cv (i2w n1) u)` >>
  qabbrev_tac `gg = DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {ev})` >>
  qabbrev_tac `tt = tn with t_var :=
    set_var_taint (set_var_taint tn.t_var [cv] {}) [ev] {}` >>
  `!ss. step_inst_base (mk_inst j1 ASSIGN [Lit (i2w n1)] [cv]) ss =
     OK (update_var cv (i2w n1) ss)` by
    (gen_tac >> simp[mk_inst_def] >>
     irule acBaseProofsTheory.step_assign_value >> simp[eval_operand_def]) >>
  `!ss. step_inst_base
     (mk_inst j2 ADD [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev]) ss =
     OK (update_var ev (i2w n2) ss)` by
    (gen_tac >> `(i2w n2:256 word) = i2w n1 + (i2w n2 - i2w n1)` by
       simp[wordsTheory.WORD_SUB_ADD2] >>
     pop_assum (fn th => GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       empty_rewrites [th]) >> irule step_ADD >> simp[eval_operand_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tn) []
     (OK (v with vs_inst_idx := 2),gg,tt)` by
    (`u.vs_inst_idx = 0` by simp[Abbr `u`, jump_to_def] >>
     qmatch_asmsub_abbrev_tac `lookup_block entry_lbl func.fn_blocks = SOME ebb` >>
     mp_tac run_inst_seq_gas_origin_ptr_path >>
     disch_then (qspecl_then [`code`, `u`, `v`, `G`, `tn`, `gg`, `tt`,
       `ctx`, `func`, `ebb`] mp_tac) >>
     simp[Abbr `code`] >> disch_then irule >>
     simp[Abbr `v`, run_inst_seq_def] >>
     simp[Abbr `u`, Abbr `ebb`, jump_to_def] >>
     simp[is_terminator_def, mk_inst_def,
       wordsTheory.WORD_SUB_ADD2, jump_to_def,
       run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, inst_seq_ptr_def] >>
     conj_tac
     >- (rpt strip_tac >> Cases_on `pre` >> gvs[] >>
         rename1 `[_] = tail ++ [i] ++ post` >> Cases_on `tail` >> gvs[]) >>
     conj_tac
     >- (irule scalar_ptr_inst_ok_lo >>
         simp[scalar_shape_def, scalar_binary_def, scalar_unary_def,
           op_prov_def, op_taint_def] >>
         gvs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
     conj_tac
     >- (irule scalar_ptr_inst_ok_lo >>
         simp[scalar_shape_def, scalar_binary_def, scalar_unary_def,
           op_prov_def, op_taint_def, update_var_def] >>
         gvs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
     conj_tac
     >- simp[Abbr `gg`, step_prov_def, out_prov_def, first_prov_def,
           op_prov_def, set_prov_def] >>
     simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, range_bytes_def, written_taint_def, out_taint_def,
       adopt_reset_def, store_taint_def, imm_taint_def,
       eval_operand_def, op_taint_def, Abbr `tt`, update_var_def] >>
     simp[source_memory_write_ranges_def, FLOOKUP_DEF] >>
     simp[taint_component_equality, EXTENSION, SF CONJ_ss]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (v with vs_inst_idx := 2,gg,tt) []
     (OK (jump_to cond_lbl v),gg,tt)` by
    (`jump_to cond_lbl v = jump_to cond_lbl (v with vs_inst_idx := 2)` by
       simp[jump_to_def] >>
     pop_assum SUBST1_TAC >>
     irule decoderNavigationPtrTheory.jump_origin_ptr_path >>
     simp[Abbr `v`, Abbr `u`, jump_to_def, update_var_def,
       get_instruction_def, mk_inst_def] >>
     gvs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  metis_tac[gas_origin_ptr_path_trans]
QED
Resume range_literal_entry_full[literal_relation]:
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es
     (jump_to cond_lbl (update_var ev (i2w n2)
       (update_var cv (i2w n1) (jump_to entry_lbl s))))` suffices_by
    simp[jump_to_def, update_var_def] >>
  simp[stmt_state_rel_jump_to] >>
  irule stmt_state_rel_update_var >> simp[] >>
  irule stmt_state_rel_update_var >> simp[stmt_state_rel_jump_to]
QED
Resume range_literal_entry_full[literal_ghost]:
  rpt gen_tac >> strip_tac >>
  irule ghost_inv_at_exterior_frame >>
  qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >>
  simp[] >> rpt strip_tac >>
  `x <> cv /\ x <> ev` by metis_tac[] >>
  simp[lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]
QED
Resume range_literal_entry_full[literal_frame]:
  rpt gen_tac >> strip_tac >>
  irule alloca_frame_same_state >>
  qexists_tac `update_var ev (i2w n2) (update_var cv (i2w n1) s)` >>
  simp[update_var_def] >>
  `alloca_frame c0 e0 sa0 s00 cenv es
     (update_var ev (i2w n2) (update_var cv (i2w n1) s))` suffices_by
    simp[update_var_def] >>
  irule alloca_frame_update_var >> simp[] >>
  irule alloca_frame_update_var >> simp[]
QED
Finalise range_literal_entry_full

(* Ordered forced endpoints. The continuation receives one common endpoint
   and its posts at every valid horizon, never horizon-dependent witnesses. *)
Theorem range_full_endpoints:
  !DF lo explicit ctx func PG tops cx st0 typ tyv id e1 e2 bound body
     es s G tn P1 P2 Q R.
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
      (bind (eval_expr cx e1) (read_result cx)) (es, s, G, tn)
      (\H res ee G1 tn1 t1.
         ?v1. res = INL v1 /\ P1 H v1 ee G1 tn1 t1)
      (\H res ee gt r. ?ex. res = INR ex /\ R H (INR ex) ee gt r) /\
    (!marks1 v1 mid1 G1 tn1 t1.
       (!tail.
          bind (eval_expr cx e1) (read_result cx)
            (es with gas_obs :=
               gas_explicit marks1 s.vs_gas_readings ++ tail) =
          (INL v1, mid1 with gas_obs := tail)) /\
       storage_trace_domain cx st0 mid1.storage_trace /\
       (!H. valid_horizon cx st0 H mid1.storage_trace ==>
            P1 H v1 mid1 G1 tn1 t1) ==>
       gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
         (bind (eval_expr cx e2) (read_result cx)) (mid1, t1, G1, tn1)
         (\H res ee G2 tn2 t2.
            ?v2. res = INL v2 /\
                 P2 v1 mid1 G1 tn1 t1 H v2 ee G2 tn2 t2)
         (\H res ee gt r. ?ex. res = INR ex /\ R H (INR ex) ee gt r) /\
       (!marks2 v2 mid2 G2 tn2 t2.
          (!tail.
             bind (eval_expr cx e2) (read_result cx)
               (mid1 with gas_obs :=
                  gas_explicit marks2 t1.vs_gas_readings ++ tail) =
             (INL v2, mid2 with gas_obs := tail)) /\
          storage_trace_domain cx st0 mid2.storage_trace /\
          (!H. valid_horizon cx st0 H mid2.storage_trace ==>
               P2 v1 mid1 G1 tn1 t1 H v2 mid2 G2 tn2 t2) ==>
          gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
            (do rl <- lift_sum (get_range_limits v1 v2);
                check (compatible_bound (Dynamic bound) (SND rl))
                  "For too long";
                eval_for cx tyv id body
                  (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl))
             od)
            (mid2, t2, G2, tn2) Q R)) ==>
    gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
      (eval_stmt cx (For id typ (Range e1 e2) bound body))
      (es, s, G, tn) Q R
Proof
  rpt gen_tac >> strip_tac >>
  `eval_stmt cx (For id typ (Range e1 e2) bound body) =
    do v1 <- bind (eval_expr cx e1) (read_result cx);
       v2 <- bind (eval_expr cx e2) (read_result cx);
       rl <- lift_sum (get_range_limits v1 v2);
       check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
       eval_for cx tyv id body
         (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od` by
    (pure_once_rewrite_tac[Once evaluate_def] >>
     simp[LET_THM, lift_option_type_def] >>
     pure_once_rewrite_tac[Once evaluate_def] >>
     simp[LET_THM, bind_assoc, bind_return, LENGTH_GENLIST]) >>
  pop_assum SUBST1_TAC >>
  qmatch_goalsub_abbrev_tac
    `bind (bind (eval_expr cx e1) (read_result cx)) next1` >>
  `!f: evaluation_state -> value evaluation_result.
     !k: value -> evaluation_state -> unit evaluation_result.
       ignore_bind (bind f k) (return ()) =
       bind f (\v. ignore_bind (k v) (return ()))` by
    simp[ignore_bind_def, bind_assoc] >>
  irule gas_outcome_full_bind_all >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  BETA_TAC >> rpt conj_tac
  >- suspend "first_frame"
  >- (rpt strip_tac >>
      qpat_assum `!f k. ignore_bind (bind f k) _ = _`
        (fn th => irule (PURE_ONCE_REWRITE_RULE [th]
          (INST_TYPE [alpha |-> ``:unit``] forced_endpoint_tail_cert))) >>
      simp[] >> goal_assum (drule_at Any) >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!f k. ignore_bind (bind f k) _ = _`
        (fn th => irule (PURE_ONCE_REWRITE_RULE [th]
          (INST_TYPE [alpha |-> ``:unit``] forced_endpoint_error_cert))) >>
      first_assum ACCEPT_TAC)
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result, cj 5 evaluate_storage_trace_frame]) >>
  suspend "first_next"
QED

Resume range_full_endpoints[first_frame]:
  simp[Abbr `next1`] >> gen_tac >>
  irule storage_trace_frame_bind_all >> reverse conj_tac
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result, cj 5 evaluate_storage_trace_frame]) >>
  gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_lifts] >> gen_tac >> BETA_TAC >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_checks, cj 4 evaluate_storage_trace_frame]
QED

Resume range_full_endpoints[first_next]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?v. _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- fs[storage_trace_domain_def] >>
  strip_tac >> gvs[] >>
  simp[Abbr `next1`] >>
  qpat_x_assum `!marks1 v1 mid1 G1 tn1 t1. _`
    (drule_all_then strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac
    `bind (bind (eval_expr cx e2) (read_result cx)) next2` >>
  irule gas_outcome_full_bind_all >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx e2) _) _ _ _`
    (irule_at Any) >>
  BETA_TAC >> rpt conj_tac
  >- (simp[Abbr `next2`] >> gen_tac >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts] >> gen_tac >> BETA_TAC >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_checks, cj 4 evaluate_storage_trace_frame])
  >- (rpt strip_tac >>
      qpat_assum `!f k. ignore_bind (bind f k) _ = _`
        (fn th => irule (PURE_ONCE_REWRITE_RULE [th]
          (INST_TYPE [alpha |-> ``:unit``] forced_endpoint_tail_cert))) >>
      simp[] >> goal_assum (drule_at Any) >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!f k. ignore_bind (bind f k) _ = _`
        (fn th => irule (PURE_ONCE_REWRITE_RULE [th]
          (INST_TYPE [alpha |-> ``:unit``] forced_endpoint_error_cert))) >>
      first_assum ACCEPT_TAC)
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result, cj 5 evaluate_storage_trace_frame]) >>
  suspend "second_next"
QED

Resume range_full_endpoints[second_next]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?v. _`
    (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
  impl_tac >- fs[storage_trace_domain_def] >>
  strip_tac >> gvs[] >> simp[Abbr `next2`] >>
  qpat_x_assum `!marks2 v2 mid2 G2 tn2 t2. _`
    (drule_all_then (assume_tac o BETA_RULE)) >>
  first_assum ACCEPT_TAC
QED

Finalise range_full_endpoints

(* Executed bodies cannot introduce shadowing between their head and tail. *)
Theorem range_full_body_no_shadow:
  !cx body ei res ee sc rest.
    ei.scopes <> [] /\
    (!nm. nm IN FDOM (HD ei.scopes) ==>
          lookup_scopes nm (TL ei.scopes) = NONE) /\
    eval_stmts cx body ei = (res,ee) /\ ee.scopes = sc::rest ==>
    !nm. nm IN FDOM sc ==> lookup_scopes nm rest = NONE
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `nm IN FDOM (HD ei.scopes)`
  >- (Cases_on `ei.scopes` >> gvs[] >>
      `(ei with scopes := h::t) = ei` by
        simp[evaluation_state_component_equality] >>
      metis_tac[vyperEvalPreservesScopesTheory.eval_stmts_preserves_tail_lookup_none]) >>
  `nm IN FDOM (HD ee.scopes)` by simp[] >>
  drule_all vyperEvalPreservesScopesTheory.eval_stmts_new_in_head_not_in_tail >>
  simp[]
QED

(* Scope cleanup preserves the complete frame at the original loop anchor.
   The common pop contract is explicit so the Range join can discharge it. *)
Theorem range_full_body_scope_post:
  !H ctx func cenv bc c3 cx ei body res ee t sc rest D lo d G tn
   c0 e0 sa0 s0 G0 tn0.
    (!func0 ctx0 ca ea sa s00 (Ga : (string, num # num) fmap) tna c eb u Gb tnb co hd tl.
      (alloca_history func0 u /\
       (ctx_has_dalloca ctx0 ==> allocas_below_fmp u) /\
       s00.vs_alloca_next <= u.vs_alloca_next /\
       (!x w. not_fresh_at sa x /\ lookup_var x s00 = SOME w ==>
              lookup_var x u = SOME w) /\
       (!aid b. FLOOKUP s00.vs_allocas aid = SOME b ==>
                FLOOKUP u.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa x ==>
            FLOOKUP Gb x = FLOOKUP Ga x /\
            op_taint tnb (Var x) = op_taint tna (Var x)) /\
       alloca_frame ca ea sa s00 c eb u /\
       (!aid off sz i.
          FLOOKUP s00.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
          (!nm b sz'. local_region ca ea.scopes s00 nm b sz' ==>
                     off + sz <= b \/ b + sz' <= off) /\
          off <= i /\ i < off + sz /\ i IN tnb.t_mem ==> i IN tna.t_mem)) /\
      cenv_top_ext co c eb.scopes /\ eb.scopes = hd::tl /\
      (!nm. nm IN FDOM hd ==> lookup_scopes nm tl = NONE) ==>
      alloca_history func0 u /\
      (ctx_has_dalloca ctx0 ==> allocas_below_fmp u) /\
      s00.vs_alloca_next <= u.vs_alloca_next /\
      (!x w. not_fresh_at sa x /\ lookup_var x s00 = SOME w ==>
             lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s00.vs_allocas aid = SOME b ==>
               FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
           FLOOKUP Gb x = FLOOKUP Ga x /\
           op_taint tnb (Var x) = op_taint tna (Var x)) /\
      alloca_frame ca ea sa s00 co (eb with scopes := tl) u /\
      (!aid off sz i.
         FLOOKUP s00.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
         (!nm b sz'. local_region ca ea.scopes s00 nm b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\
         off <= i /\ i < off + sz /\ i IN tnb.t_mem ==> i IN tna.t_mem)) /\
    ei.scopes <> [] /\
    (!nm. nm IN FDOM (HD ei.scopes) ==>
          lookup_scopes nm (TL ei.scopes) = NONE) /\
    eval_stmts cx body ei = (res,ee) /\ ee.scopes = sc::rest /\
    cenv_top_ext cenv bc ei.scopes /\ cenv_top_ext bc c3 ee.scopes /\
    stmt_state_rel H ctx func c3 cx ee t /\
    ghost_inv_at D lo d c3 cx ee G tn t /\
    storage_well_formed_on cx ee (FST H) /\
    (alloca_history func t /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     s0.vs_alloca_next <= t.vs_alloca_next /\
     (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
            lookup_var x t = SOME w) /\
     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
              FLOOKUP t.vs_allocas aid = SOME b) /\
     (!x. not_fresh_at sa0 x ==>
          FLOOKUP G x = FLOOKUP G0 x /\
          op_taint tn (Var x) = op_taint tn0 (Var x)) /\
     alloca_frame c0 e0 sa0 s0 c3 ee t /\
     (!aid off sz i.
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
        (!nm b sz'. local_region c0 e0.scopes s0 nm b sz' ==>
                   off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) ==>
    stmt_state_rel H ctx func cenv cx (ee with scopes := rest) t /\
    ghost_inv_at D lo d cenv cx (ee with scopes := rest) G tn t /\
    storage_well_formed_on cx (ee with scopes := rest) (FST H) /\
    (alloca_history func t /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     s0.vs_alloca_next <= t.vs_alloca_next /\
     (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
            lookup_var x t = SOME w) /\
     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
              FLOOKUP t.vs_allocas aid = SOME b) /\
     (!x. not_fresh_at sa0 x ==>
          FLOOKUP G x = FLOOKUP G0 x /\
          op_taint tn (Var x) = op_taint tn0 (Var x)) /\
     alloca_frame c0 e0 sa0 s0 cenv (ee with scopes := rest) t /\
     (!aid off sz i.
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
        (!nm b sz'. local_region c0 e0.scopes s0 nm b sz' ==>
                   off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `!nm. nm IN FDOM sc ==> lookup_scopes nm rest = NONE` by
    metis_tac[range_full_body_no_shadow] >>
  `cenv_top_ext cenv c3 ee.scopes` by
    (drule vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_dom >>
     strip_tac >> irule stmtSimPropsTheory.cenv_top_ext_trans >>
     qexistsl_tac [`bc`, `ei.scopes`] >>
     gvs[vyperEvalPreservesScopesTheory.preserves_scopes_dom_def]) >>
  conj_tac
  >- (drule_all stmtSimForArrayLoopTheory.array_body_scope_projection >> simp[]) >>
  conj_tac
  >- (drule_all bodyFullSharedTheory.ghost_inv_at_pop >> simp[]) >>
  conj_tac
  >- (irule (iffRL vyperStorageFootprintTheory.storage_well_formed_on_backends) >>
      qexists_tac `ee` >> simp[]) >>
  qpat_x_assum `!func0 ctx0 ca ea sa s00 Ga tna c eb u Gb tnb co hd tl. _`
    drule_all >> simp[]
QED

(* Allocation leaves all existing bytes unchanged; newly tainted bytes start
   beyond every old allocation, including reused allocation sites. *)
Theorem range_alloca_full_frame:
  stmt_state_rel H ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\ t.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!i. i IN tn'.t_mem ==> i IN tn.t_mem \/ s.vs_alloca_next <= i) ==>
  alloca_frame cenv es sa s cenv es t /\
  (!aid off sz i.
     FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
     (!name b len. local_region cenv es.scopes s name b len ==>
                     off + sz <= b \/ b + len <= off) /\
     off <= i /\ i < off + sz /\ i IN tn'.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >> conj_tac
  >- (irule alloca_frame_of_mem_frame >> simp[] >> metis_tac[]) >>
  drule stmt_state_rel_local_ptrs_alloca >>
  simp[alloca_inv_def, alloca_next_valid_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `off + sz <= s.vs_alloca_next` by metis_tac[] >>
  `~(s.vs_alloca_next <= i)` by decide_tac >> metis_tac[]
QED

(* The checked entry's scalar prefix, including both exact revert endpoints. *)
Theorem range_checked_scalar_run:
  !(s :venom_state) (op1 :operand) (op2 :operand) (a :256 word) (b :256 word)
      (cmp :opcode) (cv :string) (rv :string) (g1 :string) (z1 :string)
      (g2 :string) (z2 :string) (ev :string) (bound :num) (i :num)
      (A :string -> bool).
    MEM cmp [SGT; GT] /\ eval_operand op1 s = SOME a /\
    eval_operand op2 s = SOME b /\ scalar_available A op1 /\
    scalar_available A op2 /\ ALL_DISTINCT [cv; rv; g1; z1; g2; z2; ev] /\
    (!(x :string).
       op1 = Var x \/ op2 = Var x ==> ~MEM x [cv; rv; g1; z1; g2; z2; ev]) ==>
    scalar_code A
      [mk_inst i ASSIGN [op1] [cv]; mk_inst (i + (1 :num)) SUB [op2; op1] [rv];
       mk_inst (i + (2 :num)) cmp [op1; op2] [g1];
       mk_inst (i + (3 :num)) ISZERO [Var g1] [z1];
       mk_inst (i + (4 :num)) ASSERT [Var z1] ([] :string list);
       mk_inst (i + (5 :num)) GT [Var rv; Lit (n2w bound :256 word)] [g2];
       mk_inst (i + (6 :num)) ISZERO [Var g2] [z2];
       mk_inst (i + (7 :num)) ASSERT [Var z2] ([] :string list);
       mk_inst (i + (8 :num)) ADD [op1; Var rv] [ev]] /\
    run_inst_seq_mem_ok
      [mk_inst i ASSIGN [op1] [cv]; mk_inst (i + (1 :num)) SUB [op2; op1] [rv];
       mk_inst (i + (2 :num)) cmp [op1; op2] [g1];
       mk_inst (i + (3 :num)) ISZERO [Var g1] [z1];
       mk_inst (i + (4 :num)) ASSERT [Var z1] ([] :string list);
       mk_inst (i + (5 :num)) GT [Var rv; Lit (n2w bound :256 word)] [g2];
       mk_inst (i + (6 :num)) ISZERO [Var g2] [z2];
       mk_inst (i + (7 :num)) ASSERT [Var z2] ([] :string list);
       mk_inst (i + (8 :num)) ADD [op1; Var rv] [ev]] s /\
    run_inst_seq
      [mk_inst i ASSIGN [op1] [cv]; mk_inst (i + (1 :num)) SUB [op2; op1] [rv];
       mk_inst (i + (2 :num)) cmp [op1; op2] [g1];
       mk_inst (i + (3 :num)) ISZERO [Var g1] [z1];
       mk_inst (i + (4 :num)) ASSERT [Var z1] ([] :string list);
       mk_inst (i + (5 :num)) GT [Var rv; Lit (n2w bound :256 word)] [g2];
       mk_inst (i + (6 :num)) ISZERO [Var g2] [z2];
       mk_inst (i + (7 :num)) ASSERT [Var z2] ([] :string list);
       mk_inst (i + (8 :num)) ADD [op1; Var rv] [ev]] s =
    (if if cmp = SGT then a > b else w2n a > w2n b then
       Abort Revert_abort
         (revert_state
            (set_returndata ([] :word8 list)
               (update_var z1
                  (bool_to_word
                     (bool_to_word
                        (if cmp = SGT then a > b else (w2n a > w2n b)) = (0w
                        :256 word)))
                  (update_var g1
                     (bool_to_word (if cmp = SGT then a > b else w2n a > w2n b))
                     (update_var rv (b - a) (update_var cv a s))))))
     else if w2n (b - a) > w2n (n2w bound :256 word) then
       Abort Revert_abort
         (revert_state
            (set_returndata ([] :word8 list)
               (update_var z2
                  (bool_to_word
                     (bool_to_word (w2n (b - a) > w2n (n2w bound :256 word)) =
                      (0w :256 word)))
                  (update_var g2
                     (bool_to_word (w2n (b - a) > w2n (n2w bound :256 word)))
                     (update_var z1
                        (bool_to_word
                           (bool_to_word
                              (if cmp = SGT then a > b else (w2n a > w2n b)) =
                            (0w :256 word)))
                        (update_var g1
                           (bool_to_word
                              (if cmp = SGT then a > b else w2n a > w2n b))
                           (update_var rv (b - a) (update_var cv a s))))))))
     else
       OK
         (update_var ev (a + (b - a))
            (update_var z2
               (bool_to_word
                  (bool_to_word (w2n (b - a) > w2n (n2w bound :256 word)) = (0w
                     :256 word)))
               (update_var g2
                  (bool_to_word (w2n (b - a) > w2n (n2w bound :256 word)))
                  (update_var z1
                     (bool_to_word
                        (bool_to_word
                           (if cmp = SGT then a > b else (w2n a > w2n b)) = (0w
                           :256 word)))
                     (update_var g1
                        (bool_to_word
                           (if cmp = SGT then a > b else w2n a > w2n b))
                        (update_var rv (b - a) (update_var cv a s)))))))) /\
    lookup_var cv
      (update_var ev (a + (b - a))
         (update_var z2
            (bool_to_word
               (bool_to_word (w2n (b - a) > w2n (n2w bound :256 word)) = (0w
                  :256 word)))
            (update_var g2
               (bool_to_word (w2n (b - a) > w2n (n2w bound :256 word)))
               (update_var z1
                  (bool_to_word
                     (bool_to_word
                        (if cmp = SGT then a > b else (w2n a > w2n b)) = (0w
                        :256 word)))
                  (update_var g1
                     (bool_to_word (if cmp = SGT then a > b else w2n a > w2n b))
                     (update_var rv (b - a) (update_var cv a s))))))) = SOME a /\
    lookup_var ev
      (update_var ev (a + (b - a))
         (update_var z2
            (bool_to_word
               (bool_to_word (w2n (b - a) > w2n (n2w bound :256 word)) = (0w
                  :256 word)))
            (update_var g2
               (bool_to_word (w2n (b - a) > w2n (n2w bound :256 word)))
               (update_var z1
                  (bool_to_word
                     (bool_to_word
                        (if cmp = SGT then a > b else (w2n a > w2n b)) = (0w
                        :256 word)))
                  (update_var g1
                     (bool_to_word (if cmp = SGT then a > b else w2n a > w2n b))
                     (update_var rv (b - a) (update_var cv a s))))))) =
    SOME (a + (b - a)) /\
    !(x :string).
      ~MEM x [cv; rv; g1; z1; g2; z2; ev] ==>
      lookup_var x
        (update_var z1
           (bool_to_word
              (bool_to_word (if cmp = SGT then a > b else (w2n a > w2n b)) =
               (0w :256 word)))
           (update_var g1
              (bool_to_word (if cmp = SGT then a > b else w2n a > w2n b))
              (update_var rv (b - a) (update_var cv a s)))) = lookup_var x s /\
      lookup_var x
        (update_var z2
           (bool_to_word
              (bool_to_word (w2n (b - a) > w2n (n2w bound :256 word)) = (0w
                 :256 word)))
           (update_var g2
              (bool_to_word (w2n (b - a) > w2n (n2w bound :256 word)))
              (update_var z1
                 (bool_to_word
                    (bool_to_word
                       (if cmp = SGT then a > b else (w2n a > w2n b)) = (0w
                       :256 word)))
                 (update_var g1
                    (bool_to_word (if cmp = SGT then a > b else w2n a > w2n b))
                    (update_var rv (b - a) (update_var cv a s)))))) =
      lookup_var x s /\
      lookup_var x
        (update_var ev (a + (b - a))
           (update_var z2
              (bool_to_word
                 (bool_to_word (w2n (b - a) > w2n (n2w bound :256 word)) = (0w
                    :256 word)))
              (update_var g2
                 (bool_to_word (w2n (b - a) > w2n (n2w bound :256 word)))
                 (update_var z1
                    (bool_to_word
                       (bool_to_word
                          (if cmp = SGT then a > b else (w2n a > w2n b)) = (0w
                          :256 word)))
                    (update_var g1
                       (bool_to_word
                          (if cmp = SGT then a > b else w2n a > w2n b))
                       (update_var rv (b - a) (update_var cv a s))))))) =
      lookup_var x s
Proof
  rpt gen_tac >> strip_tac >>
  simp[LET_THM] >>
  conj_tac
  >- (gvs[scalar_available_def] >>
      simp[scalar_code_def, scalar_shape_def, scalar_binary_def,
           scalar_unary_def, scalar_available_def, mk_inst_def]) >>
  conj_tac
  >- (gvs[] >> irule run_inst_seq_mem_ok_every >>
      simp[below_frontier_no_ranges, mk_inst_def, inst_dload_in_section_def]) >>
  reverse conj_tac
  >- (gvs[ALL_DISTINCT] >> simp[lookup_var_update_var] >> rpt strip_tac >>
      simp[lookup_var_update_var]) >>
  qabbrev_tac `bad1 = if cmp = SGT then word_gt a b else w2n a > w2n b` >>
  qabbrev_tac `bad2 = (w2n (b-a) > w2n (n2w bound : bytes32))` >>
  qabbrev_tac `s1 = update_var cv a s` >>
  qabbrev_tac `s2 = update_var rv (b-a) s1` >>
  qabbrev_tac `s3 = update_var g1 (bool_to_word bad1) s2` >>
  qabbrev_tac `s4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) s3` >>
  qabbrev_tac `s5 = update_var g2 (bool_to_word bad2) s4` >>
  qabbrev_tac `s6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) s5` >>
  `eval_operand op1 s1 = SOME a /\ eval_operand op2 s1 = SOME b /\
   eval_operand op1 s2 = SOME a /\ eval_operand op2 s2 = SOME b /\
   eval_operand op1 s6 = SOME a` by
    (Cases_on `op1` >> Cases_on `op2` >>
     gvs[eval_operand_def, lookup_var_update_var, ALL_DISTINCT,
         Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `s4`, Abbr `s5`, Abbr `s6`]) >>
  `step_inst_base (mk_inst i ASSIGN [op1] [cv]) s = OK s1` by
    (simp[Abbr `s1`] >> irule slot_copy_step_assign >> simp[]) >>
  `step_inst_base (mk_inst (i+1) SUB [op2;op1] [rv]) s1 = OK s2` by
    (simp[Abbr `s2`] >> irule step_SUB >> simp[]) >>
  `step_inst_base (mk_inst (i+2) cmp [op1;op2] [g1]) s2 = OK s3` by
    (simp[Abbr `s3`, Abbr `bad1`] >> gvs[] >>
     FIRST [irule step_SGT, irule step_GT] >> simp[]) >>
  `step_inst_base (mk_inst (i+3) ISZERO [Var g1] [z1]) s3 = OK s4` by
    (qunabbrev_tac `s4` >> irule step_ISZERO >>
     simp[Abbr `s3`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst (i+4) ASSERT [Var z1] []) s4 =
     if bad1 then Abort Revert_abort (revert_state (set_returndata [] s4))
     else OK s4` by
    (Cases_on `bad1` >> rewrite_tac[]
     >- (irule step_ASSERT_revert >>
         simp[Abbr `s4`, eval_operand_def, lookup_var_update_var]) >>
     irule step_ASSERT_ok >> qexists `1w : bytes32` >>
     simp[Abbr `s4`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2]) s4 = OK s5` by
    (qunabbrev_tac `s5` >> qunabbrev_tac `bad2` >> irule step_GT >>
     fs[ALL_DISTINCT] >>
     simp[Abbr `s4`, Abbr `s3`, Abbr `s2`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst (i+6) ISZERO [Var g2] [z2]) s5 = OK s6` by
    (qunabbrev_tac `s6` >> irule step_ISZERO >>
     simp[Abbr `s5`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst (i+7) ASSERT [Var z2] []) s6 =
     if bad2 then Abort Revert_abort (revert_state (set_returndata [] s6))
     else OK s6` by
    (Cases_on `bad2` >> rewrite_tac[]
     >- (irule step_ASSERT_revert >>
         simp[Abbr `s6`, eval_operand_def, lookup_var_update_var]) >>
     irule step_ASSERT_ok >> qexists `1w : bytes32` >>
     simp[Abbr `s6`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst (i+8) ADD [op1;Var rv] [ev]) s6 =
     OK (update_var ev (a+(b-a)) s6)` by
    (irule step_ADD >> conj_tac >- first_assum ACCEPT_TAC >>
     fs[ALL_DISTINCT] >>
     simp[Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`,
          eval_operand_def, lookup_var_update_var]) >>
  Cases_on `bad1` >> Cases_on `bad2` >> simp[run_inst_seq_def] >>
  gvs[Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`, markerTheory.Abbrev_def]
QED

(* ===== Empty suffix: the concrete test and complete outer post ===== *)
Theorem range_full_nil:
  stmt_env cenv lctx ret_ty (For id typ (Range e1 e2) bound body) sa = (cenv',sb) /\
  n1 <= n2 /\ N = Num (n2 - n1) /\
  sb.cs_current_bb = exit_lbl /\ sb.cs_current_insts = [] /\
  sb0.cs_next_var <= sb.cs_next_var /\ local_ptrs_reserved cenv sa /\
  ~not_fresh_at sa dv /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  lookup_block cond_lbl func.fn_blocks = SOME
    <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst eid EQ [Var cv; Var ev] [dv];
       mk_inst jid JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
  Inv = (\H rs ee G tn s. ?k.
    k + LENGTH rs = N /\
    rs = GENLIST (\j. Value (IntV (n1 + &(k+j)))) (LENGTH rs) /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    expr_sim_inv cenv cx env ee /\ lookup_scopes id ee.scopes = NONE /\
    s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ret_pc_ok cenv sa s /\
    return_buf_frame d cenv sb0 s /\ return_buf_sep d cenv ee s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    lookup_var cv s = SOME (i2w (n1 + &k)) /\ lookup_var ev s = SOME (i2w n2) /\
    lookup_var p s = SOME w /\ FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n w,sz) /\
    ptr_covers G tn p s sz /\ op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
    op_taint tn (Var ev) = {} /\ op_prov G (Var ev) = NONE /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
       FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es0 sa s0 cenv ee s /\
    (!aid off z i. FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
       (!nm b z'. local_region cenv es0.scopes s0 nm b z' ==> off+z <= b \/ b+z' <= off) /\
       off <= i /\ i < off+z /\ i IN tn.t_mem ==> i IN tn0.t_mem)) /\
  Done = (\H ee G tn s.
    stmt_lands lctx sb (INL ()) s /\ ~s.vs_halted /\ ~block_is_terminated sb /\
    cenv_top_ext cenv cenv' ee.scopes /\ stmt_state_rel H ctx func cenv' cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ return_buf_frame d cenv' sb s /\
    return_buf_sep d cenv' ee s /\ ghost_inv_at (DF H) lo d cenv' cx ee G tn s /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
       FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es0 sa s0 cenv' ee s /\
    (!aid off z i. FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
       (!nm b z'. local_region cenv es0.scopes s0 nm b z' ==> off+z <= b \/ b+z' <= off) /\
       off <= i /\ i < off+z /\ i IN tn.t_mem ==> i IN tn0.t_mem)) ==>
  !es s G tn.
    ~s.vs_halted /\ storage_trace_domain cx st0 es.storage_trace /\
    (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H [] es G tn s) /\
    gas_admissible (eval_for cx tyv id body []) ok es ==>
    ?t G1 tn1. !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
      Done H (es with gas_obs := []) G1 tn1 t
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qexistsl [`jump_to exit_lbl (update_var dv 1w s)`,
    `step_prov PG G (mk_inst eid EQ [Var cv; Var ev] [dv]) (update_var dv 1w s)`,
    `step_taint (mk_inst eid EQ [Var cv; Var ev] [dv]) s (update_var dv 1w s) tn`] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >>
  simp[] >> strip_tac >>
  `cenv' = cenv` by fs[range_full_outer_env] >> gvs[] >>
  `lookup_var cv s = SOME (i2w n2)` by metis_tac[i2w_counter_end] >>
  conj_asm1_tac
  >- (irule range_full_nil_path >>
      simp[eval_operand_def, get_instruction_def] >>
      reverse conj_tac >- fs[ghost_inv_at_def] >>
      qexistsl_tac [`cv`, `dv`, `eid`, `ev`, `jid`, `body_lbl`, `i2w n2`] >>
      simp[]) >>
  qmatch_goalsub_abbrev_tac `ghost_inv_at _ _ _ _ _ _ G1 tn1 t` >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
   (!x. x <> dv ==> FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x))` by
    simp[Abbr `G1`, Abbr `tn1`, Abbr `t`, SRULE [] copy_eq_jump_frames] >>
  `!x. not_fresh_at sa x ==> x <> dv` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[Abbr `t`, lookup_var_def, update_var_def, jump_to_def,
       FLOOKUP_UPDATE] >> metis_tac[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_inst_idx = 0 /\
   t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    simp[Abbr `t`, jump_to_def, update_var_def] >>
  `return_buf_sep d cenv (es with gas_obs := []) t` by
    (rewrite_tac [bodyFullSharedTheory.return_buf_sep_gas_obs] >>
     irule (INST_TYPE [alpha |-> ``:256``]
       bodyFullSharedTheory.return_buf_sep_locals_kept) >>
     conj_tac
     >- (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK _,G1,tn1)`
           (mp_then (Pos hd) mp_tac bodyFullSharedTheory.return_buf_allocas_path) >>
         disch_then (qspecl_then [`sb0`,`es`,`d`,`cenv`] mp_tac) >> simp[]) >>
     qexistsl_tac [`H`,`ctx`,`cx`,`es`,`func`,`s`,`sa`] >> simp[]) >>
  suspend "posts"
QED

Resume range_full_nil[posts]:
  simp[stmt_lands_def, block_is_terminated_def, cenv_top_ext_refl] >>
  conj_tac >- suspend "relation" >>
  conj_tac >- suspend "storage" >>
  conj_tac >- suspend "buffer" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- (irule allocaHistoryTheory.alloca_history_jump >>
              simp[] >> qexists_tac `s` >> simp[]) >>
  conj_tac >- (simp[Abbr `t`, jump_to_def, update_var_def, allocas_below_fmp_def] >>
              metis_tac[allocas_below_fmp_def]) >>
  conj_tac >- (rpt strip_tac >>
    `x <> dv` by metis_tac[] >>
    `lookup_var x s = SOME v` by
      (qpat_x_assum `!x v. not_fresh_at sa x /\ _ ==> _` irule >> simp[]) >>
    fs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  conj_tac >- suspend "allocation" >>
  metis_tac[]
QED

Resume range_full_nil[relation]:
  simp[Abbr `t`, stmt_state_rel_jump_to] >>
  irule stmt_state_rel_update_var >> simp[] >>
  metis_tac[exprSimOperandsTheory.fresh_not_local_ptr]
QED

Resume range_full_nil[storage]:
  irule (iffRL vyperStorageFootprintTheory.storage_well_formed_on_backends) >>
  qexists_tac `es` >> simp[]
QED

Resume range_full_nil[buffer]:
  Cases_on `d` >- fs[return_buf_frame_def] >>
  PairCases_on `x` >> fs[return_buf_frame_def] >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sb0` >> simp[]
QED

Resume range_full_nil[ghost]:
  irule ghost_inv_at_exterior_frame >>
  qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >> simp[]
QED

Resume range_full_nil[allocation]:
  simp[Abbr `t`] >>
  `not_local_ptr cenv es.scopes dv` by
    metis_tac[exprSimOperandsTheory.fresh_not_local_ptr] >>
  drule_all alloca_frame_update_var >>
  disch_then (qspec_then `1w` mp_tac) >>
  simp[alloca_frame_def, local_region_def, jump_to_def, lookup_var_def]
QED

Finalise range_full_nil

(* Scalar certification fixes both ghosts before the dead-set parameter. *)
Theorem range_scalar_joint_lift:
  !code A s ctx func bb PG G tn lo explicit.
    scalar_code A code /\
    (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
    ~s.vs_halted /\ allocas_from lo s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    run_inst_seq_mem_ok code s ==>
    ?G' tn' j.
      (!D. inst_seq_ptr D 0 ctx func PG G tn code s G' tn') /\
      (!v. ~MEM v (FLAT (MAP (\i. i.inst_outputs) code)) ==>
        FLOOKUP G' v = FLOOKUP G v /\
        FLOOKUP tn'.t_var v = FLOOKUP tn.t_var v /\
        op_taint tn' (Var v) = op_taint tn (Var v)) /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!t. run_inst_seq code s = OK t ==>
        (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
          (s,G,tn) []
          (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code),G',tn')) /\
        (!v. v IN A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) code)) ==>
          op_prov G' (Var v) = NONE /\ op_taint tn' (Var v) = {})) /\
      (!a t. run_inst_seq code s = Abort a t ==>
        !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
          (s,G,tn) [] (Abort a (t with vs_inst_idx := j),G',tn'))
Proof
  rpt gen_tac >> strip_tac >>
  `!D. ?H tm. inst_seq_ptr D 0 ctx func PG G tn code s H tm` by
    (gen_tac >> irule scalar_code_inst_seq_ptr_lo >>
     simp[allocas_from_def] >> qexists_tac `A` >> simp[]) >>
  qpat_assum `!D. ?H tm. _`
    (qspec_then `ARB` (qx_choosel_then [`G'`, `tn'`] assume_tac)) >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn code s G' tn'` by
    (gen_tac >> first_x_assum (qspec_then `D` strip_assume_tac) >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  drule_all scalar_seq_metadata_frame_lo >> strip_tac >>
  `!A. scalar_code A code ==>
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS /\
               i.inst_opcode <> DALLOCA) code` by
    (POP_ASSUM_LIST (K ALL_TAC) >> Induct_on `code` >>
     simp[scalar_code_def] >> rpt gen_tac >> strip_tac >>
     reverse conj_tac >- metis_tac[] >>
     gvs[scalar_shape_def, scalar_binary_def, scalar_unary_def,
         venomInstTheory.is_terminator_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS /\
               i.inst_opcode <> DALLOCA) code` by metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code` by
    fs[EVERY_MEM] >>
  `(ctx_has_dalloca ctx ==> !pre i post u'.
      code = pre ++ i::post /\ run_inst_seq pre s = OK u' ==>
      dalloca_no_wrap i u')` by
    (rpt strip_tac >> `MEM i code` by metis_tac[MEM_APPEND, MEM] >>
     fs[EVERY_MEM]) >>
  qexistsl_tac [`G'`, `tn'`] >>
  asm_simp_tac bool_ss [LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM] >>
  conj_tac >- suspend "success" >>
  suspend "abort"
QED

Resume range_scalar_joint_lift[success]:
  gen_tac >> strip_tac >> conj_tac
  >- (gen_tac >> irule (cj 1 run_inst_seq_origin_ptr_lift) >> metis_tac[]) >>
  metis_tac[scalar_seq_success_clean]
QED

Resume range_scalar_joint_lift[abort]:
  Cases_on `?a t. run_inst_seq code s = Abort a t`
  >- (pop_assum strip_assume_tac >>
      drule_all run_inst_seq_origin_ptr_abort_lift >>
      disch_then (qspecl_then [`explicit`, `PG`]
        (qx_choose_then `j` assume_tac)) >>
      qexists_tac `j` >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qexists_tac `0` >> metis_tac[]
QED

Finalise range_scalar_joint_lift

(* Paired body compilation fixes actual endpoints; containment is separate. *)
Theorem range_body_compiler_pair:
  !bc lctx ret_ty body sb0 sb1 shadow_sb0.
    compile_stmts bc lctx ret_ty body sb0 = ((),sb1) /\
    gas_shadow_state sb0 shadow_sb0 ==>
    ?bc' shadow_sb1.
      stmts_env bc lctx ret_ty body sb0 = (bc',sb1) /\
      stmts_env (gas_shadow_env T bc) lctx ret_ty (MAP gas_shadow_stmt body) shadow_sb0 =
        (gas_shadow_env T bc',shadow_sb1) /\
      compile_stmts (gas_shadow_env T bc) lctx ret_ty (MAP gas_shadow_stmt body) shadow_sb0 =
        ((),shadow_sb1) /\
      gas_shadow_state sb1 shadow_sb1
Proof
  rpt gen_tac >> rewrite_tac[compile_stmts_env] >> strip_tac >>
  qspecl_then [`body`, `bc`, `lctx`, `ret_ty`] mp_tac
    (Q.INST [`sd` |-> `T`] gas_shadow_stmts_env_env) >>
  simp[gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_def] >>
  disch_then (qspecl_then [`sb0`, `shadow_sb0`] (drule_then mp_tac)) >>
  Cases_on `stmts_env bc lctx ret_ty body sb0` >>
  Cases_on `stmts_env (gas_shadow_env T bc) lctx ret_ty (MAP gas_shadow_stmt body) shadow_sb0` >>
  gvs[]
QED

(* Restrict surrounding shadow code to the actual paired body segment. *)
Theorem range_body_pair_containment:
  !bc ret_ty body exit_lbl incr_lbl sb0 sb1 shadow_sb0 shadow_sb1
    shadow_sa shadow_sb func shadow_func.
    compile_stmts bc (InLoop exit_lbl incr_lbl) ret_ty body sb0 = ((),sb1) /\
    compile_stmts (gas_shadow_env T bc) (InLoop exit_lbl incr_lbl) ret_ty
      (MAP gas_shadow_stmt body) shadow_sb0 = ((),shadow_sb1) /\
    gas_shadow_state sb0 shadow_sb0 /\
    fn_has_code sb0 sb1 func /\
    fn_has_code shadow_sa shadow_sb shadow_func /\
    cs_extends shadow_sa shadow_sb0 /\
    cs_extends shadow_sb1 shadow_sb
    ==>
    ?body_cenv.
      stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty body sb0 =
        (body_cenv,sb1) /\
      stmts_env (gas_shadow_env T bc) (InLoop exit_lbl incr_lbl) ret_ty
        (MAP gas_shadow_stmt body) shadow_sb0 = (gas_shadow_env T body_cenv,shadow_sb1) /\
      gas_shadow_state sb1 shadow_sb1 /\
      fn_has_code sb0 sb1 func /\
      fn_has_code shadow_sb0 shadow_sb1 shadow_func
Proof
  rpt gen_tac >> strip_tac >>
  drule_all range_body_compiler_pair >> strip_tac >> gvs[] >>
  `cs_extends shadow_sb0 shadow_sb1` by
    metis_tac[cs_mono_def, cj 2 stmtLoweringMonoTheory.compile_stmt_cs_mono] >>
  irule fn_has_code_mid >> metis_tac[]
QED

(* EQ/JNZ changes only the fresh condition register and program position. *)
Theorem range_entry_condition_frame:
  !H D lo d ctx func cenv cx e sa s G tn PG cv ev dv body_lbl exit_lbl j1 j2 p
      sz.
    stmt_state_rel H ctx func cenv cx e s /\
    ghost_inv_at D lo d cenv cx e G tn s /\ local_ptrs_reserved cenv sa /\
    (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
    (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==> x <> dv) /\ not_local_ptr cenv e.scopes dv /\
    op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
    op_prov G (Var cv) = NONE /\ op_prov G (Var ev) = NONE /\ dv <> p /\
    ptr_covers G tn p s sz ==>
    step_prov PG
      (step_prov PG G (mk_inst j1 EQ [Var cv; Var ev] [dv])
         (update_var dv (bool_to_word F) s))
      (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
      (jump_to body_lbl
         (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) =
    DRESTRICT G (COMPL {dv}) /\
    step_taint (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
      (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
      (jump_to body_lbl
         (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
      (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
         (update_var dv (bool_to_word F) s) tn) =
    tn with t_var := fmupdate dv {} tn.t_var /\
    stmt_state_rel H ctx func cenv cx e
      (jump_to body_lbl
         (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) /\
    ghost_inv_at D lo d cenv cx e
      (step_prov PG
         (step_prov PG G (mk_inst j1 EQ [Var cv; Var ev] [dv])
            (update_var dv (bool_to_word F) s))
         (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
         (jump_to body_lbl
            (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
      (step_taint (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
         (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
         (jump_to body_lbl
            (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
         (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
            (update_var dv (bool_to_word F) s) tn))
      (jump_to body_lbl
         (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) /\
    ptr_covers
      (step_prov PG
         (step_prov PG G (mk_inst j1 EQ [Var cv; Var ev] [dv])
            (update_var dv (bool_to_word F) s))
         (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
         (jump_to body_lbl
            (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
      (step_taint (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
         (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
         (jump_to body_lbl
            (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
         (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
            (update_var dv (bool_to_word F) s) tn)) p
      (jump_to body_lbl
         (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) sz /\
    (jump_to body_lbl (update_var dv (bool_to_word F) s with vs_inst_idx := 1)).
    vs_current_bb = body_lbl /\
    (jump_to body_lbl (update_var dv (bool_to_word F) s with vs_inst_idx := 1)).
    vs_inst_idx = 0 /\
    ((jump_to body_lbl (update_var dv (bool_to_word F) s with vs_inst_idx := 1)).
     vs_halted <=> s.vs_halted) /\
    (jump_to body_lbl (update_var dv (bool_to_word F) s with vs_inst_idx := 1)).
    vs_memory = s.vs_memory /\
    (jump_to body_lbl (update_var dv (bool_to_word F) s with vs_inst_idx := 1)).
    vs_allocas = s.vs_allocas /\
    (jump_to body_lbl (update_var dv (bool_to_word F) s with vs_inst_idx := 1)).
    vs_alloca_next = s.vs_alloca_next /\
    !x. x <> dv ==>
        lookup_var x
          (jump_to body_lbl
             (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) =
        lookup_var x s /\
        FLOOKUP
          (step_prov PG
             (step_prov PG G (mk_inst j1 EQ [Var cv; Var ev] [dv])
                (update_var dv (bool_to_word F) s))
             (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
             (jump_to body_lbl
                (update_var dv (bool_to_word F) s with vs_inst_idx := 1))) x =
        FLOOKUP G x /\
        op_taint
          (step_taint
             (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
             (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
             (jump_to body_lbl
                (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
             (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
                (update_var dv (bool_to_word F) s) tn)) (Var x) =
        op_taint tn (Var x)
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  map_every qabbrev_tac
    [`ie = mk_inst j1 EQ [Var cv;Var ev] [dv]`,
     `ij = mk_inst j2 JNZ [Var dv;Label exit_lbl;Label body_lbl] []`,
     `ue = update_var dv (bool_to_word F) s`, `se = ue with vs_inst_idx := 1`,
     `b = jump_to body_lbl se`, `Ge = step_prov PG G ie ue`,
     `te = step_taint ie s ue tn`, `Gb = step_prov PG Ge ij b`,
     `tb = step_taint ij se b te`] >>
  `Ge = DRESTRICT G (COMPL {dv}) /\
   te = tn with t_var := tn.t_var |+ (dv,{})` by
    (simp[Abbr `Ge`, Abbr `te`, Abbr `ie`, Abbr `ue`, step_prov_def,
          set_prov_def, out_prov_def, step_taint_def, set_var_taint_def,
          out_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
          source_memory_write_ranges_def, range_bytes_def, written_taint_def,
          store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
          update_var_def, eval_operand_def, taint_component_equality,
          FLOOKUP_DEF, EXTENSION] >>
     Cases_on `lookup_var cv s` >> simp[] >> metis_tac[]) >>
  `Gb = Ge /\ tb = te` by
    (simp[Abbr `Gb`, Abbr `tb`, Abbr `ij`, Abbr `b`, Abbr `se`,
          step_prov_def, set_prov_def, out_prov_def, step_taint_def,
          set_var_taint_def, mem_taint_def, new_site_bytes_def,
          step_writes_def, source_memory_write_ranges_def, range_bytes_def,
          written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
          mk_inst_def, jump_to_def, taint_component_equality, FLOOKUP_DEF,
          DRESTRICT_UNIV, EXTENSION, SF CONJ_ss]) >>
  simp[] >>
  conj_tac >- suspend "relation" >>
  conj_tac >- suspend "ghost" >>
  fs[ptr_covers_def, op_taint_def, Abbr `b`, Abbr `se`, Abbr `ue`,
     jump_to_def, update_var_def, lookup_var_def,
     FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[]
QED

Resume range_entry_condition_frame[relation]:
  simp[Abbr `b`, Abbr `se`, Abbr `ue`, stmt_state_rel_jump_to,
       stmt_state_rel_inst_idx] >>
  irule stmt_state_rel_update_var >> simp[]
QED

Resume range_entry_condition_frame[ghost]:
  irule ghost_inv_at_exterior_frame >>
  qexistsl_tac [`G`, `e`, `s`, `sa`, `tn`] >>
  simp[Abbr `b`, Abbr `se`, Abbr `ue`, jump_to_def, update_var_def,
       lookup_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >>
  metis_tac[]
QED

Finalise range_entry_condition_frame

(* Compiler witnesses are fixed before any runtime state or horizon. *)
Theorem range_full_body_entry:
  !cx id typ e1 e2 bound body DF lo d PG tops bindings ctx shadow_ctx func
      shadow_func cenv env env' ret_ty lctx RetQ tyv sa sb shadow_sa shadow_sb.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (For id typ (Range e1 e2) bound body) /\
    (!target.
       supported_stmt_expr_exists (expr_abi_decode_target_root target)
         (For id typ (Range e1 e2) bound body) ==>
       occurs_abi_decode_target target tops) /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ (Range e1 e2) bound body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ (Range e1 e2) bound body) /\
    call_evaluation_safe cx
      (int_calls_stmt (For id typ (Range e1 e2) bound body)) /\
    frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv
      ret_ty /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
    stmt_env cenv lctx ret_ty (For id typ (Range e1 e2) bound body) sa =
    (cenv,sb) /\
    stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (For id typ (Range e1 e2) bound body)) shadow_sa =
    (gas_shadow_env T cenv,shadow_sb) /\ gas_shadow_state sa shadow_sa /\
    gas_shadow_state sb shadow_sb /\ gas_shadow_context ctx shadow_ctx /\
    ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
    (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
    ~block_is_terminated sa ==>
    ?st bc body_cenv body_env' sb0 sb1 shadow_sb0 shadow_sb1 p sz ainst cv ev
        dv nv entry_lbl cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2
        i3 sj op1 s1 op2 rv g1 z1 g2 z2.
      sz = type_memory_bytes cenv typ /\
      ainst =
      mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p] /\
      p = STRING #"%" (toString st.cs_next_var) /\
      cv = STRING #"%" (toString (st.cs_next_var + 1)) /\
      entry_lbl = fresh_label_output "for_entry" st.cs_next_label /\
      cond_lbl = fresh_label_output "for_cond" (st.cs_next_label + 1) /\
      body_lbl = fresh_label_output "for_body" (st.cs_next_label + 2) /\
      incr_lbl = fresh_label_output "for_incr" (st.cs_next_label + 3) /\
      exit_lbl = fresh_label_output "for_exit" (st.cs_next_label + 4) /\
      declare_local cenv id typ st =
      (bc,st with cs_next_var := st.cs_next_var + 1) /\ cs_extends sa st /\
      cs_extends st sb0 /\ cs_extends st sb /\
      sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id /\
      st.cs_next_id <= sb0.cs_next_id /\
      lookup_block st.cs_current_bb func.fn_blocks =
      SOME
        <|bb_label := st.cs_current_bb;
          bb_instructions :=
            st.cs_current_insts ++
            [mk_inst st.cs_next_id ALLOCA
               [Lit (n2w (type_memory_bytes cenv typ))] [p];
             mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] []]|> /\
      compile_stmt (gas_shadow_env T cenv) lctx ret_ty
        (For id typ (Range (gas_shadow_expr e1) (gas_shadow_expr e2)) bound
           (MAP gas_shadow_stmt body)) shadow_sa = ((),shadow_sb) /\
      (!a1 m1 a2 m2.
         e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2) ==>
         st = sa /\ ev = STRING #"%" (toString (sa.cs_next_var + 2)) /\
         dv = STRING #"%" (toString (sa.cs_next_var + 3)) /\
         j1 = sa.cs_next_id + 5 /\ j2 = sa.cs_next_id + 6 /\
         j3 = sa.cs_next_id + 7 /\ sb0.cs_next_var = sa.cs_next_var + 4 /\
         lookup_block entry_lbl func.fn_blocks =
         SOME
           <|bb_label := entry_lbl;
             bb_instructions :=
               [mk_inst (sa.cs_next_id + 2) ASSIGN [Lit (i2w m1)] [cv];
                mk_inst (sa.cs_next_id + 3) ADD
                  [Lit (i2w m1); Lit (i2w m2 - i2w m1)] [ev];
                mk_inst (sa.cs_next_id + 4) JMP [Label cond_lbl] []]|>) /\
      (~(?a1 m1 a2 m2. e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2)) ==>
       lower_value compile_expr cenv typ e1 sa = (op1,s1) /\
       lower_value compile_expr cenv typ e2 s1 = (op2,st) /\
       rv = STRING #"%" (toString (st.cs_next_var + 2)) /\
       g1 = STRING #"%" (toString (st.cs_next_var + 3)) /\
       z1 = STRING #"%" (toString (st.cs_next_var + 4)) /\
       g2 = STRING #"%" (toString (st.cs_next_var + 5)) /\
       z2 = STRING #"%" (toString (st.cs_next_var + 6)) /\
       ev = STRING #"%" (toString (st.cs_next_var + 7)) /\
       dv = STRING #"%" (toString (st.cs_next_var + 8)) /\
       j1 = st.cs_next_id + 12 /\ j2 = st.cs_next_id + 13 /\
       j3 = st.cs_next_id + 14 /\ sb0.cs_next_var = st.cs_next_var + 9 /\
       lookup_block entry_lbl func.fn_blocks =
       SOME
         <|bb_label := entry_lbl;
           bb_instructions :=
             [mk_inst (st.cs_next_id + 2) ASSIGN [op1] [cv];
              mk_inst (st.cs_next_id + 3) SUB [op2; op1] [rv];
              mk_inst (st.cs_next_id + 4)
                (if is_signed_type typ then SGT else GT) [op1; op2] [g1];
              mk_inst (st.cs_next_id + 5) ISZERO [Var g1] [z1];
              mk_inst (st.cs_next_id + 6) ASSERT [Var z1] [];
              mk_inst (st.cs_next_id + 7) GT [Var rv; Lit (n2w bound)] [g2];
              mk_inst (st.cs_next_id + 8) ISZERO [Var g2] [z2];
              mk_inst (st.cs_next_id + 9) ASSERT [Var z2] [];
              mk_inst (st.cs_next_id + 10) ADD [op1; Var rv] [ev];
              mk_inst (st.cs_next_id + 11) JMP [Label cond_lbl] []]|>) /\
      for_code func cenv bc ret_ty body id tyv p sz ainst cv ev dv nv cond_lbl
        exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
      lookup_block cond_lbl func.fn_blocks =
      SOME
        <|bb_label := cond_lbl;
          bb_instructions :=
            [mk_inst j1 EQ [Var cv; Var ev] [dv];
             mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
      lookup_block body_lbl func.fn_blocks = SOME bbb /\
      get_instruction bbb 0 = SOME (mk_inst j3 MSTORE [Var p; Var cv] []) /\
      sb0.cs_current_bb = body_lbl /\
      sb0.cs_current_insts = [mk_inst j3 MSTORE [Var p; Var cv] []] /\
      compile_stmts bc (InLoop exit_lbl incr_lbl) ret_ty body sb0 = ((),sb1) /\
      (~block_is_terminated sb1 ==>
       sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
       sj.cs_current_insts =
       sb1.cs_current_insts ++ [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
       fn_has_code sb1 sj func) /\ sj.cs_next_var = sb1.cs_next_var /\
      nv = STRING #"%" (toString sj.cs_next_var) /\ i1 = sj.cs_next_id /\
      i2 = sj.cs_next_id + 1 /\ i3 = sj.cs_next_id + 2 /\
      lookup_block incr_lbl func.fn_blocks =
      SOME
        <|bb_label := incr_lbl;
          bb_instructions :=
            [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
             mk_inst i2 ASSIGN [Var nv] [cv];
             mk_inst i3 JMP [Label cond_lbl] []]|> /\
      sb.cs_current_bb = exit_lbl /\ sb.cs_current_insts = [] /\
      sb0.cs_next_var <= sb.cs_next_var /\ ~not_fresh_at sa dv /\
      not_fresh_at sb0 p /\ not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\
      (!x. not_fresh_at sa x ==> not_fresh_at sb0 x) /\
      sa.cs_next_id <= ainst.inst_id /\ sa.cs_next_id <= sb0.cs_next_id /\
      sa.cs_next_var <= sb0.cs_next_var /\ cs_extends sa sb0 /\
      cs_extends shadow_sa shadow_sb0 /\ cs_extends shadow_sb1 shadow_sb /\
      stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty body sb0 = (body_cenv,sb1) /\
      stmts_env (gas_shadow_env T bc) (InLoop exit_lbl incr_lbl) ret_ty (MAP gas_shadow_stmt body)
        shadow_sb0 = (gas_shadow_env T body_cenv,shadow_sb1) /\
      gas_shadow_state sb0 shadow_sb0 /\ gas_shadow_state sb1 shadow_sb1 /\
      fn_has_code sb0 sb1 func /\
      fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
      type_stmts (extend_local env id typ F) ret_ty body = SOME body_env' /\
      body_inv tops ctx bc cx /\ supported_stmts tops bindings body /\
      (!target.
         supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
         occurs_abi_decode_target target tops) /\ stmts_exprs_ok bc body /\
      call_evaluation_safe cx (int_calls_stmts body) /\
      frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc
        ret_ty /\ local_ptrs_reserved bc sb0 /\ ~block_is_terminated sb0 /\
      (!H. dead_lo_ok H (DF H) lo bc cx) /\
      (!x z. bc.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sb0 x) /\
      (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sb0 x) /\
      !st0 es0 s0 G0 tn0 n1 n2 N k a rs es s G tn w.
        n1 <= n2 /\ N = Num (n2 - n1) /\ N < dimword (:256) /\
        value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
        body_for_full_ok cx tyv id body
          (GENLIST (\j. Value (IntV (n1 + &j))) N) /\ k + LENGTH (a::rs) = N /\
        a::rs = GENLIST (\j. Value (IntV (n1 + &(k + j)))) (LENGTH (a::rs)) /\
        body_const_cells_agree [(NONE,tops)] cx env es /\
        expr_sim_inv cenv cx env es /\ lookup_scopes id es.scopes = NONE /\
        storage_trace_domain cx st0 es.storage_trace /\
        s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
        ret_pc_ok cenv sa s /\ return_buf_frame d cenv sb0 s /\
        lookup_var cv s = SOME (i2w (n1 + &k)) /\
        lookup_var ev s = SOME (i2w n2) /\ lookup_var p s = SOME w /\
        FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n w,sz) /\
        ptr_covers G tn p s sz /\ op_taint tn (Var cv) = {} /\
        op_prov G (Var cv) = NONE /\ op_taint tn (Var ev) = {} /\
        op_prov G (Var ev) = NONE /\ alloca_history func s /\
        (!fn inst v. frag_reachable ctx func s fn inst v ==> dalloca_fmp_headroom inst v) /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
        s0.vs_alloca_next <= s.vs_alloca_next /\
        (!x v.
           not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
           lookup_var x s = SOME v) /\
        (!aid b.
           FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa x ==>
             FLOOKUP G x = FLOOKUP G0 x /\
             op_taint tn (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame cenv es0 sa s0 cenv es s /\
        (!aid off z i.
           FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
           (!nm b z'.
              local_region cenv es0.scopes s0 nm b z' ==>
              off + z <= b \/ b + z' <= off) /\ off <= i /\ i < off + z /\
           i IN tn.t_mem ==>
           i IN tn0.t_mem) /\
        (!H. valid_horizon cx st0 H es.storage_trace ==>
             stmt_state_rel H ctx func cenv cx es s /\
             storage_well_formed_on cx es (FST H) /\
             ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
        gas_admissible (eval_for cx tyv id body (a::rs)) (stmt_res_ok lctx) es ==>
        a = Value (IntV (n1 + &k)) /\ k < N /\ body_stmts_full_ok cx body /\
        bind (read_result cx a) (\v. push_scope_with_var id tyv v)
          (es with gas_obs := []) =
        (INL (),
         es with
         <|scopes :=
             fmupdate id
               <|assignable := F; type := tyv; value := IntV (n1 + &k);
                 popped := []|> FEMPTY::es.scopes; gas_obs := []|>) /\
        expr_sim_inv bc cx (extend_local env id typ F)
          (es with
           <|scopes :=
               fmupdate id
                 <|assignable := F; type := tyv; value := IntV (n1 + &k);
                   popped := []|> FEMPTY::es.scopes; gas_obs := []|>) /\
        ce_locals_declared bc (extend_local env id typ F) /\
        locals_alloc_ok bc (extend_local env id typ F) /\
        gas_admissible (eval_stmts cx body)
          (stmt_res_ok (InLoop exit_lbl incr_lbl))
          (es with
           <|scopes :=
               fmupdate id
                 <|assignable := F; type := tyv; value := IntV (n1 + &k);
                   popped := []|> FEMPTY::es.scopes; gas_obs := []|>) /\
        cenv_top_ext cenv bc
          (es with
           <|scopes :=
               fmupdate id
                 <|assignable := F; type := tyv; value := IntV (n1 + &k);
                   popped := []|> FEMPTY::es.scopes; gas_obs := []|>).scopes /\
        (mstore (w2n w) (i2w (n1 + &k))
           (jump_to body_lbl
              (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
         vs_inst_idx := 1).vs_current_bb = sb0.cs_current_bb /\
        (mstore (w2n w) (i2w (n1 + &k))
           (jump_to body_lbl
              (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
         vs_inst_idx := 1).vs_inst_idx = LENGTH sb0.cs_current_insts /\
        ~(mstore (w2n w) (i2w (n1 + &k))
           (jump_to body_lbl
              (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
         vs_inst_idx := 1).vs_halted /\
        ret_pc_ok bc sb0
          (mstore (w2n w) (i2w (n1 + &k))
             (jump_to body_lbl
                (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
           vs_inst_idx := 1) /\
        return_buf_frame d bc sb0
          (mstore (w2n w) (i2w (n1 + &k))
             (jump_to body_lbl
                (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
           vs_inst_idx := 1) /\
        alloca_history func
          (mstore (w2n w) (i2w (n1 + &k))
             (jump_to body_lbl
                (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
           vs_inst_idx := 1) /\
        (ctx_has_dalloca ctx ==>
         allocas_below_fmp
           (mstore (w2n w) (i2w (n1 + &k))
              (jump_to body_lbl
                 (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
            vs_inst_idx := 1)) /\
        (!fn inst v.
           frag_reachable ctx func
             (mstore (w2n w) (i2w (n1 + &k))
                (jump_to body_lbl
                   (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
              vs_inst_idx := 1) fn inst v ==>
           dalloca_fmp_headroom inst v) /\
        s0.vs_alloca_next <=
        (mstore (w2n w) (i2w (n1 + &k))
           (jump_to body_lbl
              (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
         vs_inst_idx := 1).vs_alloca_next /\
        (!x v.
           not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
           lookup_var x
             (mstore (w2n w) (i2w (n1 + &k))
                (jump_to body_lbl
                   (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
              vs_inst_idx := 1) = SOME v) /\
        (!aid ab.
           FLOOKUP s0.vs_allocas aid = SOME ab ==>
           FLOOKUP
             (mstore (w2n w) (i2w (n1 + &k))
                (jump_to body_lbl
                   (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
              vs_inst_idx := 1).vs_allocas aid = SOME ab) /\
        (!x. not_fresh_at sa x ==>
             FLOOKUP
               (step_prov PG
                  (step_prov PG
                     (step_prov PG G (mk_inst j1 EQ [Var cv; Var ev] [dv])
                        (update_var dv (bool_to_word F) s))
                     (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl]
                        [])
                     (jump_to body_lbl
                        (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
                  (mk_inst j3 MSTORE [Var p; Var cv] [])
                  (mstore (w2n w) (i2w (n1 + &k))
                     (jump_to body_lbl
                        (update_var dv (bool_to_word F) s with vs_inst_idx := 1))))
               x = FLOOKUP G0 x /\
             op_taint
               (step_taint (mk_inst j3 MSTORE [Var p; Var cv] [])
                  (jump_to body_lbl
                     (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
                  (mstore (w2n w) (i2w (n1 + &k))
                     (jump_to body_lbl
                        (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
                  (step_taint
                     (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl]
                        [])
                     (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
                     (jump_to body_lbl
                        (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
                     (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
                        (update_var dv (bool_to_word F) s) tn))) (Var x) =
             op_taint tn0 (Var x)) /\
        alloca_frame cenv es0 sa s0 bc
          (es with
           <|scopes :=
               fmupdate id
                 <|assignable := F; type := tyv; value := IntV (n1 + &k);
                   popped := []|> FEMPTY::es.scopes; gas_obs := []|>)
          (mstore (w2n w) (i2w (n1 + &k))
             (jump_to body_lbl
                (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
           vs_inst_idx := 1) /\
        (!aid off az i.
           FLOOKUP s0.vs_allocas aid = SOME (off,az) /\ aid < sa.cs_next_id /\
           (!nm ab z'.
              local_region cenv es0.scopes s0 nm ab z' ==>
              off + az <= ab \/ ab + z' <= off) /\ off <= i /\ i < off + az /\
           i IN
           (step_taint (mk_inst j3 MSTORE [Var p; Var cv] [])
              (jump_to body_lbl
                 (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
              (mstore (w2n w) (i2w (n1 + &k))
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
              (step_taint
                 (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
                 (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
                 (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
                    (update_var dv (bool_to_word F) s) tn))).t_mem ==>
           i IN tn0.t_mem) /\
        !H. valid_horizon cx st0 H es.storage_trace ==>
            gas_origin_ptr_path
              (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (s,G,tn)
              []
              (OK
                 (mstore (w2n w) (i2w (n1 + &k))
                    (jump_to body_lbl
                       (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
                  vs_inst_idx := 1),
               step_prov PG
                 (step_prov PG
                    (step_prov PG G (mk_inst j1 EQ [Var cv; Var ev] [dv])
                       (update_var dv (bool_to_word F) s))
                    (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
                    (jump_to body_lbl
                       (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
                 (mk_inst j3 MSTORE [Var p; Var cv] [])
                 (mstore (w2n w) (i2w (n1 + &k))
                    (jump_to body_lbl
                       (update_var dv (bool_to_word F) s with vs_inst_idx := 1))),
               step_taint (mk_inst j3 MSTORE [Var p; Var cv] [])
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
                 (mstore (w2n w) (i2w (n1 + &k))
                    (jump_to body_lbl
                       (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
                 (step_taint
                    (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
                    (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
                    (jump_to body_lbl
                       (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
                    (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
                       (update_var dv (bool_to_word F) s) tn))) /\
            stmt_state_rel H ctx func bc cx
              (es with
               <|scopes :=
                   fmupdate id
                     <|assignable := F; type := tyv; value := IntV (n1 + &k);
                       popped := []|> FEMPTY::es.scopes; gas_obs := []|>)
              (mstore (w2n w) (i2w (n1 + &k))
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
               vs_inst_idx := 1) /\
            storage_well_formed_on cx
              (es with
               <|scopes :=
                   fmupdate id
                     <|assignable := F; type := tyv; value := IntV (n1 + &k);
                       popped := []|> FEMPTY::es.scopes; gas_obs := []|>)
              (FST H) /\
            ghost_inv_at (DF H) lo d bc cx
              (es with
               <|scopes :=
                   fmupdate id
                     <|assignable := F; type := tyv; value := IntV (n1 + &k);
                       popped := []|> FEMPTY::es.scopes; gas_obs := []|>)
              (step_prov PG
                 (step_prov PG
                    (step_prov PG G (mk_inst j1 EQ [Var cv; Var ev] [dv])
                       (update_var dv (bool_to_word F) s))
                    (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
                    (jump_to body_lbl
                       (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
                 (mk_inst j3 MSTORE [Var p; Var cv] [])
                 (mstore (w2n w) (i2w (n1 + &k))
                    (jump_to body_lbl
                       (update_var dv (bool_to_word F) s with vs_inst_idx := 1))))
              (step_taint (mk_inst j3 MSTORE [Var p; Var cv] [])
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
                 (mstore (w2n w) (i2w (n1 + &k))
                    (jump_to body_lbl
                       (update_var dv (bool_to_word F) s with vs_inst_idx := 1)))
                 (step_taint
                    (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] [])
                    (update_var dv (bool_to_word F) s with vs_inst_idx := 1)
                    (jump_to body_lbl
                       (update_var dv (bool_to_word F) s with vs_inst_idx := 1))
                    (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
                       (update_var dv (bool_to_word F) s) tn)))
              (mstore (w2n w) (i2w (n1 + &k))
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with vs_inst_idx := 1)) with
               vs_inst_idx := 1)
Proof
  rpt gen_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `cenv.ce_alloca_locals` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (ACCEPT_TAC o MATCH_MP contract_inv_alloca_locals o MATCH_MP body_inv_contract)) >>
  `!c lc s t. compile_stmts c lc ret_ty body s = ((),t) ==> cs_extends s t` by
    metis_tac[cs_mono_def, cj 2 stmtLoweringMonoTheory.compile_stmt_cs_mono] >>
  drule_all range_full_static_pre >> strip_tac >>
  suspend "geometry"
QED

Resume range_full_body_entry[geometry]:
  Cases_on `?a1 m1 a2 m2. e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2)` >>
  IF (qpat_assum `?a1 m1 a2 m2. e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2)` kall_tac)
    (pop_assum (fn th => mk_asm "literal_prefix" th >>
      qx_choosel_then [`a1`,`m1`,`a2`,`m2`] strip_assume_tac th))
    (pop_assum (fn th => mk_asm "checked_prefix" th >> assume_tac th)) >>

  (* Literal endpoint prefix. *)
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (qpat_x_assum `e1 = _` SUBST_ALL_TAC >>
     qpat_x_assum `e2 = _` SUBST_ALL_TAC) all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (drule_all (cj 1 range_full_compiler_geometry) >> strip_tac) all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (qpat_assum `stmt_env _ _ _ (For _ _ _ _ _) sa = _`
       (strip_assume_tac o SRULE [range_full_outer_env])) all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (Cases_on `declare_local (gas_shadow_env T cenv) id typ shadow_sa` >>
     rename1 `declare_local _ _ _ shadow_sa = (sbc,ss1)`) all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (qpat_assum `declare_local _ _ _ shadow_sa = _`
       (mp_then Any mp_tac declare_local_ptr) >>
     (impl_tac >- simp[]) >> disch_then strip_assume_tac) all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (`sbc = gas_shadow_env T bc` by
       (mp_tac (SRULE [gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_def]
          (Q.INST [`ty` |-> `typ`, `sd` |-> `T`]
             gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_declare_local)) >>
        disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[])) all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (qpat_x_assum `sbc = _` SUBST_ALL_TAC >>
     qpat_assum `declare_local _ _ _ sa = _`
       (mp_then Any mp_tac declare_local_ptr) >>
     (impl_tac >- simp[]) >> disch_then strip_assume_tac) all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (let
       fun prefix decls compile = qpat_assum compile
         (assume_tac o SRULE (decls @
           [gas_shadow_expr_def, Once compile_stmt_def, lower_value_int_lit,
            comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM,
            emit_local_alloca_def, fresh_label_def, emitHelperTheory.emit_inst_def,
            emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
            fresh_id_def, emit_def, new_block_def, fresh_var_def,
            emitHelperTheory.emit_jmp_if_not_terminated_def, comp_get_def,
            GSYM arithmeticTheory.ADD_ASSOC]))
     in
       qpat_assum `declare_local _ _ _ shadow_sa = _` (fn decl =>
         qpat_assum `ss1 = _` (fn next =>
         qpat_assum `FLOOKUP _.ce_vars id = SOME (PtrVar (Var (STRING _ (toString shadow_sa.cs_next_var))) _)`
           (fn binding => prefix [decl,next,binding] `compile_stmt _ _ _ _ shadow_sa = _`))) >>
       qpat_assum `declare_local _ _ _ sa = _` (fn decl =>
         qpat_assum `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var (STRING _ (toString sa.cs_next_var))) _)`
           (fn binding => prefix [decl,binding] `compile_stmt _ _ _ _ sa = _`))
     end) all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (qmatch_asmsub_abbrev_tac `compile_stmts _ _ _ (MAP gas_shadow_stmt body) ss0` >>
     qmatch_asmsub_abbrev_tac
       `compile_stmts _ (InLoop (fresh_label_output "for_exit" (sa.cs_next_label + 4)) _) _ body bs0`)
    all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (`gas_shadow_state bs0 ss0` by
       (qpat_assum `gas_shadow_state sa shadow_sa`
          (strip_assume_tac o REWRITE_RULE [gas_shadow_state_def]) >>
        simp[Abbr `bs0`, Abbr `ss0`, gas_shadow_state_def, gas_shadow_block_def,
             LIST_REL_APPEND, gas_shadow_inst_def])) all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (`sa.cs_next_label = shadow_sa.cs_next_label` by fs[gas_shadow_state_def]) all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (qpat_assum `exit_lbl = _` (fn ex =>
       qpat_assum `incr_lbl = _` (fn inc =>
       qpat_assum `sa.cs_next_label = shadow_sa.cs_next_label` (fn lbl =>
       qpat_x_assum `(\(_, _). _) _ = ((),shadow_sb)`
         (assume_tac o REWRITE_RULE [SYM lbl, SYM ex, SYM inc]) >>
       qpat_x_assum `(\(_, _). _) _ = ((),sb)`
         (assume_tac o REWRITE_RULE [SYM ex, SYM inc]))))) all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (`cs_extends sa bs0` by
       (simp[cs_extends_def, Abbr `bs0`] >> qexists_tac `[_; _; _]` >> simp[])) all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (`cs_extends shadow_sa ss0` by
       (simp[cs_extends_def, Abbr `ss0`] >> qexists_tac `[_; _; _]` >> simp[])) all_tac >>

  (* Checked endpoint prefix. *)
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (namedCases_on `lower_value compile_expr cenv typ e1 sa` ["op1 s1"] >>
     namedCases_on `lower_value compile_expr cenv typ e2 s1` ["op2 st"]) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (let
       fun pair_edge expr s t rel orig shadow =
         qpat_assum rel (fn related =>
           qpat_assum orig (fn left =>
             qpat_assum shadow (fn right =>
               qspecl_then [s,t]
                 (strip_assume_tac o SRULE [left,right] o (fn th => MATCH_MP th related))
                 (REWRITE_RULE [gas_shadow_compiles_def]
                   (Q.INST [`ty` |-> `typ`, `e` |-> expr, `sd` |-> `T`]
                     gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env)))))
     in
       namedCases_on `lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e1) shadow_sa`
         ["shadow_op1 shadow_s1"] >>
       pair_edge `e1` `sa` `shadow_sa` `gas_shadow_state sa shadow_sa`
         `lower_value compile_expr cenv typ e1 sa = _`
         `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _` >>
       qpat_x_assum `op1 = shadow_op1` (SUBST_ALL_TAC o SYM) >>
       namedCases_on `lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e2) shadow_s1`
         ["shadow_op2 shadow_st"] >>
       pair_edge `e2` `s1` `shadow_s1` `gas_shadow_state s1 shadow_s1`
         `lower_value compile_expr cenv typ e2 s1 = _`
         `lower_value _ _ _ (gas_shadow_expr e2) shadow_s1 = _` >>
       qpat_x_assum `op2 = shadow_op2` (SUBST_ALL_TAC o SYM)
     end) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (qpat_assum `lower_value _ _ _ e1 sa = (op1,s1)`
       (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
     qpat_assum `lower_value _ _ _ e2 s1 = (op2,st)`
       (mp_then Any strip_assume_tac (cj 2 compile_expr_grows))) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (`cs_extends sa st /\ sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id` by
       (conj_tac >- (irule cs_extends_trans >> qexists_tac `s1` >> simp[]) >>
        conj_tac >-
          (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `s1.cs_next_var` >> simp[]) >>
        irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `s1.cs_next_id` >> simp[])) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (`cs_extends shadow_sa shadow_st` by
       (qpat_assum `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _`
          (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
        qpat_assum `lower_value _ _ _ (gas_shadow_expr e2) shadow_s1 = _`
          (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
        irule cs_extends_trans >> qexists_tac `shadow_s1` >> simp[])) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (`!e a m. gas_shadow_expr e = Literal a (IntL m) ==> e = Literal a (IntL m)` by
       (Cases >> simp[NoAsms, gas_shadow_expr_def])) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (`~(?a1 m1 a2 m2. gas_shadow_expr e1 = Literal a1 (IntL m1) /\
                       gas_shadow_expr e2 = Literal a2 (IntL m2))` by
       (strip_tac >> qpat_x_assum `~(?a1 m1 a2 m2. e1 = _ /\ e2 = _)` mp_tac >>
        simp[NoAsms] >> qexistsl_tac [`a1`,`m1`,`a2`,`m2`] >>
        conj_tac >> first_x_assum irule >> first_assum ACCEPT_TAC)) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (drule_all (cj 2 range_full_compiler_geometry) >> strip_tac) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (qpat_assum `stmt_env _ _ _ (For _ _ _ _ _) sa = _`
       (strip_assume_tac o SRULE [range_full_outer_env])) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (`for_range_checked_code cenv lctx ret_ty id typ bound body op1 op2 st = ((),sb)` by
       (qpat_assum `compile_stmt _ _ _ _ sa = ((),sb)` (SUBST1_TAC o SYM) >>
        sym_tac >> irule compile_stmt_for_range_checked >> gvs[])) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (`for_range_checked_code (gas_shadow_env T cenv) lctx ret_ty id typ bound (MAP gas_shadow_stmt body)
        op1 op2 shadow_st = ((),shadow_sb)` by
       (qpat_assum `compile_stmt _ _ _ _ shadow_sa = ((),shadow_sb)` (SUBST1_TAC o SYM) >>
        sym_tac >> irule compile_stmt_for_range_checked >> gvs[])) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (Cases_on `declare_local (gas_shadow_env T cenv) id typ shadow_st` >>
     rename1 `declare_local _ _ _ shadow_st = (sbc,ss1)`) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (qpat_assum `declare_local _ _ _ shadow_st = _`
       (mp_then Any mp_tac declare_local_ptr) >>
     (impl_tac >- simp[]) >> disch_then strip_assume_tac) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (`sbc = gas_shadow_env T bc` by
       (mp_tac (SRULE [gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_def]
          (Q.INST [`ty` |-> `typ`, `sd` |-> `T`]
             gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_declare_local)) >>
        disch_then (qspecl_then [`st`, `shadow_st`] mp_tac) >> simp[])) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (qpat_x_assum `sbc = _` SUBST_ALL_TAC >>
     qpat_assum `declare_local _ _ _ st = _`
       (mp_then Any mp_tac declare_local_ptr) >>
     (impl_tac >- simp[]) >> disch_then strip_assume_tac) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (`(if is_signed_type typ then emitHelper$emit_op SGT [op1;op2]
                             else emitHelper$emit_op GT [op1;op2]) =
      emitHelper$emit_op (if is_signed_type typ then SGT else GT) [op1;op2]` by
       (Cases_on `is_signed_type typ` >> pop_assum (fn th => simp[NoAsms, th]))) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (let
       fun prefix decl_pat binding_pat eq =
         qpat_assum decl_pat (fn decl =>
         qpat_assum binding_pat
           (fn binding =>
             qpat_assum `(if is_signed_type typ then emitHelper$emit_op SGT _ else _) = _`
               (fn order => qpat_x_assum eq (assume_tac o SRULE
                 [decl,binding,order,for_range_checked_code_def,compile_range_bound_checks_def,
                  comp_bind_def,comp_ignore_bind_def,comp_return_def,LET_THM,
                  emit_local_alloca_def,fresh_label_def,emitHelperTheory.emit_inst_def,
                  emitHelperTheory.emit_op_def,emitHelperTheory.emit_void_def,
                  fresh_id_def,emit_def,new_block_def,fresh_var_def,
                  emitHelperTheory.emit_jmp_if_not_terminated_def,comp_get_def,
                  GSYM arithmeticTheory.ADD_ASSOC]))))
     in
       qpat_assum `ss1 = _` (fn next =>
         qpat_x_assum `declare_local _ _ _ shadow_st = _`
           (assume_tac o REWRITE_RULE [next])) >>
       prefix `declare_local _ _ _ shadow_st = _`
         `FLOOKUP _.ce_vars id = SOME (PtrVar (Var (STRING _ (toString shadow_st.cs_next_var))) _)`
         `for_range_checked_code _ _ _ _ _ _ _ _ _ shadow_st = _` >>
       prefix `declare_local _ _ _ st = _`
         `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var (STRING _ (toString st.cs_next_var))) _)`
         `for_range_checked_code _ _ _ _ _ _ _ _ _ st = _`
     end) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (qmatch_asmsub_abbrev_tac `compile_stmts _ _ _ (MAP gas_shadow_stmt body) ss0` >>
     qmatch_asmsub_abbrev_tac
       `compile_stmts _ (InLoop (fresh_label_output "for_exit" (st.cs_next_label + 4)) _) _ body bs0`)
    all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (`gas_shadow_state bs0 ss0` by
       (qpat_assum `gas_shadow_state st shadow_st`
          (strip_assume_tac o REWRITE_RULE [gas_shadow_state_def]) >>
        simp[Abbr `bs0`, Abbr `ss0`, gas_shadow_state_def, gas_shadow_block_def,
             LIST_REL_APPEND, gas_shadow_inst_def])) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (`st.cs_next_label = shadow_st.cs_next_label` by fs[gas_shadow_state_def]) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (qpat_assum `exit_lbl = _` (fn ex =>
       qpat_assum `incr_lbl = _` (fn inc =>
       qpat_assum `st.cs_next_label = shadow_st.cs_next_label` (fn lbl =>
       qpat_x_assum `(\(_, _). _) _ = ((),shadow_sb)`
         (assume_tac o REWRITE_RULE [SYM lbl, SYM ex, SYM inc]) >>
       qpat_x_assum `(\(_, _). _) _ = ((),sb)`
         (assume_tac o REWRITE_RULE [SYM ex, SYM inc]))))) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (`cs_extends st bs0` by
       (simp[cs_extends_def, Abbr `bs0`] >> qexists_tac `[_; _; _]` >> simp[])) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (`cs_extends shadow_st ss0` by
       (simp[cs_extends_def, Abbr `ss0`] >> qexists_tac `[_; _; _]` >> simp[])) all_tac >>
  IF (fn g => fn ctxt => asm "checked_prefix" kall_tac g ctxt)
    (`cs_extends sa bs0` by
       (irule cs_extends_trans >> qexists_tac `st` >> simp[]) >>
     `cs_extends shadow_sa ss0` by
       (irule cs_extends_trans >> qexists_tac `shadow_st` >> simp[])) all_tac >>
  IF (fn g => fn ctxt => asm "literal_prefix" kall_tac g ctxt)
    (asm_x "literal_prefix" kall_tac) (asm_x "checked_prefix" kall_tac) >>

  (* Pair the actual body compilations. *)
  namedCases_on `compile_stmts bc (InLoop exit_lbl incr_lbl) ret_ty body bs0`
    ["unit_result bs1"] >> Cases_on `unit_result` >>
  qpat_assum `compile_stmts _ _ _ body bs0 = _`
    (mp_then Any (qspec_then `ss0` mp_tac) range_body_compiler_pair) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`body_cenv`,`ssend`] strip_assume_tac) >>
  qpat_assum `compile_stmts _ _ _ (MAP gas_shadow_stmt body) ss0 = _` (fn th =>
    qpat_x_assum `(\(_, _). _) _ = ((),shadow_sb)`
      (assume_tac o SRULE [th])) >>
  qpat_assum `compile_stmts _ _ _ body bs0 = _` (fn th =>
    qpat_x_assum `(\(_, _). _) _ = ((),sb)` (assume_tac o SRULE [th])) >>
  namedCases_on `emitHelper$emit_jmp_if_not_terminated incr_lbl bs1` ["bj_unit bj"] >>
  Cases_on `bj_unit` >>
  namedCases_on `emitHelper$emit_jmp_if_not_terminated incr_lbl ssend` ["sj_unit shj"] >>
  Cases_on `sj_unit` >>
  (let
     fun suffix step eq = qpat_assum step (fn th =>
       qpat_x_assum eq (assume_tac o SRULE
         [SRULE [emitHelperTheory.emit_jmp_if_not_terminated_def,
                 comp_bind_def, comp_get_def, emitHelperTheory.emit_inst_def,
                 LET_THM] th, GSYM arithmeticTheory.ADD_ASSOC]))
   in
     suffix `emitHelper$emit_jmp_if_not_terminated incr_lbl bs1 = _`
       `(\(_, _). _) ((if block_is_terminated bs1 then _ else _) bs1) = ((),sb)` >>
     suffix `emitHelper$emit_jmp_if_not_terminated incr_lbl ssend = _`
       `(\(_, _). _) ((if block_is_terminated ssend then _ else _) ssend) = ((),shadow_sb)`
   end) >>
  (`cs_extends bs1 bj /\ bj.cs_next_var = bs1.cs_next_var /\
      (~block_is_terminated bs1 ==>
       bj.cs_blocks = bs1.cs_blocks /\ bj.cs_current_bb = bs1.cs_current_bb /\
       bj.cs_current_insts = bs1.cs_current_insts ++
         [mk_inst bs1.cs_next_id JMP [Label incr_lbl] []])` by suspend "body_jump") >>

  (* Close the body and increment blocks in both compilations. *)
  `cs_extends ssend shj` by
    (Cases_on `block_is_terminated ssend` >>
     pop_assum (fn term =>
       qpat_assum `emitHelper$emit_jmp_if_not_terminated incr_lbl ssend = _`
         (SUBST1_TAC o SYM o SRULE
          [term, emitHelperTheory.emit_jmp_if_not_terminated_def,
           emitHelperTheory.emit_inst_def, comp_bind_def, comp_return_def,
           comp_get_def, fresh_id_def, emit_def, LET_THM])) >>
     simp[cs_extends_refl] >> irule cs_extends_same_block >> simp[]) >>
  (let
     fun finish eq =
       qpat_assum eq (SUBST1_TAC o SYM) >> simp[cs_extends_def] >>
       qexists_tac `[_; _]` >> simp[]
   in
     (`cs_extends bj sb` by finish
       `_ with <|cs_next_var := bj.cs_next_var + 1; cs_next_id := _; cs_current_bb := _; cs_current_insts := _; cs_blocks := _|> = sb`) >>
     (`cs_extends shj shadow_sb` by finish
       `_ with <|cs_next_var := shj.cs_next_var + 1; cs_next_id := _; cs_current_bb := _; cs_current_insts := _; cs_blocks := _|> = shadow_sb`)
   end) >>
  `cs_extends ssend shadow_sb` by
    (irule cs_extends_trans >> qexists_tac `shj` >> simp[]) >>
  qpat_assum `compile_stmts _ _ _ body bs0 = _` (mp_then Any strip_assume_tac
    (REWRITE_RULE [cs_mono_def] (cj 2 stmtLoweringMonoTheory.compile_stmt_cs_mono))) >>
  `cs_extends bs1 sb` by
    (irule cs_extends_trans >> qexists_tac `bj` >> simp[]) >>
  `cs_extends sa bs1` by
    (irule cs_extends_trans >> qexists_tac `bs0` >> simp[]) >>
  `cs_extends sa bj` by
    (irule cs_extends_trans >> qexists_tac `bs1` >> simp[]) >>
  (let
     fun interval l r =
       qspecl_then [`sa`, l, r, `sb`, `func`] mp_tac fn_has_code_mid >>
       simp[cs_extends_refl]
   in
     (`fn_has_code bs0 bs1 func` by interval `bs0` `bs1`) >>
     (`fn_has_code bs1 bj func` by interval `bs1` `bj`) >>
     (`fn_has_code bj sb func` by interval `bj` `sb`)
   end) >>
  drule_all range_body_pair_containment >>
  disch_then (qx_choose_then `paired_cenv` strip_assume_tac) >>
  `paired_cenv = body_cenv` by
    (qpat_assum `stmts_env _ _ _ body bs0 = (body_cenv,bs1)` (fn earlier =>
       qpat_assum `stmts_env _ _ _ body bs0 = (paired_cenv,bs1)`
         (mp_tac o PURE_REWRITE_RULE [earlier])) >> simp[NoAsms, EQ_SYM_EQ]) >>
  qpat_x_assum `paired_cenv = body_cenv` SUBST_ALL_TAC >>
  (let
     fun suffix_eq ttac = qpat_assum
       `_ with <|cs_next_var := bj.cs_next_var + 1; cs_next_id := _; cs_current_bb := _; cs_current_insts := _; cs_blocks := _|> = sb` ttac
   in
     (`emitted_blocks bj sb = [HD sb.cs_blocks; HD (TL sb.cs_blocks)]` by
       (irule emitted_blocks_append >> suffix_eq (SUBST1_TAC o SYM) >> simp[NoAsms])) >>
     (`lookup_block (HD sb.cs_blocks).bb_label func.fn_blocks = SOME (HD sb.cs_blocks)` by
       (qpat_assum `fn_has_code bj sb func`
          (qspec_then `HD sb.cs_blocks` mp_tac o CONJUNCT1 o REWRITE_RULE [fn_has_code_def]) >>
        qpat_assum `emitted_blocks bj sb = _` (fn th => simp[NoAsms, th]))) >>
     (`lookup_block incr_lbl func.fn_blocks =
        SOME <|bb_label := incr_lbl; bb_instructions :=
          [mk_inst bj.cs_next_id ADD [Var cv;Lit 1w] [STRING #"%" (toString bj.cs_next_var)];
           mk_inst (bj.cs_next_id + 1) ASSIGN [Var (STRING #"%" (toString bj.cs_next_var))] [cv];
           mk_inst (bj.cs_next_id + 2) JMP [Label cond_lbl] []]|>` by
       (qpat_assum `lookup_block (HD sb.cs_blocks).bb_label _ = _` mp_tac >>
        suffix_eq (SUBST1_TAC o SYM) >>
        qpat_assum `incr_lbl = _` (fn inc =>
          qpat_assum `cond_lbl = _` (fn cnd =>
            qpat_assum `cv = _` (fn cnt => simp[NoAsms, inc, cnd, cnt])))))
   end) >>

  (* Choose the same compiler witnesses for the static and runtime posts. *)
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z` by
    (rpt strip_tac >>
     qpat_assum `ce_locals_declared cenv env`
       (qspecl_then [`id`,`l`] mp_tac o REWRITE_RULE [ce_locals_declared_def]) >>
     simp[]) >>
  drule_all range_body_static_transport >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 assume_tac
          (qx_choose_then `body_env'` assume_tac))))) >>
  `bs0.cs_current_bb = body_lbl /\ bs0.cs_current_insts = sb0.cs_current_insts /\
   bs0.cs_next_var = sb0.cs_next_var` by simp[Abbr `bs0`] >>
  `sb.cs_next_var = bj.cs_next_var + 1` by
    (qpat_assum
       `_ with <|cs_next_var := bj.cs_next_var + 1; cs_next_id := _; cs_current_bb := _; cs_current_insts := _; cs_blocks := _|> = sb`
       (SUBST1_TAC o SYM) >> simp[NoAsms]) >>
  `bs0.cs_next_var <= sb.cs_next_var` by simp[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at bs0 x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  qabbrev_tac `sz = type_memory_bytes cenv typ` >>
  qabbrev_tac `bnv = STRING #"%" (toString bj.cs_next_var)` >>
  (IF (qpat_assum `lower_value compile_expr cenv typ e2 s1 = (op2,st)` kall_tac)
      (qabbrev_tac `bstart = st`) (qabbrev_tac `bstart = sa`)) >>
  `sa.cs_next_var <= bstart.cs_next_var /\
   bstart.cs_next_var + 1 <= bs0.cs_next_var /\
   sa.cs_next_id <= bstart.cs_next_id /\
   bstart.cs_next_id <= bs0.cs_next_id` by simp[Abbr `bstart`, Abbr `bs0`] >>
  `declare_local cenv id typ bstart = (bc,bstart with cs_next_var := bstart.cs_next_var + 1)` by
    simp[Abbr `bstart`] >>
  `local_ptrs_reserved cenv bstart` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved bc bs0` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `bstart with cs_next_var := bstart.cs_next_var + 1` >>
     simp[] >> irule declare_local_reserved >> metis_tac[]) >>
  `sz = 32 /\ type_memory_size tyv = 32 /\ word_memory_type tyv` by
    (qpat_assum `is_int_type typ` mp_tac >>
     qpat_assum `evaluate_type _ typ = SOME tyv` mp_tac >>
     simp[Abbr `sz`, NoAsms] >> rpt (pop_assum kall_tac) >>
     Cases_on `typ` >> simp[] >> rename1 `BaseT bt` >>
     Cases_on `bt` >> simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
                           type_memory_bytes_def] >> rpt strip_tac >>
     gvs[type_memory_size_def, word_memory_type_def]) >>
  `~not_fresh_at sa dv /\ (!scs. not_local_ptr cenv scs cv /\
     not_local_ptr cenv scs dv /\ not_local_ptr cenv scs bnv)` by
    (conj_tac
     >- simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
     >> gen_tac >> rpt conj_tac >> simp[Abbr `bnv`] >>
     irule stmtSimForTheory.reserved_fresh_not_local >>
     qexists_tac `bstart` >> simp[]) >>
  `bc.ce_is_ctor = cenv.ce_is_ctor /\ bc.ce_return_pc = cenv.ce_return_pc /\
   bc.ce_return_buf = cenv.ce_return_buf` by
    (rpt conj_tac >>
     qpat_assum `bc with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = cenv`
       (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [SYM th]))) >>
     simp[NoAsms]) >>
  `!H. dead_lo_ok H (DF H) lo bc cx` by
    (qpat_assum `bc.ce_is_ctor = cenv.ce_is_ctor` (fn eq =>
       qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx` mp_tac >>
       simp[NoAsms, bodyPtrDefsTheory.dead_lo_ok_def, eq])) >>
  `not_fresh_at bs0 p /\ not_fresh_at bs0 cv /\ not_fresh_at bs0 ev /\
   ~block_is_terminated bs0` by
    simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj,
         block_is_terminated_def, mk_inst_def, is_terminator_def] >>
  `MEM (mk_inst bstart.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func)` by
    (qpat_assum `lookup_block bstart.cs_current_bb func.fn_blocks = SOME _`
      (mp_then Any mp_tac fragExecTheory.lookup_block_fn_insts) >> simp[Abbr `sz`]) >>
  `bs0.cs_next_var <= bj.cs_next_var` by simp[] >>
  (let
     fun choose st ainst j1 j2 j3 checked =
       qexistsl_tac ([st, `bc`, `body_cenv`, `body_env'`, `bs0`,`bs1`,`ss0`,`ssend`,
         `p`,`sz`,ainst,
         `cv`,`ev`,`dv`,`bnv`,`entry_lbl`,`cond_lbl`,`exit_lbl`,`body_lbl`,`incr_lbl`,
         j1,j2,j3,`bbb`,`bj.cs_next_id`,`bj.cs_next_id+1`,`bj.cs_next_id+2`,`bj`] @ checked)
   in
     IF (qpat_assum `lower_value compile_expr cenv typ e2 s1 = (op2,bstart)` kall_tac)
       (choose `bstart` `mk_inst bstart.cs_next_id ALLOCA [Lit (n2w sz)] [p]`
         `bstart.cs_next_id+12` `bstart.cs_next_id+13` `bstart.cs_next_id+14`
         [`op1`,`s1`,`op2`,`rv`,`g1`,`z1`,`g2`,`z2`])
       (choose `bstart` `mk_inst bstart.cs_next_id ALLOCA [Lit (n2w sz)] [p]`
         `bstart.cs_next_id+5` `bstart.cs_next_id+6` `bstart.cs_next_id+7`
         [`Lit 0w`,`bstart`,`Lit 0w`,`""`,`""`,`""`,`""`,`""`])
   end) >>
  rpt (goal_term (fn tm =>
    if is_conj tm then
      let val head = fst (strip_comb (fst (dest_conj tm))) in
        if is_const head andalso #Name (dest_thy_const head) = "for_code"
        then conj_asm1_tac else conj_tac
      end
    else NO_TAC)) >>
  IF (qmatch_goalsub_rename_tac `for_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (PURE_REWRITE_TAC [for_code_def] >> rpt conj_tac) all_tac >>
  IF (qpat_assum `~(?u i v j. e1 = Literal u (IntL i) /\ e2 = Literal v (IntL j))` kall_tac)
    (IF (qmatch_goalsub_rename_tac `!u i v j. e1 = Literal u (IntL i) /\ e2 = Literal v (IntL j) ==> _`)
      (map_every qx_gen_tac [`au`,`mi`,`av`,`mj`] >> disch_then strip_assume_tac >>
       qpat_assum `~(?u i v j. e1 = Literal u (IntL i) /\ e2 = Literal v (IntL j))`
         (MATCH_MP_TAC o NOT_ELIM) >>
       qexistsl_tac [`au`,`mi`,`av`,`mj`] >> simp[]) all_tac)
    all_tac >>
  IF (qmatch_goalsub_rename_tac `gas_admissible (eval_for _ _ _ _ _) _ _`)
    (suspend "entry_runtime")
    (IF (first_assum ACCEPT_TAC) all_tac
       (simp[Abbr `sz`, Abbr `bnv`, cs_extends_refl, ASCIInumbersTheory.toString_inj, mk_inst_def]))
  >>> NTH_GOAL (metis_tac[]) 2
  >>> NTH_GOAL (gvs[]) 2
  >> irule cs_extends_trans >> qexists_tac `bj` >> simp[]
QED

Resume range_full_body_entry[body_jump]:
  markerLib.RESUME_TAC >> Cases_on `block_is_terminated bs1` >>
  pop_assum (fn term =>
    assume_tac term >>
    qpat_assum `emitHelper$emit_jmp_if_not_terminated incr_lbl bs1 = _`
      (SUBST1_TAC o SYM o SRULE
       [term, emitHelperTheory.emit_jmp_if_not_terminated_def,
        emitHelperTheory.emit_inst_def, comp_bind_def, comp_return_def,
        comp_get_def, fresh_id_def, emit_def, LET_THM])) >>
  simp[cs_extends_refl] >>
  irule cs_extends_same_block >> simp[]
QED

Resume range_full_body_entry[entry_runtime]:
  markerLib.RESUME_TAC >>
  map_every qx_gen_tac [`st0`, `es0`, `s0`, `G0`, `tn0`, `n1`, `n2`,
    `N`, `k`, `a`, `rs`, `es`, `s`, `G`, `tn`, `w`] >> strip_tac >>
  drule_all range_cons_source_pre >>
  disch_then (qspecl_then [`exit_lbl`, `incr_lbl`] strip_assume_tac) >>
  qpat_abbrev_tac `ie = mk_inst _ EQ [Var cv;Var ev] [dv]` >>
  qpat_abbrev_tac `ij = mk_inst _ JNZ [Var dv;Label exit_lbl;Label body_lbl] []` >>
  qpat_abbrev_tac `im = mk_inst _ MSTORE [Var p;Var cv] []` >>
  map_every qabbrev_tac
    [`z = n1 + &k`,
     `ep = es with <|scopes :=
       (FEMPTY |+ (id,<|assignable := F; type := tyv; value := IntV z;
                         popped := []|>)) :: es.scopes; gas_obs := []|>`,
     `ue = update_var dv (bool_to_word F) s`, `se = ue with vs_inst_idx := 1`,
     `b = jump_to body_lbl se`, `u = mstore (w2n w) (i2w z) b`,
     `t = u with vs_inst_idx := 1`,
     `Ge = step_prov PG G ie ue`, `te = step_taint ie s ue tn`,
     `Gb = step_prov PG Ge ij b`, `tb = step_taint ij se b te`,
     `Gf = step_prov PG Gb im u`, `tt = step_taint im b u tb`] >>
  `value_has_type tyv (IntV z)` by
    ((metisTools.METIS_TAC [stmtSimForRangeTheory.range_value_has_type])) >>
  qabbrev_tac `scoped = es with scopes :=
    (FEMPTY |+ (id,<|assignable := F; type := tyv; value := IntV z;
                      popped := []|>)) :: es.scopes` >>
  `ep = scoped with gas_obs := []` by simp[Abbr `ep`, Abbr `scoped`, NoAsms] >>
  `expr_sim_inv bc cx (extend_local env id typ F) scoped /\
   ce_locals_declared bc (extend_local env id typ F) /\
   locals_alloc_ok bc (extend_local env id typ F)` by
    (drule_all range_declared_scope_inputs >> simp[Abbr `scoped`]) >>
  `expr_sim_inv bc cx (extend_local env id typ F) ep` by
    simp[exprSimHypsDefsTheory.expr_sim_inv_gas_obs] >>
  `(do v <- read_result cx a; push_scope_with_var id tyv v od)
    (es with gas_obs := []) = (INL (),ep)` by
    (qpat_assum `a = Value _` SUBST1_TAC >>
     qpat_assum `ep = scoped with gas_obs := []` SUBST1_TAC >>
     simp[Abbr `scoped`, Abbr `z`, NoAsms, read_result_def, bind_def, return_def,
          push_scope_with_var_def] >>
     simp[NoAsms, vyperStateTheory.evaluation_state_component_equality]) >>
  qabbrev_tac `H0 = storage_trace_horizon es.storage_trace` >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `alloca_inv s` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `allocas_from lo s` by
    (qpat_assum `ghost_inv_at (DF H0) _ _ _ _ _ _ _ s` mp_tac >>
     simp[NoAsms, ghost_inv_at_def]) >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     simp[NoAsms, allocas_from_def] >> disch_then drule >> simp[]) >>
  `w2n w + 32 <= s.vs_alloca_next` by
    (qpat_assum `alloca_inv s` mp_tac >>
     simp[NoAsms, alloca_inv_def, alloca_next_valid_def] >>
     strip_tac >> first_x_assum drule >> simp[Abbr `sz`]) >>
  `k < Num (n2-n1) /\ Num (n2-n1) < dimword(:256)` by
    (qpat_assum `N = Num _` (SUBST1_TAC o SYM) >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s,G,tn) [] (OK t,Gf,tt) /\
       t.vs_current_bb = body_lbl /\ t.vs_inst_idx = 1 /\ ~t.vs_halted /\
       (!x. x <> dv ==> lookup_var x t = lookup_var x s) /\
       t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
       (!x. x <> dv ==> FLOOKUP Gf x = FLOOKUP G x /\
                        op_taint tt (Var x) = op_taint tn (Var x)) /\
       tt.t_mem = tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32} /\
       tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm` by
    (qx_gen_tac `D` >>
     `lookup_var cv s = SOME (i2w (n1 + &k))` by
       (qpat_assum `lookup_var cv s = SOME (i2w z)` mp_tac >> simp[Abbr `z`, NoAsms]) >>
     drule_all (REWRITE_RULE [LET_THM] range_entry_joint_path) >>
     disch_then (qspecl_then [`D`,`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
     simp[NoAsms, Abbr `t`, Abbr `u`, Abbr `b`, Abbr `se`, Abbr `ue`,
          Abbr `Gf`, Abbr `tt`, Abbr `Gb`, Abbr `tb`, Abbr `Ge`, Abbr `te`,
          Abbr `ie`, Abbr `ij`, Abbr `im`, Abbr `z`]) >>
  `dv <> p` by simp[ASCIInumbersTheory.toString_inj] >>
  `!x. not_fresh_at sa x ==> x <> dv` by metis_tac[] >>
  qpat_assum `!scs. not_local_ptr cenv scs cv /\ _`
    (qspec_then `es.scopes` strip_assume_tac) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es b /\
       ghost_inv_at (DF H) lo d cenv cx es Gb tb b /\
       ptr_covers Gb tb p b sz /\
       (!x. x <> dv ==> lookup_var x b = lookup_var x s /\
          op_taint tb (Var x) = op_taint tn (Var x))` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
       (qspec_then `H` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     qspecl_then [`H`, `DF H`, `lo`, `d`, `ctx`, `func`, `cenv`, `cx`, `es`,
       `sa`, `s`, `G`, `tn`, `PG`, `cv`, `ev`, `dv`, `body_lbl`, `exit_lbl`,
       `ie.inst_id`, `ij.inst_id`, `p`, `sz`] mp_tac range_entry_condition_frame >>
     impl_tac >- simp[] >>
     pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
     conj_tac >-
       (qpat_assum `stmt_state_rel H ctx func cenv cx es (jump_to _ _)` mp_tac >>
        simp[NoAsms, Abbr `b`, Abbr `se`, Abbr `ue`]) >>
     conj_tac >-
       (qpat_assum `ghost_inv_at (DF H) lo d cenv cx es (step_prov _ _ _ _) _ _` mp_tac >>
        simp[NoAsms, Abbr `Gb`, Abbr `tb`, Abbr `Ge`, Abbr `te`, Abbr `b`,
             Abbr `se`, Abbr `ue`, Abbr `ie`, Abbr `ij`, mk_inst_def]) >>
     conj_tac >-
       (qpat_assum `ptr_covers (step_prov _ _ _ _) _ p _ sz` mp_tac >>
        simp[NoAsms, Abbr `Gb`, Abbr `tb`, Abbr `Ge`, Abbr `te`, Abbr `b`,
             Abbr `se`, Abbr `ue`, Abbr `ie`, Abbr `ij`, mk_inst_def]) >>
     qpat_assum `!x. x <> dv ==> lookup_var x (jump_to _ _) = _ /\ _` mp_tac >>
     simp[NoAsms, Abbr `tb`, Abbr `te`, Abbr `b`, Abbr `se`, Abbr `ue`,
          Abbr `ie`, Abbr `ij`, mk_inst_def]) >>
  `~not_fresh_at bstart p` by
    (simp[not_fresh_at_def] >> qexists_tac `bstart.cs_next_var` >> simp[]) >>
  `not_local_ptr cenv es.scopes p /\ not_local_ptr cenv (FEMPTY::es.scopes) p` by
    (conj_tac >> irule exprSimOperandsTheory.fresh_not_local_ptr >>
     qexists_tac `bstart` >> simp[]) >>
  `not_local_ptr bc (FEMPTY::es.scopes) p` by
    (irule not_local_ptr_name_update >> qexistsl_tac [`cenv`,`id`] >>
     simp[] >> qpat_assum `bc with <|ce_vars := _; ce_var_type := _;
                                    ce_dynarray_capacity := _|> = cenv` mp_tac >>
     simp[compile_env_component_equality]) >>
  `val_wf tyv (IntV z)` by
    (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >> simp[]) >>
  `lookup_var p b = SOME w /\ b.vs_allocas = s.vs_allocas` by
    (simp[Abbr `b`, Abbr `se`, Abbr `ue`, jump_to_def, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE] >> (metis_tac[Abbr `b`, Abbr `se`, Abbr `ue`, jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE])) >>
  `FLOOKUP s.vs_allocas bstart.cs_next_id = SOME (w2n w,32)` by
    (qpat_assum `FLOOKUP s.vs_allocas (mk_inst _ ALLOCA _ _).inst_id = _` mp_tac >>
     qpat_assum `sz = 32` mp_tac >> simp[NoAsms, mk_inst_def]) >>
  qabbrev_tac `stored_taint = tb with t_mem := tb.t_mem DIFF
    {i | w2n w <= i /\ i < w2n w + 32}` >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func bc cx scoped u /\
       ghost_inv_at (DF H) lo d bc cx scoped Gb stored_taint u` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ b /\ _`
       (qspec_then `H` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     qspecl_then [`H`, `ctx`, `func`, `cenv`, `cx`, `es`, `b`, `DF H`,
       `lo`, `d`, `Gb`, `tb`, `id`, `bc`, `p`, `sz`, `w`,
       `mk_inst bstart.cs_next_id ALLOCA [Lit (n2w sz)] [p]`, `tyv`, `z`]
       mp_tac range_entry_store_scope >>
     impl_tac >- simp[readonlyMemoryArgsPropsTheory.mk_inst_acc] >>
     pure_rewrite_tac[LET_THM] >> BETA_TAC >>
     simp[NoAsms, Abbr `scoped`, Abbr `u`, Abbr `stored_taint`]) >>
  `cv <> dv` by simp[ASCIInumbersTheory.toString_inj] >>
  `eval_operand (Var cv) b = SOME (i2w z) /\ op_taint tb (Var cv) = {}` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ b /\ _`
       (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >>
     qpat_assum `!x. x <> dv ==> lookup_var x b = _ /\ _`
       (qspec_then `cv` mp_tac) >>
     strip_tac >> simp[eval_operand_def]) >>
  `Gf = Gb /\ tt = stored_taint` by
    (mp_tac (Q.INST [`G` |-> `Gb`, `id` |-> `im.inst_id`, `dst` |-> `p`,
                     `s` |-> `b`, `a` |-> `w`, `value` |-> `Var cv`,
                     `w` |-> `i2w z`, `tn` |-> `tb`]
        exprSimPtrTopLevelImmutableCopyTheory.toplevel_immutable_mstore_ghost_frame) >>
     (impl_tac >- simp[]) >>
     simp[NoAsms, Abbr `Gf`, Abbr `tt`, Abbr `im`, Abbr `u`, Abbr `stored_taint`,
          readonlyMemoryArgsPropsTheory.mk_inst_acc]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func bc cx ep t /\
       storage_well_formed_on cx ep (FST H) /\
       ghost_inv_at (DF H) lo d bc cx ep Gf tt t` by
    ((qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >>
     pure_asm_rewrite_tac [] >>
     simp[Abbr `t`, stmt_state_rel_inst_idx, exprSimWordArgsTheory.stmt_state_rel_gas_obs,
          ghost_inv_at_inst_idx] >>
     conj_tac
     >- (`storage_well_formed_on cx ep (FST H) <=> storage_well_formed_on cx es (FST H)`
           suffices_by simp[] >>
         irule storage_well_formed_on_backends >>
         qpat_assum `ep = scoped with gas_obs := []` SUBST1_TAC >>
         simp[NoAsms, Abbr `scoped`]) >>
     qpat_assum `ghost_inv_at (DF H) lo d bc cx scoped Gb stored_taint u` mp_tac >>
     simp[NoAsms, ghost_inv_at_def] >> (metis_tac[Abbr `t`, stmt_state_rel_inst_idx, exprSimWordArgsTheory.stmt_state_rel_gas_obs, ghost_inv_at_inst_idx, NoAsms, Abbr `scoped`, ghost_inv_at_def, storage_well_formed_on_backends]))) >>
  `t.vs_memory = (mstore (w2n w) (i2w z) s).vs_memory` by
    simp[Abbr `t`, Abbr `u`, Abbr `b`, Abbr `se`, Abbr `ue`, mstore_def,
         jump_to_def, update_var_def] >>
  `tt.t_mem SUBSET tn.t_mem` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ [] _ /\ _` (qspec_then `DF H0` strip_assume_tac) >>
     simp[SUBSET_DEF]) >>
  qpat_assum `!D. gas_origin_ptr_path _ _ [] _ /\ _`
    (qspec_then `DF H0` strip_assume_tac) >>
  `ep.scopes = (FEMPTY |+ (id,<|assignable := F; type := tyv;
      value := IntV z; popped := []|>)) :: es.scopes` by
    (qpat_assum `ep = scoped with gas_obs := []` SUBST1_TAC >>
     simp[NoAsms, Abbr `scoped`]) >>
  `alloca_frame cenv es0 sa s0 bc ep t /\
   (!aid off az i. FLOOKUP s0.vs_allocas aid = SOME (off,az) /\ aid < sa.cs_next_id /\
     (!nm ab z'. local_region cenv es0.scopes s0 nm ab z' ==>
                  off+az <= ab \/ ab+z' <= off) /\
     off <= i /\ i < off+az /\ i IN tt.t_mem ==> i IN tn0.t_mem)` by
    (qspecl_then [`cenv`,`es0`,`sa`,`s0`,`cenv`,`es`,`s`,`bstart.cs_next_id`,
       `w`,`sz`,`id`,`bc`,`p`,`dv`,`t`,`i2w z`,`tt`,`tn`,`tn0`,
       `<|assignable := F; type := tyv; value := IntV z; popped := []|>`]
       mp_tac range_entry_anchor_frame >>
     (impl_tac >- (simp[ASCIInumbersTheory.toString_inj] >> first_assum ACCEPT_TAC)) >>
     strip_tac >> conj_tac
     >- (qpat_assum `alloca_frame cenv es0 sa s0 bc (es with scopes := _) t` mp_tac >>
         pure_rewrite_tac[alloca_frame_def] >>
         qpat_assum `ep.scopes = _` SUBST1_TAC >> simp[NoAsms]) >>
     first_assum ACCEPT_TAC) >>
  `cenv_top_ext cenv bc ep.scopes` by
    (qpat_assum `ep.scopes = _` SUBST1_TAC >>
     drule_all stmtSimDeclComposeTheory.cenv_top_ext_declare_local >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> x <> dv` (qspec_then `x` mp_tac) >>
     simp[]) >>
  `ret_pc_ok bc bs0 t` by
    (qspecl_then [`cenv`,`bc`,`sa`,`bs0`,`s`,`t`] mp_tac ret_pc_ok_frame >>
     (impl_tac >- (simp[] >> rpt strip_tac >> simp[])) >>
     disch_then ACCEPT_TAC) >>
  `return_buf_frame d bc bs0 t` by
    (Cases_on `d` >- fs[return_buf_frame_def] >>
     rename1 `return_buf_frame (SOME buf)` >> PairCases_on `buf` >>
     qpat_assum `return_buf_frame (SOME _) cenv bs0 s` mp_tac >>
     rewrite_tac[return_buf_frame_def] >>
     disch_then (qx_choose_then `x` (qx_choose_then `slot_size` strip_assume_tac)) >>
     qexistsl_tac [`x`,`slot_size`] >>
     `not_fresh_at sa x` by
       (qpat_assum `!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> _`
          (qspecl_then [`x`,`slot_size`] mp_tac) >> simp[]) >>
     simp[]) >>
  `alloca_history func t` by
    (drule_all bodyFullPathHistoryTheory.body_full_path_alloca_history >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi]) >>
  `!fn inst v. frag_reachable ctx func t fn inst v ==> dalloca_fmp_headroom inst v` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gf,tt) /\ _`
       (qspec_then `DF H0`
         (fn th => mp_then (Pos hd) mp_tac
           bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom (CONJUNCT1 th))) >>
     asm_rewrite_tac []) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ bc _ ep t /\ _`
       (qspec_then `H0` (drule_then (fn th =>
          ACCEPT_TAC (MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp
            (CONJUNCT1 th)))))) >>
  rpt conj_tac >> simp[] >>
  IF (qmatch_goalsub_rename_tac `valid_horizon cx st0 _ es.storage_trace`)
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ _ [] _ /\ _`
       (qspec_then `DF H` strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ bc _ ep t /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[])
    (rpt strip_tac >> simp[])
  >> IF (qmatch_goalsub_rename_tac `dalloca_fmp_headroom _ _`)
       (qpat_assum `!fn inst v. frag_reachable ctx func t fn inst v ==> _`
          (drule_then ACCEPT_TAC))
       (IF (qmatch_goalsub_rename_tac `alloca_frame _ _ _ _ _ _ _`)
          (qpat_assum `alloca_frame cenv es0 sa s0 bc ep t` mp_tac >>
           qpat_assum `ep = scoped with gas_obs := []` SUBST1_TAC >>
           simp[alloca_frame_def])
          (rename1 `i IN tn0.t_mem` >>
           rename1 `FLOOKUP s0.vs_allocas aid = SOME (off,az)` >>
           qpat_assum `!a b z j. _ /\ _ /\ _ /\ _ /\ _ /\ j IN tt.t_mem ==> j IN tn0.t_mem`
             (qspecl_then [`aid`,`off`,`az`,`i`] mp_tac) >> simp[] >>
           (impl_tac >- first_assum ACCEPT_TAC) >> simp[]))
QED

Finalise range_full_body_entry

(* Complete checked post-allocation entry, retaining the original frame. *)
Theorem range_checked_entry_full:
  !DF lo explicit d ctx func PG tops cx st0 RetQ cenv env es sa s0 G0 tn0 ea sA
      GA tnA st sb0 entry_lbl cond_lbl op1 op2 p cv rv g1 z1 g2 z2 ev bound fty
      tyv n1 n2 w sz id.
    lookup_block st.cs_current_bb func.fn_blocks =
    SOME
      <|bb_label := st.cs_current_bb;
        bb_instructions :=
          st.cs_current_insts ++
          [mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p];
           mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] []]|> /\
    lookup_block entry_lbl func.fn_blocks =
    SOME
      <|bb_label := entry_lbl;
        bb_instructions :=
          [mk_inst (st.cs_next_id + 2) ASSIGN [op1] [cv];
           mk_inst (st.cs_next_id + 3) SUB [op2; op1] [rv];
           mk_inst (st.cs_next_id + 4) (if is_signed_type fty then SGT else GT)
             [op1; op2] [g1]; mk_inst (st.cs_next_id + 5) ISZERO [Var g1] [z1];
           mk_inst (st.cs_next_id + 6) ASSERT [Var z1] [];
           mk_inst (st.cs_next_id + 7) GT [Var rv; Lit (n2w bound)] [g2];
           mk_inst (st.cs_next_id + 8) ISZERO [Var g2] [z2];
           mk_inst (st.cs_next_id + 9) ASSERT [Var z2] [];
           mk_inst (st.cs_next_id + 10) ADD [op1; Var rv] [ev];
           mk_inst (st.cs_next_id + 11) JMP [Label cond_lbl] []]|> /\
    sA.vs_current_bb = st.cs_current_bb /\
    sA.vs_inst_idx = LENGTH st.cs_current_insts + 1 /\ ~sA.vs_halted /\
    eval_operand op1 sA = SOME (i2w n1) /\
    eval_operand op2 sA = SOME (i2w n2) /\
    (!l. op1 <> Label l /\ op2 <> Label l) /\
    ALL_DISTINCT [p; cv; rv; g1; z1; g2; z2; ev] /\
    (!x. op1 = Var x \/ op2 = Var x ==> not_fresh_at st x) /\
    (!x. MEM x [cv; rv; g1; z1; g2; z2; ev] ==> ~not_fresh_at st x) /\
    (!x. op1 = Var x \/ op2 = Var x ==>
         op_prov GA (Var x) = NONE /\ op_taint tnA (Var x) = {}) /\
    local_ptrs_reserved cenv st /\
    (!x. not_fresh_at sa x ==> not_fresh_at st x) /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv sa sA /\
    return_buf_frame d cenv st sA /\ is_int_type fty /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\
    value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
    bound < dimword (:256) /\ expr_sim_inv cenv cx env ea /\
    lookup_scopes id ea.scopes = NONE /\ lookup_var p sA = SOME w /\
    FLOOKUP sA.vs_allocas st.cs_next_id = SOME (w2n w,sz) /\
    ptr_covers GA tnA p sA sz /\ allocas_from lo sA /\
    (!H. valid_horizon cx st0 H ea.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ea sA /\
         storage_well_formed_on cx ea (FST H) /\
         ghost_inv_at (DF H) lo d cenv cx ea GA tnA sA) /\
    alloca_history func sA /\ (ctx_has_dalloca ctx ==> allocas_below_fmp sA) /\
    s0.vs_alloca_next <= sA.vs_alloca_next /\
    (!x v.
       not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
       lookup_var x sA = SOME v) /\
    (!aid b.
       FLOOKUP s0.vs_allocas aid = SOME b ==>
       FLOOKUP sA.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
         FLOOKUP GA x = FLOOKUP G0 x /\
         op_taint tnA (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 cenv ea sA /\
    (!aid off z i.
       FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
       (!nm b z'.
          local_region cenv es.scopes s0 nm b z' ==>
          off + z <= b \/ b + z' <= off) /\ off <= i /\ i < off + z /\
       i IN tnA.t_mem ==>
       i IN tn0.t_mem) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (bind (lift_sum (get_range_limits (IntV n1) (IntV n2)))
         (\rl.
            ignore_bind
              (check (compatible_bound (Dynamic bound) (SND rl)) "For too long")
              (return (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)))))
      (ea,sA,GA,tnA)
      (\H res ee G tn t.
         n1 <= n2 /\ Num (n2 - n1) = Num (n2 - n1) /\
         Num (n2 - n1) < dimword (:256) /\ Num (n2 - n1) <= bound /\
         res = INL (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))) /\
         expr_sim_inv cenv cx env ee /\ lookup_scopes id ee.scopes = NONE /\
         t.vs_current_bb = cond_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
         stmt_state_rel H ctx func cenv cx ee t /\
         storage_well_formed_on cx ee (FST H) /\ ret_pc_ok cenv sa t /\
         return_buf_frame d cenv sb0 t /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
         lookup_var cv t = SOME (i2w n1) /\ lookup_var ev t = SOME (i2w n2) /\
         lookup_var p t = SOME w /\
         FLOOKUP t.vs_allocas st.cs_next_id = SOME (w2n w,sz) /\
         ptr_covers G tn p t sz /\ op_taint tn (Var cv) = {} /\
         op_prov G (Var cv) = NONE /\ op_taint tn (Var ev) = {} /\
         op_prov G (Var ev) = NONE /\ alloca_history func t /\
         (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
         s0.vs_alloca_next <= t.vs_alloca_next /\
         (!x v.
            not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
            lookup_var x t = SOME v) /\
         (!aid b.
            FLOOKUP s0.vs_allocas aid = SOME b ==>
            FLOOKUP t.vs_allocas aid = SOME b) /\
         (!x. not_fresh_at sa x ==>
              FLOOKUP G x = FLOOKUP G0 x /\
              op_taint tn (Var x) = op_taint tn0 (Var x)) /\
         alloca_frame cenv es sa s0 cenv ee t /\
         !aid off z i.
           FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
           (!nm b z'.
              local_region cenv es.scopes s0 nm b z' ==>
              off + z <= b \/ b + z' <= off) /\ off <= i /\ i < off + z /\
           i IN tn.t_mem ==>
           i IN tn0.t_mem)
      (\H res ee gt r.
         ?ex.
           res = INR ex /\
           (!tail.
              stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
           halt_exit H cx ee (INR ex) r /\
           (ctx_has_dalloca ctx ==>
            !t. r = Halt t \/ (?ir. r = IntRet ir t) ==> allocas_below_fmp t))
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ source _ Q R` >>
  qspecl_then [`get_tenv cx`, `fty`, `tyv`, `n1`, `n2`] mp_tac range_end_words >>
  simp[] >> strip_tac >>
  qabbrev_tac `s = jump_to entry_lbl sA` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (sA,GA,tnA) [] (OK s,GA,tnA)` by
    (gen_tac >> simp[Abbr `s`] >> irule jmp_origin_ptr_path >> simp[] >>
     qexists_tac `st.cs_next_id + 1` >>
     simp[get_instruction_def, EL_APPEND_EQN]) >>
  qabbrev_tac `A = {x | op1 = Var x \/ op2 = Var x}` >>
  qabbrev_tac `cmp = if is_signed_type fty then SGT else GT` >>
  qmatch_asmsub_abbrev_tac
    `lookup_block entry_lbl _ = SOME <|bb_label := entry_lbl; bb_instructions := fullcode|>` >>
  qabbrev_tac `code = TAKE 9 fullcode` >>
  `MEM cmp [SGT;GT] /\ scalar_available A op1 /\ scalar_available A op2 /\
   ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
   (!x. op1 = Var x \/ op2 = Var x ==>
     ~MEM x [cv;rv;g1;z1;g2;z2;ev])` by
    (simp[Abbr `cmp`] >> conj_tac >- (Cases_on `is_signed_type fty` >> simp[]) >>
     conj_tac >- (Cases_on `op1` >> gvs[scalar_available_def, Abbr `A`] >> metis_tac[]) >>
     conj_tac >- (Cases_on `op2` >> gvs[scalar_available_def, Abbr `A`] >> metis_tac[]) >>
     conj_tac >- fs[ALL_DISTINCT] >>
     gen_tac >> strip_tac >>
     `not_fresh_at st x` by
       (qpat_x_assum `!x. op1 = Var x \/ op2 = Var x ==> not_fresh_at st x`
          irule >> simp[]) >>
     qpat_x_assum `!x. MEM x [cv;rv;g1;z1;g2;z2;ev] ==> _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `eval_operand op1 s = SOME (i2w n1) /\
   eval_operand op2 s = SOME (i2w n2)` by
    simp[Abbr `s`, eval_operand_def, lookup_var_def, jump_to_def] >>
  qabbrev_tac `bad1 = if cmp = SGT then word_gt (i2w n1 : bytes32) (i2w n2)
                       else w2n (i2w n1 : bytes32) > w2n (i2w n2 : bytes32)` >>
  qabbrev_tac `bad2 = (w2n (i2w n2 - i2w n1 : bytes32) >
                       w2n (n2w bound : bytes32))` >>
  qabbrev_tac `u1 = update_var cv (i2w n1) s` >>
  qabbrev_tac `u2 = update_var rv (i2w n2-i2w n1) u1` >>
  qabbrev_tac `u3 = update_var g1 (bool_to_word bad1) u2` >>
  qabbrev_tac `u4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) u3` >>
  qabbrev_tac `u5 = update_var g2 (bool_to_word bad2) u4` >>
  qabbrev_tac `u6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) u5` >>
  qabbrev_tac `u7 = update_var ev (i2w n1+(i2w n2-i2w n1)) u6` >>
  `scalar_code A code /\ run_inst_seq_mem_ok code s /\
   run_inst_seq code s =
     (if bad1 then Abort Revert_abort (revert_state (set_returndata [] u4))
      else if bad2 then Abort Revert_abort (revert_state (set_returndata [] u6))
      else OK u7) /\
   lookup_var cv u7 = SOME (i2w n1) /\
   lookup_var ev u7 = SOME (i2w n1+(i2w n2-i2w n1)) /\
   (!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==>
     lookup_var x u4 = lookup_var x s /\
     lookup_var x u6 = lookup_var x s /\
     lookup_var x u7 = lookup_var x s)` by
    (mp_tac (range_checked_scalar_run |> SPEC_ALL |>
       Q.INST [`i` |-> `st.cs_next_id + 2`, `a` |-> `i2w n1 : bytes32`,
               `b` |-> `i2w n2 : bytes32`]) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     simp[LET_THM, Abbr `code`, Abbr `fullcode`, Abbr `u7`, Abbr `u6`, Abbr `u5`,
          Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `bad1`, Abbr `bad2`,
          GSYM arithmeticTheory.ADD_ASSOC]) >>
  `?G' tn' j.
    (!D. inst_seq_ptr D 0 ctx func PG GA tnA code s G' tn') /\
    (!v. ~MEM v (FLAT (MAP (\i. i.inst_outputs) code)) ==>
      FLOOKUP G' v = FLOOKUP GA v /\
      FLOOKUP tn'.t_var v = FLOOKUP tnA.t_var v /\
      op_taint tn' (Var v) = op_taint tnA (Var v)) /\
    tn'.t_mem = tnA.t_mem /\ tn'.t_stor = tnA.t_stor /\
    tn'.t_trans = tnA.t_trans /\ tn'.t_imm = tnA.t_imm /\
    (!t. run_inst_seq code s = OK t ==>
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,GA,tnA) []
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code),G',tn')) /\
      (!v. v IN A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) code)) ==>
        op_prov G' (Var v) = NONE /\ op_taint tn' (Var v) = {})) /\
    (!a t. run_inst_seq code s = Abort a t ==>
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,GA,tnA) [] (Abort a (t with vs_inst_idx := j),G',tn'))` by
    (`!v. v IN A ==> op_prov GA (Var v) = NONE /\ op_taint tnA (Var v) = {}` by
       (simp[Abbr `A`] >> asm_rewrite_tac[]) >>
     `~s.vs_halted /\ allocas_from lo s /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
       (pure_rewrite_tac[allocas_from_def, allocas_below_fmp_def] >>
        simp[Abbr `s`, jump_to_def] >>
        conj_tac >-
          (qpat_x_assum `allocas_from lo sA` mp_tac >>
           pure_rewrite_tac[allocas_from_def] >> asm_rewrite_tac[]) >>
        qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp sA` mp_tac >>
        pure_rewrite_tac[allocas_below_fmp_def] >> asm_rewrite_tac[]) >>
     irule range_scalar_joint_lift >> asm_rewrite_tac[] >>
     qexists_tac `<|bb_label := entry_lbl; bb_instructions := fullcode|>` >>
     simp[Abbr `s`, jump_to_def, Abbr `code`, Abbr `fullcode`,
          rich_listTheory.IS_PREFIX_APPEND]) >>
  `bad1 = (n2 < n1)` by
    (simp[Abbr `bad1`, Abbr `cmp`] >>
     Cases_on `is_signed_type fty` >> fs[]) >>
  `n1 <= n2 ==> (bad2 = (bound < Num (n2-n1)))` by
    (strip_tac >> simp[Abbr `bad2`]) >>
  Cases_on `bad1` >- suspend "order_error" >>
  `n1 <= n2` by
    (qpat_x_assum `bad1 = (n2 < n1)` mp_tac >>
     asm_rewrite_tac[] >> POP_ASSUM_LIST (K ALL_TAC) >> intLib.COOPER_TAC) >>
  Cases_on `bad2` >- suspend "bound_error" >>
  suspend "success"
QED

Resume range_checked_entry_full[order_error]:
  qpat_x_assum `T = (n2 < n1)` mp_tac >>
  pure_rewrite_tac[EQ_CLAUSES] >> strip_tac >>
  irule gas_outcome_full_exit >>
  reverse conj_tac >- (qpat_x_assum `~sA.vs_halted` ACCEPT_TAC) >>
  qexistsl_tac [`G'`, `ea`,
    `Abort Revert_abort ((revert_state (set_returndata [] u4)) with vs_inst_idx := j)`,
    `INR (Error (RuntimeError "no range"))`, `tn'`] >>
  simp[Abbr `source`, get_range_limits_def, lift_sum_def, bind_def,
       raise_def, exit_result_def] >>
  conj_tac >-
    (`~(n1 <= n2)` by (qpat_x_assum `n2 < n1` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> intLib.COOPER_TAC) >>
     simp[raise_def]) >>
  gen_tac >> strip_tac >> conj_tac >-
    (`!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,GA,tnA) []
       (Abort Revert_abort ((revert_state (set_returndata [] u4)) with vs_inst_idx := j),G',tn')` by
       (qpat_x_assum `!a t. run_inst_seq code s = Abort a t ==> _` irule >>
        asm_rewrite_tac[]) >>
     qpat_x_assum `!D. gas_origin_ptr_path _ (sA,GA,tnA) _ _`
       (qspec_then `DF H` assume_tac) >>
     qpat_x_assum `!D. gas_origin_ptr_path _ (s,GA,tnA) _ _`
       (qspec_then `DF H` assume_tac) >>
     irule (SIMP_RULE (srw_ss()) []
       (Q.SPECL [`cx`,`st`,`[]`,`out`] gas_origin_ptr_path_append)) >>
     simp[] >> metis_tac[]) >>
  simp[Abbr `R`, stmt_exit_ptr_def, exprSimDefsTheory.expr_exit_def,
       haltExitProjTheory.halt_exit_not_halt]
QED

Resume range_checked_entry_full[bound_error]:
  qpat_x_assum `n1 <= n2 ==> (T = (bound < Num (n2-n1)))` mp_tac >>
  pure_rewrite_tac[EQ_CLAUSES] >> impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  irule gas_outcome_full_exit >>
  reverse conj_tac >- (qpat_x_assum `~sA.vs_halted` ACCEPT_TAC) >>
  qexistsl_tac [`G'`, `ea`,
    `Abort Revert_abort ((revert_state (set_returndata [] u6)) with vs_inst_idx := j)`,
    `INR (Error (RuntimeError "For too long"))`, `tn'`] >>
  simp[Abbr `source`, get_range_limits_def, lift_sum_def, bind_def,
       ignore_bind_def, check_def, vyperValueTheory.compatible_bound_def, assert_def, raise_def,
       return_def, exit_result_def] >>
  gen_tac >> strip_tac >> conj_tac >-
    (`!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,GA,tnA) []
       (Abort Revert_abort ((revert_state (set_returndata [] u6)) with vs_inst_idx := j),G',tn')` by
       (qpat_x_assum `!a t. run_inst_seq code s = Abort a t ==> _` irule >>
        asm_rewrite_tac[]) >>
     qpat_x_assum `!D. gas_origin_ptr_path _ (sA,GA,tnA) _ _`
       (qspec_then `DF H` assume_tac) >>
     qpat_x_assum `!D. gas_origin_ptr_path _ (s,GA,tnA) _ _`
       (qspec_then `DF H` assume_tac) >>
     irule (SIMP_RULE (srw_ss()) []
       (Q.SPECL [`cx`,`st`,`[]`,`out`] gas_origin_ptr_path_append)) >>
     simp[] >> metis_tac[]) >>
  simp[Abbr `R`, stmt_exit_ptr_def, exprSimDefsTheory.expr_exit_def,
       haltExitProjTheory.halt_exit_not_halt]
QED

Resume range_checked_entry_full[success]:
  qpat_x_assum `n1 <= n2 ==> (F = (bound < Num (n2-n1)))` mp_tac >>
  pure_rewrite_tac[EQ_CLAUSES] >> impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `Num (n2-n1) <= bound /\ Num (n2-n1) < dimword (:256)` by simp[] >>
  `LENGTH code = 9` by simp[Abbr `code`, Abbr `fullcode`] >>
  `s.vs_inst_idx + LENGTH code = 9` by simp[Abbr `s`, jump_to_def] >>
  `run_inst_seq code s = OK u7` by asm_rewrite_tac[] >>
  qpat_x_assum `!t. run_inst_seq code s = OK t ==> _`
    (qspec_then `u7` mp_tac) >>
  simp[] >> strip_tac >>
  qabbrev_tac `pre = u7 with vs_inst_idx := 9` >>
  qabbrev_tac `fin = jump_to cond_lbl pre` >>
  `pre.vs_current_bb = entry_lbl /\ pre.vs_inst_idx = 9 /\
   pre.vs_halted = sA.vs_halted /\ pre.vs_alloca_next = sA.vs_alloca_next /\
   pre.vs_fmp = sA.vs_fmp /\ pre.vs_allocas = sA.vs_allocas /\
   pre.vs_initial_fmp = sA.vs_initial_fmp` by
    simp[Abbr `pre`, Abbr `u7`, Abbr `u6`, Abbr `u5`, Abbr `u4`,
         Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `s`, update_var_def, jump_to_def] >>
  `allocas_from lo pre /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp pre)` by
    (pure_rewrite_tac[allocas_from_def, allocas_below_fmp_def] >>
     simp[] >> conj_tac >-
       (qpat_assum `allocas_from lo sA` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp sA`
       (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def])) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (pre,G',tn') [] (OK fin,G',tn')` by
    (gen_tac >> simp[Abbr `fin`] >> irule jmp_origin_ptr_path >> simp[] >>
     qexists_tac `st.cs_next_id + 11` >> simp[get_instruction_def, Abbr `fullcode`]) >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G'`, `ea`, `INL (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1)))`,
                `fin`, `tn'`] >>
  conj_tac >-
    simp[Abbr `source`, get_range_limits_def, lift_sum_def, bind_def, ignore_bind_def,
         check_def, vyperValueTheory.compatible_bound_def, assert_def, return_def] >>
  qx_gen_tac `H` >> strip_tac >> conj_tac >-
    (qpat_assum `!D. gas_origin_ptr_path _ (sA,GA,tnA) _ _`
       (qspec_then `DF H` assume_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,GA,tnA) _ _`
       (qspec_then `DF H` assume_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (pre,G',tn') _ _`
       (qspec_then `DF H` assume_tac) >>
     irule (SIMP_RULE (srw_ss()) []
       (Q.SPECL [`cx`,`st`,`[]`,`out`] gas_origin_ptr_path_append)) >>
     simp[] >> qexistsl_tac [`GA`, `s`, `tnA`] >> simp[] >>
     irule (SIMP_RULE (srw_ss()) []
       (Q.SPECL [`cx`,`st`,`[]`,`out`] gas_origin_ptr_path_append)) >>
     simp[] >> qexistsl_tac [`G'`, `pre`, `tn'`] >> simp[]) >>
  suspend "success_post"
QED

Resume range_checked_entry_full[success_post]:
  `fin = jump_to cond_lbl (jump_to entry_lbl (sA with vs_vars := u7.vs_vars))` by
    simp[Abbr `fin`, Abbr `pre`, Abbr `u7`, Abbr `u6`, Abbr `u5`, Abbr `u4`,
         Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `s`, update_var_def, jump_to_def] >>
  `fin.vs_current_bb = cond_lbl /\ fin.vs_inst_idx = 0 /\ ~fin.vs_halted /\
   fin.vs_memory = sA.vs_memory /\ fin.vs_allocas = sA.vs_allocas /\
   fin.vs_alloca_next = sA.vs_alloca_next /\ fin.vs_call_ctx = sA.vs_call_ctx /\
   fin.vs_accounts = sA.vs_accounts /\ fin.vs_transient = sA.vs_transient /\
   fin.vs_immutables = sA.vs_immutables /\ fin.vs_fmp = sA.vs_fmp /\
   fin.vs_initial_fmp = sA.vs_initial_fmp` by simp[jump_to_def] >>
  `!x. lookup_var x fin = lookup_var x u7 /\ lookup_var x s = lookup_var x sA` by
    simp[lookup_var_def, jump_to_def, Abbr `s`] >>
  `FLAT (MAP (\i. i.inst_outputs) code) = [cv;rv;g1;z1;g2;z2;ev]` by
    simp[Abbr `code`, Abbr `fullcode`, mk_inst_def] >>
  `!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==>
    lookup_var x fin = lookup_var x sA /\ FLOOKUP G' x = FLOOKUP GA x /\
    op_taint tn' (Var x) = op_taint tnA (Var x)` by
    (qx_gen_tac `x` >> disch_tac >> conj_tac >- simp[] >>
     qpat_assum `!v. ~MEM v (FLAT (MAP _ code)) ==> _`
       (qspec_then `x` mp_tac) >> impl_tac >-
       (qpat_assum `FLAT (MAP _ code) = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >> simp[]) >>
  `!x. not_fresh_at st x ==>
    lookup_var x fin = lookup_var x sA /\ FLOOKUP G' x = FLOOKUP GA x /\
    op_taint tn' (Var x) = op_taint tnA (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==> _ /\ FLOOKUP G' x = _ /\ _`
       (qspec_then `x` mp_tac) >> impl_tac >-
       (qpat_assum `!x. MEM x [cv;rv;g1;z1;g2;z2;ev] ==> _`
          (qspec_then `x` mp_tac) >> simp[]) >>
     disch_then ACCEPT_TAC) >>
  qpat_assum `!h. valid_horizon cx st0 h ea.storage_trace ==> _`
    (qspec_then `H` mp_tac) >> impl_tac >- simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(!n x z. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var x) z) ==>
              not_fresh_at st x) /\
   (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at st x)` by
    (qpat_assum `local_ptrs_reserved cenv st`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [local_ptrs_reserved_def]) >>
     conj_tac
     >- (rpt gen_tac >> disch_tac >>
         qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP cenv.ce_vars n1 = _ ==> _`
           (mp_tac o cj 1) >> disch_then drule >> simp[])
     >- (gen_tac >> disch_tac >>
         qpat_assum `!x. cenv.ce_imm_alloca = _ ==> _`
           (mp_tac o cj 1) >> disch_then drule >> simp[])) >>
  `stmt_state_rel H ctx func cenv cx ea fin` by
    (qpat_assum `fin = jump_to _ _` SUBST1_TAC >>
     pure_rewrite_tac[stmt_state_rel_jump_to] >>
     irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
     `!x. not_fresh_at st x ==>
       lookup_var x (sA with vs_vars := u7.vs_vars) = lookup_var x sA` by
       (qx_gen_tac `x` >> disch_tac >>
        qpat_assum `!x. not_fresh_at st x ==> lookup_var x fin = _ /\ _`
          (qspec_then `x` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (mp_tac o CONJUNCT1) >>
        qpat_assum `fin = jump_to _ _` SUBST1_TAC >>
        simp[NoAsms, jump_to_def, lookup_var_def]) >>
     rpt conj_tac >> rpt gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x (sA with vs_vars := _) = _`
       irule
     >- (qpat_assum `!n x z. FLOOKUP cenv.ce_vars n = _ ==> not_fresh_at st x`
           drule >> simp[])
     >- (qpat_assum `!x. cenv.ce_imm_alloca = _ ==> not_fresh_at st x`
           drule >> simp[])) >>
  `!b. get_storage cx (ea with gas_obs := []) b = get_storage cx ea b` by
    (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  `storage_well_formed_on cx (ea with gas_obs := []) (FST H)` by
    (pure_rewrite_tac[storage_well_formed_on_def] >>
     simp[] >>
     qpat_assum `storage_well_formed_on cx ea (FST H)`
       (ACCEPT_TAC o PURE_REWRITE_RULE [storage_well_formed_on_def])) >>
  qpat_x_assum `fin = jump_to _ _` kall_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x fin = lookup_var x sA` by
    (rpt strip_tac >> simp[]) >>
  `ret_pc_ok cenv sa fin` by
    (drule ret_pc_ok_frame >> disch_then irule >> simp[]) >>
  `return_buf_frame d cenv sb0 fin` by
    (drule return_buf_frame_frame >> disch_then irule >> simp[]) >>
  `ghost_inv_at (DF H) lo d cenv cx (ea with gas_obs := []) G' tn' fin` by
    (drule ghost_inv_at_exterior_frame >> disch_then irule >> simp[] >>
     qexists_tac `st` >> simp[] >> conj_tac
     >- (Cases_on `d` >-
           (qpat_assum `return_buf_frame NONE cenv st sA` mp_tac >>
            simp[NoAsms, return_buf_frame_def]) >>
         rename1 `return_buf_frame (SOME rb) cenv st sA` >>
         PairCases_on `rb` >>
         qpat_assum `return_buf_frame (SOME _) cenv st sA` mp_tac >>
         simp[NoAsms, return_buf_frame_def] >> strip_tac >> simp[]) >>
     conj_tac
     >- (qx_gen_tac `x` >> qx_gen_tac `z` >> disch_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at st x` irule >>
         qpat_assum `ret_pc_ok cenv sa sA`
           (qspecl_then [`x`,`z`] mp_tac o REWRITE_RULE [ret_pc_ok_def]) >>
         simp[]) >>
     qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x fin = _ /\ _`
       (qspec_then `x` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (fn th =>
       qpat_assum `!x. lookup_var x fin = lookup_var x u7 /\ _`
         (fn eq => ACCEPT_TAC (PURE_REWRITE_RULE [cj 1 eq] (CONJUNCT1 th))))) >>
  `lookup_var p fin = SOME w /\ ptr_covers G' tn' p fin sz` by
    (qpat_assum `!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==> _ /\ FLOOKUP G' x = _ /\ _`
       (qspec_then `p` mp_tac) >> impl_tac >- fs[] >>
     pure_rewrite_tac[ptr_covers_def] >>
     disch_then (map_every SUBST1_TAC o CONJUNCTS) >>
     qpat_assum `ptr_covers GA tnA p sA sz`
       (mp_tac o PURE_REWRITE_RULE [ptr_covers_def]) >> simp[]) >>
  `op_prov G' (Var cv) = NONE /\ op_taint tn' (Var cv) = {} /\
   op_prov G' (Var ev) = NONE /\ op_taint tn' (Var ev) = {}` by
    (qpat_assum `!v. v IN A \/ _ ==> op_prov G' (Var v) = NONE /\ _`
       (fn th => map_every (fn q => qspec_then q mp_tac th) [`cv`, `ev`]) >>
     simp[Abbr `code`, Abbr `fullcode`, mk_inst_def]) >>
  simp[Abbr `Q`, stmt_state_rel_start_gas_obs, WORD_SUB_ADD2] >>
  conj_tac >-
    (irule allocaHistoryTheory.alloca_history_jump >> simp[] >>
     qexists_tac `sA` >> simp[]) >>
  conj_tac >-
    (pure_rewrite_tac[allocas_below_fmp_def] >> simp[] >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp sA`
       (ACCEPT_TAC o PURE_REWRITE_RULE [allocas_below_fmp_def])) >>
  conj_tac >-
    (`!nm b z. local_region cenv ea.scopes fin nm b z <=>
               local_region cenv ea.scopes sA nm b z` by
       (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
        qpat_assum `!x. not_fresh_at st x ==> lookup_var x fin = _ /\ _`
          (irule o cj 1) >>
        qpat_assum `!n x z. FLOOKUP cenv.ce_vars n = _ ==> not_fresh_at st x`
          drule >> simp[]) >>
     pure_rewrite_tac[alloca_frame_def] >>
     qpat_assum `fin.vs_memory = sA.vs_memory` SUBST1_TAC >>
     qpat_assum `!nm b z. local_region cenv ea.scopes fin nm b z <=> _`
       (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `alloca_frame cenv es sa s0 cenv ea sA`
       (ACCEPT_TAC o PURE_REWRITE_RULE [alloca_frame_def])) >>
  first_assum ACCEPT_TAC
QED

Finalise range_checked_entry_full

(* ===== Initialization: one allocation and the selected scalar suffix ===== *)

Theorem range_full_init:
  !DF lo explicit d ctx func PG tops cx st0 RetQ cenv env es sa s0 G0 tn0 ea s
      GE tnE st sb0 entry_lbl cond_lbl p cv ev bound fty tyv n1 n2 sz id.
    p = STRING #"%" (toString st.cs_next_var) /\
    lookup_block st.cs_current_bb func.fn_blocks =
    SOME
      <|bb_label := st.cs_current_bb;
        bb_instructions :=
          st.cs_current_insts ++
          [mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p];
           mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] []]|> /\
    (n1 <= n2 /\ Num (n2 - n1) <= bound /\ ALL_DISTINCT [p; cv; ev] /\
     ~not_fresh_at st cv /\ ~not_fresh_at st ev /\
     lookup_block entry_lbl func.fn_blocks =
     SOME
       <|bb_label := entry_lbl;
         bb_instructions :=
           [mk_inst (st.cs_next_id + 2) ASSIGN [Lit (i2w n1)] [cv];
            mk_inst (st.cs_next_id + 3) ADD
              [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev];
            mk_inst (st.cs_next_id + 4) JMP [Label cond_lbl] []]|> \/
     ?op1 op2 rv g1 z1 g2 z2.
       lookup_block entry_lbl func.fn_blocks =
       SOME
         <|bb_label := entry_lbl;
           bb_instructions :=
             [mk_inst (st.cs_next_id + 2) ASSIGN [op1] [cv];
              mk_inst (st.cs_next_id + 3) SUB [op2; op1] [rv];
              mk_inst (st.cs_next_id + 4)
                (if is_signed_type fty then SGT else GT) [op1; op2] [g1];
              mk_inst (st.cs_next_id + 5) ISZERO [Var g1] [z1];
              mk_inst (st.cs_next_id + 6) ASSERT [Var z1] [];
              mk_inst (st.cs_next_id + 7) GT [Var rv; Lit (n2w bound)] [g2];
              mk_inst (st.cs_next_id + 8) ISZERO [Var g2] [z2];
              mk_inst (st.cs_next_id + 9) ASSERT [Var z2] [];
              mk_inst (st.cs_next_id + 10) ADD [op1; Var rv] [ev];
              mk_inst (st.cs_next_id + 11) JMP [Label cond_lbl] []]|> /\
       eval_operand op1 s = SOME (i2w n1) /\
       eval_operand op2 s = SOME (i2w n2) /\
       (!l. op1 <> Label l /\ op2 <> Label l) /\
       ALL_DISTINCT [p; cv; rv; g1; z1; g2; z2; ev] /\
       (!x. op1 = Var x \/ op2 = Var x ==>
            not_fresh_at st x /\ op_prov GE (Var x) = NONE /\
            op_taint tnE (Var x) = {}) /\
       (!x. MEM x [cv; rv; g1; z1; g2; z2; ev] ==> ~not_fresh_at st x) /\
       is_int_type fty /\ evaluate_type (get_tenv cx) fty = SOME tyv /\
       value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2)) /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv st /\
    sz < dimword (:256) /\ bound < dimword (:256) /\
    sa.cs_next_id <= st.cs_next_id /\ sa.cs_next_var <= st.cs_next_var /\
    st.cs_next_var <= sb0.cs_next_var /\
    (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
    ret_pc_ok cenv sa s /\ return_buf_frame d cenv st s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    expr_sim_inv cenv cx env ea /\ lookup_scopes id ea.scopes = NONE /\
    storage_trace_domain cx st0 ea.storage_trace /\
    (!H. valid_horizon cx st0 H ea.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ea s /\
         storage_well_formed_on cx ea (FST H) /\
         ghost_inv_at (DF H) lo d cenv cx ea GE tnE s) /\
    (\a e0 u G0 tn0 e t G tn.
       alloca_history func t /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
       u.vs_alloca_next <= t.vs_alloca_next /\
       (!x w.
          not_fresh_at a x /\ lookup_var x u = SOME w ==>
          lookup_var x t = SOME w) /\
       (!aid b.
          FLOOKUP u.vs_allocas aid = SOME b ==>
          FLOOKUP t.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at a x ==>
            FLOOKUP G x = FLOOKUP G0 x /\
            op_taint tn (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame cenv e0 a u cenv e t /\
       !aid off z i.
         FLOOKUP u.vs_allocas aid = SOME (off,z) /\ aid < a.cs_next_id /\
         (!nm b z'.
            local_region cenv e0.scopes u nm b z' ==>
            off + z <= b \/ b + z' <= off) /\ off <= i /\ i < off + z /\
         i IN tn.t_mem ==>
         i IN tn0.t_mem) sa es s0 G0 tn0 ea s GE tnE ==>
    ?w. gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
          (bind (lift_sum (get_range_limits (IntV n1) (IntV n2)))
             (\rl.
                ignore_bind
                  (check (compatible_bound (Dynamic bound) (SND rl))
                     "For too long")
                  (return (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)))))
          (ea,s,GE,tnE)
          (\H res ee G tn t.
             ?rs.
               res = INL rs /\ n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\
               Num (n2 - n1) <= bound /\
               ?k. k + LENGTH rs = Num (n2 - n1) /\
                   rs = GENLIST (\j. Value (IntV (n1 + &(k + j)))) (LENGTH rs) /\
                   expr_sim_inv cenv cx env ee /\
                   lookup_scopes id ee.scopes = NONE /\
                   t.vs_current_bb = cond_lbl /\ t.vs_inst_idx = 0 /\
                   ~t.vs_halted /\ stmt_state_rel H ctx func cenv cx ee t /\
                   storage_well_formed_on cx ee (FST H) /\
                   ret_pc_ok cenv sa t /\ return_buf_frame d cenv sb0 t /\
                   ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
                   lookup_var cv t = SOME (i2w (n1 + &k)) /\
                   lookup_var ev t = SOME (i2w n2) /\
                   lookup_var p t = SOME w /\
                   FLOOKUP t.vs_allocas st.cs_next_id = SOME (w2n w,sz) /\
                   ptr_covers G tn p t sz /\ op_taint tn (Var cv) = {} /\
                   op_prov G (Var cv) = NONE /\ op_taint tn (Var ev) = {} /\
                   op_prov G (Var ev) = NONE /\
                   (\a e0 u G0 tn0 e t G tn.
                      alloca_history func t /\
                      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
                      u.vs_alloca_next <= t.vs_alloca_next /\
                      (!x w.
                         not_fresh_at a x /\ lookup_var x u = SOME w ==>
                         lookup_var x t = SOME w) /\
                      (!aid b.
                         FLOOKUP u.vs_allocas aid = SOME b ==>
                         FLOOKUP t.vs_allocas aid = SOME b) /\
                      (!x. not_fresh_at a x ==>
                           FLOOKUP G x = FLOOKUP G0 x /\
                           op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                      alloca_frame cenv e0 a u cenv e t /\
                      !aid off z i.
                        FLOOKUP u.vs_allocas aid = SOME (off,z) /\
                        aid < a.cs_next_id /\
                        (!nm b z'.
                           local_region cenv e0.scopes u nm b z' ==>
                           off + z <= b \/ b + z' <= off) /\ off <= i /\
                        i < off + z /\ i IN tn.t_mem ==>
                        i IN tn0.t_mem) sa es s0 G0 tn0 ee t G tn)
          (\H res ee gt r.
             ?ex.
               res = INR ex /\
               (!tail.
                  stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt
                    r) /\ halt_exit H cx ee (INR ex) r /\
               (ctx_has_dalloca ctx ==>
                !t. r = Halt t \/ (?ir. r = IntRet ir t) ==>
                    allocas_below_fmp t))
Proof
  rpt gen_tac >> SIMP_TAC pure_ss [LET_THM, pairTheory.UNCURRY_DEF] >> BETA_TAC >>
  qabbrev_tac `N = Num (n2 - n1)` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) ea.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ea.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ea.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  Cases_on `compile_alloc_buffer sz st` >>
  rename1 `compile_alloc_buffer sz st = (buf,cut)` >>
  `fn_has_code st cut func` by
    (irule range_alloc_buffer_code >> qexistsl_tac [`buf`, `sz`,
        `[mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] []]`] >> simp[]) >>
  drule_then strip_assume_tac loweringHaltTheory.compile_alloc_buffer_insts >>
  drule_all (INST_TYPE [beta |-> alpha]
    bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path_exact) >>
  disch_then (qspecl_then [`tnE`, `explicit`, `PG`, `GE`]
    (qx_choosel_then [`q`, `w`, `sA`, `GA`, `tnA`] strip_assume_tac)) >>
  `q = p` by fs[] >> qpat_x_assum `q = p` SUBST_ALL_TAC >>
  `sA.vs_current_bb = st.cs_current_bb /\
   sA.vs_inst_idx = LENGTH st.cs_current_insts + 1` by simp[] >>
  `sA.vs_memory = s.vs_memory /\ ~sA.vs_halted` by
    (qpat_assum `~s.vs_halted` mp_tac >>
     qpat_assum `sA with <|vs_vars := _; vs_allocas := _;
          vs_alloca_next := _; vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ea.storage_trace) ctx func cenv cx ea sA` by
    (qpat_assum `!H. stmt_state_rel H ctx func cenv cx ea s ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sA` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ea sA`
       (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `!x. not_fresh_at sa x ==> not_fresh_at st x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `ret_pc_ok cenv sa sA` by
    (drule ret_pc_ok_frame >> disch_then irule >> simp[]) >>
  `return_buf_frame d cenv st sA` by
    (drule return_buf_frame_frame >> disch_then irule >> simp[]) >>
  `(!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
   (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x)` by
    (conj_tac >- (rpt strip_tac >>
       qpat_assum `!x. not_fresh_at sa x ==> _` irule >>
       qpat_assum `!x z. cenv.ce_return_buf = _ ==> _` (qspecl_then [`x`,`z`] mp_tac) >> simp[]) >>
     rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> _` irule >>
     qpat_assum `ret_pc_ok cenv sa sA`
       (qspecl_then [`x`,`z`] mp_tac o REWRITE_RULE[ret_pc_ok_def]) >> simp[]) >>
  qpat_assum `stmt_state_rel _ ctx func cenv cx ea s`
    (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  `!H. valid_horizon cx st0 H ea.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ea sA /\
    storage_well_formed_on cx ea (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ea GA tnA sA` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ea.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     conj_tac >- (qpat_assum `!H. stmt_state_rel H ctx func cenv cx ea s ==> _`
        irule >> first_assum ACCEPT_TAC) >>
     simp[] >> irule bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at_locals >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`GE`, `w2n w + sz`, `func`, `s`, `st`, `tnE`] >> simp[]) >>
  `alloca_frame cenv ea st s cenv ea sA` by
    (irule (INST_TYPE [alpha |-> ``:256``] (cj 1 range_alloca_full_frame)) >> simp[] >>
     conj_tac >- ((qexistsl_tac [`tnE`, `tnA`] >> simp[SF DISJ_ss] >> (metis_tac[SF DISJ_ss]))) >>
     qexistsl_tac [`storage_trace_horizon ea.storage_trace`, `ctx`, `cx`, `func`] >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv ea sA` by
    (irule alloca_frame_trans >> (metis_tac[])) >>
  `s0.vs_alloca_next <= sA.vs_alloca_next /\
   (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x sA = SOME v) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP sA.vs_allocas aid = SOME b) /\
   (!x. not_fresh_at sa x ==> FLOOKUP GA x = FLOOKUP G0 x /\
      op_taint tnA (Var x) = op_taint tn0 (Var x))` by
    (conj_tac >- decide_tac >> rpt conj_tac >> rpt strip_tac >> simp[]) >>
  `!aid off z i. FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
     (!nm b z'. local_region cenv es.scopes s0 nm b z' ==> off+z <= b \/ b+z' <= off) /\
     off <= i /\ i < off+z /\ i IN tnA.t_mem ==> i IN tn0.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `off + z <= s.vs_alloca_next` by
       (qpat_assum `alloca_inv s` (mp_tac o REWRITE_RULE [alloca_inv_def, alloca_next_valid_def]) >>
        strip_tac >> first_x_assum (qspecl_then [`aid`, `off`, `z`] mp_tac) >> simp[]) >>
     `i IN tnE.t_mem` by
       (qpat_assum `!i. i IN tnA.t_mem <=> _` (qspec_then `i` mp_tac) >>
        `~(s.vs_alloca_next <= i)` by decide_tac >> simp[]) >>
     qpat_assum `!aid off z i. _ ==> i IN tn0.t_mem` (qspecl_then [`aid`,`off`,`z`,`i`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  qexists_tac `w` >>
  qpat_x_assum `(n1 <= n2 /\ _) \/ _` strip_assume_tac
  >- suspend "literal_init"
  >> suspend "checked_init"
QED

Resume range_full_init[literal_init]:
  `cv <> ev /\ p <> cv /\ p <> ev` by fs[] >>
  qmatch_asmsub_abbrev_tac
    `lookup_block st.cs_current_bb func.fn_blocks = SOME init_bb` >>
  `lookup_block sA.vs_current_bb func.fn_blocks = SOME init_bb /\
   get_instruction init_bb sA.vs_inst_idx =
     SOME (mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] [])` by
    simp[Abbr `init_bb`, get_instruction_def, EL_APPEND_EQN] >>
  drule_all (INST_TYPE [alpha |-> ``:256``] range_literal_entry_full) >>
  disch_then (qspecl_then [`GA`,`tnA`]
    (qx_choosel_then [`fin`,`GF`,`tnF`] (fn facts =>
      map_every assume_tac (List.take (CONJUNCTS facts,14)) >>
      mk_asm "literal_rel" (cj 15 facts) >>
      mk_asm "literal_ghost" (cj 16 facts) >>
      mk_asm "literal_frame" (cj 17 facts)))) >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`GF`, `ea`, `INL (GENLIST (\j. Value (IntV (n1 + &j))) N)`,
                `fin`, `tnF`] >>
  conj_tac >-
    simp[Abbr `N`, get_range_limits_def, lift_sum_def, bind_def, ignore_bind_def,
         check_def, vyperValueTheory.compatible_bound_def, assert_def, return_def] >>
  qx_gen_tac `H` >> strip_tac >> conj_tac >-
    (irule gas_origin_ptr_path_trans >> qexistsl_tac [`GA`,`sA`,`tnA`] >> simp[]) >>
  qpat_assum `!h. valid_horizon cx st0 h ea.storage_trace ==> stmt_state_rel _ _ _ _ _ _ sA /\ _`
    (qspec_then `H` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `not_local_ptr cenv ea.scopes cv /\ not_local_ptr cenv ea.scopes ev` by
    (conj_tac >> irule exprSimOperandsTheory.fresh_not_local_ptr >>
     qexists_tac `st` >> simp[]) >>
  `!x. not_fresh_at st x ==> x <> cv /\ x <> ev` by
    (gen_tac >> disch_tac >> conj_tac >> disch_then SUBST_ALL_TAC >> fs[]) >>
  `!x. not_fresh_at st x ==>
     lookup_var x fin = lookup_var x sA /\ FLOOKUP GF x = FLOOKUP GA x /\
     op_taint tnF (Var x) = op_taint tnA (Var x)` by
    (gen_tac >> strip_tac >> simp[]) >>
  `fin.vs_allocas = sA.vs_allocas /\ fin.vs_alloca_next = sA.vs_alloca_next /\
   fin.vs_fmp = sA.vs_fmp /\ fin.vs_initial_fmp = sA.vs_initial_fmp /\
   tnF.t_mem = tnA.t_mem` by simp[jump_to_def, update_var_def] >>
  `stmt_state_rel H ctx func cenv cx ea fin` by
    (asm "literal_rel" irule >> simp[]) >>
  `storage_well_formed_on cx (ea with gas_obs := []) (FST H)` by
    (`!b. get_storage cx (ea with gas_obs := []) b = get_storage cx ea b` by
       (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
     pure_rewrite_tac[storage_well_formed_on_def] >> simp[] >>
     qpat_assum `storage_well_formed_on cx ea (FST H)`
       (ACCEPT_TAC o PURE_REWRITE_RULE [storage_well_formed_on_def])) >>
  `ret_pc_ok cenv sa fin` by
    (qpat_assum `ret_pc_ok cenv sa sA`
       (mp_then Any irule ret_pc_ok_frame) >> simp[] >> rpt strip_tac >> simp[]) >>
  `return_buf_frame d cenv sb0 fin` by
    (qpat_assum `return_buf_frame d cenv st sA`
       (mp_then Any irule return_buf_frame_frame) >> simp[] >> rpt strip_tac >> simp[]) >>
  `ghost_inv_at (DF H) lo d cenv cx (ea with gas_obs := []) GF tnF fin` by
    (asm "literal_ghost"
       (qspecl_then [`DF H`,`d`,`cenv`,`cx`,`ea`,`st`] mp_tac) >>
     impl_tac >- simp[] >>
     qpat_assum `fin = jump_to _ _` SUBST1_TAC >>
     `ea with gas_obs := ea.gas_obs = ea` by simp[] >>
     pop_assum (fn th => CONV_TAC (LAND_CONV (PURE_ONCE_REWRITE_CONV [GSYM th]))) >>
     pure_once_rewrite_tac[fragGasEmitCtrlTheory.ghost_inv_at_jump_to] >>
     disch_then ACCEPT_TAC) >>
  `lookup_var p fin = SOME w /\ ptr_covers GF tnF p fin sz` by
    (qpat_assum `!x. x <> cv /\ x <> ev ==> _` (qspec_then `p` mp_tac) >>
     impl_tac >- simp[] >> pure_rewrite_tac[ptr_covers_def] >>
     disch_then (map_every SUBST1_TAC o CONJUNCTS) >>
     qpat_assum `ptr_covers GA tnA p sA sz`
       (mp_tac o PURE_REWRITE_RULE [ptr_covers_def]) >> simp[]) >>
  `alloca_history func fin` by
    (irule allocaHistoryTheory.alloca_history_jump >> simp[] >>
     qexists_tac `sA` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp fin` by
    (pure_rewrite_tac[allocas_below_fmp_def] >> simp[] >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp sA`
       (ACCEPT_TAC o PURE_REWRITE_RULE [allocas_below_fmp_def])) >>
  `alloca_frame cenv es sa s0 cenv ea fin` by
    (asm "literal_frame" irule >> simp[]) >>
  qexists_tac `GENLIST (\j. Value (IntV (n1 + &j))) N` >>
  pure_rewrite_tac[REFL_CLAUSE, boolTheory.AND_CLAUSES] >>
  qexists_tac `0` >>
  qpat_x_assum `p = STRING _ _` SUBST_ALL_TAC >>
  qpat_x_assum `fin = jump_to _ _` kall_tac >>
  qpat_x_assum `GF = DRESTRICT _ _` kall_tac >>
  qpat_x_assum `tnF = _ with t_var := _` kall_tac >>
  qpat_x_assum `!i. i IN tnA.t_mem <=> _` kall_tac >>
  simp[op_prov_def]
  >> (gvs[])
QED

Resume range_full_init[checked_init]:
  `!x. op1 = Var x \/ op2 = Var x ==>
       not_fresh_at st x /\ lookup_var x sA = lookup_var x s /\
       op_prov GA (Var x) = NONE /\ op_taint tnA (Var x) = {}` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. op1 = Var x \/ op2 = Var x ==> _ /\ op_prov GE _ = _ /\ _`
       (qspec_then `x` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x sA = _ /\ _`
       (qspec_then `x` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (map_every assume_tac o CONJUNCTS) >> fs[op_prov_def]) >>
  `!opr. opr = op1 \/ opr = op2 ==> eval_operand opr sA = eval_operand opr s` by
    (Cases >> simp[eval_operand_def] >> disch_tac
     >- (rename1 `lookup_var x sA = _` >>
         qpat_assum `!x. _ ==> _ /\ lookup_var x sA = _ /\ _`
           (qspec_then `x` mp_tac) >>
         impl_tac >- (pop_assum (DISJ_CASES_THEN (assume_tac o SYM)) >> simp[]) >>
         simp[]) >>
     rename1 `FLOOKUP sA.vs_labels l = _` >>
     qpat_assum `!l. op1 <> Label l /\ op2 <> Label l`
       (qspec_then `l` mp_tac) >>
     pop_assum (DISJ_CASES_THEN (assume_tac o SYM)) >> simp[]) >>
  `eval_operand op1 sA = SOME (i2w n1) /\ eval_operand op2 sA = SOME (i2w n2)` by simp[] >>
  `(!x. op1 = Var x \/ op2 = Var x ==> not_fresh_at st x) /\
   (!x. op1 = Var x \/ op2 = Var x ==>
     op_prov GA (Var x) = NONE /\ op_taint tnA (Var x) = {})` by
    (rpt conj_tac >> qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. _ ==> _ /\ lookup_var x sA = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  qexistsl_tac [`GA`, `sA`, `tnA`] >> conj_tac >- simp[] >>
  qspecl_then
    [`DF`, `lo`, `explicit`, `d`, `ctx`, `func`, `PG`, `tops`, `cx`, `st0`,
     `RetQ`, `cenv`, `env`, `es`, `sa`, `s0`, `G0`, `tn0`, `ea`, `sA`,
     `GA`, `tnA`, `st`, `sb0`, `entry_lbl`, `cond_lbl`, `op1`, `op2`, `p`,
     `cv`, `rv`, `g1`, `z1`, `g2`, `z2`, `ev`, `bound`, `fty`, `tyv`,
     `n1`, `n2`, `w`, `sz`, `id`] mp_tac range_checked_entry_full >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[LET_THM] >>
  disch_then (fn th => irule gas_outcome_full_post_mono >> irule_at Any th) >>
  BETA_TAC >>
  reverse conj_tac >- (rpt gen_tac >> disch_then ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `GENLIST (\j. Value (IntV (n1 + &j))) N` >>
  pure_rewrite_tac[REFL_CLAUSE, boolTheory.AND_CLAUSES] >>
  (* The length equation forces the initial index k to be zero. *)
  simp[] >> first_assum ACCEPT_TAC
QED

Finalise range_full_init

(* The entry cut selects compiler geometry before every runtime anchor. *)
Theorem range_full_round:
  (!(cx :evaluation_context) (id :string) (typ :type) (e1 :expr) (e2 :expr)
       (bound :num) (body :stmt list)
       (DF :(bool # 256 word # type_value) list # num list -> dead) (lo :num)
       (d :(256 word # num) option) (PG :(num # num) option list)
       (tops :toplevel list) (bindings :(string # type) list)
       (ctx :venom_context) (shadow_ctx :venom_context) (func :ir_function)
       (shadow_func :ir_function) (cenv :compile_env) (env :typing_env)
       (env' :typing_env) (ret_ty :type) (lctx :loop_ctx)
       (RetQ :(bool # 256 word # type_value) list # num list ->
              value ->
              evaluation_state ->
              (string |-> num # num) # taint -> exec_result -> bool)
       (tyv :type_value) (sa :compile_state) (sb :compile_state)
       (shadow_sa :compile_state) (shadow_sb :compile_state).
     body_inv tops ctx cenv cx /\
     supported_stmt tops bindings (For id typ (Range e1 e2) bound body) /\
     (!(target :type).
        supported_stmt_expr_exists (expr_abi_decode_target_root target)
          (For id typ (Range e1 e2) bound body) ==>
        occurs_abi_decode_target target tops) /\ ce_locals_declared cenv env /\
     locals_alloc_ok cenv env /\
     type_stmt env ret_ty (For id typ (Range e1 e2) bound body) = SOME env' /\
     stmt_exprs_ok cenv (For id typ (Range e1 e2) bound body) /\
     call_evaluation_safe cx
       (int_calls_stmt (For id typ (Range e1 e2) bound body)) /\
     frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ
       cenv ret_ty /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
     stmt_env cenv lctx ret_ty (For id typ (Range e1 e2) bound body) sa =
     (cenv,sb) /\
     stmt_env (gas_shadow_env T cenv) lctx ret_ty
       (gas_shadow_stmt (For id typ (Range e1 e2) bound body)) shadow_sa =
     (gas_shadow_env T cenv,shadow_sb) /\ gas_shadow_state sa shadow_sa /\
     gas_shadow_state sb shadow_sb /\ gas_shadow_context ctx shadow_ctx /\
     ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
     MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
     fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
     fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
     (!(H :(bool # 256 word # type_value) list # num list).
        dead_lo_ok H (DF H) lo cenv cx) /\
     (!(x :string) (z :num).
        cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
     (!(x :string) (z :num).
        cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
     ~block_is_terminated sa ==>
     ?(st :compile_state) (bc :compile_env) (body_cenv :compile_env)
         (body_env' :typing_env) (sb0 :compile_state) (sb1 :compile_state)
         (shadow_sb0 :compile_state) (shadow_sb1 :compile_state) (p :string)
         (sz :num) (ainst :instruction) (cv :string) (ev :string) (dv :string)
         (nv :string) (entry_lbl :string) (cond_lbl :string) (exit_lbl :string)
         (body_lbl :string) (incr_lbl :string) (j1 :num) (j2 :num) (j3 :num)
         (bbb :basic_block) (i1 :num) (i2 :num) (i3 :num) (sj :compile_state)
         (op1 :operand) (s1 :compile_state) (op2 :operand) (rv :string)
         (g1 :string) (z1 :string) (g2 :string) (z2 :string).
       sz = type_memory_bytes cenv typ /\
       ainst =
       mk_inst st.cs_next_id ALLOCA
         [Lit (n2w (type_memory_bytes cenv typ) :256 word)] [p] /\
       p = STRING #"%" (toString st.cs_next_var) /\
       cv = STRING #"%" (toString (st.cs_next_var + (1 :num))) /\
       entry_lbl = fresh_label_output "for_entry" st.cs_next_label /\
       cond_lbl = fresh_label_output "for_cond" (st.cs_next_label + (1 :num)) /\
       body_lbl = fresh_label_output "for_body" (st.cs_next_label + (2 :num)) /\
       incr_lbl = fresh_label_output "for_incr" (st.cs_next_label + (3 :num)) /\
       exit_lbl = fresh_label_output "for_exit" (st.cs_next_label + (4 :num)) /\
       declare_local cenv id typ st =
       (bc,st with cs_next_var := st.cs_next_var + (1 :num)) /\
       cs_extends sa st /\ cs_extends st sb0 /\ cs_extends st sb /\
       sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id /\
       st.cs_next_id <= sb0.cs_next_id /\
       lookup_block st.cs_current_bb func.fn_blocks =
       SOME
         <|bb_label := st.cs_current_bb;
           bb_instructions :=
             st.cs_current_insts ++
             [mk_inst st.cs_next_id ALLOCA
                [Lit (n2w (type_memory_bytes cenv typ) :256 word)] [p];
              mk_inst (st.cs_next_id + (1 :num)) JMP [Label entry_lbl]
                ([] :string list)]|> /\
       compile_stmt (gas_shadow_env T cenv) lctx ret_ty
         (For id typ (Range (gas_shadow_expr e1) (gas_shadow_expr e2)) bound
            (MAP gas_shadow_stmt body)) shadow_sa = ((),shadow_sb) /\
       (!(a1 :type) (m1 :int) (a2 :type) (m2 :int).
          e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2) ==>
          st = sa /\ ev = STRING #"%" (toString (sa.cs_next_var + (2 :num))) /\
          dv = STRING #"%" (toString (sa.cs_next_var + (3 :num))) /\
          j1 = sa.cs_next_id + (5 :num) /\ j2 = sa.cs_next_id + (6 :num) /\
          j3 = sa.cs_next_id + (7 :num) /\
          sb0.cs_next_var = sa.cs_next_var + (4 :num) /\
          lookup_block entry_lbl func.fn_blocks =
          SOME
            <|bb_label := entry_lbl;
              bb_instructions :=
                [mk_inst (sa.cs_next_id + (2 :num)) ASSIGN
                   [Lit (i2w m1 :256 word)] [cv];
                 mk_inst (sa.cs_next_id + (3 :num)) ADD
                   [Lit (i2w m1 :256 word);
                    Lit ((i2w m2 :256 word) - (i2w m1 :256 word))] [ev];
                 mk_inst (sa.cs_next_id + (4 :num)) JMP [Label cond_lbl]
                   ([] :string list)]|>) /\
       (~(?(a1 :type) (m1 :int) (a2 :type) (m2 :int).
           e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2)) ==>
        lower_value compile_expr cenv typ e1 sa = (op1,s1) /\
        lower_value compile_expr cenv typ e2 s1 = (op2,st) /\
        rv = STRING #"%" (toString (st.cs_next_var + (2 :num))) /\
        g1 = STRING #"%" (toString (st.cs_next_var + (3 :num))) /\
        z1 = STRING #"%" (toString (st.cs_next_var + (4 :num))) /\
        g2 = STRING #"%" (toString (st.cs_next_var + (5 :num))) /\
        z2 = STRING #"%" (toString (st.cs_next_var + (6 :num))) /\
        ev = STRING #"%" (toString (st.cs_next_var + (7 :num))) /\
        dv = STRING #"%" (toString (st.cs_next_var + (8 :num))) /\
        j1 = st.cs_next_id + (12 :num) /\ j2 = st.cs_next_id + (13 :num) /\
        j3 = st.cs_next_id + (14 :num) /\
        sb0.cs_next_var = st.cs_next_var + (9 :num) /\
        lookup_block entry_lbl func.fn_blocks =
        SOME
          <|bb_label := entry_lbl;
            bb_instructions :=
              [mk_inst (st.cs_next_id + (2 :num)) ASSIGN [op1] [cv];
               mk_inst (st.cs_next_id + (3 :num)) SUB [op2; op1] [rv];
               mk_inst (st.cs_next_id + (4 :num))
                 (if is_signed_type typ then SGT else GT) [op1; op2] [g1];
               mk_inst (st.cs_next_id + (5 :num)) ISZERO [Var g1] [z1];
               mk_inst (st.cs_next_id + (6 :num)) ASSERT [Var z1]
                 ([] :string list);
               mk_inst (st.cs_next_id + (7 :num)) GT
                 [Var rv; Lit (n2w bound :256 word)] [g2];
               mk_inst (st.cs_next_id + (8 :num)) ISZERO [Var g2] [z2];
               mk_inst (st.cs_next_id + (9 :num)) ASSERT [Var z2]
                 ([] :string list);
               mk_inst (st.cs_next_id + (10 :num)) ADD [op1; Var rv] [ev];
               mk_inst (st.cs_next_id + (11 :num)) JMP [Label cond_lbl]
                 ([] :string list)]|>) /\
       for_code func cenv bc ret_ty body id tyv p sz ainst cv ev dv nv cond_lbl
         exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
       lookup_block cond_lbl func.fn_blocks =
       SOME
         <|bb_label := cond_lbl;
           bb_instructions :=
             [mk_inst j1 EQ [Var cv; Var ev] [dv];
              mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl]
                ([] :string list)]|> /\
       lookup_block body_lbl func.fn_blocks = SOME bbb /\
       get_instruction bbb (0 :num) =
       SOME (mk_inst j3 MSTORE [Var p; Var cv] ([] :string list)) /\
       sb0.cs_current_bb = body_lbl /\
       sb0.cs_current_insts =
       [mk_inst j3 MSTORE [Var p; Var cv] ([] :string list)] /\
       compile_stmts bc (InLoop exit_lbl incr_lbl) ret_ty body sb0 = ((),sb1) /\
       (~block_is_terminated sb1 ==>
        sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
        sj.cs_current_insts =
        sb1.cs_current_insts ++
        [mk_inst sb1.cs_next_id JMP [Label incr_lbl] ([] :string list)] /\
        fn_has_code sb1 sj func) /\ sj.cs_next_var = sb1.cs_next_var /\
       nv = STRING #"%" (toString sj.cs_next_var) /\ i1 = sj.cs_next_id /\
       i2 = sj.cs_next_id + (1 :num) /\ i3 = sj.cs_next_id + (2 :num) /\
       lookup_block incr_lbl func.fn_blocks =
       SOME
         <|bb_label := incr_lbl;
           bb_instructions :=
             [mk_inst i1 ADD [Var cv; Lit (1w :256 word)] [nv];
              mk_inst i2 ASSIGN [Var nv] [cv];
              mk_inst i3 JMP [Label cond_lbl] ([] :string list)]|> /\
       sb.cs_current_bb = exit_lbl /\
       sb.cs_current_insts = ([] :instruction list) /\
       sb0.cs_next_var <= sb.cs_next_var /\ ~not_fresh_at sa dv /\
       not_fresh_at sb0 p /\ not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\
       (!(x :string). not_fresh_at sa x ==> not_fresh_at sb0 x) /\
       sa.cs_next_id <= ainst.inst_id /\ sa.cs_next_id <= sb0.cs_next_id /\
       sa.cs_next_var <= sb0.cs_next_var /\ cs_extends sa sb0 /\
       cs_extends shadow_sa shadow_sb0 /\ cs_extends shadow_sb1 shadow_sb /\
       stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty body sb0 =
       (body_cenv,sb1) /\
       stmts_env (gas_shadow_env T bc) (InLoop exit_lbl incr_lbl) ret_ty
         (MAP gas_shadow_stmt body) shadow_sb0 = (gas_shadow_env T body_cenv,shadow_sb1) /\
       gas_shadow_state sb0 shadow_sb0 /\ gas_shadow_state sb1 shadow_sb1 /\
       fn_has_code sb0 sb1 func /\
       fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
       type_stmts (extend_local env id typ F) ret_ty body = SOME body_env' /\
       body_inv tops ctx bc cx /\ supported_stmts tops bindings body /\
       (!(target :type).
          supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
          occurs_abi_decode_target target tops) /\ stmts_exprs_ok bc body /\
       call_evaluation_safe cx (int_calls_stmts body) /\
       frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ
         bc ret_ty /\ local_ptrs_reserved bc sb0 /\ ~block_is_terminated sb0 /\
       (!(H :(bool # 256 word # type_value) list # num list).
          dead_lo_ok H (DF H) lo bc cx) /\
       (!(x :string) (z :num).
          bc.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sb0 x) /\
       (!(x :string) (z :num).
          bc.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sb0 x) /\
       !(st0 :evaluation_state) (es0 :evaluation_state) (s0 :venom_state)
           (G0 :string |-> num # num) (tn0 :taint) (n1 :int) (n2 :int) (N :num)
           (k :num) (a :eval_result) (rs :eval_result list)
           (es :evaluation_state) (s :venom_state) (G :string |-> num # num)
           (tn :taint) (w :256 word).
         n1 <= n2 /\ N = Num (n2 - n1) /\ N < dimword (:256) /\
         value_has_type tyv (IntV n1 :value) /\
         value_has_type tyv (IntV n2 :value) /\
         body_for_full_ok cx tyv id body
           (GENLIST (\(j :num). Value (IntV (n1 + ((&j) :int)) :value)) N) /\
         k + LENGTH (a::rs) = N /\
         a::rs =
         GENLIST (\(j :num). Value (IntV (n1 + ((&(k + j)) :int)) :value))
           (LENGTH (a::rs)) /\ body_const_cells_agree [(NONE,tops)] cx env es /\
         expr_sim_inv cenv cx env es /\
         lookup_scopes id es.scopes = (NONE :scope_entry option) /\
         storage_trace_domain cx st0 es.storage_trace /\
         s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = (0 :num) /\
         ~s.vs_halted /\ ret_pc_ok cenv sa s /\
         return_buf_frame d cenv sb0 s /\
         lookup_var cv s = SOME (i2w (n1 + ((&k) :int)) :256 word) /\
         lookup_var ev s = SOME (i2w n2 :256 word) /\
         lookup_var p s = SOME w /\
         FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n w,sz) /\
         ptr_covers G tn p s sz /\ op_taint tn (Var cv) = ({} :num -> bool) /\
         op_prov G (Var cv) = (NONE :(num # num) option) /\
         op_taint tn (Var ev) = ({} :num -> bool) /\
         op_prov G (Var ev) = (NONE :(num # num) option) /\
         alloca_history func s /\
         (!fn inst v. frag_reachable ctx func s fn inst v ==> dalloca_fmp_headroom inst v) /\
         (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
         s0.vs_alloca_next <= s.vs_alloca_next /\
         (!(x :string) (v :256 word).
            not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
            lookup_var x s = SOME v) /\
         (!(aid :num) (b :num # num).
            FLOOKUP s0.vs_allocas aid = SOME b ==>
            FLOOKUP s.vs_allocas aid = SOME b) /\
         (!(x :string).
            not_fresh_at sa x ==>
            FLOOKUP G x = FLOOKUP G0 x /\
            op_taint tn (Var x) = op_taint tn0 (Var x)) /\
         alloca_frame cenv es0 sa s0 cenv es s /\
         (!(aid :num) (off :num) (z :num) (i :num).
            FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
            (!(nm :string) (b :num) (z' :num).
               local_region cenv es0.scopes s0 nm b z' ==>
               off + z <= b \/ b + z' <= off) /\ off <= i /\ i < off + z /\
            i IN tn.t_mem ==>
            i IN tn0.t_mem) /\
         (!(H :(bool # 256 word # type_value) list # num list).
            valid_horizon cx st0 H es.storage_trace ==>
            stmt_state_rel H ctx func cenv cx es s /\
            storage_well_formed_on cx es (FST H) /\
            ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
         gas_admissible (eval_for cx tyv id body (a::rs)) (stmt_res_ok lctx) es ==>
         a = Value (IntV (n1 + ((&k) :int)) :value) /\ k < N /\
         body_stmts_full_ok cx body /\
         bind (read_result cx a) (\(v :value). push_scope_with_var id tyv v)
           (es with gas_obs := ([] :256 word list)) =
         ((INL () :unit + vyperState$exception),
          es with
          <|scopes :=
              fmupdate id
                <|assignable := F; type := tyv;
                  value := (IntV (n1 + ((&k) :int)) :value);
                  popped := ([] :(subscript list # value) list)|>
                (FEMPTY :string |-> scope_entry)::es.scopes;
            gas_obs := ([] :256 word list)|>) /\
         expr_sim_inv bc cx (extend_local env id typ F)
           (es with
            <|scopes :=
                fmupdate id
                  <|assignable := F; type := tyv;
                    value := (IntV (n1 + ((&k) :int)) :value);
                    popped := ([] :(subscript list # value) list)|>
                  (FEMPTY :string |-> scope_entry)::es.scopes;
              gas_obs := ([] :256 word list)|>) /\
         ce_locals_declared bc (extend_local env id typ F) /\
         locals_alloc_ok bc (extend_local env id typ F) /\
         gas_admissible (eval_stmts cx body)
           (stmt_res_ok (InLoop exit_lbl incr_lbl))
           (es with
            <|scopes :=
                fmupdate id
                  <|assignable := F; type := tyv;
                    value := (IntV (n1 + ((&k) :int)) :value);
                    popped := ([] :(subscript list # value) list)|>
                  (FEMPTY :string |-> scope_entry)::es.scopes;
              gas_obs := ([] :256 word list)|>) /\
         cenv_top_ext cenv bc
           (es with
            <|scopes :=
                fmupdate id
                  <|assignable := F; type := tyv;
                    value := (IntV (n1 + ((&k) :int)) :value);
                    popped := ([] :(subscript list # value) list)|>
                  (FEMPTY :string |-> scope_entry)::es.scopes;
              gas_obs := ([] :256 word list)|>).scopes /\
         (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
            (jump_to body_lbl
               (update_var dv (bool_to_word F) s with vs_inst_idx := (1 :num))) with
          vs_inst_idx := (1 :num)).vs_current_bb = sb0.cs_current_bb /\
         (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
            (jump_to body_lbl
               (update_var dv (bool_to_word F) s with vs_inst_idx := (1 :num))) with
          vs_inst_idx := (1 :num)).vs_inst_idx = LENGTH sb0.cs_current_insts /\
         ~(mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
            (jump_to body_lbl
               (update_var dv (bool_to_word F) s with vs_inst_idx := (1 :num))) with
          vs_inst_idx := (1 :num)).vs_halted /\
         ret_pc_ok bc sb0
           (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
              (jump_to body_lbl
                 (update_var dv (bool_to_word F) s with vs_inst_idx := (1 :num))) with
            vs_inst_idx := (1 :num)) /\
         return_buf_frame d bc sb0
           (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
              (jump_to body_lbl
                 (update_var dv (bool_to_word F) s with vs_inst_idx := (1 :num))) with
            vs_inst_idx := (1 :num)) /\
         alloca_history func
           (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
              (jump_to body_lbl
                 (update_var dv (bool_to_word F) s with vs_inst_idx := (1 :num))) with
            vs_inst_idx := (1 :num)) /\
         (ctx_has_dalloca ctx ==>
          allocas_below_fmp
            (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
               (jump_to body_lbl
                  (update_var dv (bool_to_word F) s with
                   vs_inst_idx := (1 :num))) with vs_inst_idx := (1 :num))) /\
         (!(fn :ir_function) (inst :instruction) (v :venom_state).
            frag_reachable ctx func
              (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with
                     vs_inst_idx := (1 :num))) with vs_inst_idx := (1 :num)) fn
              inst v ==>
            dalloca_fmp_headroom inst v) /\
         s0.vs_alloca_next <=
         (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
            (jump_to body_lbl
               (update_var dv (bool_to_word F) s with vs_inst_idx := (1 :num))) with
          vs_inst_idx := (1 :num)).vs_alloca_next /\
         (!(x :string) (v :256 word).
            not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
            lookup_var x
              (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with
                     vs_inst_idx := (1 :num))) with vs_inst_idx := (1 :num)) =
            SOME v) /\
         (!(aid :num) (ab :num # num).
            FLOOKUP s0.vs_allocas aid = SOME ab ==>
            FLOOKUP
              (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with
                     vs_inst_idx := (1 :num))) with vs_inst_idx := (1 :num)).
              vs_allocas aid = SOME ab) /\
         (!(x :string).
            not_fresh_at sa x ==>
            FLOOKUP
              (step_prov PG
                 (step_prov PG
                    (step_prov PG G (mk_inst j1 EQ [Var cv; Var ev] [dv])
                       (update_var dv (bool_to_word F) s))
                    (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl]
                       ([] :string list))
                    (jump_to body_lbl
                       (update_var dv (bool_to_word F) s with
                        vs_inst_idx := (1 :num))))
                 (mk_inst j3 MSTORE [Var p; Var cv] ([] :string list))
                 (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
                    (jump_to body_lbl
                       (update_var dv (bool_to_word F) s with
                        vs_inst_idx := (1 :num))))) x = FLOOKUP G0 x /\
            op_taint
              (step_taint (mk_inst j3 MSTORE [Var p; Var cv] ([] :string list))
                 (jump_to body_lbl
                    (update_var dv (bool_to_word F) s with
                     vs_inst_idx := (1 :num)))
                 (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
                    (jump_to body_lbl
                       (update_var dv (bool_to_word F) s with
                        vs_inst_idx := (1 :num))))
                 (step_taint
                    (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl]
                       ([] :string list))
                    (update_var dv (bool_to_word F) s with
                     vs_inst_idx := (1 :num))
                    (jump_to body_lbl
                       (update_var dv (bool_to_word F) s with
                        vs_inst_idx := (1 :num)))
                    (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
                       (update_var dv (bool_to_word F) s) tn))) (Var x) =
            op_taint tn0 (Var x)) /\
         alloca_frame cenv es0 sa s0 bc
           (es with
            <|scopes :=
                fmupdate id
                  <|assignable := F; type := tyv;
                    value := (IntV (n1 + ((&k) :int)) :value);
                    popped := ([] :(subscript list # value) list)|>
                  (FEMPTY :string |-> scope_entry)::es.scopes;
              gas_obs := ([] :256 word list)|>)
           (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
              (jump_to body_lbl
                 (update_var dv (bool_to_word F) s with vs_inst_idx := (1 :num))) with
            vs_inst_idx := (1 :num)) /\
         (!(aid :num) (off :num) (az :num) (i :num).
            FLOOKUP s0.vs_allocas aid = SOME (off,az) /\ aid < sa.cs_next_id /\
            (!(nm :string) (ab :num) (z' :num).
               local_region cenv es0.scopes s0 nm ab z' ==>
               off + az <= ab \/ ab + z' <= off) /\ off <= i /\ i < off + az /\
            i IN
            (step_taint (mk_inst j3 MSTORE [Var p; Var cv] ([] :string list))
               (jump_to body_lbl
                  (update_var dv (bool_to_word F) s with
                   vs_inst_idx := (1 :num)))
               (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
                  (jump_to body_lbl
                     (update_var dv (bool_to_word F) s with
                      vs_inst_idx := (1 :num))))
               (step_taint
                  (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl]
                     ([] :string list))
                  (update_var dv (bool_to_word F) s with
                   vs_inst_idx := (1 :num))
                  (jump_to body_lbl
                     (update_var dv (bool_to_word F) s with
                      vs_inst_idx := (1 :num)))
                  (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
                     (update_var dv (bool_to_word F) s) tn))).t_mem ==>
            i IN tn0.t_mem) /\
         !(H :(bool # 256 word # type_value) list # num list).
           valid_horizon cx st0 H es.storage_trace ==>
           gas_origin_ptr_path
             (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (s,G,tn)
             ([] :bool list)
             (OK
                (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
                   (jump_to body_lbl
                      (update_var dv (bool_to_word F) s with
                       vs_inst_idx := (1 :num))) with vs_inst_idx := (1 :num)),
              step_prov PG
                (step_prov PG
                   (step_prov PG G (mk_inst j1 EQ [Var cv; Var ev] [dv])
                      (update_var dv (bool_to_word F) s))
                   (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl]
                      ([] :string list))
                   (jump_to body_lbl
                      (update_var dv (bool_to_word F) s with
                       vs_inst_idx := (1 :num))))
                (mk_inst j3 MSTORE [Var p; Var cv] ([] :string list))
                (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
                   (jump_to body_lbl
                      (update_var dv (bool_to_word F) s with
                       vs_inst_idx := (1 :num)))),
              step_taint (mk_inst j3 MSTORE [Var p; Var cv] ([] :string list))
                (jump_to body_lbl
                   (update_var dv (bool_to_word F) s with
                    vs_inst_idx := (1 :num)))
                (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
                   (jump_to body_lbl
                      (update_var dv (bool_to_word F) s with
                       vs_inst_idx := (1 :num))))
                (step_taint
                   (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl]
                      ([] :string list))
                   (update_var dv (bool_to_word F) s with
                    vs_inst_idx := (1 :num))
                   (jump_to body_lbl
                      (update_var dv (bool_to_word F) s with
                       vs_inst_idx := (1 :num)))
                   (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
                      (update_var dv (bool_to_word F) s) tn))) /\
           stmt_state_rel H ctx func bc cx
             (es with
              <|scopes :=
                  fmupdate id
                    <|assignable := F; type := tyv;
                      value := (IntV (n1 + ((&k) :int)) :value);
                      popped := ([] :(subscript list # value) list)|>
                    (FEMPTY :string |-> scope_entry)::es.scopes;
                gas_obs := ([] :256 word list)|>)
             (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
                (jump_to body_lbl
                   (update_var dv (bool_to_word F) s with
                    vs_inst_idx := (1 :num))) with vs_inst_idx := (1 :num)) /\
           storage_well_formed_on cx
             (es with
              <|scopes :=
                  fmupdate id
                    <|assignable := F; type := tyv;
                      value := (IntV (n1 + ((&k) :int)) :value);
                      popped := ([] :(subscript list # value) list)|>
                    (FEMPTY :string |-> scope_entry)::es.scopes;
                gas_obs := ([] :256 word list)|>) (FST H) /\
           ghost_inv_at (DF H) lo d bc cx
             (es with
              <|scopes :=
                  fmupdate id
                    <|assignable := F; type := tyv;
                      value := (IntV (n1 + ((&k) :int)) :value);
                      popped := ([] :(subscript list # value) list)|>
                    (FEMPTY :string |-> scope_entry)::es.scopes;
                gas_obs := ([] :256 word list)|>)
             (step_prov PG
                (step_prov PG
                   (step_prov PG G (mk_inst j1 EQ [Var cv; Var ev] [dv])
                      (update_var dv (bool_to_word F) s))
                   (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl]
                      ([] :string list))
                   (jump_to body_lbl
                      (update_var dv (bool_to_word F) s with
                       vs_inst_idx := (1 :num))))
                (mk_inst j3 MSTORE [Var p; Var cv] ([] :string list))
                (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
                   (jump_to body_lbl
                      (update_var dv (bool_to_word F) s with
                       vs_inst_idx := (1 :num)))))
             (step_taint (mk_inst j3 MSTORE [Var p; Var cv] ([] :string list))
                (jump_to body_lbl
                   (update_var dv (bool_to_word F) s with
                    vs_inst_idx := (1 :num)))
                (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
                   (jump_to body_lbl
                      (update_var dv (bool_to_word F) s with
                       vs_inst_idx := (1 :num))))
                (step_taint
                   (mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl]
                      ([] :string list))
                   (update_var dv (bool_to_word F) s with
                    vs_inst_idx := (1 :num))
                   (jump_to body_lbl
                      (update_var dv (bool_to_word F) s with
                       vs_inst_idx := (1 :num)))
                   (step_taint (mk_inst j1 EQ [Var cv; Var ev] [dv]) s
                      (update_var dv (bool_to_word F) s) tn)))
             (mstore (w2n w) (i2w (n1 + ((&k) :int)) :256 word)
                (jump_to body_lbl
                   (update_var dv (bool_to_word F) s with
                    vs_inst_idx := (1 :num))) with vs_inst_idx := (1 :num))) /\
  (!(func0 :ir_function) (ctx0 :venom_context) (c0 :compile_env)
       (e0 :evaluation_state) (sa0 :compile_state) (s0 :venom_state)
       (G0 :string |-> 'a) (tn0 :taint) (c1 :compile_env)
       (e1 :evaluation_state) (sa1 :compile_state) (s1 :venom_state)
       (G1 :string |-> 'a) (tn1 :taint) (c2 :compile_env)
       (e2 :evaluation_state) (s2 :venom_state) (G2 :string |-> 'a)
       (tn2 :taint).
     (alloca_history func0 s1 /\
      (ctx_has_dalloca ctx0 ==> allocas_below_fmp s1) /\
      s0.vs_alloca_next <= s1.vs_alloca_next /\
      (!(x :string) (w :256 word).
         not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s1 = SOME w) /\
      (!(aid :num) (b :num # num).
         FLOOKUP s0.vs_allocas aid = SOME b ==>
         FLOOKUP s1.vs_allocas aid = SOME b) /\
      (!(x :string).
         not_fresh_at sa0 x ==>
         FLOOKUP G1 x = FLOOKUP G0 x /\
         op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame c0 e0 sa0 s0 c1 e1 s1 /\
      !(aid :num) (off :num) (sz :num) (i :num).
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
        (!(nm :string) (b :num) (sz' :num).
           local_region c0 e0.scopes s0 nm b sz' ==>
           off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
        i IN tn1.t_mem ==>
        i IN tn0.t_mem) /\
     (alloca_history func0 s2 /\
      (ctx_has_dalloca ctx0 ==> allocas_below_fmp s2) /\
      s1.vs_alloca_next <= s2.vs_alloca_next /\
      (!(x :string) (w :256 word).
         not_fresh_at sa1 x /\ lookup_var x s1 = SOME w ==>
         lookup_var x s2 = SOME w) /\
      (!(aid :num) (b :num # num).
         FLOOKUP s1.vs_allocas aid = SOME b ==>
         FLOOKUP s2.vs_allocas aid = SOME b) /\
      (!(x :string).
         not_fresh_at sa1 x ==>
         FLOOKUP G2 x = FLOOKUP G1 x /\
         op_taint tn2 (Var x) = op_taint tn1 (Var x)) /\
      alloca_frame c1 e1 sa1 s1 c2 e2 s2 /\
      !(aid :num) (off :num) (sz :num) (i :num).
        FLOOKUP s1.vs_allocas aid = SOME (off,sz) /\ aid < sa1.cs_next_id /\
        (!(nm :string) (b :num) (sz' :num).
           local_region c1 e1.scopes s1 nm b sz' ==>
           off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
        i IN tn2.t_mem ==>
        i IN tn1.t_mem) /\ sa0.cs_next_id <= sa1.cs_next_id /\
     (!(x :string). not_fresh_at sa0 x ==> not_fresh_at sa1 x) ==>
     alloca_history func0 s2 /\
     (ctx_has_dalloca ctx0 ==> allocas_below_fmp s2) /\
     s0.vs_alloca_next <= s2.vs_alloca_next /\
     (!(x :string) (w :256 word).
        not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
        lookup_var x s2 = SOME w) /\
     (!(aid :num) (b :num # num).
        FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP s2.vs_allocas aid = SOME b) /\
     (!(x :string).
        not_fresh_at sa0 x ==>
        FLOOKUP G2 x = FLOOKUP G0 x /\
        op_taint tn2 (Var x) = op_taint tn0 (Var x)) /\
     alloca_frame c0 e0 sa0 s0 c2 e2 s2 /\
     !(aid :num) (off :num) (sz :num) (i :num).
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
       (!(nm :string) (b :num) (sz' :num).
          local_region c0 e0.scopes s0 nm b sz' ==>
          off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
       i IN tn2.t_mem ==>
       i IN tn0.t_mem) /\
  (!(func0 :ir_function) (ctx0 :venom_context) (c0 :compile_env)
       (e0 :evaluation_state) (sa0 :compile_state) (s0 :venom_state)
       (G0 :string |-> 'b) (tn0 :taint) (c :compile_env) (ee :evaluation_state)
       (t :venom_state) (G :string |-> 'b) (tn :taint) (cenv0 :compile_env)
       (sc :string |-> scope_entry) (rest :(string |-> scope_entry) list).
     (alloca_history func0 t /\
      (ctx_has_dalloca ctx0 ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      (!(x :string) (w :256 word).
         not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t = SOME w) /\
      (!(aid :num) (b :num # num).
         FLOOKUP s0.vs_allocas aid = SOME b ==>
         FLOOKUP t.vs_allocas aid = SOME b) /\
      (!(x :string).
         not_fresh_at sa0 x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame c0 e0 sa0 s0 c ee t /\
      !(aid :num) (off :num) (sz :num) (i :num).
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
        (!(nm :string) (b :num) (sz' :num).
           local_region c0 e0.scopes s0 nm b sz' ==>
           off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
        i IN tn.t_mem ==>
        i IN tn0.t_mem) /\ cenv_top_ext cenv0 c ee.scopes /\
     ee.scopes = sc::rest /\
     (!(nm :string).
        nm IN FDOM sc ==> lookup_scopes nm rest = (NONE :scope_entry option)) ==>
     alloca_history func0 t /\
     (ctx_has_dalloca ctx0 ==> allocas_below_fmp t) /\
     s0.vs_alloca_next <= t.vs_alloca_next /\
     (!(x :string) (w :256 word).
        not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
     (!(aid :num) (b :num # num).
        FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
     (!(x :string).
        not_fresh_at sa0 x ==>
        FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
     alloca_frame c0 e0 sa0 s0 cenv0 (ee with scopes := rest) t /\
     !(aid :num) (off :num) (sz :num) (i :num).
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
       (!(nm :string) (b :num) (sz' :num).
          local_region c0 e0.scopes s0 nm b sz' ==>
          off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
       i IN tn.t_mem ==>
       i IN tn0.t_mem) /\
  (!(DF0 :(bool # 256 word # type_value) list # num list -> dead) (lo0 :num)
       (d0 :string # num -> bool) (ctx0 :venom_context) (func0 :ir_function)
       (PG0 :(num # num) option list) (tops0 :toplevel list)
       (cx0 :evaluation_context) (st0 :evaluation_state) (body0 :stmt list)
       (es0 :evaluation_state) (s :venom_state) (G :string |-> num # num)
       (tn :taint)
       (Q :(bool # 256 word # type_value) list # num list ->
           unit + vyperState$exception ->
           evaluation_state ->
           (string |-> num # num) -> taint -> venom_state -> bool)
       (R :(bool # 256 word # type_value) list # num list ->
           unit + vyperState$exception ->
           evaluation_state ->
           (string |-> num # num) # taint -> exec_result -> bool).
     es0.scopes <> ([] :(string |-> scope_entry) list) /\
     gas_outcome_full (DF0,lo0,d0,ctx0,func0,PG0) tops0 cx0 st0
       (eval_stmts cx0 body0) (es0,s,G,tn) Q R ==>
     gas_outcome_full (DF0,lo0,d0,ctx0,func0,PG0) tops0 cx0 st0
       (finally
          (try
             (ignore_bind (eval_stmts cx0 body0)
                (return F :
                 evaluation_state ->
                 (bool + vyperState$exception) # evaluation_state))
             handle_loop_exception) pop_scope) (es0,s,G,tn)
       (\(H :(bool # 256 word # type_value) list # num list)
          (res' :bool + vyperState$exception) (ee :evaluation_state)
          (G :string |-> num # num) (tn :taint) (t :venom_state).
          ?(res :unit + vyperState$exception) (sc :string |-> scope_entry).
            res' =
            (case res of INL u => INL F | INR ex =>
               if ex = BreakException then INL T else
               if ex = ContinueException then INL F else INR ex) /\
            Q H res (ee with scopes := sc::ee.scopes) G tn t)
       (\(H :(bool # 256 word # type_value) list # num list)
          (res' :bool + vyperState$exception) (ee :evaluation_state)
          (gt :(string |-> num # num) # taint) (r :exec_result).
          ?(res :unit + vyperState$exception) (sc :string |-> scope_entry).
            res' =
            (case res of INL u => INL F | INR ex =>
               if ex = BreakException then INL T else
               if ex = ContinueException then INL F else INR ex) /\
            R H res (ee with scopes := sc::ee.scopes) gt r)) /\
  (!(RetQ0 :(bool # 'c word # type_value) list # num list ->
               value -> evaluation_state -> 'd -> exec_result -> bool)
       (H :(bool # 'c word # type_value) list # num list)
       (cx0 :evaluation_context) (ee :evaluation_state)
       (res :unit + vyperState$exception) (gt :'d) (r :exec_result)
       (ctx0 :venom_context) (sc :(string |-> scope_entry) list)
       (g :256 word list).
     (!(tail :256 word list).
        stmt_exit_ptr (RetQ0 H) (ee with gas_obs := tail) res gt r) /\
     halt_exit H cx0 ee res r /\
     (ctx_has_dalloca ctx0 ==>
      !(s :venom_state).
        r = Halt s \/ (?(ir :internal_return). r = IntRet ir s) ==>
        allocas_below_fmp s) ==>
     (!(tail :256 word list).
        stmt_exit_ptr (RetQ0 H)
          (ee with <|gas_obs := tail; scopes := sc; gas_obs := g|>) res gt r) /\
     halt_exit H cx0 (ee with <|scopes := sc; gas_obs := g|>) res r /\
     (ctx_has_dalloca ctx0 ==>
      !(s :venom_state).
        r = Halt s \/ (?(ir :internal_return). r = IntRet ir s) ==>
        allocas_below_fmp s)) ==>
  !(cx :evaluation_context) (id :string) (typ :type) (e1 :expr) (e2 :expr)
      (bound :num) (body :stmt list)
      (DF :(bool # 256 word # type_value) list # num list -> dead) (lo :num)
      (d :(256 word # num) option) (PG :(num # num) option list)
      (tops :toplevel list) (bindings :(string # type) list)
      (ctx :venom_context) (shadow_ctx :venom_context) (func :ir_function)
      (shadow_func :ir_function) (cenv :compile_env) (env :typing_env)
      (env' :typing_env) (ret_ty :type) (lctx :loop_ctx)
      (RetQ :(bool # 256 word # type_value) list # num list ->
             value ->
             evaluation_state ->
             (string |-> num # num) # taint -> exec_result -> bool)
      (tyv :type_value) (sa :compile_state) (sb :compile_state)
      (shadow_sa :compile_state) (shadow_sb :compile_state).
    shadow_body_inv tops ctx shadow_ctx /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (For id typ (Range e1 e2) bound body) /\
    (!(target :type).
       supported_stmt_expr_exists (expr_abi_decode_target_root target)
         (For id typ (Range e1 e2) bound body) ==>
       occurs_abi_decode_target target tops) /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ (Range e1 e2) bound body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ (Range e1 e2) bound body) /\
    call_evaluation_safe cx
      (int_calls_stmt (For id typ (Range e1 e2) bound body)) /\
    frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv
      ret_ty /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
    stmt_env cenv lctx ret_ty (For id typ (Range e1 e2) bound body) sa =
    (cenv,sb) /\
    stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (For id typ (Range e1 e2) bound body)) shadow_sa =
    (gas_shadow_env T cenv,shadow_sb) /\ gas_shadow_state sa shadow_sa /\
    gas_shadow_state sb shadow_sb /\ gas_shadow_context ctx shadow_ctx /\
    ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!(H :(bool # 256 word # type_value) list # num list).
       dead_lo_ok H (DF H) lo cenv cx) /\
    (!(x :string) (z :num).
       cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
    (!(x :string) (z :num).
       cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
    ~block_is_terminated sa ==>
    ?(st :compile_state) (bc :compile_env) (body_cenv :compile_env)
        (body_env' :typing_env) (sb0 :compile_state) (sb1 :compile_state)
        (shadow_sb0 :compile_state) (shadow_sb1 :compile_state) (p :string)
        (sz :num) (ainst :instruction) (cv :string) (ev :string) (dv :string)
        (nv :string) (entry_lbl :string) (cond_lbl :string) (exit_lbl :string)
        (body_lbl :string) (incr_lbl :string) (j1 :num) (j2 :num) (j3 :num)
        (bbb :basic_block) (i1 :num) (i2 :num) (i3 :num) (sj :compile_state)
        (op1 :operand) (s1 :compile_state) (op2 :operand) (rv :string)
        (g1 :string) (z1 :string) (g2 :string) (z2 :string).
      sz = type_memory_bytes cenv typ /\
      ainst =
      mk_inst st.cs_next_id ALLOCA
        [Lit (n2w (type_memory_bytes cenv typ) :256 word)] [p] /\
      p = STRING #"%" (toString st.cs_next_var) /\
      cv = STRING #"%" (toString (st.cs_next_var + (1 :num))) /\
      entry_lbl = fresh_label_output "for_entry" st.cs_next_label /\
      cond_lbl = fresh_label_output "for_cond" (st.cs_next_label + (1 :num)) /\
      body_lbl = fresh_label_output "for_body" (st.cs_next_label + (2 :num)) /\
      incr_lbl = fresh_label_output "for_incr" (st.cs_next_label + (3 :num)) /\
      exit_lbl = fresh_label_output "for_exit" (st.cs_next_label + (4 :num)) /\
      declare_local cenv id typ st =
      (bc,st with cs_next_var := st.cs_next_var + (1 :num)) /\
      cs_extends sa st /\ cs_extends st sb0 /\ cs_extends st sb /\
      sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id /\
      st.cs_next_id <= sb0.cs_next_id /\
      lookup_block st.cs_current_bb func.fn_blocks =
      SOME
        <|bb_label := st.cs_current_bb;
          bb_instructions :=
            st.cs_current_insts ++
            [mk_inst st.cs_next_id ALLOCA
               [Lit (n2w (type_memory_bytes cenv typ) :256 word)] [p];
             mk_inst (st.cs_next_id + (1 :num)) JMP [Label entry_lbl]
               ([] :string list)]|> /\
      compile_stmt (gas_shadow_env T cenv) lctx ret_ty
        (For id typ (Range (gas_shadow_expr e1) (gas_shadow_expr e2)) bound
           (MAP gas_shadow_stmt body)) shadow_sa = ((),shadow_sb) /\
      (!(a1 :type) (m1 :int) (a2 :type) (m2 :int).
         e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2) ==>
         st = sa /\ ev = STRING #"%" (toString (sa.cs_next_var + (2 :num))) /\
         dv = STRING #"%" (toString (sa.cs_next_var + (3 :num))) /\
         j1 = sa.cs_next_id + (5 :num) /\ j2 = sa.cs_next_id + (6 :num) /\
         j3 = sa.cs_next_id + (7 :num) /\
         sb0.cs_next_var = sa.cs_next_var + (4 :num) /\
         lookup_block entry_lbl func.fn_blocks =
         SOME
           <|bb_label := entry_lbl;
             bb_instructions :=
               [mk_inst (sa.cs_next_id + (2 :num)) ASSIGN
                  [Lit (i2w m1 :256 word)] [cv];
                mk_inst (sa.cs_next_id + (3 :num)) ADD
                  [Lit (i2w m1 :256 word);
                   Lit ((i2w m2 :256 word) - (i2w m1 :256 word))] [ev];
                mk_inst (sa.cs_next_id + (4 :num)) JMP [Label cond_lbl]
                  ([] :string list)]|>) /\
      (~(?(a1 :type) (m1 :int) (a2 :type) (m2 :int).
          e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2)) ==>
       lower_value compile_expr cenv typ e1 sa = (op1,s1) /\
       lower_value compile_expr cenv typ e2 s1 = (op2,st) /\
       rv = STRING #"%" (toString (st.cs_next_var + (2 :num))) /\
       g1 = STRING #"%" (toString (st.cs_next_var + (3 :num))) /\
       z1 = STRING #"%" (toString (st.cs_next_var + (4 :num))) /\
       g2 = STRING #"%" (toString (st.cs_next_var + (5 :num))) /\
       z2 = STRING #"%" (toString (st.cs_next_var + (6 :num))) /\
       ev = STRING #"%" (toString (st.cs_next_var + (7 :num))) /\
       dv = STRING #"%" (toString (st.cs_next_var + (8 :num))) /\
       j1 = st.cs_next_id + (12 :num) /\ j2 = st.cs_next_id + (13 :num) /\
       j3 = st.cs_next_id + (14 :num) /\
       sb0.cs_next_var = st.cs_next_var + (9 :num) /\
       lookup_block entry_lbl func.fn_blocks =
       SOME
         <|bb_label := entry_lbl;
           bb_instructions :=
             [mk_inst (st.cs_next_id + (2 :num)) ASSIGN [op1] [cv];
              mk_inst (st.cs_next_id + (3 :num)) SUB [op2; op1] [rv];
              mk_inst (st.cs_next_id + (4 :num))
                (if is_signed_type typ then SGT else GT) [op1; op2] [g1];
              mk_inst (st.cs_next_id + (5 :num)) ISZERO [Var g1] [z1];
              mk_inst (st.cs_next_id + (6 :num)) ASSERT [Var z1]
                ([] :string list);
              mk_inst (st.cs_next_id + (7 :num)) GT
                [Var rv; Lit (n2w bound :256 word)] [g2];
              mk_inst (st.cs_next_id + (8 :num)) ISZERO [Var g2] [z2];
              mk_inst (st.cs_next_id + (9 :num)) ASSERT [Var z2]
                ([] :string list);
              mk_inst (st.cs_next_id + (10 :num)) ADD [op1; Var rv] [ev];
              mk_inst (st.cs_next_id + (11 :num)) JMP [Label cond_lbl]
                ([] :string list)]|>) /\
      for_code func cenv bc ret_ty body id tyv p sz ainst cv ev dv nv cond_lbl
        exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
      lookup_block cond_lbl func.fn_blocks =
      SOME
        <|bb_label := cond_lbl;
          bb_instructions :=
            [mk_inst j1 EQ [Var cv; Var ev] [dv];
             mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl]
               ([] :string list)]|> /\
      lookup_block body_lbl func.fn_blocks = SOME bbb /\
      get_instruction bbb (0 :num) =
      SOME (mk_inst j3 MSTORE [Var p; Var cv] ([] :string list)) /\
      sb0.cs_current_bb = body_lbl /\
      sb0.cs_current_insts =
      [mk_inst j3 MSTORE [Var p; Var cv] ([] :string list)] /\
      compile_stmts bc (InLoop exit_lbl incr_lbl) ret_ty body sb0 = ((),sb1) /\
      (~block_is_terminated sb1 ==>
       sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
       sj.cs_current_insts =
       sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr_lbl] ([] :string list)] /\
       fn_has_code sb1 sj func) /\ sj.cs_next_var = sb1.cs_next_var /\
      nv = STRING #"%" (toString sj.cs_next_var) /\ i1 = sj.cs_next_id /\
      i2 = sj.cs_next_id + (1 :num) /\ i3 = sj.cs_next_id + (2 :num) /\
      lookup_block incr_lbl func.fn_blocks =
      SOME
        <|bb_label := incr_lbl;
          bb_instructions :=
            [mk_inst i1 ADD [Var cv; Lit (1w :256 word)] [nv];
             mk_inst i2 ASSIGN [Var nv] [cv];
             mk_inst i3 JMP [Label cond_lbl] ([] :string list)]|> /\
      sb.cs_current_bb = exit_lbl /\
      sb.cs_current_insts = ([] :instruction list) /\
      sb0.cs_next_var <= sb.cs_next_var /\ ~not_fresh_at sa dv /\
      not_fresh_at sb0 p /\ not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\
      (!(x :string). not_fresh_at sa x ==> not_fresh_at sb0 x) /\
      sa.cs_next_id <= ainst.inst_id /\ sa.cs_next_id <= sb0.cs_next_id /\
      sa.cs_next_var <= sb0.cs_next_var /\ cs_extends sa sb0 /\
      cs_extends shadow_sa shadow_sb0 /\ cs_extends shadow_sb1 shadow_sb /\
      stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty body sb0 = (body_cenv,sb1) /\
      stmts_env (gas_shadow_env T bc) (InLoop exit_lbl incr_lbl) ret_ty (MAP gas_shadow_stmt body)
        shadow_sb0 = (gas_shadow_env T body_cenv,shadow_sb1) /\
      gas_shadow_state sb0 shadow_sb0 /\ gas_shadow_state sb1 shadow_sb1 /\
      fn_has_code sb0 sb1 func /\
      fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
      type_stmts (extend_local env id typ F) ret_ty body = SOME body_env' /\
      body_inv tops ctx bc cx /\ supported_stmts tops bindings body /\
      (!(target :type).
         supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
         occurs_abi_decode_target target tops) /\ stmts_exprs_ok bc body /\
      call_evaluation_safe cx (int_calls_stmts body) /\
      frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc
        ret_ty /\ local_ptrs_reserved bc sb0 /\ ~block_is_terminated sb0 /\
      (!(H :(bool # 256 word # type_value) list # num list).
         dead_lo_ok H (DF H) lo bc cx) /\
      (!(x :string) (z :num).
         bc.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sb0 x) /\
      (!(x :string) (z :num).
         bc.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sb0 x) /\
      !(st0 :evaluation_state) (es0 :evaluation_state) (s0 :venom_state)
          (G0 :string |-> num # num) (tn0 :taint) (n1 :int) (n2 :int) (N :num)
          (w :256 word).
        n1 <= n2 /\ N = Num (n2 - n1) /\ N < dimword (:256) /\
        value_has_type tyv (IntV n1 :value) /\
        value_has_type tyv (IntV n2 :value) /\
        body_for_full_ok cx tyv id body
          (GENLIST (\(j :num). Value (IntV (n1 + ((&j) :int)) :value)) N) ==>
        !(cenv' :compile_env)
            (Inv :(bool # 256 word # type_value) list # num list ->
                  eval_result list ->
                  evaluation_state ->
                  (string |-> num # num) -> taint -> venom_state -> bool)
            (Done :(bool # 256 word # type_value) list # num list ->
                   evaluation_state ->
                   (string |-> num # num) -> taint -> venom_state -> bool)
            (R :(bool # 256 word # type_value) list # num list ->
                vyperState$exception ->
                evaluation_state ->
                (string |-> num # num) # taint -> exec_result -> bool).
          cenv' = cenv /\
          Inv =
          (\(H :(bool # 256 word # type_value) list # num list)
             (rs :eval_result list) (ee :evaluation_state)
             (G :string |-> num # num) (tn :taint) (s :venom_state).
             ?(k :num).
               k + LENGTH rs = N /\
               rs =
               GENLIST
                 (\(j :num). Value (IntV (n1 + ((&(k + j)) :int)) :value))
                 (LENGTH rs) /\ body_const_cells_agree [(NONE,tops)] cx env ee /\
               expr_sim_inv cenv cx env ee /\
               lookup_scopes id ee.scopes = (NONE :scope_entry option) /\
               s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = (0 :num) /\
               ~s.vs_halted /\ stmt_state_rel H ctx func cenv cx ee s /\
               storage_well_formed_on cx ee (FST H) /\ ret_pc_ok cenv sa s /\
               return_buf_frame d cenv sb0 s /\ return_buf_sep d cenv ee s /\
               ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
               lookup_var cv s = SOME (i2w (n1 + ((&k) :int)) :256 word) /\
               lookup_var ev s = SOME (i2w n2 :256 word) /\
               lookup_var p s = SOME w /\
               FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n w,sz) /\
               ptr_covers G tn p s sz /\
               op_taint tn (Var cv) = ({} :num -> bool) /\
               op_prov G (Var cv) = (NONE :(num # num) option) /\
               op_taint tn (Var ev) = ({} :num -> bool) /\
               op_prov G (Var ev) = (NONE :(num # num) option) /\
               alloca_history func s /\
               (!(fn :ir_function) (inst :instruction) (v :venom_state).
                  frag_reachable ctx func s fn inst v ==> dalloca_fmp_headroom inst v) /\
               (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
               s0.vs_alloca_next <= s.vs_alloca_next /\
               (!(x :string) (v :256 word).
                  not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
                  lookup_var x s = SOME v) /\
               (!(aid :num) (b :num # num).
                  FLOOKUP s0.vs_allocas aid = SOME b ==>
                  FLOOKUP s.vs_allocas aid = SOME b) /\
               (!(x :string).
                  not_fresh_at sa x ==>
                  FLOOKUP G x = FLOOKUP G0 x /\
                  op_taint tn (Var x) = op_taint tn0 (Var x)) /\
               alloca_frame cenv es0 sa s0 cenv ee s /\
               !(aid :num) (off :num) (z :num) (i :num).
                 FLOOKUP s0.vs_allocas aid = SOME (off,z) /\
                 aid < sa.cs_next_id /\
                 (!(nm :string) (b :num) (z' :num).
                    local_region cenv es0.scopes s0 nm b z' ==>
                    off + z <= b \/ b + z' <= off) /\ off <= i /\
                 i < off + z /\ i IN tn.t_mem ==>
                 i IN tn0.t_mem) /\
          Done =
          (\(H :(bool # 256 word # type_value) list # num list)
             (ee :evaluation_state) (G :string |-> num # num) (tn :taint)
             (s :venom_state).
             stmt_lands lctx sb (INL () :unit + vyperState$exception) s /\
             ~s.vs_halted /\ ~block_is_terminated sb /\
             cenv_top_ext cenv cenv' ee.scopes /\
             stmt_state_rel H ctx func cenv' cx ee s /\
             storage_well_formed_on cx ee (FST H) /\
             return_buf_frame d cenv' sb s /\ return_buf_sep d cenv' ee s /\
             ghost_inv_at (DF H) lo d cenv' cx ee G tn s /\
             alloca_history func s /\
             (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
             s0.vs_alloca_next <= s.vs_alloca_next /\
             (!(x :string) (v :256 word).
                not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
                lookup_var x s = SOME v) /\
             (!(aid :num) (b :num # num).
                FLOOKUP s0.vs_allocas aid = SOME b ==>
                FLOOKUP s.vs_allocas aid = SOME b) /\
             (!(x :string).
                not_fresh_at sa x ==>
                FLOOKUP G x = FLOOKUP G0 x /\
                op_taint tn (Var x) = op_taint tn0 (Var x)) /\
             alloca_frame cenv es0 sa s0 cenv' ee s /\
             !(aid :num) (off :num) (z :num) (i :num).
               FLOOKUP s0.vs_allocas aid = SOME (off,z) /\
               aid < sa.cs_next_id /\
               (!(nm :string) (b :num) (z' :num).
                  local_region cenv es0.scopes s0 nm b z' ==>
                  off + z <= b \/ b + z' <= off) /\ off <= i /\ i < off + z /\
               i IN tn.t_mem ==>
               i IN tn0.t_mem) /\
          R =
          (\(H :(bool # 256 word # type_value) list # num list)
             (ex :vyperState$exception) (ee :evaluation_state)
             (gt :(string |-> num # num) # taint) (r :exec_result).
             (!(tail :256 word list).
                stmt_exit_ptr (RetQ H) (ee with gas_obs := tail)
                  (INR ex :unit + vyperState$exception) gt r) /\
             halt_exit H cx ee (INR ex :'e + vyperState$exception) r /\
             (ctx_has_dalloca ctx ==>
              !(s :venom_state).
                r = Halt s \/ (?(ir :internal_return). r = IntRet ir s) ==>
                allocas_below_fmp s)) ==>
          !(a :eval_result) (rs :eval_result list) (es :evaluation_state)
              (s :venom_state) (G :string |-> num # num) (tn :taint).
            ~s.vs_halted /\
            (!(H :(bool # 256 word # type_value) list # num list).
               valid_horizon cx st0 H es.storage_trace ==>
               Inv H (a::rs) es G tn s) /\
            gas_admissible (eval_for cx tyv id body (a::rs)) (stmt_res_ok lctx)
              es ==>
            gas_outcome_full
              (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
              (cx_tops cx) cx st0
              (bind (read_result cx a)
                 (\(v :value).
                    ignore_bind (push_scope_with_var id tyv v)
                      (finally
                         (try
                            (ignore_bind (eval_stmts cx body)
                               (return F :
                                evaluation_state ->
                                (bool + vyperState$exception) #
                                evaluation_state)) handle_loop_exception)
                         pop_scope))) (es,s,G,tn)
              (\(H :(bool # 256 word # type_value) list # num list)
                 (res :bool + vyperState$exception) (ee :evaluation_state)
                 (G1 :string |-> num # num) (tn1 :taint) (t :venom_state).
                 ee.gas_obs = ([] :256 word list) /\ ~t.vs_halted /\
                 ?(b :bool).
                   res = (INL b :bool + vyperState$exception) /\
                   (b ==> Done H ee G1 tn1 t) /\ (~b ==> Inv H rs ee G1 tn1 t))
              (\(H :(bool # 256 word # type_value) list # num list)
                 (res :bool + vyperState$exception) (ee :evaluation_state)
                 (gt :(string |-> num # num) # taint) (r :exec_result).
                 ?(ex :vyperState$exception).
                   res = (INR ex :bool + vyperState$exception) /\
                   R H ex ee gt r)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "entry")
    (CONJUNCTS_THEN2 (mk_asm "frame_compose")
      (CONJUNCTS_THEN2 (mk_asm "frame_pop")
        (CONJUNCTS_THEN2 assume_tac (mk_asm "exit_scope"))))) >>
  rpt gen_tac >> pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  disch_then (fn pre => strip_assume_tac pre >>
    asm_x "entry" (fn entry =>
      qx_choosel_then
      [`st`, `bc`, `body_cenv`, `body_env'`, `sb0`, `sb1`, `shadow_sb0`, `shadow_sb1`,
       `p`, `sz`, `ainst`, `cv`, `ev`, `dv`, `nv`, `entry_lbl`, `cond_lbl`, `exit_lbl`,
       `body_lbl`, `incr_lbl`, `j1`, `j2`, `j3`, `bbb`, `i1`, `i2`, `i3`, `sj`,
       `op1`, `s1`, `op2`, `rv`, `g1`, `z1`, `g2`, `z2`]
       (fn pkg =>
         let val clauses = CONJUNCTS pkg in
           EVERY (map assume_tac (Lib.butlast clauses)) >>
           mk_asm "enter_cons" (List.last clauses)
         end)
       (MATCH_MP (BETA_RULE (PURE_ONCE_REWRITE_RULE [LET_THM] entry))
          (CONJUNCT2 pre)))) >>
  qexistsl_tac
    [`st`, `bc`, `body_cenv`, `body_env'`, `sb0`, `sb1`, `shadow_sb0`, `shadow_sb1`,
     `p`, `sz`, `ainst`, `cv`, `ev`, `dv`, `nv`, `entry_lbl`, `cond_lbl`, `exit_lbl`,
     `body_lbl`, `incr_lbl`, `j1`, `j2`, `j3`, `bbb`, `i1`, `i2`, `i3`, `sj`,
     `op1`, `s1`, `op2`, `rv`, `g1`, `z1`, `g2`, `z2`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >> conj_tac
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result] >> gen_tac >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates] >>
      irule storage_trace_frame_finally >> simp[storage_trace_frame_pop_scope] >>
      irule storage_trace_frame_try >>
      simp[storage_trace_frame_loop_handler,
           CONJUNCT1 (CONJUNCT2 evaluate_storage_trace_frame),
           storage_trace_frame_return, storage_trace_frame_ignore_bind]) >>
  asm_rewrite_tac [] >> strip_tac >>
  qabbrev_tac `k = N - LENGTH (a::rs)` >>
  `!j. j + LENGTH (a::rs) = N ==> j = k` by
    (simp[Abbr `k`] >> decide_tac) >>
  qpat_assum `Inv = _` (fn inv_def =>
    qpat_x_assum `!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es G tn s`
      (mk_asm "inv_cons" o BETA_RULE o PURE_REWRITE_RULE [inv_def])) >>
  asm "inv_cons" (qspec_then `storage_trace_horizon es.storage_trace`
    (drule_then (qx_choose_then `j` strip_assume_tac) o
      PURE_ONCE_REWRITE_RULE [GSYM storage_trace_domain_def])) >>
  `j = k` by
    (qpat_assum `!j. j + LENGTH (a::rs) = N ==> j = k` irule >>
     first_assum ACCEPT_TAC) >> pop_assum SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G tn s` by
    (qx_gen_tac `H` >> strip_tac >>
     asm "inv_cons" (qspec_then `H` (drule_then strip_assume_tac)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm_x "enter_cons" (qspecl_then
    [`st0`, `es0`, `s0`, `G0`, `tn0`, `n1`, `n2`, `N`, `k`, `a`, `rs`,
     `es`, `s`, `G`, `tn`, `w`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o CONV_RULE (TOP_DEPTH_CONV BETA_CONV) o
    PURE_REWRITE_RULE [LET_THM]) >>
  qmatch_asmsub_abbrev_tac `expr_sim_inv bc cx (extend_local env id typ F) ep` >>
  qmatch_asmsub_abbrev_tac `ret_pc_ok bc sb0 t` >>
  qabbrev_tac `s_eq = update_var dv (bool_to_word F) s` >>
  qabbrev_tac `s_jnz = jump_to body_lbl (s_eq with vs_inst_idx := 1)` >>
  qabbrev_tac `s_store = mstore (w2n w) (i2w (n1 + &k)) s_jnz` >>
  qabbrev_tac `Gentry = step_prov PG
    (step_prov PG (step_prov PG G (mk_inst j1 EQ [Var cv;Var ev] [dv]) s_eq)
       (mk_inst j2 JNZ [Var dv;Label exit_lbl;Label body_lbl] []) s_jnz)
    (mk_inst j3 MSTORE [Var p;Var cv] []) s_store` >>
  qabbrev_tac `tt = step_taint (mk_inst j3 MSTORE [Var p;Var cv] []) s_jnz s_store
    (step_taint (mk_inst j2 JNZ [Var dv;Label exit_lbl;Label body_lbl] [])
       (s_eq with vs_inst_idx := 1) s_jnz
       (step_taint (mk_inst j1 EQ [Var cv;Var ev] [dv]) s s_eq tn))` >>
  `ep.storage_trace = es.storage_trace /\ ep.scopes <> [] /\ ep.gas_obs = []` by
    simp[Abbr `ep`] >>
  `!H. valid_horizon cx st0 H ep.storage_trace ==>
     stmt_state_rel H ctx func bc cx ep t /\ storage_well_formed_on cx ep (FST H) /\
     ghost_inv_at (DF H) lo d bc cx ep Gentry tt t` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
       gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gentry,tt) /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- (qpat_assum `ep.storage_trace = es.storage_trace`
                    (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `return_buf_sep d bc ep t` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
       gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gentry,tt) /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     (impl_tac >- simp[GSYM storage_trace_domain_def]) >> strip_tac >>
     `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t` by
       (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gentry,tt)`
          (mp_then (Pos hd) mp_tac bodyFullSharedTheory.return_buf_allocas_path) >>
        disch_then (qspecl_then [`sb0`,`es`,`d`,`cenv`] mp_tac) >>
        qpat_assum `return_buf_frame d cenv sb0 s` (fn frame =>
          qpat_assum `return_buf_sep d cenv es s` (fn sep => rewrite_tac [frame,sep]))) >>
     `cenv.ce_alloca_locals` by
       (qpat_assum `body_inv tops ctx cenv cx`
          (ACCEPT_TAC o MATCH_MP contract_inv_alloca_locals o MATCH_MP body_inv_contract)) >>
     drule_all_then strip_assume_tac stmtSimPropsTheory.declare_local_ptr >>
     `p <> dv` by
       (Cases_on `?a1 m1 a2 m2. e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2)`
        >- (qpat_x_assum `?a1 m1 a2 m2. _` strip_assume_tac >>
            qpat_assum `!a1 m1 a2 m2. _ ==> st = sa /\ _`
              (drule_all_then strip_assume_tac) >>
            qpat_assum `dv = _` (fn dv_eq => qpat_assum `p = _` (fn p_eq =>
              qpat_assum `st = sa` (fn st_eq =>
                simp[NoAsms, dv_eq, p_eq, st_eq, ASCIInumbersTheory.toString_inj])))) >>
        qpat_assum `~(?a1 m1 a2 m2. _) ==> _` (drule_then strip_assume_tac) >>
        qpat_assum `dv = _` (fn dv_eq => qpat_assum `p = _` (fn p_eq =>
          simp[NoAsms, dv_eq, p_eq, ASCIInumbersTheory.toString_inj]))) >>
     `!x. x <> dv ==> lookup_var x t = lookup_var x s` by
       simp[NoAsms, Abbr `t`, Abbr `s_store`, Abbr `s_jnz`, Abbr `s_eq`,
            lookup_var_def, update_var_def, jump_to_def, mstore_def, FLOOKUP_UPDATE] >>
     `t.vs_allocas = s.vs_allocas` by
       simp[NoAsms, Abbr `t`, Abbr `s_store`, Abbr `s_jnz`, Abbr `s_eq`,
            update_var_def, jump_to_def, mstore_def] >>
     irule (INST_TYPE [alpha |-> ``:256``]
       bodyFullSharedTheory.return_buf_sep_allocated_local) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `t.vs_allocas = s.vs_allocas` (fn maps =>
       qpat_assum `FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n w,sz)`
         (irule_at Any o PURE_REWRITE_RULE [GSYM maps])) >>
     qpat_assum `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s`
       (irule_at Any) >>
     qpat_assum `local_ptrs_reserved cenv sa` (irule_at Any) >>
     `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz)` by
       (qpat_assum `p = _` SUBST1_TAC >> qpat_assum `sz = _` SUBST1_TAC >>
        first_assum ACCEPT_TAC) >>
     pop_assum (irule_at Any) >>
     `lookup_var p t = SOME w` by
       (qpat_assum `!x. x <> dv ==> lookup_var x t = _` (drule_then SUBST1_TAC) >>
        first_assum ACCEPT_TAC) >>
     pop_assum (irule_at Any) >>
     conj_tac
     >- (qx_gen_tac `x'` >> qx_gen_tac `v'` >> strip_tac >>
         `x' <> dv` by
           (disch_then (fn eq =>
              qpat_assum `not_fresh_at sa x'` (assume_tac o REWRITE_RULE [eq])) >>
            qpat_assum `~not_fresh_at sa dv` (fn th => first_assum (CONTR_TAC o MATCH_MP th))) >>
         qpat_assum `!x. x <> dv ==> lookup_var x t = _` (drule_then SUBST1_TAC) >>
         first_assum ACCEPT_TAC) >>
     conj_tac
     >- (qx_gen_tac `nm` >> gen_tac >>
         simp[NoAsms, Abbr `ep`, lookup_scopes_def, FLOOKUP_UPDATE, EQ_SYM_EQ,
              SF CONJ_ss] >> strip_tac >>
         qpat_assum `SOME _ = lookup_scopes nm es.scopes` (SUBST1_TAC o SYM) >> simp[]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `body_const_cells_agree [(NONE,tops)] cx env ep` by
    (irule (iffLR body_const_cells_agree_immutables) >>
     qexists_tac `es` >> simp[Abbr `ep`]) >>
  `stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cx (InLoop exit_lbl incr_lbl) RetQ bc
     (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty body)
     (stmts_env (gas_shadow_env T bc) (InLoop exit_lbl incr_lbl) ret_ty
        (MAP gas_shadow_stmt body))
     (eval_stmts cx body) ep` by
    (qpat_x_assum `body_stmts_full_ok cx body`
      (irule o PURE_ONCE_REWRITE_RULE [body_stmts_full_ok_def]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qexistsl_tac [`bindings`, `extend_local env id typ F`, `body_env'`, `tops`] >>
         simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `stmt_frag_full _ _ _ _ _ _ _ _ _`
    (qspecl_then [`st0`, `sb0`, `sb1`, `shadow_sb0`, `shadow_sb1`,
                  `t`, `Gentry`, `tt`, `body_cenv`] mp_tac o
     PURE_ONCE_REWRITE_RULE [bodySimFullTheory.stmt_frag_full_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_stmts cx body) (ep,t,Gentry,tt) BQ BR` >>
  qabbrev_tac `SourceQ = \H res ee Gb tb u.
    (?xs. !tail. eval_stmts cx body (ep with gas_obs := xs ++ tail) =
                (res,ee with gas_obs := tail)) /\
    ee.gas_obs = [] /\ BQ H res ee Gb tb u` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_stmts cx body) (ep,t,Gentry,tt) SourceQ BR` by
    (irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
     simp[Abbr `SourceQ`]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ BQ BR` kall_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  qabbrev_tac `EnrichedQ = \H res ee Gb tb u.
    SourceQ H res ee Gb tb u /\
    (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z)` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_stmts cx body) (ep,t,Gentry,tt) EnrichedQ BR` by
    (irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_x_assum `gas_outcome_full _ _ _ _ _ _ SourceQ BR` (irule_at Any) >>
     simp[NoAsms, Abbr `EnrichedQ`] >> rpt strip_tac >>
     qpat_assum `gas_origin_ptr_path _ (t,Gentry,tt) _ (OK _,_,_)`
       (mp_then (Pos hd) mp_tac bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac [] >> disch_then (drule_then ACCEPT_TAC)) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ SourceQ BR` kall_tac >>
  qpat_assum `!DF0 lo0 d0 ctx0 func0 PG0 tops0 cx0 st0 body0 es0 s G tn Q R. _`
    (drule_all_then (mk_asm "popped_outcome")) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0
     (finally (try (do eval_stmts cx body; return F od)
                   handle_loop_exception) pop_scope) (ep,t,Gentry,tt)
     (\H res ee G1 tn1 u. ee.gas_obs = [] /\ ~u.vs_halted /\
       ?b. res = INL b /\ (b ==> Done H ee G1 tn1 u) /\
       (~b ==> Inv H rs ee G1 tn1 u))
     (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)` by
    (irule gas_outcome_full_zero_suffix_mono >>
     asm_x "popped_outcome" (fn th => irule_at Any th) >>
     conj_tac >- suspend "exception_suffix" >> suspend "normal_suffix") >>
  pop_assum (mk_asm "clean_outcome") >>
  suspend "attach_prefix"
QED

Resume range_full_round[exception_suffix]:
  rpt gen_tac >> simp[Abbr `BR`] >> strip_tac >>
  rename1 `halt_exit H cx (ee with scopes := sc::ee.scopes) raw r` >>
  Cases_on `raw`
  >- (qpat_assum `!tail. stmt_exit_ptr _ _ _ _ _` (qspec_then `[]` mp_tac) >>
      Cases_on `r` >> simp[NoAsms, bodyPtrDefsTheory.stmt_exit_ptr_def,
                           exprSimDefsTheory.expr_exit_def]) >>
  rename1 `halt_exit H cx (ee with scopes := sc::ee.scopes) (INR ex) r` >>
  `ex <> BreakException /\ ex <> ContinueException` by
    (conj_tac >> disch_then (fn eq =>
       qpat_assum `!tail. stmt_exit_ptr _ _ (INR ex) _ r`
         (qspec_then `[]` (mp_tac o PURE_REWRITE_RULE [eq]))) >>
     Cases_on `r` >> simp[NoAsms, bodyPtrDefsTheory.stmt_exit_ptr_def,
                          exprSimDefsTheory.expr_exit_def]) >>
  qexists_tac `ex` >> simp[] >>
  qabbrev_tac `prepop = ee with scopes := sc::ee.scopes` >>
  `!tail. stmt_exit_ptr (RetQ H) (prepop with gas_obs := tail)
            (INR ex : unit + exception) gt r` by
    (qpat_assum `!tail. stmt_exit_ptr _ _ (INR ex) _ r` mp_tac >>
     simp[NoAsms, Abbr `prepop`]) >>
  conj_tac
  >- (qx_gen_tac `tail` >>
      qpat_assum `!tail. stmt_exit_ptr _ (prepop with gas_obs := tail) (INR ex) _ r`
        (qspec_then `tail` mp_tac) >>
      simp[NoAsms, Abbr `prepop`, bodyPtrDefsTheory.stmt_exit_ptr_def]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  `halt_exit H cx (prepop with <|scopes := ee.scopes; gas_obs := ee.gas_obs|>)
       (INR ex : unit + exception) r` suffices_by
    (simp[NoAsms, Abbr `prepop`] >> disch_then (fn th =>
       MATCH_ACCEPT_TAC (MATCH_MP (iffLR haltExitProjTheory.halt_exit_INR_type) th))) >>
  irule bodyFullForControlTheory.halt_exit_scopes_gas_obs >>
  first_assum ACCEPT_TAC
QED

Resume range_full_round[normal_suffix]:
  rpt gen_tac >> simp[NoAsms, Abbr `EnrichedQ`, Abbr `SourceQ`, Abbr `BQ`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "body_post")) >>
  asm "body_post" (qspec_then `storage_trace_horizon ee.storage_trace`
    (drule_then (qx_choosel_then [`raw0`,`sc0`] strip_assume_tac) o
     PURE_ONCE_REWRITE_RULE [GSYM storage_trace_domain_def])) >>
  (* The normal landing has a JMP at its cursor; the Continue landing has ADD.
     This separates the two cases even though both map to INL F. *)
  `~(t'.vs_current_bb = incr_lbl /\ t'.vs_inst_idx = 0 /\
     stmt_lands (InLoop exit_lbl incr_lbl) sb1 (INL ()) t' /\
     ~block_is_terminated sb1)` by
    (strip_tac >>
     qpat_assum `stmt_lands _ sb1 (INL ()) t'`
       (strip_assume_tac o SRULE [stmt_lands_def]) >>
     qpat_assum `~block_is_terminated sb1 ==> _` drule >> strip_tac >>
     drule_all fn_has_code_same_block >> strip_tac >>
     `sb1.cs_current_bb = incr_lbl /\ LENGTH sb1.cs_current_insts = 0` by
       (qpat_assum `t'.vs_current_bb = sb1.cs_current_bb` (SUBST1_TAC o SYM) >>
        qpat_assum `t'.vs_inst_idx = LENGTH sb1.cs_current_insts` (SUBST1_TAC o SYM) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!i. i < LENGTH [_] ==> _` (qspec_then `0` mp_tac) >>
     qpat_assum `lookup_block incr_lbl _ = SOME <|bb_label := incr_lbl; bb_instructions := _|>` mp_tac >>
     qpat_assum `lookup_block sb1.cs_current_bb _ = SOME _` mp_tac >>
     qpat_assum `sb1.cs_current_bb = incr_lbl` SUBST1_TAC >>
     qpat_assum `LENGTH sb1.cs_current_insts = 0` SUBST1_TAC >>
     simp[NoAsms] >> strip_tac >>
     simp[NoAsms, get_instruction_def, mk_inst_def]) >>
  `!raw. stmt_lands (InLoop exit_lbl incr_lbl) sb1 raw t' /\
        (raw = INL () ==> ~block_is_terminated sb1) /\
        res = (case raw of INL u => INL F
                 | INR BreakException => INL T
                 | INR ContinueException => INL F | INR ex => INR ex) ==>
        raw = (if res = INL T then INR BreakException
               else if t'.vs_current_bb = incr_lbl /\ t'.vs_inst_idx = 0
               then INR ContinueException else INL ())` by
    (qx_gen_tac `raw` >>
     disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
     qpat_assum `stmt_lands _ sb1 raw t'`
       (strip_assume_tac o SRULE [stmt_lands_def])
     >- (`~(t'.vs_current_bb = incr_lbl /\ t'.vs_inst_idx = 0)` by
           (strip_tac >>
            qpat_assum `raw = INL () ==> _` drule >> disch_tac >>
            qpat_assum `raw = INL ()` SUBST_ALL_TAC >>
            qpat_assum `~(t'.vs_current_bb = incr_lbl /\ _)`
              (MATCH_MP_TAC o NOT_ELIM) >>
            rpt conj_tac >> first_assum ACCEPT_TAC) >>
         qpat_assum `res = _` mp_tac >>
         qpat_assum `raw = INL ()` SUBST1_TAC >>
         qpat_assum `~(t'.vs_current_bb = incr_lbl /\ t'.vs_inst_idx = 0)`
           (fn th => simp[NoAsms, th]))
     >- (qpat_assum `res = _` mp_tac >>
         qpat_assum `raw = INR BreakException` SUBST1_TAC >>
         simp[NoAsms]) >>
     qpat_assum `res = _` mp_tac >>
     qpat_assum `raw = INR ContinueException` SUBST1_TAC >>
     qpat_assum `t'.vs_current_bb = incr_lbl` SUBST1_TAC >>
     qpat_assum `t'.vs_inst_idx = 0` SUBST1_TAC >> simp[NoAsms]) >>
  qabbrev_tac `landing_raw = if res = INL T then INR BreakException
    else if t'.vs_current_bb = incr_lbl /\ t'.vs_inst_idx = 0
    then INR ContinueException else INL ()` >>
  `raw0 = landing_raw` by
    (qpat_assum `!raw. _ ==> raw = landing_raw` (qspec_then `raw0` MATCH_MP_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac
     >- (disch_tac >> qpat_assum `raw0 = INL () ==> _`
           (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
     qpat_assum `res = _` mp_tac >>
     Cases_on `raw0` >> simp[NoAsms] >> rename1 `INR ex` >> Cases_on `ex` >> simp[NoAsms]) >>
  (Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
     `landing_raw = INL () \/ landing_raw = INR BreakException \/
      landing_raw = INR ContinueException` >-
    (qpat_assum `raw0 = landing_raw` (SUBST1_TAC o SYM) >>
     qpat_assum `stmt_lands _ sb1 raw0 t'` mp_tac >>
     simp[NoAsms, stmt_lands_def] >> strip_tac >>
     asm_rewrite_tac [])) >>
  qabbrev_tac `at_incr = if landing_raw = INL () then jump_to incr_lbl t' else t'` >>
  qabbrev_tac `countw = i2w (n1 + &k) : bytes32` >>
  qexistsl_tac
    [`if landing_raw = INR BreakException then t'
      else jump_to cond_lbl (update_var cv (countw+1w) (update_var nv (countw+1w) at_incr))`,
     `if landing_raw = INR BreakException then G1
      else DRESTRICT (DRESTRICT G1 (COMPL {nv})) (COMPL {cv})`,
     `if landing_raw = INR BreakException then tn1
      else tn1 with t_var := tn1.t_var |+ (nv,{}) |+ (cv,{})`] >>
  qx_gen_tac `H` >> strip_tac >>
  asm_x "body_post" (qspec_then `H`
    (drule_then (qx_choosel_then [`rawH`,`scH`] strip_assume_tac))) >>
  `rawH = landing_raw` by
    (qpat_assum `!raw. _ ==> raw = landing_raw` (qspec_then `rawH` MATCH_MP_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac
     >- (disch_tac >> qpat_assum `rawH = INL () ==> _`
           (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
     qpat_assum `res = _` mp_tac >>
     Cases_on `rawH` >> simp[NoAsms] >> rename1 `INR ex` >> Cases_on `ex` >> simp[NoAsms]) >>
  rename1 `stmt_state_rel H ctx func cH cx (ee with scopes := scH::ee.scopes) t'` >>
  `ee with <|scopes := scH::ee.scopes; gas_obs := []|> =
   ee with scopes := scH::ee.scopes` by
    simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. eval_stmts cx body _ = (rawH,_)`
    (qspec_then `[]` mp_tac) >>
  qpat_assum `ee with <|scopes := _; gas_obs := []|> = ee with scopes := _`
    (fn th => simp[NoAsms, APPEND_NIL, th]) >>
  disch_tac >> qmatch_asmsub_abbrev_tac `eval_stmts cx body epH = (rawH,_)` >>
  qabbrev_tac `prepop = ee with scopes := scH::ee.scopes` >>
  asm_x "frame_compose" (fn comp =>
    qpat_assum `alloca_frame cenv es0 sa s0 bc ep t`
      (mp_then (Pos (el 7)) (fn half =>
        qpat_assum `alloca_frame bc ep sb0 t cH prepop t'`
          (mp_then (Pos (el 14)) mp_tac half)) comp)) >>
  (* The common contract is polymorphic in the map range. Its structural
     frame uses empty maps; the actual provenance equations compose directly. *)
  disch_then (mp_tac o Q.SPECL [`func`,`ctx`,`FEMPTY`,`tn0`,`FEMPTY`,`tt`,`FEMPTY`,`tn1`]) >>
  (impl_tac >- (asm_rewrite_tac [] >>
    rpt conj_tac >> qx_gen_tac `x` >> disch_tac >>
    first_assum (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
  strip_tac >>
  `!x. not_fresh_at sa x ==>
       FLOOKUP G1 x = FLOOKUP G0 x /\ op_taint tn1 (Var x) = op_taint tn0 (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sb0 x` drule >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP Gentry x = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sb0 x ==> FLOOKUP G1 x = _ /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac []) >>
  `epH.scopes = ep.scopes` by simp[Abbr `epH`] >>
  `cenv_top_ext cenv bc epH.scopes /\ epH.scopes <> []` by asm_rewrite_tac [] >>
  `FDOM (HD ep.scopes) = {id} /\ TL ep.scopes = es.scopes` by
    simp[Abbr `ep`, finite_mapTheory.FDOM_FUPDATE] >>
  `!nm. nm IN FDOM (HD epH.scopes) ==> lookup_scopes nm (TL epH.scopes) = NONE` by
    simp[] >>
  `return_buf_sep d cenv ee t'` by
    (irule bodyFullSharedTheory.return_buf_sep_pop >>
     qexistsl [`cH`,`scH`] >>
     `prepop.scopes = scH::ee.scopes` by simp[Abbr `prepop`] >>
     `cenv_top_ext cenv cH prepop.scopes` by
       (drule vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_dom >>
        strip_tac >> irule stmtSimPropsTheory.cenv_top_ext_trans >>
        qexistsl [`bc`,`epH.scopes`] >>
        qpat_assum `preserves_scopes_dom epH prepop` (strip_assume_tac o
          REWRITE_RULE [vyperEvalPreservesScopesTheory.preserves_scopes_dom_def]) >>
        asm_rewrite_tac []) >>
     conj_tac >-
       (qpat_assum `eval_stmts cx body epH = (rawH,prepop)`
          (mp_then (Pat `eval_stmts _ _ _ = _`) mp_tac range_full_body_no_shadow) >>
        disch_then (qspecl_then [`scH`,`ee.scopes`] mp_tac) >> asm_rewrite_tac []) >>
     conj_tac >- (qpat_assum `prepop.scopes = _` (SUBST1_TAC o SYM) >>
                  asm_rewrite_tac []) >>
     qpat_assum `return_buf_sep d cH prepop t'` mp_tac >>
     simp[NoAsms, Abbr `prepop`]) >>
  qpat_assum `stmt_state_rel H ctx func cH cx prepop t'`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) (fn scope =>
      qpat_assum `ghost_inv_at (DF H) lo d cH cx prepop G1 tn1 t'`
        (mp_then (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`) (fn scope =>
          qpat_assum `eval_stmts cx body epH = (rawH,prepop)`
            (mp_then (Pat `eval_stmts _ _ _ = _`) (fn scope =>
              qpat_assum `alloca_frame cenv es0 sa s0 cH prepop t'`
                (mp_then (Pat `alloca_frame _ _ _ _ _ _ _`) mp_tac scope)) scope)) scope))
      range_full_body_scope_post) >>
  disch_then (fn scope =>
    qpat_assum `cenv_top_ext cenv bc epH.scopes`
      (mp_then (Pat `cenv_top_ext _ _ _`) mp_tac scope)) >>
  disch_then (qspecl_then [`scH`,`ee.scopes`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >-
    (conj_tac
     >- (map_every qx_gen_tac
           [`f0`,`cx0`,`ca`,`ea`,`sa'`,`s00`,`Ga`,`tna`,`c`,`eb`,`u`,
            `Gb`,`tnb`,`co`,`hd`,`tl`] >>
         strip_tac >>
         `!x. not_fresh_at sa' x ==> op_taint tnb (Var x) = op_taint tna (Var x)` by
           (qx_gen_tac `x` >> disch_tac >>
            qpat_assum `!x. not_fresh_at sa' x ==> FLOOKUP Gb x = _ /\ _`
              (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
         asm "frame_pop" (mp_tac o Q.SPECL
           [`f0`,`cx0`,`ca`,`ea`,`sa'`,`s00`,`FEMPTY`,`tna`,`c`,`eb`,`u`,
            `FEMPTY`,`tnb`,`co`,`hd`,`tl`]) >>
         (impl_tac >- asm_rewrite_tac []) >>
         strip_tac >> asm_rewrite_tac []) >>
     `prepop.scopes = scH::ee.scopes` by simp[Abbr `prepop`] >>
     asm_rewrite_tac [])) >>
  `prepop with scopes := ee.scopes = ee` by
    simp[Abbr `prepop`, evaluation_state_component_equality] >>
  asm_rewrite_tac [] >> strip_tac >>
  `allocas_from lo t'` by
    (qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t'` mp_tac >>
     simp[NoAsms, ghost_inv_at_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee t'`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t',G1,tn1) [] (OK at_incr,G1,tn1) /\
   at_incr.vs_inst_idx = 0 /\
   (landing_raw = INR BreakException ==> t'.vs_current_bb = exit_lbl) /\
   (landing_raw <> INR BreakException ==> at_incr.vs_current_bb = incr_lbl)` by
    (qpat_assum `stmt_lands (InLoop exit_lbl incr_lbl) sb1 rawH t'`
       (mp_then (Pos hd) mp_tac range_full_body_lands_path) >>
     disch_then (qspecl_then
       [`ctx`,`func`,`sj`,`lo`,`DF H`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G1`,`tn1`]
       mp_tac) >>
     (impl_tac >-
       (`rawH = INL () ==> ~block_is_terminated sb1` by
          (disch_tac >> qpat_assum `rawH = INL () ==> _`
             (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
        `rawH = INL () \/ rawH = INR BreakException \/ rawH = INR ContinueException` by
          (qpat_assum `rawH = landing_raw` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        asm_rewrite_tac [])) >>
     qpat_assum `rawH = landing_raw` SUBST1_TAC >>
     simp[NoAsms, Abbr `at_incr`]) >>
  `bc.ce_return_buf = cenv.ce_return_buf` by
    (qpat_assum `cenv_top_ext cenv bc ep.scopes` mp_tac >>
     simp[NoAsms, cenv_top_ext_def, compile_env_component_equality]) >>
  `return_buf_frame d cenv sb0 t'` by
    (qpat_assum `return_buf_frame d bc sb0 t`
       (mp_then (Pos hd) mp_tac return_buf_frame_frame) >>
     disch_then (qspecl_then [`cenv`,`sb0`,`t'`] mp_tac) >> simp[]) >>
  Cases_on `landing_raw = INR BreakException`
  >- (`return_buf_frame d cenv sb t'` by
        (qpat_assum `return_buf_frame d cenv sb0 t'`
           (mp_then (Pos hd) mp_tac return_buf_frame_frame) >>
         disch_then (qspecl_then [`cenv`,`sb`,`t'`] mp_tac) >> simp[]) >>
      `at_incr = t'` by
        (qpat_assum `landing_raw = INR BreakException`
           (fn th => simp[NoAsms, Abbr `at_incr`, th])) >>
      `t'.vs_current_bb = exit_lbl /\ t'.vs_inst_idx = 0` by
        (conj_tac
         >- (qpat_assum `landing_raw = INR BreakException ==> _`
               (drule_then ACCEPT_TAC)) >>
         qpat_assum `at_incr = t'` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
      qpat_assum `landing_raw = INR BreakException`
        (fn th => simp[NoAsms, th]) >>
      conj_tac >- (irule (cj 1 gas_origin_ptr_path_rules) >> first_assum ACCEPT_TAC) >>
      asm_rewrite_tac [stmt_lands_def, block_is_terminated_def, cenv_top_ext_refl] >>
      simp[NoAsms]) >>
  suspend "backedge"
QED

Resume range_full_round[backedge]:
  qpat_assum `landing_raw <> INR BreakException` (fn th => simp[NoAsms, th]) >>
  qpat_assum `for_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE [for_code_def]) >>
  `!x. x <> dv ==> lookup_var x t = lookup_var x s /\
                    FLOOKUP Gentry x = FLOOKUP G x /\
                    op_taint tt (Var x) = op_taint tn (Var x)` by
    (simp[NoAsms, Abbr `t`, Abbr `s_store`, Abbr `s_jnz`, Abbr `s_eq`,
      Abbr `Gentry`, Abbr `tt`, lookup_var_def, update_var_def, jump_to_def,
      mstore_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, step_prov_def,
      step_taint_def, set_prov_def, out_prov_def, set_var_taint_def, op_taint_def,
      mk_inst_def]) >>
  `lookup_var cv t' = SOME countw /\ lookup_var ev t' = SOME (i2w n2) /\
   lookup_var p t' = SOME w /\ op_prov G1 (Var cv) = NONE /\
   op_taint tn1 (Var cv) = {} /\ op_prov G1 (Var ev) = NONE /\
   op_taint tn1 (Var ev) = {} /\ ptr_covers G1 tn1 p t' sz` by
    suspend "loop_registers" >>
  `FLOOKUP t'.vs_allocas ainst.inst_id = SOME (w2n w,sz)` by
    (qpat_assum `!aid b. FLOOKUP t.vs_allocas aid = SOME b ==> _` irule >>
     qpat_assum `FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n w,sz)` mp_tac >>
     simp[NoAsms, Abbr `t`, Abbr `s_store`, Abbr `s_jnz`, Abbr `s_eq`,
          mstore_def, jump_to_def, update_var_def]) >>
  `at_incr.vs_current_bb = incr_lbl` by
    (qpat_assum `landing_raw <> INR BreakException ==> _`
      (drule_then ACCEPT_TAC)) >>
  `lookup_var cv at_incr = SOME countw /\ ~at_incr.vs_halted /\
   allocas_from lo at_incr` by
    (Cases_on `landing_raw = INL ()` >>
     pop_assum (fn th =>
       simp[NoAsms, Abbr `at_incr`, th, jump_to_def, lookup_var_def, allocas_from_def]) >>
     rpt conj_tac >> first_assum (ACCEPT_TAC o
           SRULE [lookup_var_def, allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp at_incr` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t'` mp_tac >>
     Cases_on `landing_raw = INL ()` >>
     pop_assum (fn th => simp[NoAsms, th, Abbr `at_incr`, jump_to_def, allocas_below_fmp_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (t',G1,tn1) []
     (OK (jump_to cond_lbl (update_var cv (countw+1w) (update_var nv (countw+1w) at_incr))),
      DRESTRICT (DRESTRICT G1 (COMPL {nv})) (COMPL {cv}),
      tn1 with t_var := tn1.t_var |+ (nv,{}) |+ (cv,{}))` by
    (qpat_assum `gas_origin_ptr_path _ (t',G1,tn1) [] (OK at_incr,G1,tn1)`
        (mp_then (Pos hd) mp_tac gas_origin_ptr_path_append) >>
      simp[NoAsms] >> disch_then irule >>
      irule (SRULE [NoAsms] range_full_increment_path) >>
      qpat_assum `at_incr.vs_current_bb = incr_lbl` SUBST1_TAC >>
      qpat_assum `lookup_block incr_lbl func.fn_blocks = SOME _`
        (fn th => irule_at Any th) >>
      qpat_assum `at_incr.vs_inst_idx = 0` SUBST1_TAC >>
      simp[NoAsms, get_instruction_def] >>
      qexistsl_tac [`i3`,`i2`,`i1`] >> asm_rewrite_tac [] >>
      qpat_assum `cv = STRING _ _` (SUBST1_TAC o SYM) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `gas_origin_ptr_path _ (t',G1,tn1) [] (OK (jump_to _ _),_,_)` mp_tac >>
     qpat_assum `cond_lbl = fresh_label_output _ _` (fn cond_eq =>
       qpat_assum `cv = STRING _ _` (fn cv_eq =>
         qpat_assum `nv = STRING _ _` (fn nv_eq =>
           qpat_assum `sj.cs_next_var = sb1.cs_next_var` (fn age =>
             simp[NoAsms, cond_eq, cv_eq, nv_eq, age, DRESTRICT_DRESTRICT]))))) >>
  `!fn inst v. frag_reachable ctx func
      (jump_to cond_lbl (update_var cv (countw+1w) (update_var nv (countw+1w) at_incr)))
      fn inst v ==> dalloca_fmp_headroom inst v` by
    (qpat_assum `gas_origin_ptr_path _ (t',G1,tn1) [] (OK (jump_to _ _),_,_)`
       (mp_then (Pos hd) mp_tac bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac []) >>
  `ret_pc_ok cenv sa t'` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >>
     asm_rewrite_tac [arithmeticTheory.LE_REFL] >>
     map_every qx_gen_tac [`x`,`u`] >> strip_tac >>
     `x <> dv` by
       (disch_then SUBST_ALL_TAC >>
        qpat_assum `~not_fresh_at sa dv` mp_tac >> asm_rewrite_tac []) >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sb0 x`
       (drule_then assume_tac) >>
     qpat_assum `!x. x <> dv ==> _` (drule_then strip_assume_tac) >>
     `lookup_var x t = SOME u` by asm_rewrite_tac [] >>
     qpat_assum `!x u. not_fresh_at sb0 x /\ lookup_var x t = SOME u ==>
                       lookup_var x t' = SOME u` irule >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H ctx func cenv cx ee at_incr /\
   ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 at_incr /\
   ret_pc_ok cenv sa at_incr /\ return_buf_frame d cenv sb0 at_incr /\
   return_buf_sep d cenv ee at_incr` by
    (Cases_on `landing_raw = INL ()` >>
     pop_assum (fn th => simp[NoAsms, Abbr `at_incr`, th,
       stmt_state_rel_jump_to, bodyFullSharedTheory.ghost_inv_at_jump,
       ret_pc_ok_jump_to, return_buf_frame_jump_to,
       bodyFullSharedTheory.return_buf_sep_jump]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `at_incr.vs_allocas = t'.vs_allocas /\ at_incr.vs_memory = t'.vs_memory /\
   at_incr.vs_vars = t'.vs_vars /\ at_incr.vs_alloca_next = t'.vs_alloca_next` by
    (Cases_on `landing_raw = INL ()` >>
     pop_assum (fn th => simp[NoAsms, Abbr `at_incr`, th, jump_to_def])) >>
  `!x. lookup_var x at_incr = lookup_var x t'` by
    (simp[NoAsms, lookup_var_def] >>
     qpat_assum `at_incr.vs_vars = t'.vs_vars` (fn th => simp[NoAsms, th])) >>
  `alloca_history func at_incr` by
    (irule allocaHistoryTheory.alloca_history_jump >>
     qpat_assum `alloca_history func t'` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_frame cenv es0 sa s0 cenv ee at_incr` by
    (irule alloca_frame_same_state >>
     qpat_assum `alloca_frame cenv es0 sa s0 cenv ee t'` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ptr_covers G1 tn1 p at_incr sz` by
    (qpat_assum `ptr_covers G1 tn1 p t' sz` mp_tac >>
     qpat_assum `!x. lookup_var x at_incr = lookup_var x t'`
       (fn th => simp[NoAsms, ptr_covers_def, th])) >>
  `sb0.cs_next_var <= sb1.cs_next_var` by
    (qpat_assum `compile_stmts bc (InLoop exit_lbl incr_lbl) ret_ty body sb0 = ((),sb1)`
       (mp_then Any (ACCEPT_TAC o CONJUNCT2)
          (SRULE [cs_mono_def] (cj 2 stmtLoweringMonoTheory.compile_stmt_cs_mono)))) >>
  `~not_fresh_at sa cv /\ ~not_fresh_at sa nv` by
    (simp[NoAsms, not_fresh_at_def] >> conj_tac
     >- (qexists_tac `st.cs_next_var + 1` >> asm_rewrite_tac [] >> decide_tac) >>
     qexists_tac `sb1.cs_next_var` >> asm_rewrite_tac [] >> decide_tac) >>
  `!oldreg oldval. not_fresh_at sa oldreg /\
       lookup_var oldreg at_incr = SOME oldval ==>
       lookup_var oldreg (update_var cv (countw + 1w)
         (update_var nv (countw + 1w) at_incr)) = SOME oldval` by
    (map_every qx_gen_tac [`oldreg`,`oldval`] >> strip_tac >>
     `oldreg <> cv /\ oldreg <> nv` by
       (conj_tac >> disch_then (fn eq =>
          qpat_assum `not_fresh_at sa oldreg` (mp_tac o REWRITE_RULE [eq])) >>
        asm_rewrite_tac []) >>
     qpat_assum `oldreg <> cv` (fn hcv =>
       qpat_assum `oldreg <> nv` (fn hnv =>
         qpat_assum `lookup_var oldreg at_incr = SOME oldval` (fn hval =>
           simp[NoAsms, hcv, hnv, hval, emitHelperPropsTheory.lookup_var_update_var])))) >>
  `return_buf_sep d cenv ee
     (jump_to cond_lbl (update_var cv (countw + 1w)
       (update_var nv (countw + 1w) at_incr)))` by
    (rewrite_tac [bodyFullSharedTheory.return_buf_sep_jump] >>
     irule (INST_TYPE [alpha |-> ``:256``]
       bodyFullSharedTheory.return_buf_sep_locals_kept) >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `d = SOME (bw,capacity)` (fn deq =>
           qpat_assum `return_buf_sep d cenv ee at_incr`
             (mp_tac o CONJUNCT1 o
              REWRITE_RULE [deq,bodySimFullTheory.return_buf_sep_def])) >>
         rewrite_tac [allocas_from_def, update_var_def] >> simp[NoAsms]) >>
     qexistsl_tac [`H`,`ctx`,`cx`,`ee`,`func`,`at_incr`,`sa`] >>
     simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `stmt_state_rel H ctx func cenv cx ee at_incr`
    (mp_then (Pos hd) mp_tac range_full_increment_frame) >>
  disch_then (qspecl_then
    [`DF H`,`lo`,`d`,`sa`,`sb0`,`es0`,`s0`,`G0`,`tn0`,`G1`,`tn1`,
     `cv`,`nv`,`ev`,`p`,`sz`,`countw`,`i2w n2`,`cond_lbl`] mp_tac) >>
  (impl_tac >-
    (map_every (fn pat => qpat_assum pat
        (assume_tac o ONCE_REWRITE_RULE [EQ_SYM_EQ]))
       [`nv <> cv`, `cv <> p`, `nv <> p`, `cv <> ev`, `nv <> ev`] >>
     asm_rewrite_tac [] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC))) >>
  disch_then (strip_assume_tac o REWRITE_RULE [DRESTRICT_DRESTRICT]) >>
  (Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
     `rawH = INL () \/ rawH = INR ContinueException` >-
    (qpat_assum `rawH = landing_raw` SUBST1_TAC >>
     qpat_assum `landing_raw = INL () \/ landing_raw = INR BreakException \/ _`
       (fn th => mp_tac th >>
         qpat_assum `landing_raw <> INR BreakException`
           (fn neq => simp[NoAsms, neq])))) >>
  `value_has_type tyv (IntV (n1 + &k))` by
    (qspecl_then [`tyv`,`n1`,`n2`] mp_tac stmtSimForRangeTheory.range_value_has_type >>
     asm_rewrite_tac [] >> disch_then irule >>
     qpat_assum `N = Num (n2 - n1)` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `esH = es with gas_obs := xs'` >>
  `expr_sim_inv cenv cx env esH` by simp[Abbr `esH`] >>
  `epH = esH with scopes :=
    (FEMPTY |+ (id, <|assignable := F; type := tyv;
                       value := IntV (n1 + &k); popped := []|>)) :: esH.scopes` by
    simp[NoAsms, Abbr `epH`, Abbr `ep`, Abbr `esH`, evaluation_state_component_equality] >>
  `body_const_cells_agree [(NONE,tops)] cx env ee` by
    (`body_const_cells_agree [(NONE,tops)] cx (extend_local env id typ F) epH` by
       simp[Abbr `epH`] >>
     `body_const_cells_agree [(NONE,tops)] cx (extend_local env id typ F) prepop` by
       (irule body_const_cells_agree_stmts >>
        qpat_assum `eval_stmts cx body epH = (rawH,prepop)` (irule_at Any) >>
        qexists_tac `ret_ty` >> simp[]) >>
     qpat_assum
       `body_const_cells_agree _ cx (extend_local env id typ F) prepop` mp_tac >>
     simp[NoAsms, Abbr `prepop`, body_const_cells_agree_extend_local,
          body_const_cells_agree_state_updates]) >>
  `expr_sim_inv cenv cx env ee` by
    (qpat_assum `prepop with scopes := ee.scopes = ee` (SUBST1_TAC o SYM) >>
     irule bodyExprPreFactsTheory.expr_sim_inv_for_pop >>
     conj_tac >- (qexists_tac `scH` >> simp[NoAsms, Abbr `prepop`]) >>
     qexistsl_tac [`bindings`,`body`,`body_env'`,`esH`,`typ`,`id`,`rawH`,
                  `ret_ty`,`tops`,`tyv`,`IntV (n1 + &k)`] >>
     qpat_assum `type_stmt env ret_ty (For _ _ _ _ _) = SOME env'`
       (mp_then Any strip_assume_tac type_stmt_for_projection) >>
     qpat_assum `body_inv tops ctx cenv cx`
       (strip_assume_tac o MATCH_MP body_inv_main_support) >>
     qpat_assum `epH = esH with scopes := _` (SUBST1_TAC o SYM) >>
     asm_rewrite_tac [] >> simp[Abbr `prepop`]) >>
  `lookup_scopes id ee.scopes = NONE` by
    (irule vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom >>
     qexists_tac `es.scopes` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `eval_stmts cx body epH = (rawH,prepop)`
       (mp_then Any mp_tac vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_dom) >>
     simp[vyperEvalPreservesScopesTheory.preserves_scopes_dom_def,
          Abbr `prepop`, Abbr `epH`, Abbr `ep`]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `F` >> conj_tac
  >- (qpat_assum `rawH = landing_raw` (SUBST1_TAC o SYM) >>
      qpat_assum `rawH = INL () \/ rawH = INR ContinueException`
        (DISJ_CASES_THEN SUBST1_TAC) >> simp[NoAsms]) >>
  simp[NoAsms] >> qexists_tac `SUC k` >>
  conj_tac
  >- (qpat_assum `k + LENGTH (a::rs) = N` mp_tac >>
      qpat_assum `N = Num (n2 - n1)` (fn th => rewrite_tac [th,LENGTH]) >>
      decide_tac) >>
  conj_tac
  >- (qpat_assum `a::rs = GENLIST _ _` mp_tac >>
      simp[NoAsms, listTheory.GENLIST_CONS, combinTheory.o_DEF] >>
      disch_then (fn th => CONV_TAC (LAND_CONV (REWR_CONV (CONJUNCT2 th)))) >>
      simp[NoAsms, listTheory.GENLIST_FUN_EQ] >> decide_tac) >>
  `countw + 1w = (i2w (n1 + &(SUC k)) : bytes32)` by
    simp[NoAsms, Abbr `countw`, arithmeticTheory.ADD1,
         stmtSimForPartsTheory.i2w_counter_suc] >>
  `lookup_var p at_incr = SOME w /\
   FLOOKUP at_incr.vs_allocas ainst.inst_id = SOME (w2n w,sz)` by
    (qpat_assum `!x. lookup_var x at_incr = lookup_var x t'` (fn lv =>
     qpat_assum `at_incr.vs_allocas = t'.vs_allocas` (fn al =>
       rewrite_tac [lv,al])) >> conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `p = STRING _ _` (SUBST1_TAC o SYM) >>
  qpat_assum `ainst = mk_inst _ _ _ _` (SUBST1_TAC o SYM) >>
  qpat_assum `sz = type_memory_bytes cenv typ` (SUBST1_TAC o SYM) >>
  qpat_assum `cv = STRING _ _` (SUBST1_TAC o SYM) >>
  qpat_assum `cond_lbl = fresh_label_output _ _` (SUBST1_TAC o SYM) >>
  qpat_assum `nv = STRING _ (toString sj.cs_next_var)` (fn nv_def =>
    qpat_assum `sj.cs_next_var = sb1.cs_next_var` (fn age =>
      SUBST1_TAC (SYM (REWRITE_RULE [age] nv_def)))) >>
  qpat_assum `landing_raw <> INR BreakException`
    (fn th => rewrite_tac [th]) >>
  qpat_assum `lookup_var p (jump_to _ _) = lookup_var p at_incr`
    (fn th => assume_tac (SRULE [NoAsms] th)) >>
  qpat_assum `lookup_var cv (jump_to _ _) = SOME (countw + 1w)`
    (fn th => assume_tac (SRULE [NoAsms] th)) >>
  qpat_assum `lookup_var ev (jump_to _ _) = SOME (i2w n2)`
    (fn th => assume_tac (SRULE [NoAsms] th)) >>
  asm_rewrite_tac [] >> conj_tac
  >- (`st.cs_next_id = ainst.inst_id` by
        (qpat_assum `ainst = mk_inst _ ALLOCA _ _`
          (fn th => simp[NoAsms, th, mk_inst_def])) >>
      pop_assum SUBST1_TAC >>
      qpat_assum `sz = type_memory_bytes cenv typ` (SUBST1_TAC o SYM) >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `countw + 1w = i2w (n1 + &(SUC k))` (SUBST1_TAC o SYM) >>
  qpat_assum `cv = STRING _ _` (SUBST1_TAC o SYM) >>
  qpat_assum `nv = STRING _ (toString sj.cs_next_var)` (fn nv_def =>
    qpat_assum `sj.cs_next_var = sb1.cs_next_var` (fn age =>
      SUBST1_TAC (SYM (REWRITE_RULE [age] nv_def)))) >>
  qpat_assum `!x v. _ /\ lookup_var x s0 = SOME v ==>
                        lookup_var x (jump_to _ _) = SOME v`
    (ACCEPT_TAC o SRULE [NoAsms])
QED

Resume range_full_round[loop_registers]:
  `!x u. x <> dv /\ not_fresh_at sb0 x /\ lookup_var x s = SOME u ==>
    lookup_var x t' = SOME u /\ FLOOKUP G1 x = FLOOKUP G x /\
    op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (map_every qx_gen_tac [`x`,`u`] >> strip_tac >>
     qpat_assum `!x. x <> dv ==> _` (drule_then strip_assume_tac) >>
     `lookup_var x t = SOME u` by asm_rewrite_tac [] >>
     `lookup_var x t' = SOME u` by
       (qpat_assum `!x u. not_fresh_at sb0 x /\ lookup_var x t = SOME u ==>
                          lookup_var x t' = SOME u` irule >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at sb0 x ==> FLOOKUP G1 x = _ /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac []) >>
  qpat_assum `!x u. x <> dv /\ not_fresh_at sb0 x /\ lookup_var x s = SOME u ==> _`
    (fn th => map_every (fn (reg,v) =>
      qspecl_then [reg,v] mp_tac th >>
      (impl_tac >-
       (conj_tac >- (once_rewrite_tac [EQ_SYM_EQ] >> first_assum ACCEPT_TAC) >>
        conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac)
      [(`cv`,`countw`), (`ev`,`i2w n2`), (`p`,`w`)]) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (simp[NoAsms, op_prov_def] >>
      qpat_assum `FLOOKUP G1 cv = FLOOKUP G cv` SUBST1_TAC >>
      qpat_assum `op_prov G (Var cv) = NONE`
        (ACCEPT_TAC o SRULE [NoAsms, op_prov_def])) >>
  conj_tac
  >- (qpat_assum `op_taint tn1 (Var cv) = op_taint tn (Var cv)` SUBST1_TAC >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (simp[NoAsms, op_prov_def] >>
      qpat_assum `FLOOKUP G1 ev = FLOOKUP G ev` SUBST1_TAC >>
      qpat_assum `op_prov G (Var ev) = NONE`
        (ACCEPT_TAC o SRULE [NoAsms, op_prov_def])) >>
  conj_tac
  >- (qpat_assum `op_taint tn1 (Var ev) = op_taint tn (Var ev)` SUBST1_TAC >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `ptr_covers G tn p s sz` (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
  pure_rewrite_tac [ptr_covers_def] >>
  qpat_assum `op_taint tn1 (Var p) = op_taint tn (Var p)` SUBST1_TAC >>
  qpat_assum `FLOOKUP G1 p = FLOOKUP G p` SUBST1_TAC >>
  `!v. lookup_var p t' = SOME v <=> lookup_var p s = SOME v` by
    (qpat_assum `lookup_var p t' = SOME w` SUBST1_TAC >>
     qpat_assum `lookup_var p s = SOME w` SUBST1_TAC >> rewrite_tac []) >>
  pop_assum (fn th => pure_rewrite_tac [th]) >>
  conj_tac >- first_assum ACCEPT_TAC >> goal_assum (drule_at Any) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume range_full_round[attach_prefix]:
  qabbrev_tac `head = bind (read_result cx a) (push_scope_with_var id tyv)` >>
  qabbrev_tac `clean =
    finally (try (do eval_stmts cx body; return F od) handle_loop_exception) pop_scope` >>
  `bind head (\u:unit. clean) =
    (do v <- read_result cx a; push_scope_with_var id tyv v; clean od)` by
    simp[NoAsms, Abbr `head`, vyperStateTheory.bind_assoc, vyperStateTheory.ignore_bind_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule gas_outcome_full_bind >> BETA_TAC >>
  conj_tac
  >- (gen_tac >> simp[NoAsms, Abbr `clean`] >>
      irule storage_trace_frame_finally >> simp[NoAsms, storage_trace_frame_pop_scope] >>
      irule storage_trace_frame_try >> simp[NoAsms, storage_trace_frame_loop_handler] >>
      irule storage_trace_frame_ignore_bind >>
      simp[NoAsms, storage_trace_frame_return,
           CONJUNCT1 (CONJUNCT2 evaluate_storage_trace_frame)]) >>
  conj_tac
  >- (qx_gen_tac `left` >> qx_gen_tac `value` >>
      qx_gen_tac `mid` >> qx_gen_tac `t_mid` >> rpt strip_tac >>
      irule gas_exempt_cert_bind_unit >>
      qexistsl [`mid`,`t_mid`,`value`] >> BETA_TAC >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_unit >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (simp[NoAsms, Abbr `head`] >> irule storage_trace_frame_bind_all >>
      simp[NoAsms, storage_trace_frame_read_result, storage_trace_frame_state_updates]) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gentry`,`ep`,`INL ()`,`t`,`tt`] >>
  conj_tac
  >- (qunabbrev_tac `head` >> qpat_assum `a = Value _` SUBST1_TAC >>
      simp[NoAsms, Abbr `ep`, vyperStateTheory.bind_def,
           vyperStateTheory.read_result_def, vyperStateTheory.return_def,
           vyperStateTheory.push_scope_with_var_def, evaluation_state_component_equality]) >>
  qx_gen_tac `H` >> strip_tac >> BETA_TAC >> conj_tac
  >- (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gentry,tt) /\ _`
      (qspec_then `H` mp_tac) >>
      (impl_tac >- (qpat_assum `ep.storage_trace = es.storage_trace`
                    (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC)) >>
      strip_tac >> first_assum ACCEPT_TAC) >>
  `ep with gas_obs := [] = ep` by simp[NoAsms, Abbr `ep`] >>
  pop_assum SUBST1_TAC >> qexists_tac `()` >>
  conj_tac >- REFL_TAC >>
  qpat_assum `Done = _` (fn done_eq =>
    qpat_assum `Inv = _` (fn inv_eq =>
      qpat_assum `R = _` (fn exit_eq =>
        let
          fun apply_geometry [] equations =
                asm "clean_outcome"
                  (ACCEPT_TAC o PURE_REWRITE_RULE equations o
                   BETA_RULE o PURE_REWRITE_RULE [done_eq, inv_eq, exit_eq])
            | apply_geometry (pat :: rest) equations =
                qpat_assum pat (fn th => apply_geometry rest (th :: equations))
        in
          apply_geometry
            [`cenv' = cenv`, `N = Num (n2 - n1)`,
             `cond_lbl = fresh_label_output _ _`, `ainst = mk_inst _ ALLOCA _ _`,
             `p = STRING _ _`, `cv = STRING _ _`, `sz = type_memory_bytes cenv typ`]
            []
        end)))
QED

Finalise range_full_round

val _ = Parse.hide "body";

(* The computed-range guard compares the declared bound to a word literal. *)
Theorem range_full_computed_bound[local]:
  type_stmt env ret_ty (For id typ (Range e1 e2) n body) = SOME env' /\
  ~(?a1 m1 a2 m2.
      e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2)) ==>
  n < dimword (:256)
Proof
  strip_tac >>
  drule (SIMP_RULE std_ss [pairTheory.FORALL_PROD]
    (CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX))) body_range_typing)) >>
  impl_tac >- metis_tac[] >>
  strip_tac >>
  `dimword (:256) = 2 ** 256` by
    simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  pop_assum SUBST1_TAC >>
  Cases_on `typ` >> gvs[] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_formed_type_def, vyperValueTheory.evaluate_type_def, AllCaseEqs(),
      well_typed_literal_def, vyperValueTheory.within_int_bound_def, LET_THM] >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
  goal_assum (drule_at (Pat `n < _`)) >>
  pure_once_rewrite_tac [GSYM (EVAL ``(2:num) ** 256``)] >>
  irule bitTheory.TWOEXP_MONO2 >> decide_tac
QED

Theorem compile_for_range_frag_full:
!cx id typ e1 e2 n body DF lo d PG tops bindings ctx shadow_ctx func
 shadow_func cenv env env' ret_ty lctx RetQ es.
 (
  (!func0 ctx0 c0 e0 sa0 s0 G0 tn0 c1 e1 sa1 s1 G1 tn1 c2 e2 s2 G2 tn2.
    (alloca_history func0 s1 /\
     (ctx_has_dalloca ctx0 ==> allocas_below_fmp s1) /\
     s0.vs_alloca_next <= s1.vs_alloca_next /\
     (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
            lookup_var x s1 = SOME w) /\
     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
              FLOOKUP s1.vs_allocas aid = SOME b) /\
     (!x. not_fresh_at sa0 x ==>
          FLOOKUP G1 x = FLOOKUP G0 x /\
          op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
     alloca_frame c0 e0 sa0 s0 c1 e1 s1 /\
     (!aid off sz i.
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
       aid < sa0.cs_next_id /\
       (!nm b sz'. local_region c0 e0.scopes s0 nm b sz' ==>
                   off + sz <= b \/ b + sz' <= off) /\
       off <= i /\ i < off + sz /\ i IN tn1.t_mem ==> i IN tn0.t_mem)) /\
    (alloca_history func0 s2 /\
     (ctx_has_dalloca ctx0 ==> allocas_below_fmp s2) /\
     s1.vs_alloca_next <= s2.vs_alloca_next /\
     (!x w. not_fresh_at sa1 x /\ lookup_var x s1 = SOME w ==>
            lookup_var x s2 = SOME w) /\
     (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
              FLOOKUP s2.vs_allocas aid = SOME b) /\
     (!x. not_fresh_at sa1 x ==>
          FLOOKUP G2 x = FLOOKUP G1 x /\
          op_taint tn2 (Var x) = op_taint tn1 (Var x)) /\
     alloca_frame c1 e1 sa1 s1 c2 e2 s2 /\
     (!aid off sz i.
       FLOOKUP s1.vs_allocas aid = SOME (off,sz) /\
       aid < sa1.cs_next_id /\
       (!nm b sz'. local_region c1 e1.scopes s1 nm b sz' ==>
                   off + sz <= b \/ b + sz' <= off) /\
       off <= i /\ i < off + sz /\ i IN tn2.t_mem ==> i IN tn1.t_mem)) /\
    sa0.cs_next_id <= sa1.cs_next_id /\
    (!x. not_fresh_at sa0 x ==> not_fresh_at sa1 x) ==>
    alloca_history func0 s2 /\
    (ctx_has_dalloca ctx0 ==> allocas_below_fmp s2) /\
    s0.vs_alloca_next <= s2.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s2 = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s2.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa0 x ==>
         FLOOKUP G2 x = FLOOKUP G0 x /\
         op_taint tn2 (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame c0 e0 sa0 s0 c2 e2 s2 /\
    (!aid off sz i.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sa0.cs_next_id /\
      (!nm b sz'. local_region c0 e0.scopes s0 nm b sz' ==>
                  off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tn2.t_mem ==> i IN tn0.t_mem)) /\
  (!func0 ctx0 c0 e0 sa0 s0 G0 tn0 c ee t G tn cenv0 sc rest.
    (alloca_history func0 t /\
     (ctx_has_dalloca ctx0 ==> allocas_below_fmp t) /\
     s0.vs_alloca_next <= t.vs_alloca_next /\
     (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
            lookup_var x t = SOME w) /\
     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
              FLOOKUP t.vs_allocas aid = SOME b) /\
     (!x. not_fresh_at sa0 x ==>
          FLOOKUP G x = FLOOKUP G0 x /\
          op_taint tn (Var x) = op_taint tn0 (Var x)) /\
     alloca_frame c0 e0 sa0 s0 c ee t /\
     (!aid off sz i.
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
       aid < sa0.cs_next_id /\
       (!nm b sz'. local_region c0 e0.scopes s0 nm b sz' ==>
                   off + sz <= b \/ b + sz' <= off) /\
       off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) /\
    cenv_top_ext cenv0 c ee.scopes /\ ee.scopes = sc :: rest /\
    (!nm. nm IN FDOM sc ==> lookup_scopes nm rest = NONE) ==>
    alloca_history func0 t /\
    (ctx_has_dalloca ctx0 ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa0 x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame c0 e0 sa0 s0 cenv0 (ee with scopes := rest) t /\
    (!aid off sz i.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sa0.cs_next_id /\
      (!nm b sz'. local_region c0 e0.scopes s0 nm b sz' ==>
                  off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) /\
  (!DF0 lo0 d0 ctx0 func0 PG0 tops0 cx0 st0 body0 es0 s G tn Q R.
    es0.scopes <> [] /\
    gas_outcome_full (DF0,lo0,d0,ctx0,func0,PG0) tops0 cx0 st0
      (eval_stmts cx0 body0) (es0,s,G,tn) Q R ==>
    gas_outcome_full (DF0,lo0,d0,ctx0,func0,PG0) tops0 cx0 st0
      (finally (try (do eval_stmts cx0 body0; return F od)
         handle_loop_exception) pop_scope) (es0,s,G,tn)
      (\H res' ee G tn t. ?res sc.
        res' = (case res of INL u => INL F | INR ex =>
          if ex = BreakException then INL T else
          if ex = ContinueException then INL F else INR ex) /\
        Q H res (ee with scopes := sc::ee.scopes) G tn t)
      (\H res' ee gt r. ?res sc.
        res' = (case res of INL u => INL F | INR ex =>
          if ex = BreakException then INL T else
          if ex = ContinueException then INL F else INR ex) /\
        R H res (ee with scopes := sc::ee.scopes) gt r)) /\
  (!RetQ0 H cx0 ee (res:unit+exception) gt r ctx0 sc g.
    ((!tail. stmt_exit_ptr (RetQ0 H) (ee with gas_obs:=tail) res gt r) /\
     halt_exit H cx0 ee res r /\
     (ctx_has_dalloca ctx0 ==> !s.
       (r=Halt s \/ ?ir. r=IntRet ir s) ==> allocas_below_fmp s)) ==>
    ((!tail. stmt_exit_ptr (RetQ0 H)
       ((ee with <|scopes:=sc;gas_obs:=g|>) with gas_obs:=tail) res gt r) /\
     halt_exit H cx0 (ee with <|scopes:=sc;gas_obs:=g|>) res r /\
     (ctx_has_dalloca ctx0 ==> !s.
       (r=Halt s \/ ?ir. r=IntRet ir s) ==> allocas_below_fmp s))) /\
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
      (INL tyv,t) /\ eval_iterator cx (Range e1 e2) s'3' = (INL vs,t') /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
      (INL x,t'') ==> body_for_full_ok cx tyv id body vs) /\
  (!tenv s'' tyv t.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
      (INL tyv,t) ==> body_iterator_full_ok cx (Range e1 e2)) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Range e1 e2) n body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Range e1 e2) n body) ==>
      occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ (Range e1 e2) n body) = SOME env' /\
  stmt_exprs_ok cenv (For id typ (Range e1 e2) n body) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Range e1 e2) n body)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty
 ) ==>
 stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
   cx lctx RetQ cenv
   (stmt_env cenv lctx ret_ty (For id typ (Range e1 e2) n body))
   (stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (For id typ (Range e1 e2) n body)))
   (eval_stmt cx (For id typ (Range e1 e2) n body)) es
Proof
  rpt gen_tac >>
  disch_then (fn th =>
    let val clauses = CONJUNCTS th in
      EVERY (map assume_tac clauses) >> mk_asm "frame_comp" (hd clauses)
    end) >>
  pure_once_rewrite_tac [bodySimFullTheory.stmt_frag_full_def] >>
  rpt gen_tac >> strip_tac >>
  `cenv' = cenv` by (metis_tac[range_full_outer_env]) >>
  pop_assum SUBST_ALL_TAC >>
  drule_all range_full_static_pre >> strip_tac >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    (drule_then assume_tac exprSimAbiDecodeEntryTypingTheory.abi_decode_inv_type_env >>
     drule assignable_type_well_formed >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x` by
    (rpt strip_tac >>
     qpat_assum `ret_pc_ok cenv sa s0`
       (drule_then (ACCEPT_TAC o CONJUNCT1) o REWRITE_RULE [ret_pc_ok_def])) >>
  mp_tac range_full_round >>
  impl_tac
  >- (conj_tac >- ACCEPT_TAC range_full_body_entry >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then
    [`cx`, `id`, `typ`, `e1`, `e2`, `n`, `body`, `DF`, `lo`, `d`, `PG`, `tops`,
     `bindings`, `ctx`, `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `env'`,
     `ret_ty`, `lctx`, `RetQ`, `tyv`, `sa`, `sb`, `shadow_sa`, `shadow_sb`]
    (mp_tac o BETA_RULE o PURE_ONCE_REWRITE_RULE [LET_THM])) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then
      [`st`, `bc`, `body_cenv`, `body_env'`, `sb0`, `sb1`, `shadow_sb0`, `shadow_sb1`,
       `p`, `sz`, `ainst`, `cv`, `ev`, `dv`, `nv`, `entry_lbl`, `cond_lbl`, `exit_lbl`,
       `body_lbl`, `incr_lbl`, `j1`, `j2`, `j3`, `bbb`, `i1`, `i2`, `i3`, `sj`,
       `op1`, `s1`, `op2`, `rv`, `g1`, `z1`, `g2`, `z2`]
      (fn pkg =>
        let val clauses = CONJUNCTS pkg in
          EVERY (map assume_tac (Lib.butlast clauses)) >>
          mk_asm "round_cons" (List.last clauses)
        end) o BETA_RULE o PURE_REWRITE_RULE [LET_THM]) >>
  Q_TAC ASM_CASES_TAC `?a1 m1 a2 m2. e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2)`
  >- suspend "literal" >>
  qpat_x_assum `~(?a1 m1 a2 m2. e1 = _ /\ e2 = _) ==> _`
    (fn th => drule_then strip_assume_tac th) >>
  suspend "checked"
QED

Resume compile_for_range_frag_full[checked]:
  let
    fun shadow_edge expr start shadowStart related leftEq shadowRun rightEq out mid =
      namedCases_on shadowRun [out ^ " " ^ mid] >>
      qpat_assum related (fn rel =>
        qpat_assum leftEq (fn left =>
          qpat_assum rightEq (fn right =>
            qspecl_then [start,shadowStart]
              (strip_assume_tac o SRULE [rel,left,right])
              (REWRITE_RULE [gas_shadow_compiles_def]
                (Q.INST [`ty` |-> `typ`, `e` |-> expr, `sd` |-> `T`]
                  gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env)))))
  in
    shadow_edge `e1` `sa` `shadow_sa` `gas_shadow_state sa shadow_sa`
      `lower_value compile_expr cenv typ e1 sa = _`
      `lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e1) shadow_sa`
      `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _`
      "shadow_op1" "shadow_s1" >>
    qpat_x_assum `op1 = shadow_op1` (SUBST_ALL_TAC o SYM) >>
    shadow_edge `e2` `s1` `shadow_s1` `gas_shadow_state s1 shadow_s1`
      `lower_value compile_expr cenv typ e2 s1 = _`
      `lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e2) shadow_s1`
      `lower_value _ _ _ (gas_shadow_expr e2) shadow_s1 = _`
      "shadow_op2" "shadow_st" >>
    qpat_x_assum `op2 = shadow_op2` (SUBST_ALL_TAC o SYM)
  end >>
  let
    fun grows eq = qpat_assum eq
      (mp_then Any strip_assume_tac (cj 2 compile_expr_grows))
  in
    grows `lower_value _ _ _ e1 sa = (op1,s1)` >>
    grows `lower_value _ _ _ e2 s1 = (op2,st)` >>
    grows `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = (op1,shadow_s1)` >>
    grows `lower_value _ _ _ (gas_shadow_expr e2) shadow_s1 = (op2,shadow_st)`
  end >>
  `cs_extends shadow_sa shadow_st` by
    (irule cs_extends_trans >> qexists_tac `shadow_s1` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!e a m. gas_shadow_expr e = Literal a (IntL m) ==> e = Literal a (IntL m)` by
    (Cases >> simp[NoAsms, gas_shadow_expr_def]) >>
  `~(?a1 m1 a2 m2. gas_shadow_expr e1 = Literal a1 (IntL m1) /\
                     gas_shadow_expr e2 = Literal a2 (IntL m2))` by
    (strip_tac >> qpat_x_assum `~(?a1 m1 a2 m2. e1 = _ /\ e2 = _)` mp_tac >>
     simp[NoAsms] >> qexistsl_tac [`a1`,`m1`,`a2`,`m2`] >>
     conj_tac >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `for_range_checked_code (gas_shadow_env T cenv) lctx ret_ty id typ n (MAP gas_shadow_stmt body)
      op1 op2 shadow_st = ((),shadow_sb)` by
    (qpat_assum `compile_stmt _ _ _ _ shadow_sa = ((),shadow_sb)` (SUBST1_TAC o SYM) >>
     sym_tac >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _`
       (mp_then Any irule compile_stmt_for_range_checked) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `cenv.ce_alloca_locals` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (ACCEPT_TAC o MATCH_MP contract_inv_alloca_locals o MATCH_MP body_inv_contract)) >>
  `!c lc s t. compile_stmts c lc ret_ty (MAP gas_shadow_stmt body) s = ((),t) ==>
               cs_extends s t` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (cj 2 stmtLoweringMonoTheory.compile_stmt_cs_mono) >>
     simp[NoAsms, cs_mono_def] >> disch_then drule >> simp[]) >>
  `cs_extends shadow_st shadow_sb` by
    (qpat_assum `for_range_checked_code _ _ _ _ _ _ _ _ _ shadow_st = _`
       (mp_then Any (qspecl_then [`shadow_sa`,`shadow_func`] mp_tac)
          for_range_checked_parts) >>
     impl_tac
     >- (conj_tac >- simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  let
    fun split a b c fnm = qspecl_then [a,b,c,fnm] mp_tac fn_has_code_split >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac
  in
    split `sa` `st` `sb` `func` >>
    split `sa` `s1` `st` `func` >>
    split `shadow_sa` `shadow_st` `shadow_sb` `shadow_func` >>
    split `shadow_sa` `shadow_s1` `shadow_st` `shadow_func`
  end >>
  `supported_pure_expr tops e1 /\ supported_pure_expr tops e2` by
    (qpat_assum `supported_iterator _ _ _ _` mp_tac >>
     qpat_assum `~(?a1 m1 a2 m2. e1 = _ /\ e2 = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[supported_iterator_def, AllCaseEqs()] >>
     Cases_on `e1` >> simp[] >> Cases_on `e2` >> simp[] >>
     simp[supportedExprsTheory.supported_pure_expr_def]) >>
  `cx_tops cx = tops` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (ACCEPT_TAC o cj 2 o MATCH_MP body_inv_main_code)) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
            is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)` by
    (qpat_assum `cx_tops cx = tops` (rewrite_tac o single) >>
     gen_tac >> disch_tac >>
     qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `is_dynamic (vyper_to_abi_type (get_tenv cx) target)`
         (fn abi => ACCEPT_TAC
           (MATCH_MP body_inv_singleton_abi_types (CONJ inv abi))))) >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (ACCEPT_TAC o MATCH_MP body_inv_main_support)) >>
  let
    fun ready e =
      sg ([QUOTE "!ee. expr_sim_inv cenv cx env ee ==> expr_body_pre cenv cx env "] @
          e @ [QUOTE " ee"]) >-
      (qx_gen_tac `ee` >> strip_tac >>
       sg ([QUOTE "supported_expr tops "] @ e) >-
         simp[supportedExprsTheory.supported_expr_def] >>
       drule_all_then strip_assume_tac
         bodySingletonCallSupportTheory.supported_singleton_expr_body_calls >>
       sg ([QUOTE "~supported_expr_exists (const_name_root cx) "] @ e) >-
         (drule_all body_inv_stmt_const_name_free >>
          simp[supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
               supportedStmtTraverseTheory.supported_iterator_exists_def]) >>
       sg ([QUOTE "~is_extcode "] @ e) >-
         (qpat_assum ([QUOTE "alloc_limits_expr cenv "] @ e)
           (mp_then Any ACCEPT_TAC allocLimitsPropsTheory.alloc_limits_expr_not_extcode)) >>
       qspecl_then [`cenv`,`cx`,`env`,e,`ee`,`[]`] mp_tac stmt_expr_body_pre_alloc >>
       impl_tac >- (simp[] >> strip_tac >> qexists_tac `tops` >> simp[]) >>
       disch_then ACCEPT_TAC)
  in
    ready `e1` >> ready `e2`
  end >>
  qpat_assum `!tenv s'' tyv t. _ ==> body_iterator_full_ok _ _`
    (qspecl_then [`get_tenv cx`,`es`,`tyv`,`es`] mp_tac) >>
  impl_tac >- simp[lift_option_type_def, return_def] >>
  pure_once_rewrite_tac [body_iterator_full_ok_def] >> strip_tac >>
  `expr_body_pre cenv cx env e1 es` by
    (qpat_assum `!ee. _ ==> expr_body_pre _ _ _ e1 ee`
      (qspec_then `es` mp_tac) >> simp[]) >>
  qpat_assum `body_expr_full_ok cx e1`
    (mp_tac o CONJUNCT1 o PURE_ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
  disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
      `func`,`shadow_func`,`cenv`,`env`,`typ`,`es`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o CONJUNCT1 o BETA_RULE) >>
  pure_once_rewrite_tac [bodySimFullTheory.expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`shadow_s1`,
      `op1`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC,
           irule exprSimSourceTheory.expr_body_pre_gas_admissible >>
           goal_assum (drule_at Any)]) >>
  disch_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (fn inv => qpat_assum `MEM func ctx.ctx_functions`
         (fn member => ACCEPT_TAC
           (MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi (CONJ inv member))))) >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full cfg tops' cx st0 (bind (eval_expr cx e1) _) (es,s0,G0,tn0) Q0 R0` >>
  `gas_outcome_full cfg tops' cx st0 (bind (eval_expr cx e1) (read_result cx))
     (es,s0,G0,tn0) (\H res ee G tn t. Q0 H res ee G tn t /\
       (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z)) R0` by
    (unabbrev_all_tac >> irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx e1) _) _ _ _`
       (irule_at Any) >> simp[NoAsms] >> rpt strip_tac >>
     drule_all bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >>
     simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx e1) _) _ Q0 R0` kall_tac >>
  unabbrev_all_tac >>
  suspend "join_endpoints"
QED

Resume compile_for_range_frag_full[join_endpoints]:
  irule (BETA_RULE (Q.INST [
    `tyv` |-> `tyv`,
    `P1` |-> `\H v ee G tn t.
      expr_post H ctx func cenv cx e1 es sa s1 s0 ee v op1 t /\
      expr_store_bound cx (post_value_type cenv e1) v op1 t /\
      t.vs_current_bb = s1.cs_current_bb /\
      t.vs_inst_idx = LENGTH s1.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv e1) v op1 G tn t /\
      (~is_word_type (post_value_type cenv e1) ==> ptr_buf_ok cenv e1 op1 G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      ee.gas_obs = [] /\ ~t.vs_halted /\
      (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z) /\
      (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) t)`,
    `P2` |-> `\(v1:value) mid1 G1 tn1 t1 H v ee G tn t.
      expr_post H ctx func cenv cx e2 mid1 s1 st t1 ee v op2 t /\
      expr_store_bound cx (post_value_type cenv e2) v op2 t /\
      t.vs_current_bb = st.cs_current_bb /\
      t.vs_inst_idx = LENGTH st.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      t1.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv e2) v op2 G tn t /\
      (~is_word_type (post_value_type cenv e2) ==> ptr_buf_ok cenv e2 op2 G t) /\
      ghost_kept_at lo cenv mid1 s1 G1 tn1 t1 G tn /\
      ee.gas_obs = [] /\ ~t.vs_halted /\
      (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z) /\
      (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) t)`]
      (SPEC_ALL range_full_endpoints))) >>
  map_every qexists_tac [`G0`,`cenv`,`d`,`op1`,`op2`,`s0`,`s1`,`sa`,`st`,`tn0`,`tyv`] >>
  BETA_TAC >>
  conj_tac >- suspend "first_success" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "first_exit"
QED

Resume compile_for_range_frag_full[first_exit]:
  drule_all_then (assume_tac o BETA_RULE)
    (Q.INST [`d` |-> `d`, `cenv` |-> `cenv`, `sa` |-> `sa`]
       bodyFullSharedTheory.gas_outcome_full_return_buf_allocas) >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx e1) _) _ _ _`
    (irule_at Any) >>
  BETA_TAC >> conj_tac >- (rpt strip_tac >> qexists_tac `v` >> simp[] >> first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`H`,`res`,`ee`,`gt`,`r`] >> strip_tac >>
  namedCases_on `res` ["v", "ex"]
  >- (qpat_assum `expr_exit (INL _) _` mp_tac >> simp[NoAsms,exprSimDefsTheory.expr_exit_INL]) >>
  simp[NoAsms,stmt_exit_ptr_def] >> conj_tac
  >- (gen_tac >> disj1_tac >>
      irule (iffLR (SPEC_ALL (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``]
        stmtSimPropsTheory.expr_exit_INR_type))) >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule (iffLR (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``]
        haltExitProjTheory.halt_exit_INR_type)) >> first_assum ACCEPT_TAC) >>
  disch_tac >> gen_tac >> strip_tac
  >- (qpat_assum `ctx_has_dalloca ctx ==> !s. r = Halt s ==> _` mp_tac >> simp[]) >>
  qpat_assum `expr_exit (INR ex) r` mp_tac >>
  qpat_assum `r = IntRet _ _` SUBST1_TAC >>
  Cases_on `ex` >> simp[NoAsms,exprSimDefsTheory.expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) _ ==> _` >> Cases_on `err` >>
  simp[NoAsms,exprSimDefsTheory.expr_exit_def]
QED

Resume compile_for_range_frag_full[first_success]:
  map_every qx_gen_tac [`marks1`,`v1`,`mid1`,`G1`,`tn1`,`t1`] >> strip_tac >>
  `!fn inst z. frag_reachable ctx func t1 fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid1.storage_trace` mp_tac) >>
     impl_tac >- (qpat_assum `storage_trace_domain cx st0 mid1.storage_trace`
       (ACCEPT_TAC o PURE_ONCE_REWRITE_RULE [storage_trace_domain_def])) >>
     disch_then strip_assume_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!tail. bind (eval_expr cx e1) (read_result cx) _ = (INL v1,mid1 with gas_obs := tail)`
    (qspec_then `[]` (mk_asm "read1")) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid1` by
    (`well_typed_expr env e1` by
       qpat_assum `expr_body_pre cenv cx env e1 es`
         (ACCEPT_TAC o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
     `body_const_cells_agree [(NONE,tops)] cx env (mid1 with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     asm "read1" (irule_at Any) >> simp[]) >>
  `expr_sim_inv cenv cx env mid1 /\ expr_result_typed env e1 (Value v1)` by
    (asm "read1" (mp_then Any mp_tac
       (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval)) >>
     disch_then (qspecl_then [`cenv`,`env`] mp_tac) >>
     impl_tac >- simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
     simp[NoAsms, exprSimHypsDefsTheory.expr_sim_inv_gas_obs]) >>
  `body_expr_full_ok cx e2` by
    (qpat_assum `(?s tv t s1 v t1. eval_expr cx e1 s = _ /\ _) ==> _` irule >>
     asm "read1" (mp_then Any mp_tac vyperStatePreservationTheory.bind_split) >>
     simp[NoAsms] >> disch_then (qx_choosel_then [`tv`,`src1`] strip_assume_tac) >>
     qexistsl_tac [`es with gas_obs := gas_explicit marks1 s0.vs_gas_readings`,
       `tv`,`src1`,`src1`,`v1`,`mid1 with gas_obs := []`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `expr_body_pre cenv cx env e2 mid1` by
    (qpat_assum `!ee. _ ==> expr_body_pre _ _ _ e2 ee`
       (qspec_then `mid1` mp_tac) >> simp[]) >>
  `return_buf_frame d cenv s1 t1 /\
   (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) t1)` by
    (qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid1.storage_trace` mp_tac) >>
     impl_tac >- simp[GSYM storage_trace_domain_def] >>
     disch_then (strip_assume_tac o PURE_ONCE_REWRITE_RULE [expr_post_def]) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC]) >>
  qpat_assum `body_expr_full_ok cx e2`
    (mp_tac o CONJUNCT1 o PURE_ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
  disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
      `func`,`shadow_func`,`cenv`,`env`,`typ`,`mid1`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o CONJUNCT1 o BETA_RULE) >>
  pure_once_rewrite_tac [bodySimFullTheory.expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`s1`,`st`,`shadow_s1`,`shadow_st`,
      `op2`,`t1`,`G1`,`tn1`] mp_tac) >>
  impl_tac >- suspend "second_entry" >>
  disch_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full cfg tops' cx st0 (bind (eval_expr cx e2) _) (mid1,t1,G1,tn1) Q0 R0` >>
  `gas_outcome_full cfg tops' cx st0 (bind (eval_expr cx e2) (read_result cx))
     (mid1,t1,G1,tn1) (\H res ee G tn t. Q0 H res ee G tn t /\
       (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z)) R0` by
    (unabbrev_all_tac >> irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx e2) _) _ _ _`
       (irule_at Any) >> simp[NoAsms] >> rpt strip_tac >>
     drule_all bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >>
     simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx e2) _) _ Q0 R0` kall_tac >>
  unabbrev_all_tac >>
  conj_tac >- suspend "second_exit" >>
  suspend "second_success"
QED

Resume compile_for_range_frag_full[second_entry]:
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid1.storage_trace` mp_tac) >>
  impl_tac >- (qpat_assum `storage_trace_domain cx st0 mid1.storage_trace`
      (ACCEPT_TAC o PURE_ONCE_REWRITE_RULE [storage_trace_domain_def])) >> strip_tac >>
  qpat_assum `expr_post _ _ _ _ _ e1 es sa s1 s0 mid1 v1 op1 t1`
    (assume_tac o cj 6 o PURE_ONCE_REWRITE_RULE [expr_post_def]) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[],
    gen_tac >> gen_tac >> disch_tac >> irule not_fresh_at_mono >>
      qexists_tac `sa` >> simp[],
    irule exprSimSourceTheory.expr_body_pre_gas_admissible >>
      goal_assum (drule_at Any),
    qx_gen_tac `H` >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
    disch_then (strip_assume_tac o PURE_ONCE_REWRITE_RULE [expr_post_def]) >>
    rpt conj_tac >> first_assum ACCEPT_TAC]
QED

Resume compile_for_range_frag_full[second_exit]:
  drule_all_then (assume_tac o BETA_RULE)
    (Q.INST [`d` |-> `d`, `cenv` |-> `cenv`, `sa` |-> `s1`]
       bodyFullSharedTheory.gas_outcome_full_return_buf_allocas_from) >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx e2) _) _ _ _`
    (irule_at Any) >>
  BETA_TAC >> conj_tac >- (rpt strip_tac >> qexists_tac `v` >> simp[] >> first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`H`,`res`,`ee`,`gt`,`r`] >> strip_tac >>
  namedCases_on `res` ["v", "ex"]
  >- (qpat_assum `expr_exit (INL _) _` mp_tac >> simp[NoAsms,exprSimDefsTheory.expr_exit_INL]) >>
  qexists_tac `ex` >> simp[NoAsms,stmt_exit_ptr_def] >> conj_tac
  >- (gen_tac >> disj1_tac >>
      irule (iffLR (SPEC_ALL (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``]
        stmtSimPropsTheory.expr_exit_INR_type))) >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule (iffLR (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``]
        haltExitProjTheory.halt_exit_INR_type)) >> first_assum ACCEPT_TAC) >>
  disch_tac >> gen_tac >> strip_tac
  >- (qpat_assum `ctx_has_dalloca ctx ==> !s. r = Halt s ==> _` mp_tac >> simp[]) >>
  qpat_assum `expr_exit (INR ex) r` mp_tac >>
  qpat_assum `r = IntRet _ _` SUBST1_TAC >>
  Cases_on `ex` >> simp[NoAsms,exprSimDefsTheory.expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) _ ==> _` >> Cases_on `err` >>
  simp[NoAsms,exprSimDefsTheory.expr_exit_def]
QED

Resume compile_for_range_frag_full[second_success]:
  map_every qx_gen_tac [`marks2`,`v2`,`mid2`,`G2`,`tn2`,`t2`] >> strip_tac >>
  qpat_assum `!tail. bind (eval_expr cx e2) (read_result cx) _ = (INL v2,mid2 with gas_obs := tail)`
    (qspec_then `[]` (mk_asm "read2")) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid2` by
    (`well_typed_expr env e2` by
       qpat_assum `expr_body_pre cenv cx env e2 mid1`
         (ACCEPT_TAC o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
     `body_const_cells_agree [(NONE,tops)] cx env (mid2 with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     asm "read2" (irule_at Any) >> simp[]) >>
  `expr_sim_inv cenv cx env mid2 /\ expr_result_typed env e2 (Value v2)` by
    (asm "read2" (mp_then Any mp_tac
       (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval)) >>
     disch_then (qspecl_then [`cenv`,`env`] mp_tac) >>
     impl_tac >- simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
     simp[NoAsms, exprSimHypsDefsTheory.expr_sim_inv_gas_obs]) >>
  let
    val endpoint = SRULE [SF ETA_ss] (SIMP_RULE std_ss [pairTheory.FORALL_PROD]
      (CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX))) body_range_endpoint_read))
    fun read pre start value finish label num =
      sg pre >- simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
      qpat_x_assum pre (mp_then Any mp_tac endpoint) >>
      disch_then (qspecl_then [`tyv`,value,finish] mp_tac) >>
      impl_tac >- asm label (fn th => simp[SRULE [SF ETA_ss] th]) >>
      disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then num strip_assume_tac))
  in
    read `expr_body_pre cenv cx env e1 (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings)`
      `es` `v1` `mid1 with gas_obs := []` "read1" `n1` >>
    read `expr_body_pre cenv cx env e2 (mid1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings)`
      `mid1` `v2` `mid2 with gas_obs := []` "read2" `n2`
  end >>
  let
    fun project post domain horizon =
      qpat_assum post (qspec_then horizon mp_tac) >>
      impl_tac >- (qpat_assum domain
        (ACCEPT_TAC o PURE_ONCE_REWRITE_RULE [storage_trace_domain_def])) >>
      disch_then (strip_assume_tac o
        PURE_ONCE_REWRITE_RULE [expr_post_def,ghost_kept_at_def])
  in
    project `!H. valid_horizon _ _ H mid1.storage_trace ==> expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
      `storage_trace_domain cx st0 mid1.storage_trace` `storage_trace_horizon mid1.storage_trace` >>
    project `!H. valid_horizon _ _ H mid2.storage_trace ==> expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _ /\ _`
      `storage_trace_domain cx st0 mid2.storage_trace` `storage_trace_horizon mid2.storage_trace`
  end >>
  `storage_trace_domain cx st0 es.storage_trace` by
    (asm "read1" (mp_then Any mp_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
       storage_trace_frame_prefix)) >>
     impl_tac >- simp[storage_trace_frame_bind_all,storage_trace_frame_read_result,
                      cj 5 evaluate_storage_trace_frame] >>
     simp[NoAsms] >> disch_then (qx_choose_then `obs` assume_tac) >>
     irule storage_trace_domain_prefix >> qexists_tac `obs` >>
     qpat_assum `mid1.storage_trace = _` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ es s0 /\ _`
    (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
  impl_tac >- (qpat_assum `storage_trace_domain cx st0 es.storage_trace`
    (ACCEPT_TAC o PURE_ONCE_REWRITE_RULE [storage_trace_domain_def])) >> strip_tac >>
  asm "read1" (mp_then Any mp_tac eval_read_preserves_scopes_dom) >>
  asm "read2" (mp_then Any mp_tac eval_read_preserves_scopes_dom) >>
  simp[NoAsms] >> rpt (disch_then assume_tac) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv mid1 t1` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qexistsl_tac [`storage_trace_horizon es.storage_trace`,`ctx`,`cx`,`func`] >>
       first_assum ACCEPT_TAC]) >>
  `alloca_frame cenv mid1 s1 t1 cenv mid2 t2` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qexistsl_tac [`storage_trace_horizon mid1.storage_trace`,`ctx`,`cx`,`func`] >>
       first_assum ACCEPT_TAC]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s1 x` by
    (gen_tac >> disch_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  asm "frame_comp" (fn comp =>
    qpat_assum `alloca_frame cenv es sa s0 cenv mid1 t1`
      (mp_then (Pat `alloca_frame _ _ _ _ _ _ _`) (mk_asm "frame_comp_1") comp)) >>
  asm "frame_comp_1" (fn comp =>
    qpat_assum `alloca_frame cenv mid1 s1 t1 cenv mid2 t2`
      (mp_then (Pat `alloca_frame _ _ _ _ _ _ _`) mp_tac comp)) >>
  (* The abstract map range of the conditional frame is fixed by its
     hypothesis. Compose the real provenance equalities separately. *)
  disch_then (mp_tac o Q.SPECL
    [`func`,`ctx`,`FEMPTY`,`tn0`,`FEMPTY`,`tn1`,`FEMPTY`,`tn2`]) >>
  (impl_tac >- (asm_rewrite_tac [] >>
    rpt conj_tac >> qx_gen_tac `x` >> disch_tac >>
    first_assum (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
  strip_tac >>
  `!x. not_fresh_at sa x ==>
    FLOOKUP G2 x = FLOOKUP G0 x /\ op_taint tn2 (Var x) = op_taint tn0 (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at s1 x`
       (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP G1 x = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at s1 x ==> FLOOKUP G2 x = _ /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac []) >>
  `is_word_type typ` by
    (qpat_assum `is_int_type typ` mp_tac >> Cases_on `typ` >> simp[NoAsms] >>
     rename1 `is_int_type (BaseT bt) ==> _` >> Cases_on `bt` >>
     simp[NoAsms,is_word_type_def]) >>
  let
    fun word goal rel = sg goal >-
      (qpat_assum rel
         (qx_choose_then `we` (CONJUNCTS_THEN2 assume_tac (qspec_then `tyv` mp_tac)) o
          PURE_ONCE_REWRITE_RULE [expr_val_rel_def]) >>
       simp[post_value_type_word, exprSimPropsTheory.typed_val_to_w256_word_value,
            word_value_def, val_to_w256_def])
  in
    word `eval_operand op1 t1 = SOME (i2w n1)` `expr_val_rel _ _ _ op1 t1` >>
    word `eval_operand op2 t2 = SOME (i2w n2)` `expr_val_rel _ _ _ op2 t2`
  end >>
  qpat_assum `lower_value _ _ _ e1 sa = (op1,s1)`
    (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
  disch_then (qspecl_then [`cx`,`env`,`es`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_assum `lower_value _ _ _ e2 s1 = (op2,st)`
    (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
  disch_then (qspecl_then [`cx`,`env`,`mid1`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `eval_operand op1 t2 = SOME (i2w n1)` by
    (MATCH_MP_TAC (Q.SPECL [`op1`,`s1`,`t1`,`t2`,`i2w n1`]
       exprBopSimPropsTheory.eval_operand_frame) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `is_word_type (post_value_type cenv e1)` by simp[post_value_type_word] >>
  qpat_assum `is_word_type (post_value_type cenv e1)` (fn wt =>
    qpat_assum `ptr_val_ok _ _ _ op1 G1 tn1 t1`
      (strip_assume_tac o REWRITE_RULE [ptr_val_ok_def,wt])) >>
  `is_word_type (post_value_type cenv e2)` by simp[post_value_type_word] >>
  qpat_assum `is_word_type (post_value_type cenv e2)` (fn wt =>
    qpat_assum `ptr_val_ok _ _ _ op2 G2 tn2 t2`
      (strip_assume_tac o REWRITE_RULE [ptr_val_ok_def,wt])) >>
  `!x. op1 = Var x \/ op2 = Var x ==>
       not_fresh_at st x /\ op_prov G2 (Var x) = NONE /\ op_taint tn2 (Var x) = {}` by
    (qx_gen_tac `x` >> strip_tac
     >- (`not_fresh_at s1 x` by (first_assum irule >> first_assum ACCEPT_TAC) >>
         qpat_assum `!x. not_fresh_at s1 x ==> FLOOKUP G2 x = _ /\ _`
           (drule_then strip_assume_tac) >>
         `not_fresh_at st x` by (irule not_fresh_at_mono >> qexists_tac `s1` >> simp[]) >>
         qpat_assum `op1 = Var x` (fn eq =>
           qpat_assum `op_prov G1 op1 = NONE`
             (assume_tac o SRULE [eq,op_prov_def]) >>
           qpat_assum `op_taint tn1 op1 = {}` (assume_tac o REWRITE_RULE [eq])) >>
         simp[op_prov_def]) >>
     qpat_assum `!z. op2 = Var z ==> not_fresh_at st z`
       (drule_then assume_tac) >>
     qpat_assum `op2 = Var x` (SUBST1_TAC o SYM) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `lookup_scopes id mid2.scopes = NONE` by
    (namedCases_on `lookup_scopes id mid2.scopes` ["", "entry"] >> simp[] >>
     qpat_assum `expr_sim_inv cenv cx env mid2`
       (qspecl_then [`id`,`entry`] mp_tac o cj 4 o REWRITE_RULE
          [exprSimHypsDefsTheory.expr_sim_inv_def,
           vyperTypeInvariantsTheory.env_consistent_def,
           vyperTypeInvariantsTheory.env_scopes_consistent_def]) >>
     simp[FLOOKUP_DEF]) >>
  suspend "checked_init"
QED

(* Apply the selected initialization witness and recover its full iterator list. *)
fun range_join_init_tac replay scopes immutables =
  irule gas_outcome_full_bind_all_path >>
  conj_tac >- simp[cj 4 evaluate_storage_trace_frame] >>
  conj_tac >-
    (rpt strip_tac >> irule gas_exempt_cert_bind_results >>
     qexistsl [`mid`,`t`,`v`] >> BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (rpt strip_tac >> irule gas_exempt_cert_error_results >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (simp[Abbr `init`] >> irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_lifts, storage_trace_frame_checks,
          storage_trace_frame_return, storage_trace_frame_ignore_bind]) >>
  BETA_TAC >>
  qpat_assum `gas_outcome_full _ _ _ _ init _ _ _`
    (fn th => EXISTS_TAC (List.nth (#2 (strip_comb (concl th)), 6))) >>
  reverse conj_tac >-
    (irule gas_outcome_full_post_mono >>
     qpat_assum `gas_outcome_full _ _ _ _ init _ _ _` (irule_at Any) >>
     simp[NoAsms] >> rpt gen_tac >> strip_tac >>
     qexists `ex` >> asm_rewrite_tac [] >>
     irule (iffLR haltExitProjTheory.halt_exit_INR_type) >>
     first_assum ACCEPT_TAC) >>
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    (rewrite_tac[GSYM storage_trace_domain_def] >> first_assum ACCEPT_TAC) >>
  `?rs. res = INL rs /\ n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\ Num (n2 - n1) <= n` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                  (?rs. res = INL rs /\ _) /\ _`
       (drule_then strip_assume_tac) >> qexists `rs` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!st. init st = (INL (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))),st)` by
    (simp[Abbr `init`, get_range_limits_def, lift_sum_def, bind_def,
          ignore_bind_def, check_def, assert_def,
          vyperValueTheory.compatible_bound_def, return_def]) >>
  qpat_assum replay
    (qspec_then `[]` (fn step =>
      qpat_assum `!st. init st = _` (fn init =>
        qpat_assum `res = INL rs` (fn res =>
          strip_assume_tac
            (PURE_REWRITE_RULE [init, res, pairTheory.PAIR_EQ, sumTheory.INL_11]
               step))))) >>
  sg `rs = GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))` >-
    (FIRST [first_assum ACCEPT_TAC, irule EQ_SYM >> first_assum ACCEPT_TAC]) >>
  sg scopes >-
    (qpat_assum `_ with gas_obs := _ = mid with gas_obs := []`
       (mp_tac o Q.AP_TERM `(\s:evaluation_state. s.scopes)`) >> simp[NoAsms]) >>
  sg immutables >-
    (qpat_assum `_ with gas_obs := _ = mid with gas_obs := []`
       (mp_tac o Q.AP_TERM `(\s:evaluation_state. s.immutables)`) >> simp[NoAsms]) >>
  disj1_tac >> qexists `rs` >> conj_tac >- first_assum ACCEPT_TAC;

val range_init_admissible_tac =
  qpat_assum `gas_admissible (bind init _) _ _`
    (mp_then Any mp_tac (SRULE [gasContextTheory.gas_admissible_gas_obs]
      stmtSimForRoundsTheory.gas_admissible_bind_tail)) >>
  disch_then (fn th => qpat_assum `res = INL rs` (fn eq =>
    qpat_assum `!tail. init _ = (res,mid with gas_obs := tail)`
    (mp_then Any ACCEPT_TAC th o PURE_REWRITE_RULE [eq])));

Resume compile_for_range_frag_full[checked_init]:
  `local_ptrs_reserved cenv st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `ret_pc_ok cenv sa t2` by
    (irule ret_pc_ok_frame >>
     qpat_assum `ret_pc_ok cenv sa s0` (irule_at Any) >>
     asm_rewrite_tac [arithmeticTheory.LESS_EQ_REFL]) >>
  `return_buf_frame d cenv st t2` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC]) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid2 t2 /\
       storage_well_formed_on cx mid2 (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid2 G2 tn2 t2` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ e2 _ _ _ _ _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o PURE_ONCE_REWRITE_RULE [expr_post_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `n < dimword (:256)` by
    (qpat_assum `type_stmt env ret_ty (For id typ (Range e1 e2) n body) = SOME env'`
       (mp_then Any mp_tac range_full_computed_bound) >>
     asm_rewrite_tac []) >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (irule arithmeticTheory.LESS_TRANS >>
     qexists `2 ** 64` >>
     simp[wordsTheory.dimword_def,venomMemPropsTheory.dimindex_256,
          bitTheory.TWOEXP_MONO]) >>
  qspecl_then
    [`DF`,`lo`,`gas_explicit_sites ctx shadow_ctx`,`d`,`ctx`,`func`,`PG`,
     `cx_tops cx`,`cx`,`st0`,`RetQ`,`cenv`,`env`,`es`,`sa`,`s0`,`G0`,`tn0`,
     `mid2`,`t2`,`G2`,`tn2`,`st`,`sb0`,`entry_lbl`,`cond_lbl`,`p`,`cv`,`ev`,
     `n`,`typ`,`tyv`,`n1`,`n2`,`sz`,`id`] mp_tac range_full_init >>
  `st.cs_next_var <= st.cs_next_var + 9` by decide_tac >>
  simp[NoAsms,LET_THM] >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[] >>
     conj_tac >-
       (disj2_tac >> qexistsl_tac [`op1`,`op2`,`rv`,`g1`,`z1`,`g2`,`z2`] >>
        asm_rewrite_tac [] >>
        simp[NoAsms,ASCIInumbersTheory.toString_inj,not_fresh_at_def,
             DISJ_IMP_THM,FORALL_AND_THM]) >>
     asm_rewrite_tac [])) >>
  disch_then (qx_choose_then `w` assume_tac) >>
  qabbrev_tac
    `init = bind (lift_sum (get_range_limits (IntV n1) (IntV n2)))
       (\rl. ignore_bind (check (compatible_bound (Dynamic n) (SND rl)) "For too long")
         (return (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl))))` >>
  `bind (lift_sum (get_range_limits v1 v2))
     (\rl. ignore_bind (check (compatible_bound (Dynamic n) (SND rl)) "For too long")
       (eval_for cx tyv id body (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)))) =
   bind init (eval_for cx tyv id body)` by
    (simp[Abbr `init`, ignore_bind_def, bind_assoc, bind_return]) >>
  pop_assum (fn th => mk_asm "init_bind" th >> SUBST1_TAC th) >>
  drule_all_then (assume_tac o BETA_RULE)
    (Q.INST [`d` |-> `d`, `cenv` |-> `cenv`, `sa` |-> `st`]
       bodyFullSharedTheory.gas_outcome_full_return_buf_allocas_from) >>
  range_join_init_tac
    `!tail. init (mid2 with gas_obs := gas_explicit _ _ ++ tail) =
       (res,mid with gas_obs := tail)`
    `mid.scopes = mid2.scopes` `mid.immutables = mid2.immutables` >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule (iffLR body_const_cells_agree_immutables) >> qexists_tac `mid2` >> simp[]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by simp[] >>
  `gas_admissible (eval_for cx tyv id body rs) (stmt_res_ok lctx) mid` by
    (`eval_stmt cx (For id typ (Range e1 e2) n body) =
         do a <- bind (eval_expr cx e1) (read_result cx);
            b <- bind (eval_expr cx e2) (read_result cx);
            rl <- lift_sum (get_range_limits a b);
            check (compatible_bound (Dynamic n) (SND rl)) "For too long";
            eval_for cx tyv id body (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl))
         od` by
       (pure_once_rewrite_tac[Once evaluate_def] >>
        simp[LET_THM, lift_option_type_def] >>
        pure_once_rewrite_tac[Once evaluate_def] >>
        simp[LET_THM, bind_assoc, bind_return, LENGTH_GENLIST]) >>
     pop_assum (fn eq =>
       qpat_assum `gas_admissible (eval_stmt cx (For _ _ _ _ _)) _ es`
         (assume_tac o PURE_REWRITE_RULE [eq])) >>
     let
       val tail = SRULE [gasContextTheory.gas_admissible_gas_obs]
         stmtSimForRoundsTheory.gas_admissible_bind_tail
       fun advance adm replay = qpat_assum adm (mp_then Any mp_tac tail) >>
         disch_then (fn th => qpat_assum replay
           (mp_then Any (assume_tac o BETA_RULE) th))
     in
       advance `gas_admissible (bind (bind (eval_expr cx e1) (read_result cx)) _) _ es`
         `!tail. bind (eval_expr cx e1) (read_result cx) _ = (INL v1,mid1 with gas_obs := tail)` >>
       advance `gas_admissible (bind (bind (eval_expr cx e2) (read_result cx)) _) _ mid1`
         `!tail. bind (eval_expr cx e2) (read_result cx) _ = (INL v2,mid2 with gas_obs := tail)`
     end >>
     asm "init_bind" (fn eq =>
       qpat_x_assum `gas_admissible (bind (lift_sum (get_range_limits v1 v2)) _) _ mid2`
         (assume_tac o PURE_REWRITE_RULE [eq])) >>
     range_init_admissible_tac) >>
  `?start finish. eval_iterator cx (Range e1 e2) start = (INL rs,finish)` by
    ((`eval_iterator cx (Range e1 e2) =
        do a <- bind (eval_expr cx e1) (read_result cx);
           b <- bind (eval_expr cx e2) (read_result cx);
           rl <- lift_sum (get_range_limits a b);
           return (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od` by
       simp[Once evaluate_def, LET_THM, bind_assoc] >>
     pop_assum SUBST1_TAC >>
     qexistsl [`es with gas_obs := gas_explicit marks1 s0.vs_gas_readings ++ gas_explicit marks2 t1.vs_gas_readings`,
               `mid2 with gas_obs := []`] >>
     qpat_assum `!tail. bind (eval_expr cx e1) (read_result cx) _ = _`
       (qspec_then `gas_explicit marks2 t1.vs_gas_readings` (mk_asm "range_read1")) >>
     asm "range_read1" (fn th => simp[NoAsms, Once bind_def, th]) >>
     asm "read2" (fn th => simp[NoAsms, Once bind_def, REWRITE_RULE [APPEND_NIL] th]) >>
     qpat_assum `v1 = IntV n1` (fn v1 =>
       qpat_assum `v2 = IntV n2` (fn v2 =>
         qpat_assum `n1 <= n2` (fn bounds =>
           qpat_assum `rs = GENLIST _ _` (fn rs =>
             simp[NoAsms, v1, v2, bounds, rs, bind_def, get_range_limits_def,
                  lift_sum_def, return_def])))))) >>
  suspend "range_rounds"
QED

(* Instantiate the empty round with the predicate in its own premise. *)
fun defer_exists_conv tm =
  ((SWAP_EXISTS_CONV THENC QUANT_CONV defer_exists_conv) ORELSEC ALL_CONV) tm;

(* Both initializer cases continue with the same selected compiler package. *)
val range_join_rounds_source_tac =
  `lift_option_type (evaluate_type (get_tenv cx) typ) "For evaluate_type" es = (INL tyv,es)` by
    (qpat_assum `evaluate_type (get_tenv cx) typ = SOME tyv`
       (fn ty => simp[NoAsms, ty, lift_option_type_def, return_def])) >>
  `check (compatible_bound (Dynamic n) (LENGTH rs)) "For too long" es = (INL (),es)` by
    (qpat_assum `rs = GENLIST _ _` (fn rs =>
      qpat_assum `Num (n2 - n1) <= n` (fn length =>
        simp[NoAsms, rs, length, LENGTH_GENLIST, vyperValueTheory.compatible_bound_def,
             check_def, assert_def, return_def]))) >>
  `body_for_full_ok cx tyv id body rs` by
    (qpat_assum `!tenv s'' tyv t s'3' vs t' s'4' x t''. _ ==> body_for_full_ok _ _ _ _ _`
       irule >>
     conj_tac >- (qpat_assum `eval_iterator cx (Range e1 e2) _ = (INL rs,_)`
       (irule_at Any) >> simp[]) >>
     conj_tac >- (qexistsl [`es`,`es`,`()`] >> first_assum ACCEPT_TAC) >>
     qexistsl [`es`,`es`,`get_tenv cx`] >> simp[]);

val range_join_rounds_invariants_tac =
  qabbrev_tac `Inv = \H rs ee G tn s. ?k.
    k + LENGTH rs = Num (n2 - n1) /\
    rs = GENLIST (\j. Value (IntV (n1 + &(k+j)))) (LENGTH rs) /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    expr_sim_inv cenv cx env ee /\ lookup_scopes id ee.scopes = NONE /\
    s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ret_pc_ok cenv sa s /\ return_buf_frame d cenv sb0 s /\ return_buf_sep d cenv ee s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    lookup_var cv s = SOME (i2w (n1 + &k)) /\ lookup_var ev s = SOME (i2w n2) /\
    lookup_var p s = SOME w /\ FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n w,sz) /\
    ptr_covers G tn p s sz /\ op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
    op_taint tn (Var ev) = {} /\ op_prov G (Var ev) = NONE /\
    alloca_history func s /\
    (!fn inst v. frag_reachable ctx func s fn inst v ==> dalloca_fmp_headroom inst v) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 cenv ee s /\
    (!aid off z i. FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
      (!nm b z'. local_region cenv es.scopes s0 nm b z' ==> off+z <= b \/ b+z' <= off) /\
      off <= i /\ i < off+z /\ i IN tn.t_mem ==> i IN tn0.t_mem)` >>
  qabbrev_tac `Done = \H ee G tn s.
    stmt_lands lctx sb (INL ()) s /\ ~s.vs_halted /\ ~block_is_terminated sb /\
    cenv_top_ext cenv cenv ee.scopes /\ stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ return_buf_frame d cenv sb s /\
    return_buf_sep d cenv ee s /\ ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 cenv ee s /\
    (!aid off z i. FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
      (!nm b z'. local_region cenv es.scopes s0 nm b z' ==> off+z <= b \/ b+z' <= off) /\
      off <= i /\ i < off+z /\ i IN tn.t_mem ==> i IN tn0.t_mem)` >>
  qabbrev_tac `R = \H ex ee gt r.
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex : unit + exception) gt r) /\
    halt_exit H cx ee (INR ex : unit + exception) r /\
    (ctx_has_dalloca ctx ==> !s.
      (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)`;

val range_join_rounds_post_tac =
  irule gas_outcome_full_post_mono >>
  qexistsl [`\H res ee G tn t. res = INL () /\ Done H ee G tn t`,
            `\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r`] >>
  BETA_TAC >>
  conj_tac >-
    (rpt gen_tac >> simp[NoAsms, Abbr `Done`] >> strip_tac >>
     qexists `cenv` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (simp[NoAsms, Abbr `R`] >> rpt gen_tac >>
     disch_then (qx_choose_then `ex` (CONJUNCTS_THEN2 SUBST1_TAC assume_tac)) >>
     pop_assum ACCEPT_TAC);

val range_join_rounds_cons_tac =
  irule eval_for_rounds_full >>
  conj_tac >-
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                  (?rs. res = INL rs /\ _) /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`Inv`,`\rs b. if b then return () else eval_for cx tyv id body rs`,
            `stmt_res_ok lctx`,
            `\a. do v <- read_result cx a;
                    push_scope_with_var id tyv v;
                    finally (try (do eval_stmts cx body; return F od)
                                 handle_loop_exception) pop_scope od`] >>
  BETA_TAC >>
  conj_tac >-
    (asm "round_cons"
       (qspecl_then [`st0`,`es`,`s0`,`G0`,`tn0`,`n1`,`n2`,`Num (n2-n1)`,`w`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >>
       FIRST [first_assum ACCEPT_TAC, REFL_TAC,
         qpat_assum `rs = GENLIST _ _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC])) >>
     disch_then (qspecl_then [`cenv`,`Inv`,`Done`,`R`] mp_tac) >>
     (impl_tac >-
       (simp[NoAsms,Abbr `Inv`,Abbr `Done`,Abbr `R`,FUN_EQ_THM] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
        metis_tac[haltExitProjTheory.halt_exit_INR_type])) >>
     disch_then ACCEPT_TAC);

val range_join_rounds_nil_tac =
  conj_tac >-
    (rpt strip_tac >> irule gas_exempt_cert_bind_bool >>
     qexistsl [`mid'`,`t'`,`b`] >> BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (rpt strip_tac >> irule gas_exempt_cert_error_bool >> first_assum ACCEPT_TAC) >>
  conj_tac >- (gen_tac >> REFL_TAC) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >> irule range_full_nil >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexists `G0` >> CONV_TAC defer_exists_conv >>
     qexistsl [`Num (n2-n1)`,`ainst`,`body`,`body_lbl`,`n`,`cenv`,`cenv`,
               `cond_lbl`,`cv`,`d`,`dv`,`e1`,`e2`,`j1`,`env`,`es`,`ev`,`exit_lbl`,
               `id`,`j2`,`lctx`,`n1`,`n2`,`stmt_res_ok lctx`,`p`,`ret_ty`,`s0`,
               `sa`,`sb`,`sb0`,`sz`,`tn0`,`tops`,`typ`,`tyv`,`w`] >>
     (fn (asl, goal) =>
        let
          val (inv, body) = dest_exists goal
          val eq = find_term (fn tm => is_eq tm andalso aconv (lhs tm) inv) body
        in EXISTS_TAC (rhs eq) (asl, goal) end) >>
     rpt conj_tac >> (FIRST [first_assum ACCEPT_TAC, REFL_TAC,
       simp[NoAsms,Abbr `Done`]]) >>
     qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> Inv H [] _ _ _ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[NoAsms, Abbr `Inv`] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> REFL_TAC) >>
  reverse conj_tac >- first_assum ACCEPT_TAC;

val range_join_rounds_entry_tac =
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                (?rs. _) /\ (!bw capacity. _ ==> allocas_from _ t)`
    (drule_then strip_assume_tac) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions`
         (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi o CONJ inv))) >>
  `!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                  gas_origin_ptr_path _ _ _ (OK t,_,_)`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_then (Pos hd) mp_tac
       bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac []);

val range_join_rounds_sep_tac =
  `return_buf_sep d cenv mid t` by
    (irule (INST_TYPE [alpha |-> ``:256``]
       bodyFullSharedTheory.return_buf_sep_locals_kept) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`storage_trace_horizon es.storage_trace`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC);

val range_join_rounds_pack_tac =
  qpat_x_assum `res = INL rs'` mp_tac >>
  qpat_assum `res = INL rs` (fn th => rewrite_tac[th,sumTheory.INL_11]) >>
  disch_then SUBST_ALL_TAC >>
  simp[NoAsms,Abbr `Inv`,arithmeticTheory.ADD_COMM] >>
  qexists `k` >>
  `ainst.inst_id = st.cs_next_id` by
    (qpat_assum `ainst = mk_inst _ _ _ _`
      (fn th => simp[NoAsms,th,venomInstTheory.mk_inst_def])) >>
  qpat_assum `p = STRING _ _` SUBST1_TAC >>
  qpat_assum `ainst.inst_id = st.cs_next_id` SUBST1_TAC >>
  rpt conj_tac >> first_assum ACCEPT_TAC;

Resume compile_for_range_frag_full[literal]:
  qpat_x_assum `?a1 m1 a2 m2. e1 = _ /\ e2 = _`
    (qx_choosel_then [`a1`,`n1`,`a2`,`n2`] strip_assume_tac) >>
  qpat_x_assum `!a1 m1 a2 m2. e1 = _ /\ e2 = _ ==> _`
    (qspecl_then [`a1`,`n1`,`a2`,`n2`] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[cj 1 evaluate_storage_trace_frame] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disch_tac >>
  `n1 <= n2 /\ n = Num (n2 - n1)` by
    (qpat_assum `supported_iterator _ _ _ _` mp_tac >>
     qpat_assum `e1 = Literal a1 (IntL n1)` SUBST1_TAC >>
     qpat_assum `e2 = Literal a2 (IntL n2)` SUBST1_TAC >>
     simp[supported_iterator_def]) >>
  `value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2)` by
    (`well_typed_literal typ (IntL n1)` by
       (qpat_assum `well_typed_expr env e1` mp_tac >>
        qpat_assum `expr_type e1 = typ` mp_tac >>
        qpat_assum `e1 = Literal a1 (IntL n1)` SUBST1_TAC >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[well_typed_expr_def, expr_type_def]) >>
     `well_typed_literal typ (IntL n2)` by
       (qpat_assum `well_typed_expr env e2` mp_tac >>
        qpat_assum `expr_type e2 = typ` mp_tac >>
        qpat_assum `e2 = Literal a2 (IntL n2)` SUBST1_TAC >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[well_typed_expr_def, expr_type_def]) >>
     conj_tac >-
       (irule (REWRITE_RULE [vyperValueOperationTheory.evaluate_literal_def]
          (Q.INST [`lit` |-> `IntL n1`] vyperTypeValuesTheory.well_typed_literal_sound)) >>
        qexistsl [`get_tenv cx`,`typ`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule (REWRITE_RULE [vyperValueOperationTheory.evaluate_literal_def]
       (Q.INST [`lit` |-> `IntL n2`] vyperTypeValuesTheory.well_typed_literal_sound)) >>
     qexistsl [`get_tenv cx`,`typ`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `n < dimword (:256)` by
    (qspecl_then [`get_tenv cx`,`typ`,`tyv`,`n1`,`n2`] mp_tac range_end_words >>
     simp[]) >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (irule arithmeticTheory.LESS_TRANS >> qexists `2 ** 64` >>
     simp[wordsTheory.dimword_def,venomMemPropsTheory.dimindex_256,bitTheory.TWOEXP_MONO]) >>
  `lookup_scopes id es.scopes = NONE` by
    (namedCases_on `lookup_scopes id es.scopes` ["", "entry"] >> simp[] >>
     qpat_assum `expr_sim_inv cenv cx env es`
       (qspecl_then [`id`,`entry`] mp_tac o cj 4 o REWRITE_RULE
          [exprSimHypsDefsTheory.expr_sim_inv_def,
           vyperTypeInvariantsTheory.env_consistent_def,
           vyperTypeInvariantsTheory.env_scopes_consistent_def]) >>
     simp[FLOOKUP_DEF]) >>
  `alloca_frame cenv es sa s0 cenv es s0` by (irule alloca_frame_same >> simp[]) >>
  `st.cs_next_var <= sb0.cs_next_var` by simp[] >>
  qspecl_then
    [`DF`,`lo`,`gas_explicit_sites ctx shadow_ctx`,`d`,`ctx`,`func`,`PG`,
     `cx_tops cx`,`cx`,`st0`,`RetQ`,`cenv`,`env`,`es`,`sa`,`s0`,`G0`,`tn0`,
     `es`,`s0`,`G0`,`tn0`,`st`,`sb0`,`entry_lbl`,`cond_lbl`,`p`,`cv`,`ev`,
     `n`,`typ`,`tyv`,`n1`,`n2`,`sz`,`id`] mp_tac range_full_init >>
  simp[NoAsms,LET_THM] >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[] >>
     conj_tac >-
       (disj1_tac >>
        simp[ASCIInumbersTheory.toString_inj,not_fresh_at_def]) >>
     asm_rewrite_tac [] >> simp[])) >>
  disch_then (qx_choose_then `w` assume_tac) >>
  qabbrev_tac
    `init = bind (lift_sum (get_range_limits (IntV n1) (IntV n2)))
       (\rl. ignore_bind (check (compatible_bound (Dynamic n) (SND rl)) "For too long")
         (return (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl))))` >>
  `eval_iterator cx (Range e1 e2) =
     return (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)))` by
    (qpat_assum `e1 = Literal a1 (IntL n1)` SUBST1_TAC >>
     qpat_assum `e2 = Literal a2 (IntL n2)` SUBST1_TAC >>
     simp[FUN_EQ_THM, eval_iterator_range_lit, return_def]) >>
  `eval_stmt cx (For id typ (Range e1 e2) n body) =
     bind init (eval_for cx tyv id body)` by
    (pure_once_rewrite_tac[Once evaluate_def] >>
     simp[LET_THM, lift_option_type_def, bind_return, ignore_bind_def,
          Abbr `init`, get_range_limits_def, lift_sum_def, LENGTH_GENLIST, bind_assoc]) >>
  pop_assum (fn eq =>
    qpat_assum `gas_admissible (eval_stmt cx (For _ _ _ _ _)) _ es`
      (assume_tac o PURE_REWRITE_RULE [eq]) >> SUBST1_TAC eq) >>
  drule_all_then (assume_tac o BETA_RULE)
    (Q.INST [`d` |-> `d`, `cenv` |-> `cenv`, `sa` |-> `sa`]
       bodyFullSharedTheory.gas_outcome_full_return_buf_allocas) >>
  range_join_init_tac
    `!tail. init (es with gas_obs := gas_explicit _ _ ++ tail) =
       (res,mid with gas_obs := tail)`
    `mid.scopes = es.scopes` `mid.immutables = es.immutables` >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule (iffLR body_const_cells_agree_immutables) >> qexists_tac `es` >> simp[]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by simp[] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ es s0 /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     simp[GSYM storage_trace_domain_def]) >>
  `gas_admissible (eval_for cx tyv id body rs) (stmt_res_ok lctx) mid` by
    range_init_admissible_tac >>
  `?start finish. eval_iterator cx (Range e1 e2) start = (INL rs,finish)` by
    (qexistsl [`es`,`es`] >>
     qpat_assum `eval_iterator cx (Range e1 e2) = _` (fn iter =>
       qpat_assum `rs = GENLIST _ _` (fn rs =>
         simp[NoAsms, iter, rs, return_def]))) >>
  suspend "literal_rounds"
QED

Resume compile_for_range_frag_full[literal_rounds]:
  range_join_rounds_source_tac >>
  range_join_rounds_invariants_tac >>
  range_join_rounds_post_tac >>
  range_join_rounds_cons_tac >>
  range_join_rounds_nil_tac >>
  range_join_rounds_entry_tac >>
  range_join_rounds_sep_tac >>
  range_join_rounds_pack_tac
QED

Resume compile_for_range_frag_full[range_rounds]:
  range_join_rounds_source_tac >>
  range_join_rounds_invariants_tac >>
  range_join_rounds_post_tac >>
  range_join_rounds_cons_tac >>
  range_join_rounds_nil_tac >>
  range_join_rounds_entry_tac >>
  range_join_rounds_sep_tac >>
  range_join_rounds_pack_tac
QED

Finalise compile_for_range_frag_full
