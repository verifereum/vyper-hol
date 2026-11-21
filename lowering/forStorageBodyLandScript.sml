(* Pointwise cleanup after a storage-loop body. The saved operand is old at
   body entry; nothing here depends on which storage region it denotes. *)
Theory forStorageBodyLand
Ancestors
  bodyFullForFrame bodyFullShared bodyFullPreds bodyFullMemoryFrames
  bodyExprPreFacts bodySimDeclCases stmtSimForArrayLoop stmtSimProps
  stmtLowering stmtLoweringMono exprLoweringProps placeTypedCopyPath fragGasOriginPtrLoop
  decoderGhostFramePtr assignTuplePtrCopyLen ptrSafeRun venomExecSemantics
  venomExecProps venomState ptrDiscipline vyperState words vyperAST exprLowering
  gasExplicitSites bodyMemoryDefs allocaHistory finite_map list pred_set arithmetic
  compileEnv context bodyPtrDefs loweringStateRelDefs stmtSimDefs loweringPosts
  bodySimFull fragGasOriginPtr venomInst fragExecMem instMemFrontier
  emitHelper codegenRel contextCodegenRel memSafeRun
  vyperEvalPreservesScopes vyperStorageTrace vyperStorageFootprint
  exprSimHypsDefs unitTransformDefs vyperInterpreter[qualified]
Libs
  monadsyntax

Theorem storage_body_trace_extension[local]:
  !cx stmts es raw ef. eval_stmts cx stmts es = (raw,ef) ==>
  ?delta. ef.storage_trace = es.storage_trace ++ delta
Proof
  metis_tac[storage_trace_frame_prefix, cj 2 evaluate_storage_trace_frame]
QED

Theorem storage_body_saved_operand[local]:
  (∀x. bop ≠ Label x) /\ (∀x. bop = Var x ==> not_fresh_at sb0 x) /\
  (∀x w. not_fresh_at sb0 x /\ lookup_var x s = SOME w ==>
     lookup_var x t = SOME w) /\
  (∀x. not_fresh_at sb0 x ==> op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  eval_operand bop s = SOME slot /\ op_taint tn bop = {} ==>
  eval_operand bop t = SOME slot /\ op_taint tn1 bop = {}
Proof
  Cases_on `bop` >> simp[eval_operand_def, op_taint_def]
QED

Theorem for_storage_body_post_land_at:
  !DF lo d ctx shadow_ctx func PG cx c0 e0 sa0 sb s0 G0 tn0 bop slot dst tyv typ
    len nb id env p idx lvo sd stmts si lctx ei v bc bc1 sb0 sb1 sj tops bindings
    ret_ty env_b k H st0 s G tn raw ef G1 tn1 t exit incr.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    supported_stmts tops bindings stmts /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\ value_has_type tyv v /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    call_evaluation_safe cx (int_calls_stmts stmts) /\
    expr_sim_inv c0 cx env ei /\ lookup_scopes id ei.scopes = NONE /\
    ce_locals_declared c0 env /\ locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ei.scopes /\
    cenv_top_ext c0 bc (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))::ei.scopes).scopes /\
    same_frame c0 bc /\
    local_ptrs_reserved c0 sb0 /\ sa0.cs_next_id <= sb0.cs_next_id /\
    (!x. not_fresh_at sa0 x ==> not_fresh_at sb0 x) /\
    stmts_env bc (InLoop exit incr) ret_ty stmts sb0 = (bc1,sb1) /\
    (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\ fn_has_code sb1 sj func /\
    si.cs_current_bb = incr /\ si.cs_current_insts = [] /\
    sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\ ~block_is_terminated sb /\
    well_formed_type_value tyv /\ s.vs_current_bb = sb0.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s.vs_halted /\
    lookup_var idx s = SOME (n2w k) /\ FLOOKUP G idx = NONE /\
    op_taint tn (Var idx) = {} /\ eval_operand lvo s = SOME (n2w len) /\
    op_taint tn lvo = {} /\ op_prov G lvo = NONE /\
    eval_operand bop s = SOME slot /\ op_taint tn bop = {} /\
    (!x. bop = Var x ==> not_fresh_at sb0 x) /\ (!x. bop <> Label x) /\
    lookup_var p s = SOME dst /\ FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
    ptr_covers G tn p s nb /\ 32 * type_slot_size tyv <= nb /\
    w2n dst + nb < 2 ** 256 /\ w2n dst + nb <= s.vs_alloca_next /\
    (!name b sz. local_region c0 ei.scopes s name b sz ==>
       w2n dst + nb <= b \/ b + sz <= w2n dst) /\
    return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\ body_stmts_full_ok cx stmts /\
    stmt_state_rel H ctx func bc cx (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))::ei.scopes) s /\
    storage_well_formed_on cx (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))::ei.scopes) (FST H) /\
    ghost_inv_at (DF H) lo d bc cx (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))::ei.scopes) G tn s /\
    (\c ee u GG tt.
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
         lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa0 x ==>
         FLOOKUP GG x = FLOOKUP G0 x /\ op_taint tt (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame c0 e0 sa0 s0 c ee u /\
      (!aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
         (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
            off+sz <= b \/ b+sz' <= off) /\ off <= i /\ i < off+sz /\
         i IN tt.t_mem ==> i IN tn0.t_mem)) bc (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))::ei.scopes) s G tn /\
    (?c3. stmt_lands (InLoop exit incr) sb1 raw t /\ ~t.vs_halted /\
      (raw = INL () ==> ~block_is_terminated sb1 /\ c3 = bc1) /\
      cenv_top_ext bc c3 ef.scopes /\ stmt_state_rel H ctx func c3 cx ef t /\
      storage_well_formed_on cx ef (FST H) /\ return_buf_frame d c3 sb1 t /\
      alloca_history func t /\ return_buf_sep d c3 ef t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d c3 cx ef G1 tn1 t /\
      (!x w. not_fresh_at sb0 x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sb0 x ==>
         FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
      alloca_frame bc (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))::ei.scopes) sb0 s c3 ef t /\
      (!aid off sz i.
         FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sb0.cs_next_id /\
         (!name b sz'. local_region bc (ei with scopes :=
           (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))::ei.scopes).scopes s name b sz' ==>
            off+sz <= b \/ b+sz' <= off) /\ off <= i /\ i < off+sz /\
         i IN tn1.t_mem ==> i IN tn.t_mem)) /\
    (lookup_var idx t = lookup_var idx s /\ lookup_var p t = lookup_var p s /\
     eval_operand lvo t = eval_operand lvo s /\
     FLOOKUP G1 idx = FLOOKUP G idx /\ FLOOKUP G1 p = FLOOKUP G p /\
     op_prov G1 lvo = op_prov G lvo /\
     op_taint tn1 (Var idx) = op_taint tn (Var idx) /\
     op_taint tn1 (Var p) = op_taint tn (Var p) /\ op_taint tn1 lvo = op_taint tn lvo) /\
    ef.gas_obs = [] /\ valid_horizon cx st0 H ef.storage_trace /\
    (?xs. !tail. eval_stmts cx stmts ((ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))::ei.scopes)
      with gas_obs := xs ++ tail) = (raw,ef with gas_obs := tail)) ==>
    ?sc rest b. ef.scopes = sc::rest /\
      (case raw of INL _ => INL F | INR ex => FST (handle_loop_exception ex ef)) = INL b /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (t,G1,tn1) []
        (OK (if raw = INL () then jump_to incr t else t),G1,tn1) /\
      (ef with scopes := rest).gas_obs = [] /\ ~(if raw = INL () then jump_to incr t else t).vs_halted /\
      (?delta. ef.storage_trace = ei.storage_trace ++ delta) /\
      (b ==> ?c.
        stmt_lands lctx sb (INL ()) (if raw = INL () then jump_to incr t else t) /\
        ~(if raw = INL () then jump_to incr t else t).vs_halted /\
        ~block_is_terminated sb /\ c = c0 /\ cenv_top_ext c0 c (ef with scopes := rest).scopes /\
        stmt_state_rel H ctx func c cx (ef with scopes := rest) (if raw = INL () then jump_to incr t else t) /\
        storage_well_formed_on cx (ef with scopes := rest) (FST H) /\
        return_buf_frame d c sb (if raw = INL () then jump_to incr t else t) /\
        return_buf_sep d c (ef with scopes := rest) (if raw = INL () then jump_to incr t else t) /\
        ghost_inv_at (DF H) lo d c cx (ef with scopes := rest) G1 tn1 (if raw = INL () then jump_to incr t else t) /\
        (\c ee u GG tt.
          alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          s0.vs_alloca_next <= u.vs_alloca_next /\
          (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
             lookup_var x u = SOME w) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
          (!x. not_fresh_at sa0 x ==>
             FLOOKUP GG x = FLOOKUP G0 x /\ op_taint tt (Var x) = op_taint tn0 (Var x)) /\
          alloca_frame c0 e0 sa0 s0 c ee u /\
          (!aid off sz i.
             FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
             (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
                off+sz <= b \/ b+sz' <= off) /\ off <= i /\ i < off+sz /\
             i IN tt.t_mem ==> i IN tn0.t_mem)) c (ef with scopes := rest)
          (if raw = INL () then jump_to incr t else t) G1 tn1) /\
      (~b ==> evaluate_type (get_tenv cx) typ = SOME tyv /\ well_formed_type_value tyv /\
        (if raw = INL () then jump_to incr t else t).vs_current_bb = si.cs_current_bb /\
        (if raw = INL () then jump_to incr t else t).vs_inst_idx = LENGTH si.cs_current_insts /\
        ~(if raw = INL () then jump_to incr t else t).vs_halted /\
        lookup_var idx (if raw = INL () then jump_to incr t else t) = SOME (n2w k) /\ FLOOKUP G1 idx = NONE /\
        op_taint tn1 (Var idx) = {} /\ eval_operand lvo (if raw = INL () then jump_to incr t else t) = SOME (n2w len) /\
        op_taint tn1 lvo = {} /\ op_prov G1 lvo = NONE /\
        eval_operand bop (if raw = INL () then jump_to incr t else t) = SOME slot /\ op_taint tn1 bop = {} /\
        lookup_var p (if raw = INL () then jump_to incr t else t) = SOME dst /\
        FLOOKUP (if raw = INL () then jump_to incr t else t).vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
        ptr_covers G1 tn1 p (if raw = INL () then jump_to incr t else t) nb /\ 32 * type_slot_size tyv <= nb /\
        w2n dst + nb < 2 ** 256 /\ w2n dst + nb <= (if raw = INL () then jump_to incr t else t).vs_alloca_next /\
        (!name b sz. local_region c0 (ef with scopes := rest).scopes
           (if raw = INL () then jump_to incr t else t) name b sz ==>
           w2n dst + nb <= b \/ b + sz <= w2n dst) /\
        lookup_scopes id (ef with scopes := rest).scopes = NONE /\ expr_sim_inv c0 cx env (ef with scopes := rest) /\
        ce_locals_declared c0 env /\ locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 (ef with scopes := rest).scopes /\
        stmt_state_rel H ctx func c0 cx (ef with scopes := rest) (if raw = INL () then jump_to incr t else t) /\
        storage_well_formed_on cx (ef with scopes := rest) (FST H) /\
        ghost_inv_at (DF H) lo d c0 cx (ef with scopes := rest) G1 tn1 (if raw = INL () then jump_to incr t else t) /\
        return_buf_frame d c0 sa0 (if raw = INL () then jump_to incr t else t) /\
        ret_pc_ok c0 sa0 (if raw = INL () then jump_to incr t else t) /\
        return_buf_sep d c0 (ef with scopes := rest) (if raw = INL () then jump_to incr t else t) /\
        body_stmts_full_ok cx stmts /\
        (\c ee u GG tt.
          alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          s0.vs_alloca_next <= u.vs_alloca_next /\
          (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
             lookup_var x u = SOME w) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
          (!x. not_fresh_at sa0 x ==>
             FLOOKUP GG x = FLOOKUP G0 x /\ op_taint tt (Var x) = op_taint tn0 (Var x)) /\
          alloca_frame c0 e0 sa0 s0 c ee u /\
          (!aid off sz i.
             FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
             (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
                off+sz <= b \/ b+sz' <= off) /\ off <= i /\ i < off+sz /\
             i IN tt.t_mem ==> i IN tn0.t_mem)) c0 (ef with scopes := rest)
          (if raw = INL () then jump_to incr t else t) G1 tn1)
Proof
  rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `cenv_top_ext c0 bc eb.scopes` >>
  qmatch_goalsub_abbrev_tac `Fr bc eb s G tn` >>
  qabbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?xs. !tail. eval_stmts _ _ _ = _` (qx_choose_then `xs` assume_tac) >>
  `eval_stmts cx stmts (eb with gas_obs := xs) = (raw,ef)` by
    suspend "body_eval" >>
  `?sc rest. ef.scopes = sc::rest /\
     (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
     MAP FDOM ei.scopes = MAP FDOM rest` by suspend "scope_shape" >>
  qpat_x_assum `?c3. stmt_lands _ _ _ _ /\ _` strip_assume_tac >>
  `cenv_top_ext c0 c3 ef.scopes` by suspend "environment" >>
  `stmt_state_rel H ctx func c0 cx (ef with scopes := rest) t /\
   ghost_inv_at (DF H) lo d c0 cx (ef with scopes := rest) G1 tn1 t /\
   return_buf_sep d c0 (ef with scopes := rest) t` by suspend "scope_projection" >>
  `Fr c3 ef t G1 tn1` by suspend "compose_frame" >>
  `Fr c0 (ef with scopes := rest) t G1 tn1` by suspend "pop_frame" >>
  `!name b sz. local_region c0 rest t name b sz ==>
     w2n dst+nb <= b \/ b+sz <= w2n dst` by suspend "item_separation" >>
  `ptr_covers G1 tn1 p t nb` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl [`G`, `s`, `tn`] >> asm_rewrite_tac[] >> metis_tac[]) >>
  `(raw = INL () \/ raw = INR ContinueException) ==>
     expr_sim_inv c0 cx env (ef with scopes := rest)` by suspend "source_typed" >>
  `return_buf_frame d c0 sa0 t /\ ret_pc_ok c0 sa0 t` by suspend "return_frame" >>
  `?delta. ef.storage_trace = ei.storage_trace ++ delta` by
    (drule storage_body_trace_extension >> simp[NoAsms, Abbr `eb`]) >>
  `storage_well_formed_on cx (ef with scopes := rest) (FST H)` by
    (`storage_well_formed_on cx (ef with scopes := rest) (FST H) <=>
      storage_well_formed_on cx ef (FST H)` by
       (irule storage_well_formed_on_backends >> simp[]) >> asm_rewrite_tac[]) >>
  `lookup_scopes id rest = NONE` by
    (irule lookup_scopes_none_map_fdom >> qexists `ei.scopes` >> asm_rewrite_tac[]) >>
  `eval_operand bop t = SOME slot /\ op_taint tn1 bop = {}` by
    suspend "saved_operand" >>
  Cases_on `raw = INL ()` >- suspend "normal" >>
  Cases_on `raw = INR BreakException` >- suspend "break" >>
  suspend "continue"
QED

Resume for_storage_body_post_land_at[body_eval]:
  `ef with gas_obs := [] = ef` by
    (simp[NoAsms, evaluation_state_component_equality] >> first_assum ACCEPT_TAC) >>
  qpat_assum `ef with gas_obs := [] = ef` (fn upd =>
    qpat_assum `!tail. eval_stmts _ _ _ = _`
      (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL, upd])))
QED

Resume for_storage_body_post_land_at[scope_shape]:
  `eval_stmts cx stmts
     ((ei with gas_obs := xs) with scopes :=
       (FEMPTY |+ (id, <|assignable := F; type := tyv;
         value := v; popped := []|>))::(ei with gas_obs := xs).scopes) =
     (raw,ef)` by
    (qpat_assum `eval_stmts _ _ (eb with gas_obs := xs) = _` mp_tac >>
     simp[NoAsms, Abbr `eb`, evaluation_state_fupdfupds, evaluation_state_fn_updates]) >>
  `lookup_scopes id (ei with gas_obs := xs).scopes = NONE` by
    (pure_rewrite_tac [evaluation_state_accfupds] >> first_assum ACCEPT_TAC) >>
  drule_all array_body_scope_shape >> strip_tac >>
  qexistsl [`sc`, `rest`] >> asm_rewrite_tac[] >>
  qpat_assum `eval_stmts _ _ (eb with gas_obs := xs) = _`
    (mp_tac o MATCH_MP eval_stmts_preserves_scopes_dom) >>
  simp[NoAsms, preserves_scopes_dom_def, Abbr `eb`, evaluation_state_accfupds] >>
  asm_rewrite_tac[] >> simp[]
QED

Resume for_storage_body_post_land_at[environment]:
  qpat_assum `eval_stmts _ _ (eb with gas_obs := xs) = _`
    (mp_tac o MATCH_MP eval_stmts_preserves_scopes_dom) >>
  simp_tac (srw_ss()) [preserves_scopes_dom_def] >> strip_tac >>
  irule cenv_top_ext_trans >> qexistsl [`bc`, `eb.scopes`] >> asm_rewrite_tac[]
QED

Resume for_storage_body_post_land_at[scope_projection]:
  conj_tac >-
    (irule array_body_scope_projection >>
     conj_tac >- (qexists `sc` >> asm_rewrite_tac[]) >>
     qexistsl [`bc`, `c3`, `eb with gas_obs := xs`, `raw`, `stmts`] >>
     asm_rewrite_tac[evaluation_state_accfupds]) >>
  conj_tac >-
    (irule ghost_inv_at_pop >> conj_tac >- (qexists `sc` >> asm_rewrite_tac[]) >>
     qexists `c3` >> asm_rewrite_tac[]) >>
  irule return_buf_sep_pop >> qexistsl [`c3`, `sc`] >>
  `((ef with scopes := rest) with scopes := sc::rest) = ef` by
    simp[evaluation_state_component_equality] >>
  asm_rewrite_tac[evaluation_state_accfupds, combinTheory.K_THM] >>
  qpat_assum `cenv_top_ext c0 c3 ef.scopes` mp_tac >>
  qpat_assum `ef.scopes = sc::rest` (rewrite_tac o single)
QED

Resume for_storage_body_post_land_at[compose_frame]:
  qpat_assum `Fr bc eb s G tn` mp_tac >>
  simp_tac pure_ss [Abbr `Fr`] >> BETA_TAC >> strip_tac >>
  irule for_full_frame_compose >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at Any) >> qexists `G` >> asm_rewrite_tac[] >>
  qexistsl [`bc`, `eb`, `s`, `sb0`] >> asm_rewrite_tac[]
QED

Resume for_storage_body_post_land_at[pop_frame]:
  qpat_assum `Fr c3 ef t G1 tn1` mp_tac >>
  simp_tac pure_ss [Abbr `Fr`] >> BETA_TAC >> strip_tac >>
  irule for_full_frame_pop >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
  conj_tac >- (qexists `sc` >> asm_rewrite_tac[]) >>
  qexists `c3` >> asm_rewrite_tac[] >> metis_tac[for_full_frame_pop]
QED

Resume for_storage_body_post_land_at[item_separation]:
  `stmt_state_rel H ctx func c0 cx ei s` by
    (`ei = eb with scopes := ei.scopes` by
       simp[NoAsms, Abbr `eb`, evaluation_state_fupdfupds] >>
     pop_assum SUBST1_TAC >> irule stmt_state_rel_pop_top_ext >>
     reverse conj_tac >- (qexists `bc` >> asm_rewrite_tac[]) >>
     simp[NoAsms, Abbr `eb`, evaluation_state_accfupds] >>
     asm_rewrite_tac[FDOM_FUPDATE, FDOM_FEMPTY, IN_INSERT, NOT_IN_EMPTY]) >>
  rpt strip_tac >>
  `local_region c0 ei.scopes s name b sz` by
    (irule (INST_TYPE [alpha |-> ``:256``] local_region_kept) >>
     reverse conj_tac >-
       (qexistsl [`H`, `ctx`, `cx`, `func`] >> first_assum ACCEPT_TAC) >>
     qexistsl [`ef with scopes := rest`, `t`, `sb0`] >>
     asm_rewrite_tac[evaluation_state_accfupds] >> simp[]) >>
  metis_tac[]
QED

Resume for_storage_body_post_land_at[source_typed]:
  disch_tac >>
  `eval_stmts cx stmts
     ((ei with gas_obs := xs) with scopes :=
       (FEMPTY |+ (id, <|assignable := F; type := tyv;
         value := v; popped := []|>))::(ei with gas_obs := xs).scopes) =
     (raw,ef)` by
    (qpat_assum `eval_stmts _ _ (eb with gas_obs := xs) = _` mp_tac >>
     simp[NoAsms, Abbr `eb`, evaluation_state_fupdfupds, evaluation_state_fn_updates]) >>
  `expr_sim_inv c0 cx env (ei with gas_obs := xs)` by simp[] >>
  drule_all expr_sim_inv_for_pop >> disch_then ACCEPT_TAC
QED

Resume for_storage_body_post_land_at[return_frame]:
  conj_tac >- (irule return_buf_frame_frame >> qexistsl [`c0`, `s`, `sa0`] >>
    simp[] >> rpt strip_tac >>
    qpat_assum `!x w. not_fresh_at sb0 x /\ _ ==> _` irule >>
    asm_rewrite_tac[] >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  irule ret_pc_ok_frame >> qexistsl [`c0`, `s`, `sa0`] >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!x w. not_fresh_at sb0 x /\ _ ==> _` irule >>
  asm_rewrite_tac[] >> first_x_assum irule >> first_assum ACCEPT_TAC
QED

Resume for_storage_body_post_land_at[saved_operand]:
  irule storage_body_saved_operand >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`s`, `sb0`, `tn`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> res_tac
QED

Resume for_storage_body_post_land_at[break]:
  qpat_x_assum `raw = INR BreakException` SUBST_ALL_TAC >>
  simp[NoAsms, vyperInterpreterTheory.handle_loop_exception_def, return_def] >>
  qexistsl [`sc`, `rest`] >> asm_rewrite_tac[] >>
  simp[gas_origin_ptr_path_rules, cenv_top_ext_refl] >>
  conj_tac >-
    (qpat_x_assum `stmt_lands (InLoop _ _) _ _ _` mp_tac >> simp[stmt_lands_def]) >>
  qpat_assum `return_buf_frame d c0 sa0 t` mp_tac >>
  Cases_on `d` >- simp[NoAsms, return_buf_frame_def] >>
  rename1 `return_buf_frame (SOME pair) c0 sb t` >> Cases_on `pair` >>
  simp[NoAsms, return_buf_frame_def] >>
  strip_tac >> qexistsl [`x`, `slot_size`] >> asm_rewrite_tac[] >>
  qpat_assum `!x sz. c0.ce_return_buf = _ ==> not_fresh_at sb x` irule >>
  qexists `slot_size` >> first_assum ACCEPT_TAC
QED

Resume for_storage_body_post_land_at[continue]:
  `raw = INR ContinueException` by
    (qpat_assum `stmt_lands (InLoop _ _) _ _ _`
       (mp_tac o REWRITE_RULE [stmt_lands_def]) >> asm_rewrite_tac[] >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
  simp[NoAsms, vyperInterpreterTheory.handle_loop_exception_def, return_def] >>
  qexistsl [`sc`, `rest`] >>
  simp[evaluation_state_accfupds, gas_origin_ptr_path_rules, cenv_top_ext_refl] >>
  conj_tac >-
    (qpat_assum `stmt_lands (InLoop _ _) _ _ _` mp_tac >> simp[NoAsms, stmt_lands_def]) >>
  conj_tac >-
    (qpat_assum `stmt_lands (InLoop _ _) _ _ _` mp_tac >> simp[NoAsms, stmt_lands_def]) >>
  qpat_assum `!name b sz. local_region c0 rest t name b sz ==> _` mp_tac >>
  qpat_assum `w2n dst + nb < 2 ** 256` mp_tac >>
  simp[NoAsms, ADD_COMM]
QED

Resume for_storage_body_post_land_at[normal]:
  qpat_x_assum `raw = INL ()` SUBST_ALL_TAC >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) []
    (OK (jump_to incr t),G1,tn1)` by suspend "normal_jump" >>
  `Fr c0 (ef with scopes := rest) (jump_to incr t) G1 tn1` by suspend "jump_frame" >>
  `return_buf_sep d c0 (ef with scopes := rest) (jump_to incr t)` by
    simp[return_buf_sep_jump] >>
  simp[NoAsms] >> qexistsl [`sc`, `rest`] >>
  `eval_operand bop (jump_to incr t) = SOME slot` by
    (Cases_on `bop` >> fs[eval_operand_def, jump_to_def, lookup_var_def]) >>
  simp[evaluation_state_accfupds, stmt_state_rel_jump_to,
    ghost_inv_at_jump, return_buf_frame_jump_to, ret_pc_ok_jump_to,
    jump_to_def, lookup_var_def, cenv_top_ext_refl] >>
  conj_tac >-
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl [`G1`, `t`, `tn1`] >> simp[NoAsms, lookup_var_def] >> first_assum ACCEPT_TAC) >>
  `!name b sz. local_region c0 rest
    (t with <|vs_prev_bb := SOME t.vs_current_bb;
              vs_current_bb := incr; vs_inst_idx := 0|>) name b sz =
   local_region c0 rest t name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> simp[lookup_var_def]) >>
  asm_rewrite_tac[] >>
  qpat_assum `!name b sz. local_region c0 rest t name b sz ==> _` mp_tac >>
  qpat_assum `w2n dst + nb < 2 ** 256` mp_tac >>
  simp[NoAsms, ADD_COMM]
QED

Resume for_storage_body_post_land_at[normal_jump]:
  `~block_is_terminated sb1` by metis_tac[] >>
  `emit_inst JMP [Label incr] [] sb1 = ((),sj)` by
    (qpat_assum `emit_jmp_if_not_terminated incr sb1 = _` mp_tac >>
     simp[NoAsms, emit_jmp_if_not_terminated_def, comp_get_def, comp_bind_def] >>
     asm_rewrite_tac[]) >>
  `t.vs_current_bb = sb1.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb1.cs_current_insts` by
    (qpat_assum `stmt_lands (InLoop _ _) _ _ _` mp_tac >> simp[NoAsms, stmt_lands_def]) >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx =
      SOME (mk_inst sb1.cs_next_id JMP [Label incr] [])` by
    (asm_rewrite_tac[] >> irule place_copy_emit_instruction >>
     qexists `sj` >> asm_rewrite_tac[]) >>
  `allocas_from lo t` by
    (qpat_assum `ghost_inv_at _ _ _ c0 _ _ _ _ t` mp_tac >> simp[NoAsms, ghost_inv_at_def]) >>
  irule fragGasOriginPtrLoopTheory.jump_origin_ptr_path >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`bb`, `mk_inst sb1.cs_next_id JMP [Label incr] []`] >>
  asm_rewrite_tac[] >>
  simp[NoAsms, mk_inst_def, is_terminator_def,
    unitTransformDefsTheory.inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    venomExecPropsTheory.step_jmp_behavior] >>
  simp[ptrSafeRunTheory.ptr_safe_step_def, ptrSafeRunTheory.ptr_inst_ok_def,
    access_ok_def, taint_ok_def, mk_inst_def, step_inst_non_invoke,
    venomExecPropsTheory.step_jmp_behavior, jump_to_def,
    source_memory_write_ranges_def, source_memory_read_ranges_def, op_taint_def]
QED

Resume for_storage_body_post_land_at[jump_frame]:
  qpat_assum `Fr c0 (ef with scopes := rest) t G1 tn1` mp_tac >>
  simp[NoAsms, Abbr `Fr`] >> strip_tac >>
  conj_tac >- (irule alloca_history_jump >> simp[jump_to_def] >>
    qexists `t` >> simp[]) >>
  `allocas_below_fmp (jump_to incr t) = allocas_below_fmp t` by
    simp[allocas_below_fmp_def, jump_to_def] >>
  asm_rewrite_tac[] >> simp[jump_to_def, lookup_var_def] >>
  irule alloca_frame_same_state >> qexists `t` >> simp[jump_to_def]
QED

Finalise for_storage_body_post_land_at
