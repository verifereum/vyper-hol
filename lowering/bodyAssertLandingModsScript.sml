(* The selected control action of an assertion whose condition has returned.
   The successful jump keeps the whole linked frame at that endpoint. *)
Theory bodyAssertLandingMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullShared
  bodyFullHashKeccakFixed fragGasEmitCtrl fragGasOriginPtrLoop
  stmtSimAssertProps stmtSimIfProps stmtSimDefs exprSimDefs
  loweringPosts loweringStateRelDefs bodyInvSplit bodyPtrDefs bodyMemoryDefs
  gasContext gasOutcomeFull gasStorage vyperStorageTrace vyperStorageFootprint
  ptrDiscipline compileEnv exprLoweringProps emitHelperProps
  stmtLowering vyperInterpreter vyperState venomExecSemantics venomState
  fragExec allocaHistory

Theorem immutable_frame_assert_jump[local]:
  immutable_frame_mods func cenv cx es (jump_to lbl s) <=>
  immutable_frame_mods func cenv cx es s
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutables_rel_def, immutable_alloca_sep_def,
       jump_to_def, local_region_def, lookup_var_def]
QED

Theorem ghost_inv_assert_jump[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn (jump_to lbl s) <=>
  ghost_inv_at_mods D lo d cenv cx es G tn s
Proof
  simp[ghost_inv_at_mods_def, jump_to_def, ptr_covers_def, stor_taint_ok_at_def,
       lookup_var_def, allocas_from_def] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

(* The landing depends only on the empty continuation block, not the
   failure arm's code. This also serves assertions with a payload. *)
Theorem assert_success_landing_mods:
  expr_post_mods H ctx func cenv cx e es sa sc s0 mid (BoolV T) op t /\
  ~t.vs_halted /\ sb.cs_current_insts = [] /\
  sa.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  MAP FDOM mid.scopes = MAP FDOM es.scopes /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  (!bw capacity. d = SOME (bw, capacity) ==>
     allocas_from (w2n bw + capacity) t) /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
  stmt_lands lctx sb (INL ()) (jump_to sb.cs_current_bb t) /\
  ~(jump_to sb.cs_current_bb t).vs_halted /\ ~block_is_terminated sb /\
  cenv_top_ext cenv cenv mid.scopes /\
  stmt_state_rel H ctx func cenv cx mid (jump_to sb.cs_current_bb t) /\
  immutable_frame_mods func cenv cx mid (jump_to sb.cs_current_bb t) /\
  storage_well_formed_on cx mid (FST H) /\
  return_buf_frame d cenv sb (jump_to sb.cs_current_bb t) /\
  alloca_history func (jump_to sb.cs_current_bb t) /\
  return_buf_sep d cenv mid (jump_to sb.cs_current_bb t) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp (jump_to sb.cs_current_bb t)) /\
  s0.vs_alloca_next <= (jump_to sb.cs_current_bb t).vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G tn (jump_to sb.cs_current_bb t) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x (jump_to sb.cs_current_bb t) = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP (jump_to sb.cs_current_bb t).vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es sa s0 cenv mid (jump_to sb.cs_current_bb t) /\
  (!aid off sz i.
     FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                off + sz <= b \/ b + sz' <= off) /\
     off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)
Proof
  simp[expr_post_mods_def] >> strip_tac >>
  drule_all assert_success_post_mem >>
  disch_then (qspec_then `lctx` mp_tac) >>
  strip_tac >> gvs[] >>
  `alloca_frame cenv es sa s0 cenv mid t` by
    (drule_all expr_post_alloca_frame >> simp[]) >>
  `return_buf_sep d cenv mid t` by
    (irule return_buf_sep_locals_kept >> simp[] >>
     qexistsl_tac [`H`, `ctx`, `cx`, `es`, `func`, `s0`, `sa`] >>
     fs[expr_post_def]) >>
  `(allocas_below_fmp (jump_to sb.cs_current_bb t) <=> allocas_below_fmp t)` by
    simp[allocas_below_fmp_def, jump_to_def] >>
  `alloca_frame cenv es sa s0 cenv mid (jump_to sb.cs_current_bb t)` by
    (irule alloca_frame_same_state >> qexists_tac `t` >> simp[jump_to_def]) >>
  fs[immutable_frame_assert_jump, ghost_inv_assert_jump, return_buf_sep_jump,
     ghost_kept_at_def] >> rpt strip_tac >>
  qpat_assum `!a off sz i. FLOOKUP s0.vs_allocas a = _ /\ _ ==> i IN tn0.t_mem`
    (qspecl_then [`aid`, `off`, `sz`, `i`] mp_tac) >> simp[] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem admissible_bare_assert_bool[local]:
  (ak = AssertBare \/ ak = AssertUnreachable) /\
  gas_admissible (eval_stmt cx (Assert e ak)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := xs ++ tail) = (INL v, mid with gas_obs := tail)) ==>
  ?b. v = BoolV b
Proof
  strip_tac >>
  Cases_on `eval_stmt cx (Assert e ak) (es with gas_obs := xs)` >>
  drule_all gas_admissible_result >> strip_tac >>
  drule_at (Pat `eval_stmt _ _ _ = _`) eval_assert_forced_ok >>
  disch_then (qspec_then `lctx` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!tail. _ = _` (qspec_then `[]` assume_tac) >>
  gvs[bind_def]
QED

Theorem assert_failure_path_mods[local]:
  (ak = AssertBare \/ ak = AssertUnreachable) /\
  emit_inst (if ak = AssertBare then REVERT else INVALID)
    (if ak = AssertBare then [Lit 0w; Lit 0w] else []) [] sf = ((),sf') /\
  fn_has_code sf sf' func /\ sf.cs_current_bb = fl /\ sf.cs_current_insts = [] /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ allocas_from lo t /\
  ~t.vs_halted ==>
  ?a u. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
              (jump_to fl t,G,tn) [] (Abort a u,G,tn)) /\
        expr_exit
          (INR (AssertException (if ak = AssertBare then "" else "UNREACHABLE"))
             : unit + exception) (Abort a u)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qabbrev_tac `opc = if ak = AssertBare then REVERT else INVALID` >>
  qabbrev_tac `ops = if ak = AssertBare then [Lit 0w; Lit 0w] else []` >>
  `?a u. step_inst_base (mk_inst sf.cs_next_id opc ops [])
           (jump_to fl t) = Abort a u /\
         expr_exit
           (INR (AssertException (if ak = AssertBare then "" else "UNREACHABLE"))
              : unit + exception) (Abort a u)` by
    (qpat_x_assum `ak = _ \/ _` strip_assume_tac >>
     gvs[Abbr `opc`, Abbr `ops`, expr_exit_def]
     >- simp[step_revert_zero] >>
     qexists_tac `ExHalt_abort` >> simp[step_invalid]) >>
  qexistsl_tac [`a`, `u`] >> simp[] >> gen_tac >>
  irule emit_abort_origin_ptr >>
  `allocas_below_fmp (jump_to fl t) <=> allocas_below_fmp t` by
    simp[allocas_below_fmp_def, jump_to_def] >>
  `(allocas_from lo (jump_to fl t) <=> allocas_from lo t)` by
    simp[NoAsms, allocas_from_def, jump_to_def] >>
  simp[] >> qexistsl_tac [`opc`, `ops`, `sf`, `sf'`] >>
  qpat_x_assum `ak = _ \/ _` strip_assume_tac >>
  gvs[Abbr `opc`, Abbr `ops`, jump_to_def]
QED

Theorem assert_selected_landing_mods:
  (ak = AssertBare \/ ak = AssertUnreachable) /\
  stmt_env cenv lctx ty (Assert e ak) sa = (cenv',sb) /\
  lower_value compile_expr cenv (BaseT BoolT) e sa = (op,sc) /\
  fn_has_code sa sb func /\ expr_type e = BaseT BoolT /\
  gas_admissible (eval_stmt cx (Assert e ak)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := xs ++ tail) = (INL v, mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~t.vs_halted /\
  t.vs_current_bb = sc.cs_current_bb /\
  t.vs_inst_idx = LENGTH sc.cs_current_insts /\
  local_ptrs_reserved cenv sa /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  (!bw capacity. d = SOME (bw, capacity) ==>
     allocas_from (w2n bw + capacity) t) /\
  ptr_val_ok cx (BaseT BoolT) v op G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post_mods H ctx func cenv cx e es sa sc s0 mid v op t /\
     ghost_inv_at_mods (DF H) lo d cenv cx mid G tn t) ==>
  ?b. v = BoolV b /\
    if b then
      !H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (t,G,tn) [] (OK (jump_to sb.cs_current_bb t),G,tn) /\
        stmt_lands lctx sb (INL ()) (jump_to sb.cs_current_bb t) /\
        ~(jump_to sb.cs_current_bb t).vs_halted /\
        (~block_is_terminated sb /\ cenv' = cenv) /\
        cenv_top_ext cenv cenv mid.scopes /\
        stmt_state_rel H ctx func cenv cx mid (jump_to sb.cs_current_bb t) /\
        immutable_frame_mods func cenv cx mid (jump_to sb.cs_current_bb t) /\
        storage_well_formed_on cx mid (FST H) /\
        return_buf_frame d cenv sb (jump_to sb.cs_current_bb t) /\
        alloca_history func (jump_to sb.cs_current_bb t) /\
        return_buf_sep d cenv mid (jump_to sb.cs_current_bb t) /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp (jump_to sb.cs_current_bb t)) /\
        s0.vs_alloca_next <= (jump_to sb.cs_current_bb t).vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d cenv cx mid G tn (jump_to sb.cs_current_bb t) /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
               lookup_var x (jump_to sb.cs_current_bb t) = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP (jump_to sb.cs_current_bb t).vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa x ==>
             FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame cenv es sa s0 cenv mid (jump_to sb.cs_current_bb t) /\
        (!aid off sz i.
           FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
           (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                      off + sz <= b \/ b + sz' <= off) /\
           off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)
    else
      ?a u. (!H. valid_horizon cx st0 H mid.storage_trace ==>
               gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
                 (t,G,tn) [] (Abort a u,G,tn)) /\
            expr_exit
              (INR (AssertException (if ak = AssertBare then "" else "UNREACHABLE"))
                 : unit + exception) (Abort a u)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_assum `stmt_env _ _ _ (Assert e ak) _ = _`
    (mp_then Any mp_tac compile_assert_parts) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `op' = op /\ s1 = sc` by fs[] >>
  qpat_x_assum `op' = op` SUBST_ALL_TAC >>
  qpat_x_assum `s1 = sc` SUBST_ALL_TAC >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `cs_extends sa sc` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  qpat_assum `cs_extends sa sc`
    (mp_then (Pos hd) mp_tac assert_compiler_code) >>
  disch_then (drule_all_then strip_assume_tac) >>
  drule_all admissible_bare_assert_bool >> strip_tac >>
  qpat_x_assum `v = BoolV _` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    (fs[expr_post_mods_def] >> drule_all if_condition_operand >>
     simp[valueEncodingTheory.val_to_w256_def]) >>
  `op_taint tn op = {} /\ allocas_from lo t` by
    fs[ptr_val_ok_def, ghost_inv_at_mods_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
            (t,G,tn) [] (OK (jump_to (if b then ok else fl) t),G,tn)` by
    (gen_tac >> irule emit_jnz_origin_ptr >> simp[] >>
     qexistsl_tac [`op`, `s3`, `s4`] >> simp[]) >>
  qexists_tac `b` >> Cases_on `b` >> simp[]
  >- suspend "true" >>
  suspend "false"
QED

Resume assert_selected_landing_mods[true]:
  gen_tac >> disch_tac >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `?ext. mid.storage_trace = es.storage_trace ++ ext` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_all storage_trace_frame_prefix >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    metis_tac[valid_horizon_append] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then assume_tac) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    fs[expr_post_mods_def, expr_post_def, locals_kept_def] >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (drule_then strip_assume_tac (cj 2 compile_expr_grows) >>
     imp_res_tac (cj 4 fresh_label_props) >>
     imp_res_tac (cj 5 new_block_props) >>
     imp_res_tac (cj 5 emit_inst_extends) >> simp[]) >>
  conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
       (qspec_then `DF H` (ACCEPT_TAC o REWRITE_RULE [COND_CLAUSES]))) >>
  drule_all assert_success_landing_mods >>
  disch_then (qspec_then `lctx` mp_tac) >>
  simp[] >> disch_then strip_assume_tac >> first_assum ACCEPT_TAC
QED

Resume assert_selected_landing_mods[false]:
  drule_all assert_failure_path_mods >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`a`, `u`] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> disch_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) _ _`
    (qspec_then `DF H` (mp_tac o REWRITE_RULE [COND_CLAUSES])) >>
  disch_then (mp_then (Pos hd) mp_tac gas_origin_ptr_path_trans) >>
  qpat_assum `!D. gas_origin_ptr_path _ (jump_to fl t,G,tn) _ _`
    (qspec_then `DF H` (fn th => disch_then (ACCEPT_TAC o C MATCH_MP th)))
QED

Finalise assert_selected_landing_mods
