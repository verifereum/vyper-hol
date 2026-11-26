(* Enter the selected linked If arm at the condition's endpoint. *)
Theory bodyIfArmEntryMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullShared bodyFullIfExpReach
  bodyInvSplit bodyMemoryDefs bodyPtrDefs compileEnv contextRawReachable
  exprLoweringProps freshWrites loweringPosts loweringStateRelDefs
  stmtSimDefs stmtSimIfProps stmtSimProps fragGasEmitCtrl gasExplicitSites
  allocaHistory fragExec gasShadow list ptrDiscipline vyperStorageFootprint vyperStorageTrace
  vyperInterpreter vyperState venomExecSemantics venomInst venomState finite_map

Theorem if_entry_immutable_frame[local]:
  immutable_frame_mods func cenv cx
    (mid with scopes := FEMPTY :: mid.scopes) (jump_to lbl t) <=>
  immutable_frame_mods func cenv cx mid t
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutables_rel_def, immutable_alloca_sep_def,
       immutable_decl_sep_alt, jump_to_def, local_region_def, lookup_scopes_def,
       lookup_var_def]
QED

Theorem if_entry_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx
    (mid with scopes := FEMPTY :: mid.scopes) G tn (jump_to lbl t) <=>
  ghost_inv_at_mods D lo d cenv cx mid G tn t
Proof
  simp[ghost_inv_at_mods_def, lookup_scopes_def, jump_to_def,
       ptr_covers_def, stor_taint_ok_at_def, lookup_var_def, allocas_from_def] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  qmatch_goalsub_rename_tac `return_buf_ptr (SOME ds) _ _ _ _` >>
  PairCases_on `ds` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem if_entry_storage[local]:
  storage_well_formed_on cx (mid with scopes := FEMPTY :: mid.scopes) regions <=>
  storage_well_formed_on cx mid regions
Proof
  irule storage_well_formed_on_backends >> simp[]
QED

Theorem if_entry_headroom[local]:
  MEM func ctx.ctx_functions /\
  (ctx_has_dalloca ctx ==> !bb. MEM bb func.fn_blocks ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,G,tn) ==>
  !fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_fmp_headroom inst s
Proof
  strip_tac >> Cases_on `ctx_has_dalloca ctx`
  >- metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom] >>
  rpt gen_tac >> disch_tac >> drule_all frag_reachable_members >> strip_tac >>
  simp[unitTransformDefsTheory.dalloca_fmp_headroom_def] >> disch_tac >>
  `ctx_has_dalloca ctx` by
    (simp_tac bool_ss [ctx_has_dalloca_def, EXISTS_MEM] >>
     qexists_tac `fn` >> simp[] >> qexists_tac `inst` >> simp[]) >> fs[]
QED

Theorem if_arm_entry_run_mods:
  expr_type e = BaseT BoolT /\
  gas_admissible (eval_stmt cx (If e yes no)) (stmt_res_ok lctx) es /\
  mid.gas_obs = [] /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs ++ tail) =
       (INL (BoolV b), mid with gas_obs := tail)) /\
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmts_env cenv lctx ty (if b then yes else no))
    (stmts_env (gas_shadow_env T cenv) lctx ty
       (if b then MAP gas_shadow_stmt yes else MAP gas_shadow_stmt no))
    (eval_stmts cx (if b then yes else no)) (mid with scopes := FEMPTY :: mid.scopes) /\
  stmts_env cenv lctx ty (if b then yes else no) entry = (cenvb,last) /\
  stmts_env (gas_shadow_env T cenv) lctx ty
    (if b then MAP gas_shadow_stmt yes else MAP gas_shadow_stmt no) sentry =
       (gas_shadow_env T cenvb,slast) /\
  gas_shadow_state entry sentry /\ gas_shadow_state last slast /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code entry last func /\ fn_has_code sentry slast shadow_func /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> !bb. MEM bb func.fn_blocks ==>
     phi_prefix_length bb.bb_instructions = 0) /\
  emit_inst JNZ [op; Label tl; Label el] [] pre = ((),post) /\
  fn_has_code pre post func /\
  pre.cs_current_bb = cond.cs_current_bb /\ pre.cs_current_insts = cond.cs_current_insts /\
  entry.cs_current_bb = (if b then tl else el) /\ entry.cs_current_insts = [] /\
  sa.cs_next_var <= entry.cs_next_var /\ local_ptrs_reserved cenv sa /\
  ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~t.vs_halted /\
  (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa cond s0 mid (BoolV b) op t /\
    t.vs_current_bb = cond.cs_current_bb /\ t.vs_inst_idx = LENGTH cond.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv e) (BoolV b) op G1 tn1 t) ==>
  (let u = jump_to (if b then tl else el) t;
       pushed = mid with scopes := FEMPTY :: mid.scopes
   in
    (!H. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK u,G1,tn1)) /\
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (eval_stmts cx (if b then yes else no)) (pushed,u,G1,tn1)
      (\H res ee G tn v. ?cb.
        stmt_lands lctx last res v /\ ~v.vs_halted /\
        (res = INL () ==> ~block_is_terminated last /\ cb = cenvb) /\
        cenv_top_ext cenv cb ee.scopes /\ stmt_state_rel H ctx func cb cx ee v /\
        immutable_frame_mods func cb cx ee v /\ storage_well_formed_on cx ee (FST H) /\
        return_buf_frame d cb last v /\ alloca_history func v /\ return_buf_sep d cb ee v /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\ u.vs_alloca_next <= v.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d cb cx ee G tn v /\
        (!x w. not_fresh_at entry x /\ lookup_var x u = SOME w ==> lookup_var x v = SOME w) /\
        (!aid ba. FLOOKUP u.vs_allocas aid = SOME ba ==> FLOOKUP v.vs_allocas aid = SOME ba) /\
        (!x. not_fresh_at entry x ==>
             FLOOKUP G x = FLOOKUP G1 x /\ op_taint tn (Var x) = op_taint tn1 (Var x)) /\
        alloca_frame cenv pushed entry u cb ee v /\
        (!aid off sz i.
          FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ aid < entry.cs_next_id /\
          (!n ba sz'. local_region cenv pushed.scopes u n ba sz' ==>
                        off + sz <= ba \/ ba + sz' <= off) /\
          off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn1.t_mem))
      (\H res ee gt r.
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==>
          !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by fs[storage_trace_domain_def, Abbr `H0`] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    (fs[expr_post_mods_def] >> drule_all if_condition_operand >>
     simp[valueEncodingTheory.val_to_w256_def]) >>
  `op_taint tn1 op = {} /\ allocas_from lo t` by
    fs[ptr_val_ok_def, ghost_inv_at_mods_def] >>
  `!H. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK (jump_to (if b then tl else el) t),G1,tn1)` by
    (gen_tac >> irule emit_jnz_origin_ptr >> simp[] >>
     qexistsl_tac [`op`, `pre`, `post`] >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `stmt_frag_full_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_full_mods_def] >>
  disch_then (qspecl_then [`st0`, `entry`, `last`, `sentry`, `slast`,
    `jump_to (if b then tl else el) t`, `G1`, `tn1`, `cenvb`] mp_tac) >>
  (impl_tac >- suspend "inputs") >> simp[]
QED

Resume if_arm_entry_run_mods[inputs]:
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
       (INL (BoolV b),mid)` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     pop_assum (fn th => rewrite_tac [th, APPEND_NIL])) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    (drule_all valid_horizon_frame >> simp[]) >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by (first_assum irule >> simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w` by
    fs[expr_post_mods_def, expr_post_def] >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule eval_read_preserves_scopes_dom >> simp[]) >>
  `return_buf_sep d cenv mid t` by
    (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >> simp[] >>
     qexistsl_tac [`H0`, `ctx`, `cx`, `es`, `func`, `s0`, `sa`] >> simp[]) >>
  `ret_pc_ok cenv entry t` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  `return_buf_frame d cenv entry t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  `!fn inst s. frag_reachable ctx func (jump_to (if b then tl else el) t) fn inst s ==>
                 dalloca_fmp_headroom inst s` by
    (rpt gen_tac >> disch_tac >> irule if_entry_headroom >>
     qpat_assum `!H. gas_origin_ptr_path _ _ _ _` (qspec_then `H0` assume_tac) >>
     goal_assum (drule_at Any) >> simp[] >> qexists_tac `fn` >> simp[] >>
     first_assum ACCEPT_TAC) >>
  `alloca_history func (jump_to (if b then tl else el) t)` by
    (irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `t` >> simp[]) >>
  `local_ptrs_reserved cenv entry` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at entry x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `gas_admissible (eval_stmts cx (if b then yes else no)) (stmt_res_ok lctx)
     (mid with scopes := FEMPTY :: mid.scopes)` by
    (drule_all if_branch_admissible >> simp[]) >>
  `(allocas_below_fmp (jump_to (if b then tl else el) t) <=> allocas_below_fmp t)` by
    simp[allocas_below_fmp_def, jump_to_def] >>
  simp[return_buf_sep_push, return_buf_sep_jump, ret_pc_ok_jump_to,
       return_buf_frame_jump_to, block_is_terminated_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!fn inst s. frag_reachable _ _ (jump_to _ _) _ _ _ ==> _` drule >> simp[]) >>
  conj_tac
  >- (simp[stmt_state_rel_jump_to, stmt_state_rel_push_scope,
           if_entry_immutable_frame, if_entry_ghost, if_entry_storage] >>
      gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (drule_then strip_assume_tac) >> fs[expr_post_mods_def, expr_post_def]) >>
  simp[jump_to_def]
QED
Finalise if_arm_entry_run_mods
