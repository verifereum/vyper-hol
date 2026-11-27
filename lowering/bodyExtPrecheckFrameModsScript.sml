(* The optional code test leaves the linked ready frame at the fetched call. *)
Theory bodyExtPrecheckFrameMods
Ancestors
  bodyFullExtCallPrecheck bodyForRangeScalarFrameMods bodyFullPathHistory
  bodyPtrMakeArrayEmission bodyFullHashKeccakFixed freshWrites allocaHistory
  exprSimHashBoundary exprSimExtCallCase exprLoweringProps loweringPosts
  exprSimDefs exprSafeOperand loweringStateRelDefs bodyPtrDefs
  stateRelProj accountsRelProps vyperRuntimeAccounts vyperInterpreter
  exprLowering compileEnv emitHelper fragGasOriginPtr venomState finite_map words
  venomExecSemantics venomInst fragExec contractInvContextProps
  bodyFullShadowBodyInv bodyFullPredsMods ptrDiscipline

Theorem extcheck_code_cut[local]:
  compile_extcodesize_check addr a = ((),b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id
Proof
  simp[compile_extcodesize_check_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  disch_then (SUBST1_TAC o SYM) >> simp[]
QED

Theorem extcheck_nonzero[local]:
  stmt_state_rel H ctx func cenv cx ee s /\ accounts_runtime_well_typed ee.accounts /\
  w2w aw = target ==>
  ((n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32) <> 0w <=>
   ext_call_precheck_ok F NoneT target ee.accounts)
Proof
  strip_tac >>
  drule stmt_state_rel_state_rel >> disch_then (strip_assume_tac o MATCH_MP state_rel_accounts) >>
  drule accounts_agree_lookup >> disch_then (qspec_then `target` strip_assume_tac) >>
  `LENGTH (lookup_account target ee.accounts).code <= 24576` by
    fs[accounts_runtime_well_typed_def, account_runtime_well_typed_def] >>
  `LENGTH (lookup_account target ee.accounts).code < dimword (:256)` by
    (simp[dimword_def] >> decide_tac) >>
  simp[ext_call_precheck_ok_def, ext_call_has_code_def, listTheory.NULL_EQ,
       n2w_11, listTheory.LENGTH_NIL]
QED

Theorem extcheck_optional_path[local]:
  (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr
   else comp_return ()) a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ w2w aw = target /\ op_taint tn addr = {} /\
  accounts_runtime_well_typed ee.accounts /\ allocas_from lo s /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee s) ==>
  !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (if ext_call_precheck_ok skip ret_type target ee.accounts then
         OK (if ret_type = NoneT /\ ~skip then
               update_var (STRING #"%" (toString a.cs_next_var))
                 (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s
               with vs_inst_idx := LENGTH b.cs_current_insts
             else s)
       else Abort Revert_abort (revert_state (set_returndata []
           (update_var (STRING #"%" (toString a.cs_next_var))
              (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s
            with vs_inst_idx := SUC s.vs_inst_idx))),
       (if ret_type = NoneT /\ ~skip then G \\ (STRING #"%" (toString a.cs_next_var)) else G),
       (if ret_type = NoneT /\ ~skip then
          tn with t_var := tn.t_var |+ (STRING #"%" (toString a.cs_next_var),{})
        else tn))
Proof
  strip_tac >> Cases_on `ret_type = NoneT /\ ~skip` >> simp[Excl "n2w_eq_0"]
  >- (fs[] >> rpt strip_tac >>
      `stmt_state_rel H ctx func cenv cx ee s` by simp[] >>
      drule stmt_state_rel_allocas_below_fmp >> strip_tac >>
      drule_all extcall_codesize_checked_path >>
      disch_then (qspecl_then [`explicit`,`PG`,`G`,`DF H`] mp_tac) >>
      drule_all extcheck_nonzero >>
      Cases_on `ext_call_precheck_ok F NoneT target ee.accounts` >> gvs[Excl "n2w_eq_0"])
  >> `ext_call_precheck_ok skip ret_type target ee.accounts` by
       (Cases_on `ret_type` >> fs[ext_call_precheck_ok_def])
  >> simp[] >> rpt strip_tac >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED

Theorem extcheck_scalar_observations[local]:
  ~not_fresh_at sp out /\ sa.cs_next_var <= sp.cs_next_var ==>
  (!x. not_fresh_at sp x ==>
    lookup_var x (update_var out w s with vs_inst_idx := idx) = lookup_var x s /\
    FLOOKUP (G \\ out) x = FLOOKUP G x /\
    op_taint (tn with t_var := tn.t_var |+ (out,{})) (Var x) = op_taint tn (Var x)) /\
  (!op. safe_operand sp op ==>
    eval_operand op (update_var out w s with vs_inst_idx := idx) = eval_operand op s /\
    op_taint (tn with t_var := tn.t_var |+ (out,{})) op = op_taint tn op /\
    (!x. op = Var x ==> FLOOKUP (G \\ out) x = FLOOKUP G x)) /\
  (ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
    ghost_kept_at lo cenv es sa G0 tn0 s0 (G \\ out)
      (tn with t_var := tn.t_var |+ (out,{}))) /\
  (!cx ty v op. safe_operand sp op /\ ptr_mem_ok cx ty v op G tn s ==>
    ptr_mem_ok cx ty v op (G \\ out) (tn with t_var := tn.t_var |+ (out,{}))
      (update_var out w s with vs_inst_idx := idx))
Proof
  strip_tac >>
  `!x. not_fresh_at sp x ==> x <> out` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> x <> out` by metis_tac[not_fresh_at_mono] >>
  conj_tac >- (rpt strip_tac >>
    simp[update_var_def, lookup_var_def, op_taint_def, FLOOKUP_UPDATE,
         fmap_domsub, FLOOKUP_DRESTRICT]) >>
  conj_tac >- (Cases >> simp[safe_operand_def, eval_operand_def, update_var_def,
    lookup_var_def, op_taint_def, FLOOKUP_UPDATE, fmap_domsub, FLOOKUP_DRESTRICT] >>
    metis_tac[]) >>
  conj_tac >- (simp[ghost_kept_at_def] >> rpt strip_tac >>
    fs[op_taint_def, FLOOKUP_UPDATE, fmap_domsub, FLOOKUP_DRESTRICT] >>
    metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `op` >>
  fs[safe_operand_def, ptr_mem_ok_def, eval_operand_def, update_var_def,
     lookup_var_def, fmap_domsub, FLOOKUP_DRESTRICT] >>
  rename1 `FLOOKUP _ p` >> `p <> out` by metis_tac[] >> fs[FLOOKUP_UPDATE]
QED

Theorem extcheck_request_scalar[local]:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\ ~not_fresh_at sp out /\
  sp.cs_next_var <= sb.cs_next_var /\ sp.cs_next_id <= sb.cs_next_id /\
  sb.cs_current_bb = sp.cs_current_bb ==>
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sb stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee
    (update_var out w s with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rewrite_tac[extcall_request_ready_def] >> strip_tac >>
  qabbrev_tac `u = update_var out w s with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `!x. not_fresh_at sp x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> `x <> out` by metis_tac[] >>
     simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `!op. safe_operand sp op ==> eval_operand op u = eval_operand op s` by
    (Cases >> simp[safe_operand_def, eval_operand_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee u /\ storage_well_formed_on cx ee (FST H)` by
    (rpt strip_tac >> simp[Abbr `u`, stmt_state_rel_inst_idx] >>
     irule hash_readonly_state_rel >> qexistsl_tac [`s`,`sp`] >>
     simp[update_var_def] >> rpt strip_tac >>
     `x <> out` by metis_tac[] >> simp[lookup_var_def, FLOOKUP_UPDATE]) >>
  `!n b sz. local_region cenv ee.scopes u n b sz <=> local_region cenv ee.scopes s n b sz` by
    (simp[local_region_def] >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `wb_frame cenv es ee sa s0 u` by
    (fs[wb_frame_def] >> simp[wb_frame_def] >> conj_tac
     >- metis_tac[not_fresh_at_mono] >>
     simp[Abbr `u`, update_var_def] >> conj_tac >- metis_tac[] >>
     irule exprSimPropsTheory.locals_kept_mem_tail >> qexists_tac `s` >> simp[]) >>
  `local_ptrs_reserved cenv sb /\ EVERY (safe_operand sb) [addr;value;gas;buf;off;len;default_op]` by
    (fs[] >> metis_tac[local_ptrs_reserved_next_var, safe_operand_mono]) >>
  `extcall_default_ready cx ret_type has_default default_op default_ty default_opt u` by
    (fs[extcall_default_ready_def, expr_val_rel_def, Abbr `u`, update_var_def, read_memory_def] >>
     metis_tac[]) >>
  `!a n. read_memory a n u = read_memory a n s` by
     simp[Abbr `u`, update_var_def, read_memory_def] >>
  `u.vs_allocas = s.vs_allocas /\ ~u.vs_halted /\
   u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts` by
     simp[Abbr `u`, update_var_def] >>
  fs[] >> conj_tac >- (qexists_tac `H` >> simp[]) >>
  conj_tac >- (qexistsl_tac [`live`,`buf_size`] >> simp[]) >> metis_tac[]
QED

(* A scalar update and cursor move do not touch either linked frame. *)
Theorem extcheck_linked_frames[local]:
  local_ptrs_reserved cenv sp /\ ~not_fresh_at sp out /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) ==>
  let t = update_var out w s with vs_inst_idx := idx in
  (immutable_frame_mods func cenv cx ee s ==> immutable_frame_mods func cenv cx ee t) /\
  (ghost_inv_at_mods D lo d cenv cx ee G tn s ==>
   ghost_inv_at_mods D lo d cenv cx ee (G \\ out) (tn with t_var := tn.t_var |+ (out,{})) t)
Proof
  strip_tac >> simp[LET_THM] >>
  `!x. not_fresh_at sp x ==> x <> out` by metis_tac[] >>
  conj_tac
  >- (strip_tac >> irule immutable_frame_mods_exterior_frame >>
      goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >> qexists_tac `sp` >>
      simp[update_var_def,lookup_var_def,FLOOKUP_UPDATE]) >>
  strip_tac >> irule ghost_inv_at_mods_exterior_frame >>
  goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >> qexists_tac `sp` >>
  simp[update_var_def,lookup_var_def,op_taint_def,FLOOKUP_UPDATE,fmap_domsub,FLOOKUP_DRESTRICT]
QED

Theorem extcall_precheck_to_call_mods:
  (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr
   else comp_return ()) sp = ((),sb) /\ fn_has_code sp sb func /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) sb = (success,sc) /\
  fn_has_code sb sc func /\
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  op_taint tn addr = {} /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  immutable_frame_mods func cenv cx ee s /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?r G1 tn1.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G1,tn1)) /\
    if ext_call_precheck_ok skip ret_type target ee.accounts then
      ?t out bb. r = OK t /\ success = Var out /\ ~not_fresh_at sb out /\
        lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb t.vs_inst_idx = SOME
          (mk_inst sb.cs_next_id (if stat then STATICCALL else CALL)
             (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
              else [gas;addr;value;off;len;buf;Lit (n2w cap)]) [out]) /\
        t.vs_current_bb = sc.cs_current_bb /\ SUC t.vs_inst_idx = LENGTH sc.cs_current_insts /\
        extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sb stat
          addr value gas buf off len cap target value_opt calldata has_default
          default_op default_ty default_opt ee t /\
        immutable_frame_mods func cenv cx ee t /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t) /\
        allocas_from lo t /\ lo <= t.vs_alloca_next /\ alloca_history func t /\
        t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
        t.vs_alloca_next = s.vs_alloca_next /\ tn1.t_mem = tn.t_mem /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==> stor_taint_ok_at (DF H) tn1 t) /\
        (!x. not_fresh_at sp x ==> lookup_var x t = lookup_var x s /\
          FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
        (!op. safe_operand sp op ==> eval_operand op t = eval_operand op s /\
          op_taint tn1 op = op_taint tn op /\
          (!x. op = Var x ==> FLOOKUP G1 x = FLOOKUP G x)) /\
        (!ty v op. safe_operand sp op /\ ptr_mem_ok cx ty v op G tn s ==>
          ptr_mem_ok cx ty v op G1 tn1 t)
    else exit_result r /\ expr_exit (INR (Error (RuntimeError "ExtCall target has no code"))) r
Proof
  strip_tac >>
  qhdtm_assum `extcall_request_ready` (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee s` by simp[] >>
  mp_tac (Q.INST [`a` |-> `sp`, `b` |-> `sb`] extcheck_optional_path) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  qabbrev_tac `chk_out = STRING #"%" (toString sp.cs_next_var)` >>
  qabbrev_tac `w = (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32)` >>
  qabbrev_tac `t0 = if ret_type = NoneT /\ ~skip then
    update_var chk_out w s with vs_inst_idx := LENGTH sb.cs_current_insts else s` >>
  qabbrev_tac `Gc = if ret_type = NoneT /\ ~skip then G \\ chk_out else G` >>
  qabbrev_tac `tc = if ret_type = NoneT /\ ~skip then
    tn with t_var := tn.t_var |+ (chk_out,{}) else tn` >>
  reverse (Cases_on `ext_call_precheck_ok skip ret_type target ee.accounts`)
  >- (qexistsl_tac [`Abort Revert_abort (revert_state (set_returndata []
                    (update_var chk_out w s with vs_inst_idx := SUC s.vs_inst_idx)))`,`Gc`,`tc`] >>
      fs[exit_result_def,expr_exit_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t0,Gc,tc)` by fs[] >>
  `alloca_history func t0` by
    (`stmt_state_rel H ctx func cenv cx ee s` by simp[] >>
     drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t0,Gc,tc)` by simp[] >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  `~not_fresh_at sp chk_out` by simp[Abbr `chk_out`,not_fresh_at_def] >>
  qpat_x_assum `stat <=> value_opt = NONE` kall_tac >>
  `extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sb stat
      addr value gas buf off len cap target value_opt calldata has_default
      default_op default_ty default_opt ee t0` by
    (Cases_on `ret_type = NoneT /\ ~skip`
     >- (simp[Abbr `t0`] >> irule extcheck_request_scalar >> qexists_tac `sp` >>
         `compile_extcodesize_check addr sp = ((),sb)` by fs[] >>
         drule extcheck_code_cut >> fs[]) >>
     `sb = sp` by (Cases_on `ret_type = NoneT` >> Cases_on `skip` >> fs[comp_return_def]) >>
     simp[Abbr `t0`]) >>
  pop_assum $ mk_asm "after_check" >>
  `t0.vs_current_bb = sb.cs_current_bb /\ t0.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (asm "after_check" (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >> simp[]) >>
  drule_all emit_op_fetch_boundary >>
  disch_then (qx_choose_then `call_out` (qx_choose_then `call_bb` strip_assume_tac)) >>
  `~not_fresh_at sb call_out` by metis_tac[] >>
  qexistsl_tac [`OK t0`,`Gc`,`tc`] >> asm "after_check" (fn th => simp[th]) >>
  reverse (Cases_on `ret_type = NoneT /\ ~skip`)
  >- (simp[Abbr `t0`, Abbr `Gc`, Abbr `tc`] >>
      rpt strip_tac >> gvs[ghost_inv_at_mods_def]) >>
  drule_all extcheck_scalar_observations >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [FORALL_AND_THM]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x` by
    metis_tac[not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x` by
    metis_tac[not_fresh_at_mono] >>
  drule_all extcheck_linked_frames >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [LET_THM, FORALL_AND_THM]) >>
  gvs[Abbr `t0`, Abbr `Gc`, Abbr `tc`, allocas_from_def, update_var_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >> rename1 `stor_taint_ok_at (DF h) _ _` >>
      `ghost_inv_at_mods (DF h) lo d cenv cx ee G tn s` by simp[] >>
      qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o ONCE_REWRITE_RULE [ghost_inv_at_mods_def]) >>
      qpat_x_assum `stor_taint_ok_at _ tn s` mp_tac >>
      simp[stor_taint_ok_at_def]) >>
  `!x. not_fresh_at sp x ==> x <> chk_out` by metis_tac[] >>
  Cases >> simp[safe_operand_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
                fmap_domsub, FLOOKUP_DRESTRICT]
QED
