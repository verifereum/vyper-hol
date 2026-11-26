(* Bind the linked forced hash operand, including the SHA precompile exit. *)
Theory bodyHashBindShaMods
Ancestors
  bodyShaHashSuffixMods bodyForcedStorageFrameMods bodyFullPostsMods
  exprSimHash exprSimDefs gasOutcomeFullBindMods gasOutcomeFullPostMods
  gasExemptCertMods haltExitProj stmtSimProps
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperContext vyperState vyperAST
Libs monadsyntax

val parent_e = ``Builtin (BaseT (BytesT (Fixed 32))) b [e]``;
val stack = ``StackValue (BaseT (BytesT (Fixed 32))) op``;
val forced = ``bind (eval_expr cx e) (read_result cx)``;
val next_sha = ``\v (u:evaluation_state).
  case builtin_result cx u.accounts (BaseT (BytesT (Fixed 32))) Sha256 [expr_type e] [v] of
    INR exc => (INR exc,u)
  | INL w => (do precompile_call_success Sha256 [v]; return (Value w) od) u``;
val next_keccak = ``\v (u:evaluation_state).
  ((case builtin_result cx u.accounts (BaseT (BytesT (Fixed 32))) Keccak256 [expr_type e] [v] of
      INL w => INL (Value w) | INR exc => INR exc), u)``;
val next_hash = ``if b = Sha256 then ^next_sha else ^next_keccak``;

val arg_post = ``expr_post_mods (H:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx e es sa sm s0 mid v x s /\
  expr_store_bound cx (post_value_type cenv e) v x s /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
  ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val arg_q = ``\(H:(bool # bytes32 # type_value) list # num list) (res:value + exception) mid G tn s.
  ?v. res = INL v /\
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
    expr_store_bound cx (post_value_type cenv e) v x s /\
    s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val parent_q = ``\(H:(bool # bytes32 # type_value) list # num list) (res:eval_result + exception) ee G tn t.
  ?tv. res = INL tv /\
    vv_post_mods H ctx func cenv cx ^parent_e es sa sb s0 ee tv ^stack t /\
    vv_store_bound cx (post_value_type cenv ^parent_e) (lowered_value_type cenv ^parent_e)
      ee tv ^stack t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    ptr_vv_ok cx (post_value_type cenv ^parent_e) tv ^stack ee G tn t /\
    (!v. tv = Value v /\ ~is_word_type (post_value_type cenv ^parent_e) /\
         ~is_bytestring_type (post_value_type cenv ^parent_e) ==>
         vv_own cenv cx (post_value_type cenv ^parent_e) sa sb ee tv ^stack t /\
         (!t' p. ^stack = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
    (cenv.ce_is_ctor /\ vv_location ^stack = SOME LocCode ==>
     ?v. read_result cx tv ee = (INL v,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv ^parent_e) = SOME rt /\
                eval_operand (vv_operand ^stack) t = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                       val_in_memory rt v (w2n w) mem)) /\
    (!t' op'. ^stack = StackValue t' op' /\ ~is_word_type (post_value_type cenv ^parent_e) ==>
              ptr_buf_ok cenv ^parent_e op' G t) /\
    (!t' p. ^stack = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv ^parent_e p.ptr_operand G t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val arg_r = ``\(H:(bool # bytes32 # type_value) list # num list) (res:value + exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;
val hash_r = ``\(H:(bool # bytes32 # type_value) list # num list) (res:eval_result + exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;
val reached = ``(!tail. ^forced (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
                         (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==> ^arg_post)``;

Theorem hash_eval_action[local]:
  b = Keccak256 \/ b = Sha256 ==>
  eval_expr cx ^parent_e = bind ^forced ^next_hash
Proof
  strip_tac >> simp[]
  >- (irule eval_expr_unary_builtin_action >>
      simp[builtin_args_length_ok_def, precompile_builtin_def, is_self_codesize_def]) >>
  simp[eval_expr_sha256_action]
QED

Theorem hash_bind_sha_or_reached_keccak_mods:
  (b = Keccak256 \/ b = Sha256) /\
  expr_body_pre_mods mods cenv cx env ^parent_e es /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_expr cenv ty ^parent_e sa = (^stack,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^parent_e) shadow_sa =
    (^stack,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
    ^forced (es,s0,G0,tn0) ^arg_q ^arg_r /\
  (b = Keccak256 ==>
   !marks v mid G tn s. ^reached ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
       (^next_keccak v) (mid,s,G,tn) ^parent_q ^hash_r) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
    (eval_expr cx ^parent_e) (es,s0,G0,tn0) ^parent_q ^hash_r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `b = Keccak256 \/ b = Sha256`
    (mp_then Any (fn th => once_rewrite_tac[th]) hash_eval_action) >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- ACCEPT_TAC bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >- (Cases_on `b = Sha256`
      >- simp[sha256_continuation_frame] >>
      simp[storage_trace_frame_def]) >>
  qexists_tac `\H res mid G tn s. (^arg_q) H res mid G tn s /\ mid.gas_obs = [] /\ ~s.vs_halted` >>
  BETA_TAC >> reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
      BETA_TAC >> conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "reached"
QED

Resume hash_bind_sha_or_reached_keccak_mods[reached]:
  qx_genl_tac [`marks`,`res`,`mid`,`G`,`tn`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> pure_rewrite_tac[REFL_CLAUSE, boolTheory.AND_CLAUSES] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> ^arg_post` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  Cases_on `b = Sha256`
  >- (qpat_x_assum `b = Sha256` SUBST_ALL_TAC >>
      pure_rewrite_tac[REFL_CLAUSE, COND_CLAUSES] >> BETA_TAC >>
      irule sha_hash_suffix_mods >> BETA_TAC >>
      rpt (first_assum (irule_at Any)) >>
      qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
      ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
      gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ^arg_post`
        (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `b <> Sha256` (fn th => pure_rewrite_tac[EQF_INTRO th, COND_CLAUSES]) >>
  BETA_TAC >>
  `b = Keccak256` by
    (qpat_x_assum `b = Keccak256 \/ b = Sha256` mp_tac >> simp[]) >>
  qpat_x_assum `b = Keccak256 ==> _` (drule_then (irule o BETA_RULE)) >>
  conj_tac >- (qexists_tac `marks` >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise hash_bind_sha_or_reached_keccak_mods
