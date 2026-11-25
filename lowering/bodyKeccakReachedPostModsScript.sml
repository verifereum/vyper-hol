(* Convert the reached Keccak machine endpoint into the linked VV outcome. *)
Theory bodyKeccakReachedPostMods
Ancestors
  bodyFullHashCleanFrame bodyForcedStorageFrameMods bodyWriteSubscriptSourceMods
  bodyExprPreFacts bodyMemoryDefs exprSimHash exprSimWordArgs exprSimMemDefs
  constSubstCorrect bodySimStmtFacts exprLowering bodyFullShadowBodyInv
  exprBodyPreProps exprSimHypsDefs gasOutcomeFullPostMods loweringPosts
  loweringStateRelDefs gasExplicitSites bodyFullPostsMods bodyFullShared
  vyperTypeEvalCaseProofs[qualified,ignore_grammar]
  abiValueEncoding[qualified,ignore_grammar]
  vyperTypeCallGraph allocLimits supportedExprTraverse vyperTyping
  vyperTypeSystem vyperTypeExprSoundness exprLoweringProps compileEnv fragExec
  vyperStorageFootprint vyperStorageTrace bodyPtrDefs
  vyperValue vyperState vyperAST venomState finite_map rich_list list

val keccak_expr = ``Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e]``;
val keccak_stack = ``StackValue (BaseT (BytesT (Fixed 32))) op``;
val keccak_source = ``\(ee:evaluation_state).
  ((case builtin_result cx ee.accounts (BaseT (BytesT (Fixed 32)))
      Keccak256 [expr_type e] [v] of INL w => INL (Value w) | INR exc => INR exc),ee)``;
val keccak_q = ``\(H:(bool # bytes32 # type_value) list # num list)
                     (res:eval_result + exception) ee G tn t.
  ?tv. res = INL tv /\
    vv_post_mods H ctx func cenv cx ^keccak_expr es sa sb s0 ee tv ^keccak_stack t /\
    vv_store_bound cx (post_value_type cenv ^keccak_expr) (lowered_value_type cenv ^keccak_expr)
      ee tv ^keccak_stack t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    ptr_vv_ok cx (post_value_type cenv ^keccak_expr) tv ^keccak_stack ee G tn t /\
    (!v. tv = Value v /\ ~is_word_type (post_value_type cenv ^keccak_expr) /\
         ~is_bytestring_type (post_value_type cenv ^keccak_expr) ==>
         vv_own cenv cx (post_value_type cenv ^keccak_expr) sa sb ee tv ^keccak_stack t /\
         (!t' p. ^keccak_stack = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
    (cenv.ce_is_ctor /\ vv_location ^keccak_stack = SOME LocCode ==>
     ?v. read_result cx tv ee = (INL v,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv ^keccak_expr) = SOME rt /\
                eval_operand (vv_operand ^keccak_stack) t = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                       val_in_memory rt v (w2n w) mem)) /\
    (!t' op'. ^keccak_stack = StackValue t' op' /\ ~is_word_type (post_value_type cenv ^keccak_expr) ==>
              ptr_buf_ok cenv ^keccak_expr op' G t) /\
    (!t' p. ^keccak_stack = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv ^keccak_expr p.ptr_operand G t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val keccak_exit = ``\(H:(bool # bytes32 # type_value) list # num list)
                         (res:eval_result + exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;
val keccak_outcome = ``gas_outcome_full_mods
  (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
  ^keccak_source (mid,s,G,tn) ^keccak_q ^keccak_exit``;
val reached_post = ``\(H:(bool # bytes32 # type_value) list # num list).
  expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
  expr_store_bound cx (post_value_type cenv e) v x s /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
  ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val all_reached_post = ``!H. valid_horizon cx st0 H mid.storage_trace ==> (^reached_post) H``;
val endpoint_common = ``
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func s``;
val fixed_entry = ``
  ^endpoint_common /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  return_buf_frame d cenv sa s0 /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn s)``;
val buffer_entry = ``
  ^endpoint_common /\ local_ptrs_reserved cenv sm /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  return_buf_frame d cenv sm s /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
          (INL v,mid with gas_obs := tail)) /\ mid.gas_obs = [] /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
    expr_store_bound cx (post_value_type cenv e) v x s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)``;
val keccak_endpoint = ``\payload. ?raw u Gf tf.
  run_inst_seq (emitted_insts sm sb) s = OK raw /\
  u = (raw with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s.vs_alloca_next <= u.vs_alloca_next /\
  op_taint tf op = {} /\ op_prov Gf op = NONE /\
  !H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf) /\
    vv_post H ctx func cenv cx ^keccak_expr es sa sb s0 mid
      (Value (BytesV (Keccak_256_w64 payload))) ^keccak_stack u /\
    immutable_frame_mods func cenv cx mid u /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid Gf tf u /\
    ghost_kept_at lo cenv mid sm G tn s Gf tf``;

Theorem keccak_reached_source[local]:
  expr_body_pre_mods mods cenv cx env ^keccak_expr es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
          (INL v,mid with gas_obs := tail)) /\ mid.gas_obs = [] ==>
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  ?bty. expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
        evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
        value_has_type (BaseTV bty) v
Proof
  strip_tac >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid)` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (drule_then mp_tac (REWRITE_RULE [ETA_THM] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `is_bytes_or_string_type (expr_type e)` by
    (drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def] >>
     strip_tac >> drule (SRULE [] (Q.INST [`b` |-> `Keccak256`] hash_builtin_types)) >> simp[]) >>
  `?bty. expr_type e = BaseT bty` by
    (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := prefix)` by
    (simp[write_subscript_source_gas_obs_mods] >>
     qpat_x_assum `expr_body_pre_mods _ _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_mods_def, Once well_typed_expr_def,
          byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
          expr_has_evm_run_thm, supported_expr_exists_def, DISJ_IMP_THM,
          FORALL_AND_THM, frame_well_typed_exprs_cons]) >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >>
     disch_then (irule o MATCH_MP vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv)) >>
  gvs[value_runtime_typed_def] >>
  drule abiValueEncodingTheory.evaluate_type_base_result >> strip_tac >> gvs[]
QED

Theorem keccak_stack_pair[local]:
  as_stack_val ty p = (StackValue ty op,sb) <=> p = (op,sb)
Proof
  Cases_on `p` >> simp[as_stack_val_def]
QED

Theorem keccak_stack_post_mods[local]:
  vv_post H ctx func cenv cx e es sa sb s0 mid (Value v) (StackValue ty op) u /\
  immutable_frame_mods func cenv cx mid u ==>
  vv_post_mods H ctx func cenv cx e es sa sb s0 mid (Value v) (StackValue ty op) u
Proof
  simp[vv_post_mods_def,vv_post_def,vv_holds_mods_def,vv_place_ptr_mods_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem keccak_endpoint_outcome[local]:
  ^all_reached_post /\ (^keccak_endpoint) payload /\
  ~s.vs_halted /\ mid.gas_obs = [] /\
  builtin_result cx mid.accounts (BaseT (BytesT (Fixed 32))) Keccak256
    [expr_type e] [v] = INL (BytesV (Keccak_256_w64 payload)) /\
  stmt_state_rel J ctx func cenv cx es s0 /\ wb_frame cenv es mid sa s0 s /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id ==>
  ^keccak_outcome
Proof
  BETA_TAC >> strip_tac >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  irule gas_outcome_full_mods_pure >> BETA_TAC >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gf`,`mid`,`INL (Value (BytesV (Keccak_256_w64 payload))):eval_result + exception`, `u`,`tf`] >>
  conj_tac >- simp[] >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf` by
    (drule_all hash_ghost_kept_wb_trans >> disch_then ACCEPT_TAC) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `vv_post_mods H ctx func cenv cx ^keccak_expr es sa sb s0 mid
      (Value (BytesV (Keccak_256_w64 payload))) ^keccak_stack u` by
    (irule keccak_stack_post_mods >> asm_rewrite_tac[]) >>
  qpat_x_assum `u = raw with vs_inst_idx := _` kall_tac >>
  simp[expr_type_def, vv_store_bound_stack_word, is_word_type_def,
       ptr_vv_ok_def, ptr_val_ok_def, contextTheory.vv_location_def, post_value_type_def,
       read_result_def, return_def]
QED

Theorem keccak_reached_from_endpoints_mods:
  expr_body_pre_mods mods cenv cx env ^keccak_expr es /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_expr cenv ty ^keccak_expr sa = (^keccak_stack,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  return_buf_frame d cenv sa s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
          (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
  ~s.vs_halted /\ ^all_reached_post /\
  (!m bs. v = BytesV bs /\ expr_type e = BaseT (BytesT (Fixed m)) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Fixed m))) /\
    value_has_type (BaseTV (BytesT (Fixed m))) v /\ compile_keccak256_bytesm x m sm = (op,sb) /\
    ^fixed_entry ==> (^keccak_endpoint) bs) /\
  (!bty payload. expr_type e = BaseT bty /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\ value_has_type (BaseTV bty) v /\
    ((?cap. expr_type e = BaseT (BytesT (Dynamic cap)) /\ v = BytesV payload) \/
     (?cap str. expr_type e = BaseT (StringT cap) /\ v = StringV str /\ payload = MAP (n2w o ORD) str)) /\
    compile_keccak256_bytes x sm = (op,sb) /\ ^buffer_entry ==> (^keccak_endpoint) payload) ==>
  ^keccak_outcome
Proof
  BETA_TAC >> strip_tac >>
  drule_all_then strip_assume_tac keccak_reached_source >>
  qabbrev_tac `J = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 J mid.storage_trace` by fs[Abbr `J`, storage_trace_domain_def] >>
  `valid_horizon cx st0 J es.storage_trace` by
    (drule_all (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] valid_horizon_frame)
       bodyForcedStorageFrameModsTheory.bop_forced_storage_frame) >> simp[]) >>
  `stmt_state_rel J ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (drule_then ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `J` (drule_then strip_assume_tac)) >>
  `expr_post J ctx func cenv cx e es sa sm s0 mid v x s` by fs[expr_post_mods_def] >>
  `wb_frame cenv es mid sa s0 s` by (drule_then ACCEPT_TAC expr_post_frame) >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (drule_then ACCEPT_TAC (cj 2 compile_expr_grows)) >>
  `local_ptrs_reserved cenv sm` by (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `return_buf_frame d cenv sm s` by
    (`!p w. not_fresh_at sa p /\ lookup_var p s0 = SOME w ==> lookup_var p s = SOME w` by
       fs[expr_post_def] >>
     irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `(!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by
    metis_tac[not_fresh_at_def,arithmeticTheory.LE_TRANS] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
    expr_store_bound cx (post_value_type cenv e) v x s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ expr_store_bound _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `?payload. (^keccak_endpoint) payload /\
    builtin_result cx mid.accounts (BaseT (BytesT (Fixed 32))) Keccak256 [expr_type e] [v] =
       INL (BytesV (Keccak_256_w64 payload))` suffices_by
    (disch_then (qx_choose_then `payload` (CONJUNCTS_THEN assume_tac) o BETA_RULE) >>
     drule_all (BETA_RULE keccak_endpoint_outcome) >> disch_then ACCEPT_TAC) >>
  BETA_TAC >>
  Cases_on `bty` >> gvs[is_bytes_or_string_type_def]
  >- suspend "string" >>
  rename1 `expr_type e = BaseT (BytesT bd)` >>
  Cases_on `bd` >> gvs[is_bytestring_type_def]
  >- suspend "fixed" >>
  suspend "dynamic"
QED

Resume keccak_reached_from_endpoints_mods[string]:
  `compile_keccak256_bytes x sm = (op,sb)` by
    (qpat_x_assum `compile_expr cenv ty (Builtin _ Keccak256 [_]) sa = _` mp_tac >>
     simp[compile_hash_singleton, is_bytestring_type_def, keccak_stack_pair]) >>
  `cs_extends sm sb` by metis_tac[hash_suffix_appends, cs_appends_def] >>
  `fn_has_code sm sb func` by (drule_all fn_has_code_split >> simp[]) >>
  `?str. v = StringV str` by (Cases_on `v` >> gvs[value_has_type_def]) >>
  qexists_tac `MAP (n2w o ORD) str` >> conj_tac
  >- (first_x_assum (qspec_then `MAP (n2w o ORD) str` mp_tac) >> simp[]) >>
  simp[builtin_result_def, vyperContextTheory.evaluate_builtin_def]
QED

Resume keccak_reached_from_endpoints_mods[fixed]:
  rename1 `expr_type e = BaseT (BytesT (Fixed width))` >>
  `compile_keccak256_bytesm x width sm = (op,sb)` by
    (qpat_x_assum `compile_expr cenv ty (Builtin _ Keccak256 [_]) sa = _` mp_tac >>
     simp[compile_hash_singleton, is_bytestring_type_def, keccak_stack_pair]) >>
  `cs_extends sm sb` by metis_tac[hash_suffix_appends, cs_appends_def] >>
  `fn_has_code sm sb func` by (drule_all fn_has_code_split >> simp[]) >>
  `?bs. v = BytesV bs` by (Cases_on `v` >> gvs[value_has_type_def]) >>
  qexists_tac `bs` >> conj_tac
  >- (first_x_assum (qspec_then `bs` mp_tac) >> simp[]) >>
  simp[builtin_result_def, vyperContextTheory.evaluate_builtin_def]
QED

Resume keccak_reached_from_endpoints_mods[dynamic]:
  `compile_keccak256_bytes x sm = (op,sb)` by
    (qpat_x_assum `compile_expr cenv ty (Builtin _ Keccak256 [_]) sa = _` mp_tac >>
     simp[compile_hash_singleton, is_bytestring_type_def, keccak_stack_pair]) >>
  `cs_extends sm sb` by metis_tac[hash_suffix_appends, cs_appends_def] >>
  `fn_has_code sm sb func` by (drule_all fn_has_code_split >> simp[]) >>
  `?bs. v = BytesV bs` by (Cases_on `v` >> gvs[value_has_type_def]) >>
  qexists_tac `bs` >> conj_tac
  >- (first_x_assum (qspec_then `bs` mp_tac) >> simp[]) >>
  simp[builtin_result_def, vyperContextTheory.evaluate_builtin_def]
QED

Finalise keccak_reached_from_endpoints_mods
