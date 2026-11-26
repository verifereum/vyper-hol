(* The Uint2Str continuation from the actual linked forced-operand landing. *)
Theory bodyUint2StrSuffixMods
Ancestors
  bodyUint2StrInputMods bodyUint2StrOperandMods bodyUint2StrAllocEntryMods
  bodyUint2StrNumericMods bodyUint2StrRegisteredFrameMods bodyUint2StrResultPostMods
  bodyFullPostsMods gasOutcomeFullPostMods fragGasOriginPtrLoop
  exprOperandVar exprSimUint2Str exprSimDefs haltExitProj vyperStorageTrace
  vyperStorageFootprint freshWrites exprLoweringProps loweringHalt context
  gasOutcomeFull loweringPosts bodyFullShadowBodyInv bodyPtrDefs compileEnv
Libs monadsyntax

val uint2str_expr = ``Builtin (BaseT (StringT n)) (Uint2Str n) [e]``;
val uint2str_next = ``\v (ee:evaluation_state).
  ((case builtin_result cx ee.accounts (BaseT (StringT n)) (Uint2Str n)
       [expr_type e] [v] of INL r => INL (Value r) | INR ex => INR ex),ee)``;

Theorem uint2str_reached_suffix_mods:
  expr_body_pre_mods mods ce cx env ^uint2str_expr es /\
  expr_body_pre_mods mods ce cx env e es /\ expr_type e = BaseT (UintT k) /\
  LENGTH (num_to_dec_string (2 ** k - 1)) <= n /\
  lower_value compile_expr ce ty e sa = (op,sm) /\
  as_ptr_val (BaseT (StringT n)) LocMemory
    (compile_uint2str op n (type_memory_bytes ce (BaseT (StringT n))) sm) = (vv,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  local_ptrs_reserved ce sa /\
  (!x len. ce.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sa x) /\
  (!x len. ce.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx fn ce cx es s0) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL v, mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\ ~s.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx fn ce cx e es sa sm s0 mid v op s /\
    expr_store_bound cx (post_value_type ce e) v op s /\
    s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history fn s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d ce cx mid G tn s /\
    ptr_val_ok cx (post_value_type ce e) v op G tn s /\
    (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G s) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) ce.ce_modules cx st0
    (^uint2str_next v) (mid,s,G,tn)
    (\H res ee Gf tf t. ?tv. res = INL tv /\
      vv_post_mods H ctx fn ce cx ^uint2str_expr es sa sb s0 ee tv vv t /\
      vv_store_bound cx (post_value_type ce ^uint2str_expr) (lowered_value_type ce ^uint2str_expr)
        ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history fn t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf t /\
      ptr_vv_ok cx (post_value_type ce ^uint2str_expr) tv vv ee Gf tf t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type ce ^uint2str_expr) /\
           ~is_bytestring_type (post_value_type ce ^uint2str_expr) ==>
           vv_own ce cx (post_value_type ce ^uint2str_expr) sa sb ee tv vv t /\
           (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
             !rt w. evaluate_type (get_tenv cx) (post_value_type ce ^uint2str_expr) = SOME rt /\
                    eval_operand (vv_operand vv) t = SOME w ==>
                    w2n w + type_memory_size rt <= lo /\
                    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
                           val_in_memory rt val (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type ce ^uint2str_expr) ==>
               ptr_buf_ok ce ^uint2str_expr op Gf t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok ce ^uint2str_expr p.ptr_operand Gf t) /\
      ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods H ctx fn ce cx e es sa sm s0 mid _ op s /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  drule_all (Q.INST [`H` |-> `H0`] (SPEC_ALL uint2str_operand_endpoint_mods)) >>
  disch_then (qx_choose_then `X` strip_assume_tac o CONJUNCT2) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule_all (Q.INST [`H` |-> `H0`] (SPEC_ALL uint2str_operand_endpoint_mods)) >> simp[]) >>
  qpat_x_assum `v = IntV _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac uint2str_capacity_mods >>
  qabbrev_tac `N = type_memory_bytes ce (BaseT (StringT n))` >>
  suspend "entry"
QED

Resume uint2str_reached_suffix_mods[entry]:
  `mid with gas_obs := [] = mid` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL (IntV (&X)),mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (pure_once_rewrite_tac o single o SYM) >>
     qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE[listTheory.APPEND_NIL]))) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  drule_all_then strip_assume_tac storage_trace_frame_prefix >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >> irule valid_horizon_append >> qexists_tac `observations` >>
     qpat_assum `mid.storage_trace = _` (PURE_ONCE_REWRITE_TAC o single o SYM o SIMP_RULE (srw_ss()) []) >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx fn ce cx mid s /\ ghost_inv_at_mods (DF H) lo d ce cx mid G tn s` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods H ctx fn ce cx e es sa sm s0 mid _ op s /\ _`
       (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]) >>
  `local_ptrs_reserved ce sm` by (drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `(!x len. ce.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x) /\
   (!x len. ce.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x)` by
    (conj_tac >> rpt strip_tac >> first_x_assum irule >> first_x_assum drule >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at sm x` by (rpt strip_tac >> drule_all compile_lower_value_var >> simp[]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `op_prov G op = NONE /\ op_taint tn op = {}` by
    fs[ptr_val_ok_def,post_value_type_word,is_word_type_def] >>
  suspend "allocation"
QED

Resume uint2str_reached_suffix_mods[allocation]:
  `N = type_memory_bytes ce (BaseT (StringT n))` by simp[Abbr `N`] >>
  drule_all (Q.INST [`N` |-> `N`, `H0` |-> `H0`, `s` |-> `s`]
    (SPEC_ALL uint2str_alloc_entry_mods)) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `ba` (qx_choose_then `a` (qx_choose_then `p` (qx_choose_then `b`
      (qx_choose_then `ready` (qx_choose_then `Gr` (qx_choose_then `tr`
        (qx_choose_then `inst` strip_assume_tac))))))))) >>
  suspend "numeric"
QED

Resume uint2str_reached_suffix_mods[numeric]:
  qabbrev_tac `bb = <|bb_label := a.cs_current_bb;
     bb_instructions := a.cs_current_insts ++ u2s_setup a op (Var p)|>` >>
  `lookup_block ready.vs_current_bb fn.fn_blocks = SOME bb /\
   bb.bb_instructions = a.cs_current_insts ++ u2s_setup a op (Var p)` by
    simp[Abbr `bb`] >>
  drule_all (Q.INST [`s` |-> `ready`, `H0` |-> `H0`]
    (SPEC_ALL u2s_setup_exit_joint_mods)) >>
  disch_then (qspecl_then [`BaseTV (StringT n)`,`explicit`,`PG`]
    (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac)))) >>
  suspend "outcome"
QED

Resume uint2str_reached_suffix_mods[outcome]:
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`mid`,`INL (Value (StringV (num_to_dec_string X)))`,`t`,`tf`] >>
  conj_tac >- simp[uint2str_source_result] >>
  qx_gen_tac `H` >> strip_tac >>
  conj_tac
  >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gr`,`ready`,`tr`] >> simp[]) >>
  qpat_assum `mid with gas_obs := [] = mid` (pure_rewrite_tac o single) >>
  suspend "post"
QED

Resume uint2str_reached_suffix_mods[post]:
  `valid_horizon cx st0 H es.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods H ctx fn ce cx e es sa sm s0 mid _ op s /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> u2s_safe H _ _ _ _ _ _ _ _ _ _ ready t /\ _`
    (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac compile_alloc_buffer_parts >>
  `inst.inst_id = sm.cs_next_id` by
    (qpat_assum `inst = mk_inst _ _ _ _` SUBST1_TAC >>
     simp_tac (srw_ss()) [venomInstTheory.mk_inst_def]) >>
  `sm.cs_next_var <= a.cs_next_var /\ sm.cs_next_id <= a.cs_next_id` by
    (qpat_assum `a.cs_next_var = _` SUBST1_TAC >> qpat_assum `a.cs_next_id = _` SUBST1_TAC >>
     simp_tac (srw_ss()) []) >>
  drule_all_then strip_assume_tac (Q.INST [`H` |-> `H`, `t` |-> `t`]
    (SPEC_ALL uint2str_registered_frame_mods)) >>
  `LENGTH (num_to_dec_string X) + 32 <= N` by
    (qpat_assum `type_memory_size (BaseTV (StringT n)) = N` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sm x ==> lookup_var x ready = lookup_var x s` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> lookup_var x ready = _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac
    (CONV_RULE (DEPTH_CONV BETA_CONV) (PURE_REWRITE_RULE [LET_THM] uint2str_result_post_mods)) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  BETA_TAC >> qexists_tac `Value (StringV (num_to_dec_string X))` >>
  `vv = LocatedValue (BaseT (StringT n)) (mk_ptr (Var (u2s_var a 2)) LocMemory)` by
    (qpat_assum `as_ptr_val _ _ _ = _` mp_tac >>
     qpat_assum `compile_uint2str _ _ _ _ = _` SUBST1_TAC >>
     simp_tac (srw_ss()) [exprLoweringTheory.as_ptr_val_def]) >>
  rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   qpat_assum `vv = LocatedValue _ _` (fn th =>
     simp_tac (srw_ss()) [th,post_value_type_def,vyperASTTheory.expr_type_def,
       compileEnvTheory.is_bytestring_type_def,vv_location_def,vv_operand_def,mk_ptr_def])) >>
  qpat_assum `ptr_buf_ok _ _ (vv_operand vv) _ _` mp_tac >>
  qpat_assum `vv = LocatedValue _ _` (fn th =>
    simp_tac (srw_ss()) [th,vv_operand_def,mk_ptr_def])
QED

Finalise uint2str_reached_suffix_mods
