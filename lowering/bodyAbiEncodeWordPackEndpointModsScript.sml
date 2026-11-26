(* Join the physical direct-word encoder and the linked result at one cut. *)
Theory bodyAbiEncodeWordPackEndpointMods
Ancestors
  bodyAbiEncodeWordPackMods bodyAbiEncodeWordPackEffectsMods
  bodyAbiEncodeWordPackFrameMods bodyAbiEncodeWordPackResourcesMods
  abiEncodeArgsSim
  bodyTypeBuiltinAbiMods bodySimStmtFacts bodyCopyReadPhysicalTypeMods
  exprSimAbiEncodePrefixWindow exprSimAbiEncodeBytesOwnership exprBodyPreProps
  exprOperandVar exprBopSimProps exprSimWordArgs exprLoweringProps
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullHashKeccakFixed
  bodyMemoryDefs loweringPosts loweringStateRelDefs freshWrites stateRelProj
  vyperStorageTrace vyperStorageFootprint vyperTypeEvalCaseProofs vyperTypeInvariants
  bodyPtrDefs ptrDiscipline abiBuiltinEncodeMethod vyperAST vyperState fragExec
  vyperTypeExprSoundness bodyWriteSubscriptSourceMods

Theorem abi_encode_word_pack_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  is_word_type (expr_type e) /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  lower_abi_encode (OPTION_MAP bytes_method_id_word mid) 32
    (\dst. comp_ignore_bind (emit_void MSTORE [dst;op]) (comp_return (Lit 32w))) sm = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := readings) = (INL v,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx e es sa sm s0 ee v op s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\
    ptr_val_ok cx (post_value_type ce e) v op G tn s /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?payload z Gz tz.
    evaluate_type_builtin cx (AbiEncode F mid) ty [expr_type e] [v] = INL (BytesV payload) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    ~z.vs_halted /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func ce cx (TypeBuiltin ann (AbiEncode F mid) ty [e])
        es sa sb s0 ee (Value (BytesV payload)) (LocatedValue ann (mk_ptr out LocMemory)) z /\
      vv_store_bound cx (post_value_type ce (TypeBuiltin ann (AbiEncode F mid) ty [e]))
        (lowered_value_type ce (TypeBuiltin ann (AbiEncode F mid) ty [e])) ee
        (Value (BytesV payload)) (LocatedValue ann (mk_ptr out LocMemory)) z /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      s0.vs_alloca_next <= z.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z /\
      ptr_vv_ok cx (post_value_type ce (TypeBuiltin ann (AbiEncode F mid) ty [e]))
        (Value (BytesV payload)) (LocatedValue ann (mk_ptr out LocMemory)) ee Gz tz z /\
      ptr_buf_ok ce (TypeBuiltin ann (AbiEncode F mid) ty [e]) out Gz z /\
      ghost_kept_at lo ce es sa G0 tn0 s0 Gz tz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_inv_mods mods ce cx env es` by
    (drule_then ACCEPT_TAC expr_body_pre_mods_inv) >>
  `expr_body_pre_mods mods ce cx env e es` by
    (drule type_builtin_body_arg_pre_mods >> simp[]) >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := readings)` by simp[] >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >> metis_tac[env_consistent_type_defs_get_tenv]) >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    fs[value_runtime_typed_def] >>
  drule_all_then (qx_choosel_then [`N`,`av`] strip_assume_tac) abi_encode_word_pack_source_mods >>
  suspend "entry"
QED

Resume abi_encode_word_pack_mods[entry]:
  qabbrev_tac `at = vyper_to_abi_type (get_tenv cx) (expr_type e)` >>
  qabbrev_tac `word = typed_val_to_w256 tv v` >>
  `LENGTH (enc at av) = 32` by simp[] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    (qpat_assum `monad_bind _ _ _ = _`
       (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_bind_all, cj 5 evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then assume_tac) >>
  `expr_post H0 ctx func ce cx e es sa sm s0 ee v op s` by fs[expr_post_mods_def] >>
  drule_then assume_tac expr_post_frame >>
  `post_value_type ce e = expr_type e` by simp[post_value_type_word] >>
  `eval_operand op s = SOME word /\ op_taint tn op = {}` by
    (fs[expr_post_def, ptr_val_ok_def] >> drule_all expr_val_rel_typed >> simp[Abbr `word`]) >>
  `stmt_state_rel H0 ctx func ce cx ee s` by fs[expr_post_def] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  suspend "code"
QED

Resume abi_encode_word_pack_mods[code]:
  `ci_mono sa sm` by
    (qspecl_then [`ce`,`expr_type e`,`e`,`sa`] mp_tac ci_mono_lower_value_compile_expr >>
     simp[]) >>
  qabbrev_tac `meth = OPTION_MAP bytes_method_id_word mid` >>
  qabbrev_tac `encode = \dst. comp_ignore_bind
    (emit_void MSTORE [dst;op]) (comp_return (Lit 32w))` >>
  `ci_mono sm sb` by
    (qpat_assum `lower_abi_encode _ _ _ sm = _`
       (SUBST1_TAC o SYM o AP_TERM ``SND : operand # compile_state -> compile_state``) >>
     mp_tac (Q.INST [`encode` |-> `encode`, `mid` |-> `meth`,
       `st` |-> `sm`, `maxlen` |-> `32`] ci_mono_lower_abi_encode) >>
     simp[Abbr `encode`, Abbr `meth`, ci_mono_ignore_bind,
          ci_mono_emit_void, ci_mono_comp_return]) >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[ci_mono_def] >>
  `fn_has_code sm sb func` by
    (qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fn_has_code_split >> fs[ci_mono_def]) >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x` by
    metis_tac[local_ptrs_reserved_imm_base] >>
  `!x. op = Var x ==> not_fresh_at sm x` by
    metis_tac[compile_lower_value_var] >>
  suspend "pack"
QED

Resume abi_encode_word_pack_mods[pack]:
  mp_tac (Q.INST [`mid` |-> `meth`, `value` |-> `op`, `st` |-> `sm`,
    `origin` |-> `sa`, `Hentry` |-> `H0`, `out` |-> `out`, `final` |-> `sb`]
    abi_encode_word_pack_effects_mods) >>
  (impl_tac >-
    (rpt conj_tac >> simp[Abbr `meth`, Abbr `encode`] >> metis_tac[])) >>
  strip_tac >>
  pop_assum (assume_tac o BETA_RULE o PURE_REWRITE_RULE [LET_THM]) >>
  pop_assum (qx_choosel_then [`p`,`q`,`z`,`Gz`,`tz`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "resources"
QED

Resume abi_encode_word_pack_mods[resources]:
  qabbrev_tac `payload = abi_encode_method_id_bytes mid ++ enc at av` >>
  qexistsl_tac [`payload`,`z`,`Gz`,`tz`] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qx_gen_tac `H` >> strip_tac >>
      `lowered_value_type ce e = expr_type e` by
        (irule abi_args_word_fits_eq >> simp[] >>
         irule copy_lowered_fits_mods >>
         qexistsl_tac [`cx`,`env`,`es`,`mods`] >>
         simp[] >> drule expr_body_pre_mods_well_typed >> simp[]) >>
      `abi_size_bound ce.ce_struct_fields (expr_type e) = 32` by
        (irule abi_encode_word_size_bound >> first_assum ACCEPT_TAC) >>
      mp_tac (Q.INST [`mid` |-> `mid`, `N` |-> `N`, `at` |-> `at`,
        `av` |-> `av`, `ce` |-> `ce`, `q` |-> `q`, `z` |-> `z`,
        `p` |-> `p`, `Gz` |-> `Gz`, `tz` |-> `tz`, `ee` |-> `ee`,
        `cx` |-> `cx`] abi_encode_word_pack_resources_mods) >>
      PURE_REWRITE_TAC [LET_THM] >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      (impl_tac >-
        (rpt conj_tac >> simp[Abbr `payload`, Abbr `meth`] >> metis_tac[])) >>
      strip_tac >>
      pop_assum (map_every assume_tac o CONJUNCTS o
        BETA_RULE o PURE_REWRITE_RULE [LET_THM]) >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      qpat_assum `expr_post_mods H ctx func ce cx e es sa sm s0 ee _ _ s`
        (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
      qpat_assum `expr_post H ctx func ce cx e es sa sm s0 ee _ _ s`
        (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
      qmatch_asmsub_abbrev_tac `p + cap <= z.vs_alloca_next` >>
      `ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z /\
       immutable_frame_mods func ce cx ee z` by
        (irule (INST_TYPE [alpha |-> ``:256``] abi_encode_word_pack_frame_mods) >>
         qexistsl_tac [`G`,`H`,`cap`,`ctx`,`p`,`s`,`sm`,`tn`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
         >- (rpt gen_tac >> disch_tac >>
             drule_all body_local_region_frontier >> strip_tac >>
             conj_tac
             >- (qpat_assum `!a n. _ ==> mem_bytes_at a n z.vs_memory = _` irule >>
                 qpat_assum `!name b n. _ ==> regions_disjoint p cap b n`
                   (mp_tac o REWRITE_RULE [regions_disjoint_def]) >> metis_tac[]) >>
             rpt strip_tac >>
             qpat_assum `!j. _ ==> j IN tn.t_mem` irule >> simp[] >> decide_tac)
         >- (qpat_assum `!name b n. _ ==> regions_disjoint p cap b n`
               (mp_tac o REWRITE_RULE [regions_disjoint_def]) >> simp[])
         >- (qpat_assum `allocas_from lo z` (irule o REWRITE_RULE [allocas_from_def]) >>
             qexistsl_tac [`sm.cs_next_id`,`cap`] >> first_assum ACCEPT_TAC)) >>
      suspend "linked_post")
QED

Resume abi_encode_word_pack_mods[linked_post]:
  `stmt_state_rel H ctx func ce cx ee z` by
    (qpat_assum `!H. stmt_state_rel H ctx func ce cx ee s ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `vv_post H ctx func ce cx (TypeBuiltin ann (AbiEncode F mid) ty [e])
      es sa sb s0 ee (Value (BytesV payload))
      (LocatedValue ann (mk_ptr out LocMemory)) z` by
    (irule (REWRITE_RULE [expr_type_def] (Q.INST
      [`e` |-> `TypeBuiltin ann (AbiEncode F mid) ty [e]`,
       `result` |-> `Value (BytesV payload)`] abi_encode_bytes_vv_post)) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- simp[read_result_def, return_def]
     >- (rewrite_tac[expr_has_effect_thm,listTheory.EXISTS_DEF] >> strip_tac >>
         qpat_assum `pure_frame ce func es sa s0 s ==> _` irule >>
         qpat_assum `~expr_has_effect e ==> _` irule >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`N`,`sm.cs_next_id`,`p`,`cap`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qpat_assum `w2n (n2w p : bytes32) = p` mp_tac >> simp[])
     >- fs[Abbr `payload`, Abbr `cap`, Abbr `meth`]
     >- (qpat_assum `!mem. _ ==> val_in_memory _ _ _ _` mp_tac >>
         disch_then (qspec_then `z.vs_memory` mp_tac) >>
         simp[mem_agree_outside_def, Abbr `payload`])) >>
  suspend "finish_post"
QED

Resume abi_encode_word_pack_mods[finish_post]:
  conj_tac
  >- (qpat_x_assum `vv_post H ctx func ce cx _ _ _ _ _ _ _ _ z` mp_tac >>
      simp[vv_post_mods_def,vv_post_def,vv_holds_mods_def,vv_place_ptr_mods_def,
           vv_place_ptr_def,contextTheory.mk_ptr_def] >>
      rpt strip_tac >> first_x_assum irule >> simp[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_x_assum `vv_store_bound _ _ _ _ _ _ z` mp_tac >>
      simp[Abbr `payload`, expr_type_def])
  >- (qpat_assum `stmt_state_rel H ctx func ce cx ee z`
        (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >> simp[])
  >- (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `s.vs_alloca_next` >> simp[])
  >- (qpat_x_assum `ptr_vv_ok _ _ _ _ _ Gz tz z` mp_tac >>
      simp[Abbr `payload`, expr_type_def]) >>
  qpat_x_assum `ptr_buf_ok _ _ _ Gz z` mp_tac >> simp[]
QED

Finalise abi_encode_word_pack_mods
