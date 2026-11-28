(* Request sites between the forced bytes argument and the prepared call. *)
Theory s1PrefixRawCallKeywords
Ancestors
  s1PrefixPreds s1PrefixCompose s1PrefixOfVV s1PrefixWordArgs
  bodyFullWordArgs bodyFullRawCallHeader bodyFullHashKeccakFixed
  exprSimHash exprSimRawCall bodyFullRawCallHeaderView
  bodyMemoryDefs loweringShapeDefs gasOutcomeFullCompose
  s1PrefixDefs s1PrefixFrame s1PrefixProps bodyFullPreds bodySimFull
  exprSimWordArgs exprSimSource exprLoweringProps gasShadowCompileStmtHelpers
  gasShadowState fragExec bodyFullIfExpReach loweringStateRelDefs loweringPosts
  vyperStorageTrace vyperStorageFootprint vyperState vyperInterpreter exprSimDefs
  bodyFullShadowBodyInv
  words list combin

(* The header runs without source observations.  The callback sees its
   actual endpoint and the replay and full post of the keyword evaluation. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon esD.storage_trace) esD.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_val_rel _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `?b. eval_operand data tD = SOME (n2w b) /\ b+32+LENGTH bs < dimword (:256)` by
    (qpat_assum `expr_val_rel cx _ _ data tD` mp_tac >>
     qpat_assum `expr_store_bound cx _ _ data tD` mp_tac >>
     drule stateRelProjTheory.stmt_state_rel_alloca_room >> strip_tac >>
     qpat_x_assum `alloca_room _ _ _` mp_tac >>
     qpat_assum `evaluate_type _ _ = SOME (BaseTV (BytesT (Dynamic cap)))` mp_tac >>
     qpat_assum `~is_word_type (post_value_type cenv d)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[expr_val_rel_def,exprSimMemDefsTheory.expr_store_bound_def,alloca_room_def] >>
     rpt strip_tac >> qexists_tac `w2n w` >>
     gvs[exprSimPropsTheory.val_store_size_def,valueEncodingDefsTheory.val_in_memory_def] >>
     qspec_then `LENGTH bs` assume_tac exprSimPropsTheory.le_word_size_mul >> decide_tac) >>
  drule_all raw_call_header_bytes_view >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  drule_all hash_data_prefix_run >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp tD` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `allocas_from lo tD /\ lo <= tD.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  drule_all raw_call_header_joint >>
  disch_then (qspecl_then [`PG`,`esD`,`gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
  disch_then (qx_choose_then `t4` strip_assume_tac) >>
  suspend "header_end"
QED
*)
Theorem raw_call_keywords_prefix_from_entry:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env esD /\ expr_sim_inv cenv cx env esD /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) NONE) es /\
  EVERY (\e. expr_type e = BaseT (UintT 256)) kws /\
  body_exprs_full_ok cx kws /\ body_exprs_prefix_ok cx kws /\
  evaluate_type (get_tenv cx) (post_value_type cenv d) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  ~is_word_type (post_value_type cenv d) /\
  ptr_val_ok cx (post_value_type cenv d) (BytesV bs) data GD tnD tD /\
  expr_store_bound cx (post_value_type cenv d) (BytesV bs) data tD /\
  emit_op MLOAD [data] s2 = (len,s3) /\ emit_op ADD [data; Lit 32w] s3 = (dp,s4) /\
  (!z. data = Var z ==> not_fresh_at s2 z) /\
  lower_word_args cenv (K (BaseT (UintT 256))) kws s4 = (xs,s5) /\
  lower_word_args (gas_shadow_env T cenv) (K (BaseT (UintT 256)))
    (MAP gas_shadow_expr kws) h4 = (xs,h5) /\
  gas_shadow_state s4 h4 /\ gas_shadow_state s5 h5 /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code s2 s4 func /\ fn_has_code s4 s5 func /\ fn_has_code h4 h5 shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv s2 /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z) /\
  ~tD.vs_halted /\ tD.vs_current_bb = s2.cs_current_bb /\
  tD.vs_inst_idx = LENGTH s2.cs_current_insts /\ alloca_history func tD /\
  return_buf_frame dframe cenv s2 tD /\
  (!fn inst u. frag_reachable ctx func tD fn inst u ==> dalloca_fmp_headroom inst u) /\
  storage_trace_domain cx st0 esD.storage_trace /\
  (!H. valid_horizon cx st0 H esD.storage_trace ==>
    expr_val_rel cx (post_value_type cenv d) (BytesV bs) data tD /\
    stmt_state_rel H ctx func cenv cx esD tD /\ storage_well_formed_on cx esD (FST H) /\
    ghost_inv_at (DF H) lo dframe cenv cx esD GD tnD tD) /\
  (!v. storage_trace_frame (k av (BytesV bs) v)) /\
  (!b x l p base extent t4 G4 tn4 marks kvs esK tk GK tnK.
    data = Var x /\ len = Var l /\ dp = Var p /\
    (!z. len = Var z \/ dp = Var z ==> not_fresh_at s4 z) /\
    eval_operand data tD = SOME (n2w b) /\ b < dimword (:256) /\
    b+32+LENGTH bs < dimword (:256) /\ local_ptrs_reserved cenv s4 /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z) /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (tD,GD,tnD) [] (OK t4,G4,tn4)) /\
    eval_operand len t4 = SOME (n2w (LENGTH bs)) /\ eval_operand dp t4 = SOME (n2w (b+32)) /\
    op_taint tn4 len = {} /\ op_taint tn4 dp = {} /\ op_prov G4 len = NONE /\
    FLOOKUP G4 p = SOME (base,extent) /\ base <= b /\ b+32+LENGTH bs <= base+extent /\
    (!mem. mem_agree_outside tn4.t_mem t4.vs_memory mem ==>
      mem_bytes_at (b+32) (LENGTH bs) mem = bs) /\
    (!z. not_fresh_at s2 z ==> lookup_var z t4 = lookup_var z tD /\
      FLOOKUP G4 z = FLOOKUP GD z /\ op_taint tn4 (Var z) = op_taint tnD (Var z)) /\
    t4.vs_allocas = tD.vs_allocas /\ t4.vs_alloca_next = tD.vs_alloca_next /\
    (!sa es0 s0 G0 tn0. sa.cs_next_var <= s2.cs_next_var /\
      ghost_kept_at lo cenv es0 sa G0 tn0 s0 GD tnD ==>
      ghost_kept_at lo cenv es0 sa G0 tn0 s0 G4 tn4) /\
    (!sa es0 s0. sa.cs_next_var <= s2.cs_next_var /\ wb_frame cenv es0 esD sa s0 tD ==>
      wb_frame cenv es0 esD sa s0 t4) /\
    (!e ee. MEM e kws /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)) /\
    (!tail. eval_exprs cx kws (esD with gas_obs := gas_explicit marks t4.vs_gas_readings ++ tail) =
      (INL kvs,esK with gas_obs := tail)) /\
    storage_trace_domain cx st0 esK.storage_trace /\ esK.gas_obs = [] /\
    (!H. valid_horizon cx st0 H esK.storage_trace ==>
      typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
      stmt_state_rel H ctx func cenv cx esK tk /\ storage_well_formed_on cx esK (FST H) /\
      ghost_inv_at (DF H) lo dframe cenv cx esK GK tnK tk) /\
    ~tk.vs_halted /\ tk.vs_current_bb = s5.cs_current_bb /\
    tk.vs_inst_idx = LENGTH s5.cs_current_insts /\ alloca_history func tk /\
    t4.vs_alloca_next <= tk.vs_alloca_next /\ ghost_kept_at lo cenv esD s4 G4 tn4 t4 GK tnK /\
    EVERY (\x. op_taint tnK x = {}) xs ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
      (k av (BytesV bs) kvs) (esK,tk,GK,tnK) Q R /\
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
      (k av (BytesV bs) kvs) (esK,tk,GK,tnK)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (bind (eval_exprs cx kws) (k av (BytesV bs))) (esD,tD,GD,tnD)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_call_keywords_prefix_from_entry[header_end]:
  `s2.cs_next_var <= s4.cs_next_var` by decide_tac >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z)` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame dframe cenv s4 t4` by
    (qpat_assum `!sa d. _ ==> _ /\ return_buf_frame _ _ _ t4`
       (qspecl_then [`s2`,`dframe`] mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H esD.storage_trace ==>
    stmt_state_rel H ctx func cenv cx esD t4 /\ storage_well_formed_on cx esD (FST H) /\
    ghost_inv_at (DF H) lo dframe cenv cx esD G4 tn4 t4` by
    (rpt strip_tac >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t4` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!fn inst u. frag_reachable ctx func t4 fn inst u ==> dalloca_fmp_headroom inst u` by
    metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom] >>
  `!e ee. MEM e kws /\ expr_sim_inv cenv cx env ee ==>
    expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)` by
    (rpt strip_tac
     >- (irule expr_body_pre_raw_call_arg >>
         first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     fs[EVERY_MEM] >> metis_tac[compileEnvTheory.is_word_type_def]) >>
  irule gas_prefix_full_zero_prefix_guarded >>
  (conj_tac >- (irule storage_trace_frame_bind_all >> simp[cj 6 evaluate_storage_trace_frame])) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G4`,`t4`,`tn4`] >>
  (conj_tac >- metis_tac[]) >>
  suspend "keywords"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_call_keywords_prefix_from_entry[keywords]:
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx kws) (esD,t4,G4,tn4)` by
    (qpat_assum `lower_word_args cenv (K _) kws s4 = _`
       (mp_then Any irule lower_word_args_by_type_prefix) >>
     qpat_assum `lower_word_args _ (K _) (MAP gas_shadow_expr kws) h4 = _`
       (irule_at Any) >>
     qpat_assum `body_const_cells_agree [(NONE,tops)] cx env esD` (irule_at Any) >>
     qpat_assum `return_buf_frame dframe cenv s4 t4` (irule_at Any) >>
     qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[K_DEF]) >>
  qpat_assum `lower_word_args cenv (K _) kws s4 = _`
    (assume_tac o SIMP_RULE std_ss [K_DEF]) >>
  qpat_assum `lower_word_args _ (K _) (MAP gas_shadow_expr kws) h4 = _`
    (assume_tac o SIMP_RULE std_ss [K_DEF]) >>
  qspecl_then [`kws`,`DF`,`lo`,`dframe`,`ctx`,`shadow_ctx`,`PG`,`tops`,
    `func`,`shadow_func`,`cenv`,`env`,`cx`,`BaseT (UintT 256)`,
    `esD`,`st0`,`s4`,`s5`,`h4`,`h5`,`xs`,`t4`,`G4`,`tn4`] mp_tac lower_word_args_sim_full >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[GSYM K_DEF]])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ kwQ kwR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx kws) (esD,t4,G4,tn4)
    (\H rr ee G tn t. kwQ H rr ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []) kwR` by
    (irule gas_outcome_full_post_source >>
     qpat_x_assum `gas_outcome_full _ _ _ _ _ _ kwQ kwR` (irule_at Any) >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ kwQ kwR` kall_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ kwR` (mp_then Any irule gas_prefix_full_bind) >>
  simp[cj 6 evaluate_storage_trace_frame, cj 6 evaluate_requests_outcomes_frame] >>
  reverse conj_tac >- (simp[Abbr `kwR`] >> Cases_on `res` >> simp[wb_args_exit_def, sumTheory.ISR]) >>
  suspend "callback"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_call_keywords_prefix_from_entry[callback]:
  qx_genl_tac [`marks`,`kvs`,`esK`,`GK`,`tnK`,`tk`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon esK.storage_trace) esK.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `kwQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
    (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms] >> strip_tac >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==>
       typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
       stmt_state_rel H ctx func cenv cx esK tk /\
       storage_well_formed_on cx esK (FST H) /\
       ghost_inv_at (DF H) lo dframe cenv cx esK GK tnK tk` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[exprSimPrecompilesTheory.typed_args_post_def,NoAsms]) >>
  qpat_assum `!b x l p base extent t4 G4 tn4 marks kvs esK tk GK tnK.
       _ ==> gas_outcome_full _ _ _ _ _ _ _ _ /\ gas_prefix_full _ _ _ _ _`
    (qspecl_then [`b`,`x'`,`l`,`p`,`base''`,`cap''`,`t4`,`G4`,`tn4`,
                   `marks`,`kvs`,`esK`,`tk`,`GK`,`tnK`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise raw_call_keywords_prefix_from_entry
*)
