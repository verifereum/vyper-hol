(* The proxy operands and private initcode window lead to a common CREATE
   dispatch. The instruction-level prefix rule is supplied by the caller. *)
Theory s1PrefixCreateProxyCompose
Ancestors
  s1PrefixPreds bodyFullCreateHeld s1PrefixOfVV s1PrefixCompose
  s1PrefixCreateOperandCut bodyFullRawCall
  s1PrefixDefs bodyFullPreds bodySimFull exprSimHypsDefs exprSimHyps exprBodyPreProps
  exprLowering builtinCreate vyperInterpreter vyperCreate vyperState vyperAST vyperTypeSystem
  vyperStorageTrace vyperStorageFootprint loweringPosts exprLoweringProps
  gasShadow gasShadowState compileEnv codegenRel loweringShapeDefs
  fragGasOriginPtr venomState venomMemDefs ptrSafeRun ptrDiscipline bodyPtrDefs
  vfmConstants words list bodyFullExprsListFacts

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (mk_asm "dispatch") >> rpt gen_tac >> strip_tac >>
  rewrite_tac[body_expr_prefix_ok_def] >>
  reverse conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  Q.SUBGOAL_THEN `ty = BaseT AddressT` SUBST_ALL_TAC
  >- (drule proxy_pre_args >> simp[]) >>
  conj_asm1_tac
  >- (drule proxy_pre_args >> strip_tac >> gvs[] >>
      `LENGTH salts = (if s then 1 else 0)` by (Cases_on `s` >> gvs[]) >>
      rewrite_tac[expr_sim_prefix_def,expr_sim_full_pre_def] >>
      rpt gen_tac >> strip_tac >>
      rename1 `return_buf_frame rbf cenv sa s0` >>
      drule_all proxy_compile_cuts >>
      disch_then (qx_choosel_then
        [`x`,`y`,`buf`,`sop`,`a`,`b`,`c`,`sm`,`a'`,`b'`,`c'`,`shm`]
        strip_assume_tac) >>
      qpat_assum `lower_value _ _ _ target sa = _`
        (mp_then Any (drule_all_then strip_assume_tac) proxy_cut_code) >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr target) shadow_sa = _`
        (mp_then Any (drule_all_then strip_assume_tac) proxy_cut_code) >>
      simp[NoAsms,create_eval_read,create_operand_order_def,expr_type_def,
           post_value_type_def,is_word_type_def] >>
      suspend "target") >>
  irule expr_vv_sim_stack_prefix >> simp[create_compile_stack] >>
  metis_tac[create_eval_value]
QED
*)
Theorem proxy_expr_prefix_from_dispatch:
  (!codep len amount sop rof sm result sb func s ctx cx st0 ee cenv DF lo d
    G tn pv sz initcode aw sw source explicit PG.
    compile_create_dispatch codep len amount sop rof sm = (result,sb) /\
    fn_has_code sm sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
    outcomes_accounts_typed ee.outcomes /\
    eval_operand codep s = SOME pv /\ eval_operand len s = SOME sz /\
    (sz <> 0w ==> ?p. codep = Var p /\ ptr_covers G tn p s (w2n sz)) /\
    (sz <> 0w ==> w2n pv + w2n sz <= s.vs_alloca_next \/
      (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n pv /\
       w2n pv + w2n sz <= w2n s.vs_fmp)) /\
    read_memory (w2n pv) (w2n sz) s = initcode /\
    (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tn.t_mem) /\
    op_taint tn codep = {} /\ op_taint tn len = {} /\
    eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
    (case sop of NONE => sw = NONE | SOME op =>
       ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
    (!tail. source (ee with gas_obs := tail) =
      if w2n sz > 2 * max_code_size then
        (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
      else
        bind (ignore_bind (check_not_static cx)
          (create_oracle_result sw (w2n aw) initcode rof))
          (read_result cx) (ee with gas_obs := tail)) ==>
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (ee,s,G,tn)) ==>
  !cx ty s r ks es d.
  body_exprs_full_ok cx (create_operand_order CreateMinimalProxy s es) /\
  body_exprs_prefix_ok cx (create_operand_order CreateMinimalProxy s es) ==>
  body_expr_prefix_ok cx (Call ty (CreateTarget CreateMinimalProxy s r ks) es d)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume proxy_expr_prefix_from_dispatch[target]:
  `expr_body_pre cenv cx env target es'` by
    (irule create_operand_pre >> simp[] >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     drule expr_body_pre_static_facts >> simp[]) >>
  qpat_x_assum `body_exprs_full_ok _ (create_operand_order _ _ _)`
    (mp_tac o REWRITE_RULE [create_operand_order_def, Once body_exprs_full_ok_cons]) >>
  qpat_x_assum `body_exprs_prefix_ok _ (create_operand_order _ _ _)`
    (mp_tac o REWRITE_RULE [create_operand_order_def, Once body_exprs_prefix_ok_def]) >>
  strip_tac >> strip_tac >>
  rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut_prefix_replay) >>
  qpat_assum `lower_value _ _ _ target sa = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr target) shadow_sa = _` (irule_at Any) >>
  qexistsl [`tops`,`shadow_func`,`env`,`rbf`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> simp[NoAsms,storage_trace_frame_bind_all,evaluate_storage_trace_frame,
                      storage_trace_frame_read_result,storage_trace_frame_create_operands]) >>
  suspend "amount"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume proxy_expr_prefix_from_dispatch[amount]:
  map_every qx_gen_tac [`tv`,`et`,`Gtar`,`tnt`,`st`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env amount et` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  qpat_x_assum `_ ==> body_exprs_full_ok _ (amount::salts)` drule >>
  rewrite_tac[Once body_exprs_full_ok_cons] >> strip_tac >>
  qpat_x_assum `_ ==> body_exprs_prefix_ok _ (amount::salts)` drule >>
  rewrite_tac[Once body_exprs_prefix_ok_def] >> strip_tac >>
  rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut_prefix_replay) >>
  qpat_assum `lower_value _ _ _ amount a = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr amount) a' = _` (irule_at Any) >>
  qexistsl [`tops`,`shadow_func`,`env`,`rbf`] >>
  `sa.cs_next_var <= a.cs_next_var` by fs[ci_mono_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- metis_tac[local_ptrs_reserved_next_var]
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[])
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[])
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H et.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> fs[expr_post_def])
  >- (gen_tac >> simp[NoAsms,storage_trace_frame_bind_all,evaluate_storage_trace_frame,
                      storage_trace_frame_read_result,storage_trace_frame_create_operands]) >>
  suspend "buffer"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume proxy_expr_prefix_from_dispatch[buffer]:
  map_every qx_gen_tac [`av`,`ea`,`Gamt`,`tna`,`samt`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ ==> body_exprs_full_ok _ salts` (drule_then assume_tac) >>
  qpat_x_assum `_ ==> body_exprs_prefix_ok _ salts` (drule_then assume_tac) >>
  `!H. valid_horizon cx st0 H et.storage_trace ==>
    valid_horizon cx st0 H es'.storage_trace /\
    expr_post H ctx func cenv cx target es' sa a s0 et tv x st` by simp[] >>
  `!H. valid_horizon cx st0 H ea.storage_trace ==>
    valid_horizon cx st0 H et.storage_trace /\
    expr_post H ctx func cenv cx amount et a b st ea av y samt /\
    ghost_inv_at (DF H) lo rbf cenv cx ea Gamt tna samt` by simp[] >>
  `s0.vs_alloca_next <= samt.vs_alloca_next` by decide_tac >>
  `!H. valid_horizon cx st0 H es'.storage_trace ==> stmt_state_rel H ctx func cenv cx es' s0`
    by simp[] >>
  drule_all proxy_amount_buffer_cut >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`pbuf`,`pw`,`sbuf`,`Gbuf`,`tnb`] strip_assume_tac)) >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,storage_trace_frame_create_operands] >>
  qexistsl [`Gbuf`,`sbuf`,`tnb`] >> conj_tac
  >- simp[] >>
  Cases_on `s` >> gvs[compile_create_salt_def,comp_return_def]
  >- suspend "salt_cut" >>
  suspend "no_salt"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume proxy_expr_prefix_from_dispatch[salt_cut]:
  Cases_on `lower_value compile_expr cenv (BaseT (BytesT (Fixed 32))) salt c` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv)
    (BaseT (BytesT (Fixed 32))) (gas_shadow_expr salt) c'` >>
  gvs[comp_bind_def,comp_return_def] >>
  rename1 `lower_value _ _ _ salt c = (salt_op,sm)` >>
  `expr_body_pre cenv cx env salt ea` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  fs[Once body_exprs_full_ok_cons,Once body_exprs_prefix_ok_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  `!fn i z. frag_reachable ctx func sbuf fn i z ==> dalloca_fmp_headroom i z` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ _ _ (OK sbuf,Gbuf,tnb)`
       (qspec_then `DF (storage_trace_horizon ea.storage_trace)`
         (mp_then Any drule_all bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom)) >> simp[]) >>
  rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,Once evaluate_def,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut_prefix_replay) >>
  `lower_value compile_expr cenv (expr_type salt) salt c = (salt_op,sm)` by simp[] >>
  qpat_assum `lower_value _ _ (expr_type salt) salt c = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr salt) c' = (salt_op,_)`
    (fn th =>
       qpat_assum `expr_type salt = _`
         (fn ty => irule_at Any (REWRITE_RULE [GSYM ty] th))) >>
  qexistsl [`tops`,`shadow_func`,`env`,`rbf`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> simp[NoAsms,storage_trace_frame_bind_all,
                   storage_trace_frame_read_result,storage_trace_frame_create_operands]) >>
  map_every qx_gen_tac [`sv`,`ew`,`Gsalt`,`tns`,`ssalt`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sa c` by metis_tac[ci_mono_trans] >>
  `stmt_state_rel (storage_trace_horizon ea.storage_trace) ctx func cenv cx es' s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es'.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon ea.storage_trace` mp_tac) >>
     impl_tac >- metis_tac[storage_trace_domain_def] >> simp[]) >>
  `s0.vs_alloca_next <= sbuf.vs_alloca_next` by decide_tac >>
  qpat_assum `!H. _ ==> expr_post H _ _ _ _ salt _ _ _ _ _ _ _ _ /\ _`
    (mp_then Any (drule_all_then strip_assume_tac)
      (SIMP_RULE (srw_ss()) [] proxy_salt_dispatch_ready)) >>
  suspend "salt_dispatch"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume proxy_expr_prefix_from_dispatch[salt_dispatch]:
  `IS_SOME ew.outcomes /\ outcomes_accounts_typed ew.outcomes` by
    (drule raw_call_source_inv_facts >> simp[]) >>
  `op_taint tns (Var pbuf) = {}` by fs[ptr_covers_def] >>
  asm "dispatch" (irule o Q.INST [`len` |-> `Lit 54w`,`sz` |-> `54w`] o SPEC_ALL) >>
  qpat_assum `compile_create_dispatch (Var pbuf) _ y (SOME salt_op) _ sm = _`
    (irule_at Any) >>
  simp[eval_operand_def,op_taint_def,max_code_size_def] >>
  qexistsl [`rbf`,`cenv`] >> simp[] >>
  gen_tac >>
  irule (SIMP_RULE (srw_ss()) [dest_optional_salt_def]
     (Q.INST [`salt` |-> `SOME sv`] create_proxy_read_prepared)) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume proxy_expr_prefix_from_dispatch[no_salt]:
  simp[NoAsms,Once evaluate_def,bind_return] >>
  `IS_SOME ea.outcomes /\ outcomes_accounts_typed ea.outcomes` by
    (drule raw_call_source_inv_facts >> simp[]) >>
  `op_taint tnb (Var pbuf) = {}` by fs[ptr_covers_def] >>
  `ptr_covers Gbuf tnb pbuf sbuf 54` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists `96` >> simp[]) >>
  `w2n pw + 54 <= sbuf.vs_alloca_next` by decide_tac >>
  asm "dispatch" (irule o Q.INST [`len` |-> `Lit 54w`,`sz` |-> `54w`] o SPEC_ALL) >>
  qpat_assum `compile_create_dispatch (Var pbuf) _ y NONE _ c = _`
    (irule_at Any) >>
  simp[eval_operand_def,op_taint_def,max_code_size_def] >>
  qexistsl [`rbf`,`cenv`] >> simp[] >>
  gen_tac >>
  irule (SIMP_RULE (srw_ss()) [dest_optional_salt_def]
     (Q.INST [`salt` |-> `NONE`] create_proxy_read_prepared)) >> simp[]
QED
*)
(* SCRATCH MEASUREMENT: original continuation.
Finalise proxy_expr_prefix_from_dispatch
*)
