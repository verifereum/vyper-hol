(* Keep the actual destination ADD, unwrap and store witnesses of a
   successfully evaluated StructLit field. *)
Theory entryCreateStructLitContinuation
Ancestors
  bodyFullStructLit bodyFullStructLitAddEndpoint bodyFullIfExpReach
  entryCreateStructLit entryCreateStructLitSmallStore entryCreateStructLitBytesStore
  entryCreateStructLitReadObserve entryCreateStructLitReadCut
  entryCreateStructLitStoreObserve entryCreateStructLitExitFetch entryCreateStructLitAggregateStore
  entryCreateIfExpTypedObserverCode entryCreateIfExpTypedObserverPath
  entryCreatePosSnapshotCode exprSimAbiEncodeObliviousCode
  compileExprAllocaFresh fragGasOriginPtrExec entryCreateFocusSpec
  entryCreateIntervalLayout fragFuel bodyFullIfExpObserve
  entryCreateStructLitVisit venomExecProofs fragExec list vyperStorageFootprint
  abiEncoderProps venomInst venomExecSemantics

Definition field_admin_observation_def:
  field_admin_observation E ctx f tops cx st0 source es a b s t <=>
    create_layout a b /\ no_phi_fn f ==>
    create_operand_full_scope a b E ctx f s [] (OK t) /\
    create_operand_cut a b E ctx f tops cx st0 source (es,s)
End

Triviality field_store_observations:
  structlit_word_store_observed
    (field_admin_observation explicit ctx func tops cx st0 source es) ctx func explicit /\
  structlit_zero_store_observed
    (field_admin_observation explicit ctx func tops cx st0 source es) ctx func explicit /\
  structlit_bytes_store_observed
    (field_admin_observation explicit ctx func tops cx st0 source es) ctx func explicit
Proof
  simp_tac bool_ss [structlit_word_store_observed_def,
    structlit_zero_store_observed_def, structlit_bytes_store_observed_def] >>
  rpt conj_tac >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  >- (mp_tac (SIMP_RULE bool_ss [create_operand_at_def]
        structlit_word_store_site) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (qx_choosel_then [`t`,`Gf`,`tnf`] strip_assume_tac) >>
      qexistsl_tac [`t`,`Gf`,`tnf`] >> (conj_tac >- simp[field_admin_observation_def]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (mp_tac (SIMP_RULE bool_ss [create_operand_at_def]
        structlit_zero_store_site) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (qx_choosel_then [`t`,`Gf`,`tnf`] strip_assume_tac) >>
      qexistsl_tac [`t`,`Gf`,`tnf`] >> (conj_tac >- simp[field_admin_observation_def]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac structlit_bytes_store_site >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 (qx_choosel_then [`u`,`G2`,`tn2`] (REPEAT_TCL CONJUNCTS_THEN assume_tac)) assume_tac) >>
  qexistsl_tac [`u`,`G2`,`tn2`] >> (conj_tac >- simp[field_admin_observation_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `!i. ~(w2n dw <= i /\ i < _) ==> _` mp_tac >>
  simp_tac bool_ss [DE_MORGAN_THM]
QED

Triviality field_add_observation:
  structlit_add_observed
    (field_admin_observation E ctx func tops cut_cx cut_st0 source cut_es) ctx func
Proof
  simp_tac bool_ss [structlit_add_observed_def, AND_CLAUSES] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all structlit_child_add_full_endpoint >>
  disch_then (qspec_then `PG` (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac)) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >>
  conj_tac >- (simp_tac bool_ss [field_admin_observation_def] >> disch_tac >>
    mp_tac (SIMP_RULE bool_ss [create_operand_at_def] (Q.INST [`sa` |-> `sm`,
      `sb` |-> `sn`, `dst` |-> `out`, `f` |-> `func`, `C` |-> `ctx`,
      `cx` |-> `cut_cx`, `st0` |-> `cut_st0`, `es` |-> `cut_es`] structlit_add_site)) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Triviality field_typed_store_observation:
  ifexp_observed_typed_store
    (\ctx f a b s t. create_layout a b /\ no_phi_fn f ==>
      create_operand_at a s /\ create_operand_full_scope a b E ctx f s [] (OK t))
Proof
  irule ifexp_typed_store_observation_from_install >>
  rpt gen_tac >> strip_tac >> drule_all ifexp_typed_store_observer_code >>
  disch_then (qx_choose_then `id` strip_assume_tac) >>
  qexists_tac `id` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Triviality field_aggregate_store_observation:
  structlit_aggregate_store_observed
    (field_admin_observation E ctx f tops cx st0 source es) ctx f E
Proof
  `structlit_aggregate_store_observed
    (\a b s t. create_layout a b /\ no_phi_fn f ==>
      create_operand_full_scope a b E ctx f s [] (OK t) /\
      !tops cx st0 (source : evaluation_state -> 'a evaluation_result) es.
        create_operand_cut a b E ctx f tops cx st0 source (es,s)) ctx f E` by
    (irule structlit_aggregate_observation_from_typed >>
     simp_tac bool_ss [field_typed_store_observation] >>
     rpt gen_tac >> MATCH_ACCEPT_TAC structlit_nonbytes_store_here) >>
  pop_assum mp_tac >>
  simp_tac bool_ss [field_admin_observation_def, structlit_aggregate_store_observed_def] >>
  disch_then (mk_asm "aggregate") >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  asm "aggregate" (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then drule_all >>
  disch_then (qspec_then `PG` (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  conj_tac
  >- (disch_tac >>
      qpat_assum `create_layout sa sb /\ no_phi_fn f ==> _` mp_tac >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (CONJUNCTS_THEN2 assume_tac
        (qspecl_then [`tops`,`cx`,`st0`,`source`,`es`] assume_tac)) >>
      asm_rewrite_tac[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Triviality field_read_exit_fetch:
  unwrap_value ce vv a = (op,b) /\ create_layout a b /\
  fn_has_code a b f /\ fn_inst_ids_distinct f ==>
  !bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
    i.inst_id NOTIN frag_ids a b
Proof
  strip_tac >>
  `entry_shape a b` by
    (drule (REWRITE_RULE [code_action_def] admin_unwrap_code_action) >>
     simp[code_step_def]) >>
  rpt gen_tac >> strip_tac >>
  irule installed_covered_exit_fetch >> simp[] >> metis_tac[unwrap_value_added_id]
QED

Definition field_read_observation_def:
  field_read_observation E ctx f (cx : evaluation_context) (st0 : evaluation_state)
      (tv : eval_result) (ee : evaluation_state) a b s t <=>
    ((!bb. lookup_block b.cs_current_bb f.fn_blocks = SOME bb ==>
           phi_prefix_length bb.bb_instructions = 0) /\
     (!bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
             get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
             i.inst_id NOTIN frag_ids a b)) ==>
    create_operand_full_scope a b E ctx f s [] (OK t)
End

Triviality field_read_observation:
  structlit_read_observed (field_read_observation E ctx f) ctx f E
Proof
  simp_tac bool_ss [structlit_read_observed_def, field_read_observation_def] >>
  MATCH_ACCEPT_TAC (BETA_RULE (REWRITE_RULE [structlit_read_observed_def]
    structlit_read_observed_scoped))
QED

Triviality field_path_normal_not_halted:
  gas_origin_ptr_path cfg (s,G,tn) marks (OK t,G',tn') ==> ~t.vs_halted
Proof
  PairCases_on `cfg` >> strip_tac >> drule gas_origin_ptr_path_exec >>
  simp[exit_result_def] >> metis_tac[]
QED

Theorem structlit_field_normal_selected:
  !inv'. inv' = (\(H : (bool # bytes32 # type_value) list # num list) ee cs G tn s cells off.
    stmt_state_rel H ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s /\
    wb_frame ce ees ee fr sf s /\ ghost_kept_at lo ce ees fr Gf tnf sf G tn /\
    MAP FDOM ees.scopes = MAP FDOM ee.scopes /\
    ~s.vs_halted /\ expr_sim_full_endpoint func cs sf s /\
    not_fresh_at cs root /\ lookup_var root s = SOME (n2w addr) /\
    ptr_covers G tn root s capacity /\
    FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\
    MEM (mk_inst aid ALLOCA [Lit(n2w capacity)] [root]) (fn_insts func) /\
    lo <= addr /\ addr+capacity < dimword(:256) /\
    fr.cs_next_id <= aid /\ aid < cs.cs_next_id /\
    fr.cs_next_var <= cs.cs_next_var /\ off <= capacity /\
    (!name p k. local_region ce ee.scopes s name p k ==>
      addr+capacity <= p \/ p+k <= addr) /\
    (!name p k. local_region ce ees.scopes sf name p k ==>
      addr+capacity <= p \/ p+k <= addr) /\
    (!old p k. FLOOKUP sf.vs_allocas old = SOME(p,k) /\ old < fr.cs_next_id ==>
      addr+capacity <= p \/ p+k <= addr) /\
    EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+off) cells /\
    literal_prefix_ok cells tn s /\
    (pure ==> pure_frame ce func ees fr sf s)) ==>
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit(n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst fty (lowered_value_type ce e) su = ((),ss) /\
  fn_has_code sm sn func /\ fn_has_code sn su func /\ fn_has_code su ss func /\
  create_layout sm sn /\ create_layout sn su /\ create_layout su ss /\
  fn_inst_ids_distinct func /\ MEM func ctx.ctx_functions /\
  body_inv (cx_tops cx) ctx ce cx /\
  body_const_cells_agree [(NONE,cx_tops cx)] cx env es /\
  body_exprs_full_ok cx (e::MAP SND (fs : (string # expr) list)) /\
  expr_body_pre ce cx env e es /\ expr_sim_inv ce cx env es /\
  (?Hbase : (bool # bytes32 # type_value) list # num list.
    stmt_state_rel Hbase ctx func ce cx ees sf) /\
  arg_type_fits (expr_type e) fty /\ evaluate_type (get_tenv cx) fty = SOME ftv /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME(PtrVar(Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME(PtrVar(Var x) sz) ==> not_fresh_at si x) /\
  return_buf_frame d ce si s0 /\
  (pure ==> ~EXISTS expr_has_effect (e::MAP SND fs)) /\
  storage_trace_domain cx st0 es.storage_trace /\
  off + type_memory_size_list (ftv::rest_tvs) <= capacity /\
  gas_admissible (eval_exprs cx (e::MAP SND fs))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     inv' H es si G0 tn0 s0 cells off) /\
  (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL tv,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~t.vs_halted /\ mid.gas_obs = [] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,si,sm,s0,vv,G0,tn0)
       H (INL tv : eval_result + exception) mid G1 tn1 t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) marks (OK t,G1,tn1)) ==>
  ?v t' G' tn' z G'' tn'' u G2 tn2.
    structlit_admin_visit (gas_explicit_sites ctx shadow_ctx) ctx func
      (cx_tops cx) cx st0 source cut_es sm sn t t' /\
    structlit_admin_visit (gas_explicit_sites ctx shadow_ctx) ctx func
      (cx_tops cx) cx st0 source cut_es sn su t' z /\
    structlit_admin_visit (gas_explicit_sites ctx shadow_ctx) ctx func
      (cx_tops cx) cx st0 source cut_es su ss z u /\
    read_result cx tv mid = (INL v,mid) /\ value_has_type ftv v /\
    type_memory_bytes ce fty = type_memory_size ftv /\
    local_ptrs_reserved ce ss /\
    (!x sz. ce.ce_return_buf = SOME(PtrVar(Var x) sz) ==> not_fresh_at ss x) /\
    (!x sz. ce.ce_return_pc = SOME(PtrVar(Var x) sz) ==> not_fresh_at ss x) /\
    return_buf_frame d ce ss u /\
    (!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_fmp_headroom inst s) /\
    body_const_cells_agree [(NONE,cx_tops cx)] cx env mid /\
    expr_sim_inv ce cx env mid /\ body_exprs_full_ok cx (MAP SND fs) /\
    off + type_memory_size ftv + type_memory_size_list rest_tvs <= capacity /\
    gas_admissible (eval_exprs cx (MAP SND fs))
      (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) mid /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       inv' H mid ss G2 tn2 u
         (cells++[(ftv,v,addr+off,type_memory_size ftv)]) (off+type_memory_size ftv)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (t,G1,tn1) [] (OK t',G',tn') /\
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (t',G',tn') [] (OK z,G'',tn'') /\
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (z,G'',tn'') [] (OK u,G2,tn2) /\
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (t,G1,tn1) [] (OK u,G2,tn2))
Proof
  gen_tac >> disch_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `fld_admin = field_admin_observation (gas_explicit_sites ctx shadow_ctx)
    ctx func (cx_tops cx) cx st0 source cut_es` >>
  qabbrev_tac `fld_read = field_read_observation (gas_explicit_sites ctx shadow_ctx) ctx func` >>
  qspec_then `inv'` mp_tac
    (Q.INST [`field_obs` |-> `fld_admin`, `field_read_obs` |-> `fld_read`]
      structlit_field_normal_continuation_observed) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- simp[Abbr `fld_admin`, Abbr `fld_read`, field_add_observation,
    field_read_observation, field_store_observations, field_aggregate_store_observation]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`v`,`t'`,`G'`,`tn'`,`z`,`G''`,`tn''`,`u`,`G2`,`tn2`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (mp_tac (Q.INST [`tops` |-> `cx_tops cx`, `cenv` |-> `ce`, `fn` |-> `func`]
       body_inv_no_phi) >> asm_simp_tac bool_ss []) >>
  `no_phi_fn func` by simp[no_phi_fn_def, EVERY_MEM] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  `~t'.vs_halted /\ ~z.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
      (drule_then (strip_assume_tac o
        SIMP_RULE bool_ss [field_path_normal_not_halted] )) >>
     conj_tac >> (irule field_path_normal_not_halted >> first_assum (irule_at Any))) >>
  qexistsl_tac [`v`,`t'`,`G'`,`tn'`,`z`,`G''`,`tn''`,`u`,`G2`,`tn2`] >>
  conj_tac
  >- (qpat_x_assum `fld_admin sm sn t t'` mp_tac >>
      asm_simp_tac bool_ss [Abbr `fld_admin`, field_admin_observation_def,
        structlit_admin_visit_def]) >>
  conj_tac
  >- (simp[structlit_admin_visit_def] >> conj_tac
      >- (`!bb. lookup_block su.cs_current_bb func.fn_blocks = SOME bb ==>
               phi_prefix_length bb.bb_instructions = 0` by
            (rpt strip_tac >> drule venomExecProofsTheory.lookup_block_MEM >> simp[]) >>
          `!bb i. lookup_block su.cs_current_bb func.fn_blocks = SOME bb /\
                  get_instruction bb (LENGTH su.cs_current_insts) = SOME i ==>
                  i.inst_id NOTIN frag_ids sn su` by
            (mp_tac (Q.INST [`a` |-> `sn`, `b` |-> `su`, `f` |-> `func`,
               `op` |-> `op`] field_read_exit_fetch) >> asm_simp_tac bool_ss []) >>
          qpat_x_assum `fld_read cx st0 tv mid sn su t' z` mp_tac >>
          simp_tac bool_ss [Abbr `fld_read`, field_read_observation_def] >>
          disch_then irule >> conj_tac >> first_assum ACCEPT_TAC) >>
      irule structlit_installed_read_cut >> simp[] >>
      qexistsl_tac [`ce`,`op`,`vv`] >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `fld_admin su ss z u` mp_tac >>
      asm_simp_tac bool_ss [Abbr `fld_admin`, field_admin_observation_def,
        structlit_admin_visit_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
