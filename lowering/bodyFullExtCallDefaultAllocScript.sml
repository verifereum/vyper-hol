(* The nonword default buffer allocation, before reading the captured value.
   The path and the retained child judgment use the same endpoint. *)
Theory bodyFullExtCallDefaultAlloc
Ancestors
  bodyFullAllocaFresh abiEncodeMaterialize stateRelProj
  bodyFullHashKeccakFixed abiCallerAllocation abiCallerLocalScratch
  vyperStorageFootprint loweringPosts fragGasOriginPtr bodySimFull
  compileEnv exprLowering venomState venomExecSemantics venomMemDefs
  finite_map words freshWrites abiBuiltinAllocation emitHelperProps exprLoweringProps

val default_alloc_inputs = ``
  compile_alloc_buffer n sm = (buf,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  n < dimword (:256) /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts``;

val default_alloc_post = ``
    buf.buf_operand = Var q /\ not_fresh_at sn q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
           (s,G,tn) [] (OK u,Ga,ta)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sm s0 ee tv vv u /\
       ghost_inv_at (DF H) lo d cenv cx ee Ga ta u) /\
    ghost_kept_at lo cenv es sa Gi ti s0 Ga ta /\
    ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    u with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
              vs_alloca_next := s.vs_alloca_next;
              vs_inst_idx := s.vs_inst_idx |> = s /\
    u.vs_memory = s.vs_memory /\
    alloca_history func u /\ allocas_from lo u /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    lookup_var q u = SOME w /\ ptr_covers Ga ta q u n /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,n) /\
    FLOOKUP Ga q = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ w2n w + n <= u.vs_alloca_next /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
               FLOOKUP u.vs_allocas aid = SOME ent) /\
    (!aid b len. aid < sm.cs_next_id /\
                 FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n w) n b len) /\
    (!name b len. local_region cenv ee.scopes u name b len ==>
                  regions_disjoint (w2n w) n b len) /\
    ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
    (!i. i IN ta.t_mem <=>
         i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < w2n w + n)) /\
    (!x. not_fresh_at sm x ==>
         lookup_var x u = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
         op_taint ta (Var x) = op_taint tn (Var x))``;

Theorem extcall_default_alloc_cut_step:
  ^default_alloc_inputs ==>
  ?q w u Ga ta.
    (?r. step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [q]) s = OK r /\
         u = r with vs_inst_idx := SUC s.vs_inst_idx) /\
    ^default_alloc_post
Proof
  strip_tac >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace)
                  ctx func cenv cx ee s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     impl_tac >- fs[storage_trace_domain_def] >> simp[vv_post_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``]
    (SPEC_ALL alloc_buffer_origin_ptr_path_with_raw_endpoint)) >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`]
    (qx_choosel_then [`q`,`w`,`u`,`Ga`,`ta`,`r`]
       (map_every assume_tac o CONJUNCTS))) >>
  `emit_op ALLOCA [Lit (n2w n)] sm = (Var q,sn)` by
    (drule abi_builtin_alloc_buffer_shape >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [q]) s = OK r` by
    (qpat_x_assum `run_inst_seq _ _ = OK r` mp_tac >>
     fs[run_inst_seq_def, AllCaseEqs()]) >>
  `u = r with vs_inst_idx := SUC s.vs_inst_idx` by simp[arithmeticTheory.ADD1] >>
  `u.vs_halted = s.vs_halted /\ u.vs_memory = s.vs_memory /\
   contract_storage u = contract_storage s /\
   contract_transient u = contract_transient s` by
    (qpat_assum `u with <| vs_vars := _; vs_allocas := _;
                          vs_alloca_next := _; vs_inst_idx := _ |> = s`
       (SUBST1_TAC o SYM) >>
     simp[contract_storage_def, contract_transient_def]) >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s` by
    (Cases_on `vv_operand vv` >> simp[eval_operand_def] >>
     qpat_assum `u with <| vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _; vs_inst_idx := _ |> = s`
       (SUBST1_TAC o SYM) >> fs[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace)
                  ctx func cenv cx ee u` by
    (qpat_assum `!K. stmt_state_rel K ctx func cenv cx ee s ==>
                         stmt_state_rel K ctx func cenv cx ee u`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >> simp[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ ee u`
       (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  qexistsl [`q`, `w`, `u`, `Ga`, `ta`] >>
  conj_tac >- (qexists `r` >> simp[]) >>
  qpat_x_assum `u = r with vs_inst_idx := SUC _` kall_tac >>
  qpat_x_assum `u = r with vs_inst_idx := LENGTH _` kall_tac >>
  qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `ta = step_taint _ _ _ _` kall_tac >>
  simp[] >> conj_tac >- suspend "horizon_post" >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "caller_ghost"
QED

Resume extcall_default_alloc_cut_step[horizon_post]:
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` (strip_assume_tac o UNDISCH)) >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
  `stmt_state_rel H ctx func cenv cx ee u` by
    (qpat_assum `!K. stmt_state_rel K ctx func cenv cx ee s ==>
                     stmt_state_rel K ctx func cenv cx ee u`
       (qspec_then `H` mp_tac) >> simp[]) >>
  conj_tac
  >- (irule materialize_vv_post_alloc_storage_frame >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      qexistsl [`s`, `sm`] >> simp[] >> rpt strip_tac >>
      qpat_assum `!x. not_fresh_at sm x ==> lookup_var x u = _ /\ _`
        drule >> simp[]) >>
  `local_ptrs_rel func cenv ee.scopes s` by
    (qpat_assum `stmt_state_rel H _ _ _ _ ee s`
       (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  irule alloc_buffer_ghost_inv_at_locals >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`G`, `w2n w + n`, `func`, `s`, `sm`, `tn`] >> simp[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Resume extcall_default_alloc_cut_step[caller_ghost]:
  qpat_assum `stmt_state_rel H0 _ _ _ _ es s0`
    (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  `!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
     b + len <= s.vs_alloca_next` by
    (rpt strip_tac >> irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists `s0.vs_alloca_next` >> simp[] >>
     irule abi_caller_allocation_end >> simp[] >>
     qexistsl [`len`, `aid`, `b`] >> simp[arithmeticTheory.ADD_COMM]) >>
  `!name b len. local_region cenv es.scopes s0 name b len ==>
     b + len <= s.vs_alloca_next` by
    (rpt strip_tac >> irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists `s0.vs_alloca_next` >> simp[] >>
     irule abi_caller_local_end >>
     qexistsl [`cenv`, `func`, `name`, `es.scopes`] >> simp[]) >>
  irule alloc_buffer_ghost_kept_at >>
  qexistsl [`G`, `w2n w + n`, `s`, `tn`] >> simp[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Finalise extcall_default_alloc_cut_step

Theorem extcall_default_alloc_cut:
  ^default_alloc_inputs ==> ?q w u Ga ta. ^default_alloc_post
Proof
  disch_tac >> mp_tac (SPEC_ALL extcall_default_alloc_cut_step) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`q`,`w`,`u`,`Ga`,`ta`] (assume_tac o CONJUNCT2)) >>
  qexistsl_tac [`q`,`w`,`u`,`Ga`,`ta`] >> first_assum ACCEPT_TAC
QED
