(* Source and compiler premises for the storage aggregate pointer branch. *)
Theory exprSimPtrTopLevelStorageBranch
Ancestors
  sourceUnitExecution
  exprSimPtrTopLevelStorageSemantic exprSimPtrTopLevelStorageFrame
  exprSimTopLevelStorage exprSimUnwrapProps exprSimPtrTopLevelStorageAlloc
  vyperTypeGlobalLookupSoundness vyperStorageLayoutSafety
  exprSimHypsDefs exprSimTopLevelProps accountsRelProps exprSimMemorySource
  vyperInterpreter vyperLookupStorage vyperAST context vyperState
  exprSimHyps exprLowering exprLoweringProps compileEnv loweringStateRelDefs loweringPosts exprSimSource
  bodyPtrDefs exprSimPtrTopLevelStorageCopy words pred_set venomState storageDecodeMemory
  exprSimPtrTopLevelStorageDecode exprSimStorageCopy
  exprSimPtrTopLevelStorageEnsure exprSimPtrTopLevelStoragePost exprSimCopy exprSimAlloc
  loweringHalt fragExec ghostPcTransportPtr fragGasPathPtr valueEncoding venomInst
  gasSummary ptrSafetyTransport vyperStorageFootprint exprSimUnwrap ptrDiscipline

Theorem toplevel_storage_branch_source:
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  read_storage_slot cx tr (n2w slot) tv es = (INL v,es) /\
  stmt_state_rel H ctx fn cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\
  regions_consistent (FST H) /\ MEM (tr,n2w slot,tv) (FST H) ==>
  typ = ann /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tv /\
  w2n ((n2w slot):bytes32) + type_slot_size tv <= dimword (:256) /\
  vv_post H ctx fn cenv cx (TopLevelName ann (src,id)) es sa sa s
    (es with <|storage_trace := obs; gas_obs := []|>) (Value v)
    (LocatedValue ann (mk_ptr (Lit (n2w slot))
      (if tr then LocTransient else LocStorage))) s
Proof
  strip_tac >>
  `typ = ann` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     metis_tac[TopLevelName_storage_decl_type_eq]) >> gvs[] >>
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tv` by
    (qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
     qpat_x_assum `MEM _ _` mp_tac >> rpt (pop_assum kall_tac) >>
     rpt strip_tac >> gvs[storage_well_formed_on_def]) >>
  `w2n ((n2w slot):bytes32) + type_slot_size tv <= dimword (:256)` by
    (qpat_x_assum `regions_consistent _` mp_tac >>
     qpat_x_assum `MEM _ _` mp_tac >> rpt (pop_assum kall_tac) >>
     rpt strip_tac >> gvs[regions_consistent_def] >>
     qpat_x_assum `!b slot tv. MEM _ _ ==> _` (drule_then mp_tac) >> simp[]) >>
  `!st. storage_read_live H tr st (n2w slot) tv` by
    metis_tac[observed_storage_region_read_live] >>
  `!p tail. read_result cx (PlaceR (StoragePlace tr (n2w slot) tv))
       (es with <|gas_obs := tail; storage_trace := p|>) =
     (INL v, es with <|gas_obs := tail; storage_trace := p|>)` by
    (rpt gen_tac >>
     `read_result cx (PlaceR (StoragePlace tr (n2w slot) tv)) es = (INL v,es)` by
       simp[read_result_def, read_place_def] >>
     drule read_result_gas_obs >> disch_then (qspec_then `tail` assume_tac) >>
     qspecl_then [`cx`, `PlaceR (StoragePlace tr (n2w slot) tv)`,
                  `es with gas_obs := tail`, `p`] mp_tac
       (Q.GENL [`cx`, `r`, `st`, `p`] vyperEvalPureExprTheory.read_result_trace) >>
     simp[]) >>
  simp[] >>
  conj_tac >- (fs[] >> decide_tac) >>
  conj_tac >- (fs[] >> decide_tac) >>
  irule vv_post_read_result >>
  qexists_tac `PlaceR (StoragePlace tr (n2w slot) tv)` >>
  conj_tac >- simp[] >>
  irule (SRULE [] toplevel_storage_value_post) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- fs[]
  >- first_assum ACCEPT_TAC
  >- (qexists_tac `v` >> first_assum ACCEPT_TAC)
  >- fs[]
  >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED

Theorem toplevel_storage_branch_compile:
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  read_storage_slot cx tr (n2w slot) tv es = (INL v,es) /\
  stmt_state_rel H ctx fn cenv cx es s /\ ~is_word_type ann /\
  lower_value compile_expr cenv ty (TopLevelName ann (src,id)) sa = (op,sb) ==>
  compile_ensure_in_memory (Lit (n2w slot))
    (if tr then LocTransient else LocStorage)
    (type_memory_bytes cenv ann) (type_slot_size tv)
    cenv.ce_is_ctor cenv.ce_imm_alloca sa = (op,sb) /\
  type_memory_bytes cenv ann = 32 * type_slot_size tv /\
  type_memory_size tv <= type_memory_bytes cenv ann /\
  type_memory_bytes cenv ann < dimword (:256)
Proof
  strip_tac >>
  `typ = ann` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     metis_tac[TopLevelName_storage_decl_type_eq]) >> gvs[] >>
  `expr_body_pre cenv cx env (TopLevelName ann (src,id)) es` by
    metis_tac[expr_sim_pre_body_pre] >>
  drule_all toplevel_storage_copy_capacity >> strip_tac >>
  drule_all toplevel_storage_copy_word_count >> strip_tac >>
  `type_memory_size tv <= type_memory_bytes cenv ann` by
    (drule expr_body_pre_copy_ok >> simp[expr_type_def]) >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  Cases_on `tr` >>
  gvs[lower_value_def, comp_bind_def, compile_expr_def, expr_type_def,
      unwrap_value_def, mk_ptr_def]
QED

Theorem toplevel_storage_backend_taint_dead:
  stor_taint_ok H cx tn s ==>
  !tr k j. (k,j) IN toplevel_copy_source_taint
    (if tr then LocTransient else LocStorage) tn ==>
    storage_dead H tr
      (if tr then contract_transient s else contract_storage s) (w2n k) j
Proof
  strip_tac >> Cases >> rpt gen_tac >> strip_tac >>
  gvs[stor_taint_ok_def, cx_dead_def, toplevel_copy_source_taint_def,
      SUBSET_DEF, pairTheory.FORALL_PROD] >>
  Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >>
  gvs[contract_storage_def, contract_transient_def, vfmStateTheory.lookup_account_def] >>
  metis_tac[]
QED

Theorem toplevel_storage_branch_taint_live:
  ghost_inv H d cenv cx es G tn s /\
  (!st. storage_read_live H tr st a tv) /\
  w2n a + type_slot_size tv <= dimword (:256) ==>
  !i j. i < type_slot_size tv /\ j < 32 /\
    (a+n2w i,j) IN toplevel_copy_source_taint
      (if tr then LocTransient else LocStorage) tn ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n a) tv (w2n a+i) j
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `stor_taint_ok H cx tn s` by fs[ghost_inv_def] >>
  drule toplevel_storage_backend_taint_dead >>
  disch_then (qspecl_then [`tr`, `a+n2w i`, `j`] mp_tac) >> simp[] >>
  `w2n (a+n2w i) = w2n a+i` by
    (`w2n a+i < dimword (:256)` by decide_tac >>
     `a+n2w i = n2w (w2n a+i)` by metis_tac[word_add_n2w, n2w_w2n] >>
     asm_rewrite_tac[w2n_n2w] >> simp[]) >>
  simp[] >> strip_tac >>
  `w2n a <= w2n a+i /\ w2n a+i < w2n a+type_slot_size tv` by decide_tac >>
  fs[storage_read_live_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem toplevel_storage_range_dead_bytes:
  storage_range_agree st rt a tv ==>
  !k j. dead_bytes rt (w2n a) tv k j = dead_bytes st (w2n a) tv k j
Proof
  strip_tac >> rpt gen_tac >> irule (cj 1 dead_bytes_live_frame) >>
  rpt strip_tac >>
  `i < dimword (:256)` by fs[storage_range_agree_def] >>
  qpat_x_assum `storage_range_agree _ _ _ _` mp_tac >>
  simp[storage_range_agree_def] >>
  disch_then (qspec_then `n2w i` mp_tac) >> simp[]
QED

Theorem toplevel_storage_live_memory_range:
  storage_range_agree st rt a tv /\
  storage_live_memory rt (w2n a) tv b mem ==>
  storage_live_memory st (w2n a) tv b mem
Proof
  strip_tac >> drule toplevel_storage_range_dead_bytes >> strip_tac >>
  simp[storage_live_memory_def, copy_bytes_def] >> rpt strip_tac >>
  `w2n a+i < dimword (:256)` by fs[storage_range_agree_def] >>
  `~dead_bytes rt (w2n a) tv (w2n a+i) b'` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  qpat_x_assum `storage_live_memory _ _ _ _ _` mp_tac >>
  simp[storage_live_memory_def, copy_bytes_def] >>
  disch_then (qspecl_then [`i`, `b'`] mp_tac) >> simp[] >>
  disch_then SUBST1_TAC >>
  qpat_x_assum `storage_range_agree _ _ _ _` mp_tac >>
  simp[storage_range_agree_def] >> strip_tac >>
  qpat_x_assum `!k b. _` (qspecl_then [`n2w (w2n a+i)`, `b'`] mp_tac) >>
  simp[vyperStorageTheory.read_slot_def]
QED

Theorem toplevel_storage_copy_robust_contents:
  stor_taint_ok H cx tn u /\
  (!st. storage_read_live H tr st a tv) /\
  well_formed_type_value tv /\ slots_in_range st (w2n a) tv /\
  decode_value st (w2n a) tv = SOME v /\
  storage_range_agree st
    (if tr then contract_transient u else contract_storage u) a tv /\
  copy_prefix (if tr then LocTransient else LocStorage)
    a b (type_slot_size tv) u (type_slot_size tv) t /\
  tnf.t_mem SUBSET toplevel_copy_taint_bound
    (if tr then LocTransient else LocStorage) a b tn (type_slot_size tv) ==>
  !mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
    val_in_memory tv v b mem
Proof
  strip_tac >>
  `w2n a+type_slot_size tv <= dimword (:256)` by fs[storage_range_agree_def] >>
  `!i. i < type_slot_size tv ==> w2n (a+n2w i) = w2n a+i` by
    (rpt strip_tac >>
     `w2n a+i < dimword (:256)` by decide_tac >>
     `a+n2w i = n2w (w2n a+i)` by metis_tac[word_add_n2w, n2w_w2n] >>
     asm_rewrite_tac[w2n_n2w] >> simp[]) >>
  `storage_live_memory (if tr then contract_transient u else contract_storage u)
    (w2n a) tv b t.vs_memory` by
    (irule toplevel_copy_prefix_live_memory >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> Cases_on `tr` >>
     gvs[copy_runtime_word_def, vyperStorageTheory.read_slot_def,
         tload_def, sload_def, contract_transient_def, contract_storage_def,
         vfmStateTheory.lookup_account_def] >> rpt strip_tac >>
     `a+n2w i = n2w (i+w2n a)` by metis_tac[word_add_n2w, n2w_w2n,
       arithmeticTheory.ADD_COMM] >> simp[]) >>
  `storage_live_memory st (w2n a) tv b t.vs_memory` by
    metis_tac[toplevel_storage_live_memory_range] >>
  `!i j. i < type_slot_size tv /\ j < 32 /\
     (a+n2w i,j) IN toplevel_copy_source_taint
       (if tr then LocTransient else LocStorage) tn ==>
     dead_bytes st (w2n a) tv (w2n a+i) j` by
    (rpt strip_tac >>
     drule toplevel_storage_backend_taint_dead >>
     disch_then (qspecl_then [`tr`, `a+n2w i`, `j`] mp_tac) >> simp[] >>
     drule toplevel_storage_range_dead_bytes >> strip_tac >>
     fs[storage_read_live_def] >>
     `w2n a <= w2n a+i /\ w2n a+i < w2n a+type_slot_size tv` by decide_tac >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `!i j. i < type_slot_size tv /\ j < 32 /\ b+32*i+j IN tnf.t_mem ==>
     dead_bytes st (w2n a) tv (w2n a+i) j` by
    metis_tac[toplevel_copy_taint_dead_bytes] >>
  rpt strip_tac >> irule toplevel_storage_decode_robust >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM, arithmeticTheory.ADD_ASSOC]
QED


Theorem toplevel_local_footprint_forward[local]:
  stmt_state_rel H ctx fn cenv cx es s ==>
  (!name b sz i. local_region cenv es.scopes s name b sz /\
    b <= i /\ i < b+sz ==> i NOTIN writes) ==>
  !name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w+val_footprint entry.type entry.value ==>
      i NOTIN writes)
Proof
  metis_tac[toplevel_local_footprint_disjoint]
QED

Theorem toplevel_backend_location[local]:
  (((if tr then LocTransient else LocStorage) = LocTransient) = tr) /\
  ((if tr then LocTransient else LocStorage) = LocStorage \/
   (if tr then LocTransient else LocStorage) = LocTransient)
Proof
  Cases_on `tr` >> simp[]
QED

Theorem toplevel_storage_ensure_horizon_semantic[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory (Lit a) loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb fn /\
  (!H. valid_horizon cx st0 H obs ==> stmt_state_rel H ctx fn cenv cx es s) /\
  valid_horizon cx st0 H0 obs /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  nb = 32*n /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  !tn PG G D. ?t Gf tnf p.
    op = Var p /\ gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    ptr_covers Gf tnf p t nb /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ?u w.
      (!H. valid_horizon cx st0 H obs ==> stmt_state_rel H ctx fn cenv cx es u) /\
      u.vs_memory = s.vs_memory /\
      lookup_var p u = SOME w /\ lookup_var p t = SOME w /\
      copy_prefix loc a (w2n w) n u n t /\ copy_static t = copy_static u /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      tnf.t_mem SUBSET toplevel_copy_taint_bound loc a (w2n w) tn n /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) nb b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
        regions_disjoint (w2n w) nb b len) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
      u.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
      t.vs_transient = s.vs_transient /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,nb) /\
      sa.cs_next_id < sb.cs_next_id /\
      LENGTH u.vs_memory <= LENGTH t.vs_memory /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP u.vs_allocas aid = SOME entry) /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,nb) /\
      (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = sa.cs_next_id)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >>
  `compile_ensure_in_memory (Lit a) loc nb n ctor imm =
    do buf <- compile_alloc_buffer nb;
       (if n = 1 then
          do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [Lit a];
             emit_void MSTORE [buf.buf_operand;v] od
        else do compile_word_copy_loop (Lit a) buf.buf_operand n loc LocMemory F;
                return () od);
       return buf.buf_operand od` by
    (irule ensure_storage_memory_layout >> simp[]) >>
  qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ sa = _` mp_tac >>
  asm_rewrite_tac[] >>
  Cases_on `compile_alloc_buffer (32*n) sa` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gnvs[] >>
  drule_all (SRULE[comp_ignore_bind_def] storage_copy_suffix_extends) >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `stmt_state_rel H0 ctx fn cenv cx es s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H0` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  drule_all toplevel_alloc_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `!H. valid_horizon cx st0 H obs ==> stmt_state_rel H ctx fn cenv cx es u` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx fn cenv cx es s` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s`
          (qspec_then `H` mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
     qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ s` kall_tac >>
     qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ u` kall_tac >>
     drule_all toplevel_alloc_buffer_ptr_run >>
     disch_then (qspecl_then [`tn`, `PG`, `G`, `D`]
       (qx_choosel_then [`u1`, `w1`, `Gf1`, `tnf1`, `p1`] strip_assume_tac)) >>
     `u1 = u` by
       (qpat_x_assum `run_inst_seq _ s = OK u1` mp_tac >>
        qpat_x_assum `run_inst_seq _ s = OK u` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[]) >>
     qpat_x_assum `u1 = u` SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `q.buf_operand = op /\ _` strip_assume_tac >> gnvs[] >>
  `n < 2**256` by (fs[dimword_def] >> decide_tac) >>
  qabbrev_tac `s1 = u with vs_inst_idx := LENGTH r.cs_current_insts` >>
  `eval_operand (Lit a) s1 = SOME a /\ op_taint tnf (Lit a) = {} /\
   lookup_var p s1 = SOME w /\ ptr_covers Gf tnf p s1 (32*n) /\
   w2n w+32*n < 2**256 /\ w2n w+32*n <= s1.vs_alloca_next /\
   ~s1.vs_halted /\ s1.vs_current_bb = r.cs_current_bb /\
   s1.vs_inst_idx = LENGTH r.cs_current_insts` by
    fs[Abbr `s1`, eval_operand_def, lookup_var_def, op_taint_def, dimword_def] >>
  `w = n2w (w2n w)` by simp[] >>
  `lookup_var p s1 = SOME (n2w (w2n w))` by metis_tac[] >>
  `32*n <= 32*n /\ (!x. Lit a = Var x ==> not_fresh_at r x)` by simp[] >>
  drule_all (REWRITE_RULE[comp_ignore_bind_def] toplevel_copy_suffix_post_effects) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `copy_prefix loc a (w2n w) n u n t /\ copy_static t = copy_static u` by
    (`copy_static s1 = copy_static u` by simp[Abbr `s1`, copy_static_def] >>
     `!z. copy_runtime_word loc s1 z = copy_runtime_word loc u z` by
       metis_tac[copy_runtime_word_static] >>
     qpat_x_assum `copy_prefix _ _ _ _ _ _ _` mp_tac >>
     simp[copy_prefix_def, Abbr `s1`] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at r x` by
    (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     strip_tac >> drule storage_copy_alloc_layout >>
     simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `lookup_var p t = SOME w` by
    (qpat_x_assum `!x. not_fresh_at r x ==> _` drule >>
     simp[Abbr `s1`, lookup_var_def]) >>
  `toplevel_copy_taint_bound loc a (w2n w) tnf n SUBSET
    toplevel_copy_taint_bound loc a (w2n w) tn n` by
    (irule toplevel_copy_alloc_taint_bound >>
     simp[toplevel_copy_region_def]) >>
  `tnf'.t_mem SUBSET toplevel_copy_taint_bound loc a (w2n w) tn n` by
    metis_tac[pred_setTheory.SUBSET_TRANS] >>
  `u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP u.vs_allocas aid = SOME entry)` by
    (drule_all toplevel_alloc_buffer_static_effects >> simp[]) >>
  `t.vs_call_ctx = u.vs_call_ctx /\ t.vs_accounts = u.vs_accounts /\
   t.vs_transient = u.vs_transient /\ t.vs_allocas = u.vs_allocas` by
    metis_tac[copy_static_fields] >>
  `LENGTH u.vs_memory <= LENGTH t.vs_memory` by fs[Abbr `s1`] >>
  `?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id` by
    (drule_all buffer_alloc_code >> strip_tac >>
     goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  `sa.cs_next_id < cs'.cs_next_id` by
    (`32*n < dimword (:256)` by decide_tac >>
     drule_all (REWRITE_RULE[comp_ignore_bind_def] storage_copy_suffix_ci_mono) >> strip_tac >>
     drule_all buffer_alloc_code >> strip_tac >>
     `stmt_state_rel H0 ctx fn cenv cx es s` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s`
          (qspec_then `H0` mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
     drule_all literal_alloc_buffer_run >> strip_tac >>
     fs[ci_mono_def] >> decide_tac) >>
  qexistsl_tac [`t`, `Gf'`, `tnf'`] >> simp[] >>
  qexists_tac `u` >>
  simp[] >>
  rpt conj_tac
  >- fs[eval_operand_def, lookup_var_def]
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      fs[Abbr `s1`, lookup_var_def] >> metis_tac[]) >>
  metis_tac[]
QED


Theorem toplevel_storage_ensure_horizon_post[local]:
  (!H. valid_horizon cx st0 H obs ==>
     vv_post H ctx fn cenv cx e es sa sm s0 es' (Value v) vv s) /\
  valid_horizon cx st0 H0 obs /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (loc = LocStorage \/ loc = LocTransient) /\
  storage_holds cx (loc = LocTransient) (post_value_type cenv e) (Value v) a es' s /\
  ~is_word_type (post_value_type cenv e) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tv /\
  n = type_slot_size tv /\ type_memory_size tv <= nb /\
  compile_ensure_in_memory (Lit a) loc nb n ctor imm sm = (op,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  nb = 32*n /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  !tn PG G D. ?t Gf tnf p.
    op = Var p /\ gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    ptr_covers Gf tnf p t nb /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!H. valid_horizon cx st0 H obs ==>
       expr_post H ctx fn cenv cx e es sa sb s0 es' v op t) /\
    ?u w.
      (!H. valid_horizon cx st0 H obs ==> stmt_state_rel H ctx fn cenv cx es' u) /\
      u.vs_memory = s.vs_memory /\
      lookup_var p u = SOME w /\ lookup_var p t = SOME w /\
      copy_prefix loc a (w2n w) n u n t /\ copy_static t = copy_static u /\
      (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      tnf.t_mem SUBSET toplevel_copy_taint_bound loc a (w2n w) tn n /\
      (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) nb b len) /\
      (!name b len. local_region cenv es'.scopes u name b len ==>
        regions_disjoint (w2n w) nb b len) /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
      u.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
      t.vs_transient = s.vs_transient /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,nb) /\
      sm.cs_next_id < sb.cs_next_id /\
      LENGTH u.vs_memory <= LENGTH t.vs_memory /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP u.vs_allocas aid = SOME entry) /\
      FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,nb) /\
      (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = sm.cs_next_id)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >>
  `!H. valid_horizon cx st0 H obs ==> stmt_state_rel H ctx fn cenv cx es' s` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [vv_post_def])) >>
  drule_all toplevel_storage_ensure_horizon_semantic >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `stmt_state_rel H0 ctx fn cenv cx es' u` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u`
       (qspec_then `H0` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `storage_holds cx (loc = LocTransient) (post_value_type cenv e) (Value v) a es' u` by
    gvs[storage_holds_def, venomStateTheory.contract_storage_def,
      venomStateTheory.contract_transient_def] >>
  `loc = if loc = LocTransient then LocTransient else LocStorage` by metis_tac[] >>
  `val_wf tv v /\ val_in_memory tv v (w2n w) t.vs_memory /\
    val_footprint tv v <= type_memory_size tv` by
    (irule (INST_TYPE [alpha |-> ``:256``] copy_buffer_storage_contents) >>
     rpt (goal_assum (drule_at Any)) >>
     qpat_x_assum `copy_prefix _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `n = _` (fn th => rewrite_tac [th]) >>
     qpat_x_assum `loc = if _ then _ else _`
       (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     disch_then ACCEPT_TAC) >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u` by
    metis_tac[] >>
  `!H. valid_horizon cx st0 H obs ==>
     expr_post H ctx fn cenv cx e es sa sb s0 es' v op t` by
    (rpt strip_tac >>
     `vv_post H ctx fn cenv cx e es sa sm s0 es' (Value v) vv s` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
          (qspec_then `H` mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
     `stmt_state_rel H ctx fn cenv cx es' u` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u`
          (qspec_then `H` mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
     qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ u` kall_tac >>
     irule copy_buffer_post_transport_physical >>
     simp[] >>
     qrefinel [`_`, `sm`, `_`, `_`, `nb`] >>
     rpt (goal_assum (drule_at Any)) >>
     gvs[copy_prefix_def, venomStateTheory.eval_operand_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qexistsl_tac [`t`, `Gf`, `tnf`, `p`] >> simp[] >>
  qexists_tac `u` >> simp[] >> metis_tac[]
QED

Theorem compile_toplevel_storage_aggregate_sim_ptr:
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  read_storage_slot cx tr (n2w slot) tv es = (INL v,es) /\
  ~is_word_type ann ==>
  expr_sim_ptr d ctx PG fn cenv cx ty (TopLevelName ann (src,id)) es
Proof
  strip_tac >> rw[expr_sim_ptr_def] >>
  `typ = ann` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     metis_tac[TopLevelName_storage_decl_type_eq]) >> gvs[] >>
  `gas_marked_exec F (ctx,fn) (eval_expr cx (TopLevelName ann (src,id)))
     (es,s0) [] (INL (PlaceR (StoragePlace tr (n2w slot) tv)))
     (es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tv])
     (OK s0)` by (irule toplevel_storage_marked_exec >> metis_tac[]) >>
  `!p tail. read_result cx (PlaceR (StoragePlace tr (n2w slot) tv))
       (es with <|gas_obs := tail; storage_trace := p|>) =
     (INL v, es with <|gas_obs := tail; storage_trace := p|>)` by
    (rpt gen_tac >>
     `read_result cx (PlaceR (StoragePlace tr (n2w slot) tv)) es = (INL v,es)` by
       simp[read_result_def, read_place_def] >>
     drule read_result_gas_obs >> disch_then (qspec_then `tail` assume_tac) >>
     qspecl_then [`cx`, `PlaceR (StoragePlace tr (n2w slot) tv)`,
                  `es with gas_obs := tail`, `p`] mp_tac
       (Q.GENL [`cx`, `r`, `st`, `p`] vyperEvalPureExprTheory.read_result_trace) >>
     simp[]) >>
  `!tail. bind (eval_expr cx (TopLevelName ann (src,id))) (read_result cx)
      (es with gas_obs := tail) =
    (INL v, es with <|gas_obs := tail;
                      storage_trace := es.storage_trace ++ [StorageRoot tr slot tv]|>)` by
    (gen_tac >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o Q.SPEC `tail` o CONJUNCT1 o REWRITE_RULE [gas_marked_exec_def]) >>
     simp[gas_explicit_def, bind_def]) >>
  reverse (Cases_on `storage_trace_domain cx st0
             (es.storage_trace ++ [StorageRoot tr slot tv])`)
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gasStorageTheory.gas_bad_storage_at_def, gas_explicit_def]) >>
  `!H. valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot tv]) ==>
       valid_horizon cx st0 H es.storage_trace /\ MEM (tr,n2w slot,tv) (FST H)` by
    (rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[valid_horizon_def, storage_observations_ok_def,
         storage_trace_regions_def]) >>
  `?H0. valid_horizon cx st0 H0 (es.storage_trace ++ [StorageRoot tr slot tv])` by
    metis_tac[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot tv]) ==>
     stmt_state_rel H ctx fn cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
     ghost_inv H d cenv cx es G0 tn0 s0 /\
     !st. storage_read_live H tr st (n2w slot) tv` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> _ /\ MEM _ _` drule >>
     strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >>
     strip_tac >> simp[] >> metis_tac[observed_storage_region_read_live]) >>
  `valid_horizon cx st0 H0 es.storage_trace /\ MEM (tr,n2w slot,tv) (FST H0)` by
    (qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> _ /\ MEM _ _` drule >> simp[]) >>
  `stmt_state_rel H0 ctx fn cenv cx es s0 /\ storage_well_formed_on cx es (FST H0) /\
   ghost_inv H0 d cenv cx es G0 tn0 s0 /\
   !st. storage_read_live H0 tr st (n2w slot) tv` by
    (qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       drule >> simp[]) >>
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tv` by
    (qpat_x_assum `storage_well_formed_on _ _ (FST H0)` mp_tac >>
     qpat_x_assum `MEM _ (FST H0)` mp_tac >> rpt (pop_assum kall_tac) >>
     rpt strip_tac >> gvs[storage_well_formed_on_def]) >>
  `w2n ((n2w slot):bytes32) + type_slot_size tv <= dimword (:256)` by
    (qpat_x_assum `valid_horizon _ _ H0 es.storage_trace` mp_tac >>
     qpat_x_assum `MEM _ (FST H0)` mp_tac >> rpt (pop_assum kall_tac) >>
     rpt strip_tac >>
     gvs[valid_horizon_def, regions_consistent_def] >>
     qpat_x_assum `!b slot tv. MEM _ _ ==> _` (drule_then mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot tv]) ==>
     vv_post H ctx fn cenv cx (TopLevelName ann (src,id)) es sa sa s0
       (es with <|storage_trace := es.storage_trace ++ [StorageRoot tr slot tv];
                  gas_obs := []|>) (Value v)
       (LocatedValue ann (mk_ptr (Lit (n2w slot))
         (if tr then LocTransient else LocStorage))) s0` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       drule >> strip_tac >>
     `vv_post H ctx fn cenv cx (TopLevelName ann (src,id)) es sa sa s0
        (es with <|storage_trace := es.storage_trace ++ [StorageRoot tr slot tv];
                   gas_obs := []|>) (PlaceR (StoragePlace tr (n2w slot) tv))
        (LocatedValue ann (mk_ptr (Lit (n2w slot))
          (if tr then LocTransient else LocStorage))) s0` by
       (irule toplevel_storage_value_post >> rpt conj_tac
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC
        >- (qexists_tac `v` >> first_assum ACCEPT_TAC)
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC >>
        first_assum ACCEPT_TAC) >>
     drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) vv_post_read_result >>
     disch_then (qspec_then `v` mp_tac) >> (impl_tac >- simp[]) >> simp[]) >>
  `vv_post H0 ctx fn cenv cx (TopLevelName ann (src,id)) es sa sa s0
     (es with <|storage_trace := es.storage_trace ++ [StorageRoot tr slot tv];
                gas_obs := []|>) (Value v)
     (LocatedValue ann (mk_ptr (Lit (n2w slot))
       (if tr then LocTransient else LocStorage))) s0` by
    (qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       drule >> simp[]) >>
  drule_all toplevel_storage_branch_compile >> strip_tac >>
  `storage_holds cx tr ann (Value v) (n2w slot)
     (es with <|storage_trace := es.storage_trace ++ [StorageRoot tr slot tv];
                gas_obs := []|>) s0` by
    (qpat_x_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     fs[vv_post_def, vv_holds_def, vv_at_def, mk_ptr_def, eval_operand_def,
        expr_type_def] >> Cases_on `tr` >> gvs[expr_type_def]) >>
  drule (toplevel_storage_ensure_horizon_post
    |> Q.INST [`e` |-> `TopLevelName ann (src,id)`,
               `loc` |-> `if tr then LocTransient else LocStorage`]
    |> SRULE [expr_type_def, toplevel_backend_location]) >> simp[] >>
  disch_then (qspecl_then [`tr`, `sb`, `op`, `cenv.ce_imm_alloca`,
    `cenv.ce_is_ctor`, `n2w slot`, `H0`, `tn0`, `PG`, `G0`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    mp_tac) >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (qpat_x_assum `storage_holds _ _ _ _ _ _ s0` mp_tac >>
          rpt (pop_assum kall_tac) >> simp[])
      >- (qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _` mp_tac >>
          qpat_x_assum `type_memory_bytes _ _ = _` (fn th => rewrite_tac [th]) >>
          disch_then ACCEPT_TAC) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  `stor_taint_ok H0 cx tn0 u` by
    (qpat_x_assum `ghost_inv H0 _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `u.vs_call_ctx = _` mp_tac >>
     qpat_x_assum `u.vs_accounts = _` mp_tac >>
     qpat_x_assum `u.vs_transient = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[ghost_inv_def, stor_taint_ok_def]) >>
  `storage_holds cx tr ann (Value v) (n2w slot)
     (es with <|storage_trace := es.storage_trace ++ [StorageRoot tr slot tv];
                gas_obs := []|>) u` by
    (qpat_x_assum `storage_holds _ _ _ _ _ _ s0` mp_tac >>
     qpat_x_assum `u.vs_call_ctx = _` mp_tac >>
     qpat_x_assum `u.vs_accounts = _` mp_tac >>
     qpat_x_assum `u.vs_transient = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[storage_holds_def, contract_transient_def, contract_storage_def]) >>
  `well_formed_type_value tv` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `decode_value (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tv = SOME v` by
    (qpat_x_assum `read_storage_slot _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     fs[vyperStorageBackendTheory.read_storage_slot_eq, AllCaseEqs()]) >>
  `storage_range_agree (get_storage cx es tr)
     (if tr then contract_transient u else contract_storage u) (n2w slot) tv` by
    (qpat_x_assum `storage_holds _ _ _ _ _ _ u` mp_tac >>
     qpat_x_assum `evaluate_type _ ann = SOME tv` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `tr` >>
     gvs[storage_holds_def, vyperStorageBackendTheory.get_storage_def]) >>
  `!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
     val_in_memory tv v (w2n w) mem` by
    (rpt strip_tac >> irule (INST_TYPE [alpha |-> ``:256``] toplevel_storage_copy_robust_contents) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `expr_post H0 ctx fn cenv cx (TopLevelName ann (src,id)) es sa sb s0
     (es with <|storage_trace := es.storage_trace ++ [StorageRoot tr slot tv];
                gas_obs := []|>) v op t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H0` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `val_wf tv v` by
    (qpat_x_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `evaluate_type _ ann = SOME tv` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[expr_post_def, expr_val_at_def, expr_type_def]) >>
  `val_store_size tv v <= 32 * type_slot_size tv` by
    (drule exprSimPropsTheory.val_store_size_le >> decide_tac) >>
  `ptr_val_ok cx ann v (Var p) Gf tnf t /\
   ptr_buf_ok cenv (TopLevelName ann (src,id)) (Var p) Gf t` by
    (irule toplevel_storage_copy_pointer_post >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `!name b len. local_region cenv es.scopes s0 name b len ==>
     local_region cenv es.scopes u name b len` by
    (simp[local_region_def] >> rpt strip_tac >>
     `not_fresh_at sa p'` by metis_tac[local_ptrs_reserved_def] >>
     metis_tac[]) >>
  `!name b len i. local_region cenv es.scopes s0 name b len /\
     b <= i /\ i < b+len ==> i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv)` by
    (simp[toplevel_copy_region_def] >> rpt strip_tac >>
     `regions_disjoint (w2n w) (32*type_slot_size tv) b len` by metis_tac[] >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `!i. i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv) ==>
     mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s0.vs_memory` by
    (qpat_x_assum `copy_prefix _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `u.vs_memory = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[copy_prefix_def, toplevel_copy_region_def] >>
     first_x_assum irule >> decide_tac) >>
  `!i. i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv) /\
     i IN tnf.t_mem ==> i IN tn0.t_mem` by
    (qpat_x_assum `tnf.t_mem SUBSET _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[SUBSET_DEF, toplevel_copy_taint_bound_def, toplevel_copy_region_def,
          toplevel_copy_translated_taint_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  qpat_assum `stmt_state_rel H0 _ _ _ _ es s0`
    (mp_then Any mp_tac toplevel_local_footprint_forward) >>
  disch_then (qspec_then `toplevel_copy_region (w2n w) (type_slot_size tv)` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `ghost_kept cenv es sa G0 tn0 s0 Gf tnf` by
    (irule toplevel_ghost_kept_memory_frame >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
     qexists_tac `toplevel_copy_region (w2n w) (type_slot_size tv)` >>
     simp[] >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     rpt strip_tac >>
     `regions_disjoint (w2n w) (32*type_slot_size tv) off sz` by metis_tac[] >>
     fs[regions_disjoint_def, toplevel_copy_region_def] >> decide_tac) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL v`,
                `es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tv]`,
                `Gf`, `tnf`, `OK t`] >>
  conj_tac >- simp[gas_explicit_def] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `valid_horizon _ _ H _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  conj_tac
  >- (BETA_TAC >> rewrite_tac[listTheory.LENGTH] >>
      irule gas_path_ptr_from_no_dead >> first_assum ACCEPT_TAC) >>
  suspend "post"
QED

Resume compile_toplevel_storage_aggregate_sim_ptr[post]:
  `stmt_state_rel H ctx fn cenv cx es s0 /\ ghost_inv H d cenv cx es G0 tn0 s0` by
    (qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       drule >> simp[]) >>
  `expr_post H ctx fn cenv cx (TopLevelName ann (src,id)) es sa sb s0
     (es with <|storage_trace := es.storage_trace ++ [StorageRoot tr slot tv];
                gas_obs := []|>) v op t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `ghost_inv H d cenv cx
     (es with <|storage_trace := es.storage_trace ++ [StorageRoot tr slot tv];
                gas_obs := []|>) Gf tnf t` by
    (irule toplevel_ghost_inv_memory_frame >>
     qexistsl_tac [`G0`, `es`, `s0`, `sa`, `tn0`,
       `toplevel_copy_region (w2n w) (type_slot_size tv)`] >>
     simp[] >>
     qpat_assum `!name entry p sz w. _` (fn fp =>
       qpat_assum `!name b len i. local_region _ _ s0 _ _ _ /\ _ ==> _` (fn ex =>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[fp,ex]))) >>
  `~is_word_type ann ==> ptr_buf_ok cenv (TopLevelName ann (src,id)) (Var p) Gf t` by
    (strip_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `op = Var p` SUBST_ALL_TAC >>
  `es with <|gas_obs := []; storage_trace := es.storage_trace ++ [StorageRoot tr slot tv]|> =
   es with <|storage_trace := es.storage_trace ++ [StorageRoot tr slot tv];
             gas_obs := []|>` by simp[evaluation_state_component_equality] >>
  disj1_tac >> qexists_tac `t` >> conj_tac >- REFL_TAC >> BETA_TAC >>
  pop_assum SUBST1_TAC >> qexists_tac `v` >> rewrite_tac[expr_type_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise compile_toplevel_storage_aggregate_sim_ptr
