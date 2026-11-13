(* Representation dispatch for body-aware aggregate slice continuations. *)
Theory bodyMemAggregateSliceContinuation
Ancestors
  bodyMemAggregateBodyContinuation bodyMemAggregateSide exprSimIfExpCompat
  exprSimExtract32Post exprSimHyps exprSimWordArgs
  vyperTypeInvariants exprSimSource exprSimHypsDefs loweringPosts compileEnv
  vyperTypeSystem bodyMemAggregateStore exprSimAggregateChildren
  aggregateBytestringStorePathMem exprLowering context venomState fragGasPathMem
  wideningZeroLayout freshWrites exprSimProps exprLoweringProps
  bodyMemAggregatePhysicalRead gasSummary fragGasMode vyperInterpreter vyperState

Theorem aggregate_equal_post_store_kind[local]:
  expr_body_pre ce cx env e es /\ post_value_type ce e = expr_type e ==>
  lowered_value_type ce e = expr_type e \/ is_bytestring_type (expr_type e)
Proof
  strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
   (!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==>
      ce.ce_func_return_type (nsid_to_string fid) = sig.ret_ty)` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        env_consistent_def, env_context_consistent_def] >>
  drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `ce` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  drule ifexp_body_pre_intcall_physical >> strip_tac >>
  gvs[post_value_type_def, vyperASTTheory.expr_type_def] >>
  Cases_on `is_bytestring_type ty` >- simp[] >>
  Cases_on `is_word_type ty` >- (
    qmatch_asmsub_abbrev_tac `arg_type_fits sty ty` >>
    Cases_on `sty` >> Cases_on `ty` >>
    gvs[arg_type_fits_def, is_word_type_def] >>
    rename1 `arg_type_fits (BaseT b1) (BaseT b2)` >>
    Cases_on `b1` >> Cases_on `b2` >>
    gvs[arg_type_fits_def, is_word_type_def] >>
    rename1 `arg_type_fits (BaseT (BytesT d1)) (BaseT (BytesT d2))` >>
    Cases_on `d1` >> Cases_on `d2` >>
    gvs[arg_type_fits_def, is_word_type_def]) >>
  gvs[]
QED

Theorem aggregate_body_rebased_store_slice_mem[local]:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  expr_post H ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword(:256) /\
  stmt_state_rel H ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b+k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  (post_value_type ce e = expr_type e ==> expr_store_bound cx (expr_type e) v op s) /\
  (~is_word_type (post_value_type ce e) /\
    (post_value_type ce e <> expr_type e \/ lowered_value_type ce e = expr_type e) ==>
    !stv sw. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
      eval_operand op s = SOME sw ==>
      type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  did < sa.cs_next_id /\ FLOOKUP r.vs_allocas did = SOME (b,k) /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv <= s.vs_alloca_next /\
  w2n w + type_memory_size tv < dimword(:256) /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. gas_path_mem ctx func s 0 (OK q) /\
    val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel H ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid off sz a len.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b k. local_region ce es'.scopes r n b k ==> off+sz <= b \/ b+k <= off) /\
      off <= a /\ a+len <= off+sz /\
      (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' es' r q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ q.vs_alloca_next = s.vs_alloca_next /\
    (post_value_type ce e = expr_type e ==>
      (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
      !a len. a+len <= w2n w \/ w2n w+type_memory_size tv <= a ==>
        mem_bytes_at a len q.vs_memory = mem_bytes_at a len s.vs_memory) /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    q.vs_requests = s.vs_requests /\ q.vs_call_ctx = s.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> `eval_operand (Var x) s = SOME w` by
    (drule_at (Pos hd) expr_post_rebased_lookup >> simp[eval_operand_def]) >>
  `!z. op = Var z \/ Var x = Var z ==> not_fresh_at su z` by
    (rpt strip_tac >> gvs[] >> metis_tac[not_fresh_at_mono]) >>
  `!n b k. local_region ce es'.scopes s n b k ==>
    b+k <= w2n w \/ w2n w + type_memory_size tv <= b` by
    (map_every qx_gen_tac [`ln`, `lb`, `lk`] >> strip_tac >>
     `local_region ce es'.scopes r ln lb lk` by
       (irule local_region_frame >> conj_tac
        >- (qexists `func` >>
            gvs[expr_post_def, stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
        qexistsl_tac [`sm`, `es'.scopes`, `s`] >>
        gvs[expr_post_def, loweringStateRelDefsTheory.not_fresh_at_def]) >> metis_tac[]) >>
  Cases_on `post_value_type ce e = expr_type e`
  >- (drule_all aggregate_equal_post_store_kind >> strip_tac
      >- (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
            aggregate_store_rebased_slice_mem_cursor >>
          disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          disch_then (qspecl_then [`w`, `tv`, `env`] mp_tac) >>
          (impl_tac >- (fs[expr_body_pre_def] >> metis_tac[])) >>
          disch_then (qx_choose_then `qq` strip_assume_tac) >>
          qexists `qq` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
      `~is_word_type (expr_type e)` by
        (Cases_on `expr_type e` >> gvs[is_bytestring_type_def, is_word_type_def] >>
         rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
         gvs[is_bytestring_type_def, is_word_type_def] >>
         rename1 `~is_word_type (BaseT (BytesT bs))` >> Cases_on `bs` >>
         gvs[is_bytestring_type_def, is_word_type_def]) >>
      `expr_store_bound cx (expr_type e) v op s` by metis_tac[] >>
      drule_all aggregate_bytestring_rebased_store_path_mem >>
      strip_tac >> qexists `q` >> gvs[arithmeticTheory.ADD_COMM] >> gvs[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e)` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def] >> strip_tac >>
     drule_all post_value_type_widens >>
     gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]) >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  `post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> gvs[post_value_type_def, vyperASTTheory.expr_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     gvs[post_value_type_def, vyperASTTheory.expr_type_def] >> metis_tac[]) >>
  `!stv sw. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    eval_operand op s = SOME sw ==>
    w2n sw + type_memory_size stv <= s.vs_alloca_next` by
    (rpt strip_tac >> metis_tac[type_widens_to_zero_layout]) >>
  `FLOOKUP s.vs_allocas did = SOME (b,k)` by fs[expr_post_def] >>
  `!z. Var x = Var z \/ op = Var z ==> not_fresh_at su z` by metis_tac[] >>
  drule_all aggregate_body_physical_store_path_mem >>
  strip_tac >> qexists `q` >> gvs[arithmeticTheory.ADD_COMM] >> gvs[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem aggregate_body_unwrap_store_slice_mem_cursor:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  compile_expr ce (expr_type e) e si = (vv,sj) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tvv) es' (OK re) /\
  expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
  unwrap_value ce vv sm = (op,su) /\
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_var <= su.cs_next_var /\
  fn_has_code sm su func /\ fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  (!v. read_result cx tvv (es' with gas_obs := []) =
       (INL v,es' with gas_obs := []) ==> value_has_type tv v /\ val_wf tv v) /\
  vv_post H ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  stmt_state_rel H ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b+k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  did < sa.cs_next_id /\ FLOOKUP r.vs_allocas did = SOME (b,k) /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword(:256) /\
  w2n w + type_memory_size tv <= r.vs_alloca_next /\
  alloca_history func r /\
  (!u. gas_path_mem ctx func r 0 (OK u) ==> alloca_inv u) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v q. (~expr_has_effect e /\ local_ptrs_reserved ce sa /\
     MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
     !b asz. b <= w2n w /\ w2n w + type_memory_size tv <= b + asz /\
       (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          b + asz <= lb \/ lb + lsz <= b) ==>
       (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz q.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
       !p n. (p + n <= b \/ b + asz <= p) /\
         (!inst c sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
            sa.cs_next_id <= inst.inst_id /\
            FLOOKUP q.vs_allocas inst.inst_id = SOME (c,sz) ==>
            regions_disjoint p n c sz) ==>
         mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
          [] (INL v) es' (OK q) /\
    val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel H ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid off sz a len.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b k. local_region ce es'.scopes r n b k ==> off+sz <= b \/ b+k <= off) /\
      off <= a /\ a+len <= off+sz /\
      (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' es' r q /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ r.vs_alloca_next <= q.vs_alloca_next /\
    q.vs_accounts = r.vs_accounts /\ q.vs_transient = r.vs_transient /\
    q.vs_requests = r.vs_requests /\ q.vs_call_ctx = r.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) aggregate_body_rebased_marked_read_mem_capacity >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`expr_type e`, `sj`, `si`, `env`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  `gas_path_mem ctx func r 0 (OK u)` by
    fs[gas_marked_exec_def, gas_marked_path_def] >>
  `alloca_inv u` by metis_tac[] >>
  `~u.vs_halted` by metis_tac[gas_path_mem_exec, fragGasPathTheory.gas_path_normal] >>
  `read_result cx tvv (es' with gas_obs := []) =
    (INL v,es' with gas_obs := [])` by fs[gas_marked_exec_def] >>
  `value_has_type tv v /\ val_wf tv v` by metis_tac[] >>
  `(do res <- eval_expr cx e; read_result cx res od)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,es' with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     qpat_x_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[bind_def]) >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
    aggregate_body_rebased_store_slice_mem >>
  disch_then (drule_at (Pat `(do res <- eval_expr _ _; read_result _ res od) _ = _`)) >>
  simp[extract32_expr_post_start_gas_obs, extract32_expr_post_end_gas_obs] >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ did = SOME (b,k)`)) >>
  disch_then (qspecl_then [`w`, `env`] mp_tac) >>
  (impl_tac >- (gvs[arithmeticTheory.ADD_COMM] >> metis_tac[])) >>
  strip_tac >>
  `~expr_has_effect e /\ local_ptrs_reserved ce sa /\
   MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
   !b asz. b <= w2n w /\ w2n w + type_memory_size tv <= b + asz /\
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
        b + asz <= lb \/ lb + lsz <= b) ==>
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
        mem_bytes_at lb lsz q.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
     !p n. (p + n <= b \/ b + asz <= p) /\
       (!inst c sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
          sa.cs_next_id <= inst.inst_id /\
          FLOOKUP q.vs_allocas inst.inst_id = SOME (c,sz) ==>
          regions_disjoint p n c sz) ==>
       mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (strip_tac >>
     `post_value_type ce e = expr_type e` by
       (irule post_value_type_not_int_call >> rpt strip_tac >>
        qpat_x_assum `~expr_has_effect e` mp_tac >>
        qpat_x_assum `e = _` (fn th => rewrite_tac[th]) >> simp[]) >>
     qpat_x_assum `post_value_type ce e = expr_type e ==> _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `pure_frame ce func es sa s0 r /\
      (!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==>
         lookup_var z r = SOME a)` by
       (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        rewrite_tac[vv_post_def] >> strip_tac >> conj_tac
        >- (qpat_x_assum `~expr_has_effect e ==> _` irule >>
            first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `expr_post _ _ _ _ _ e _ _ _ _ _ _ _ u`
       (mp_then (Pos hd) mp_tac exprSimWordArgsTheory.expr_post_pure_frame) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `!aid a. FLOOKUP r.vs_allocas aid = SOME a ==>
        FLOOKUP u.vs_allocas aid = SOME a` by
       (qpat_x_assum `expr_post _ _ _ _ _ e _ _ _ _ _ _ _ u` mp_tac >>
        rewrite_tac[expr_post_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
     `pure_frame ce func es sa s0 u` by
       (match_mp_tac exprSimPropsTheory.pure_frame_trans >>
        qexistsl_tac [`es'`, `sa with cs_next_var := sm.cs_next_var`, `r`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
     qx_genl_tac [`bb`, `bsz`] >> strip_tac >>
     `!a k. a + k <= w2n w \/ w2n w + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k u.vs_memory` by
       (rpt strip_tac >>
        qpat_x_assum `!a len. _ ==> mem_bytes_at a len q.vs_memory = _` irule >>
        decide_tac) >>
     qspecl_then [`ce`, `func`, `es`, `sa`, `s0`, `u`, `q`, `bb`, `bsz`, `w2n w`,
                  `type_memory_size tv`] mp_tac aggregate_pure_frame_store >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `~expr_has_effect e /\ _ ==> _` (fn pth =>
    qexistsl_tac [`v`, `q`] >> conj_tac
    >- (strip_tac >> qx_genl_tac [`bb`, `bsz`] >> strip_tac >>
        mp_tac pth >> (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then (qspecl_then [`bb`, `bsz`] mp_tac) >>
        (impl_tac >- (rpt conj_tac >- first_assum ACCEPT_TAC >- decide_tac >>
           rpt strip_tac >> first_x_assum drule >> decide_tac)) >>
        disch_then (fn th => conj_tac >- ACCEPT_TAC (CONJUNCT1 th) >>
          qx_genl_tac [`pp`, `nn`] >> strip_tac >>
          mp_tac (Q.SPECL [`pp`, `nn`] (CONJUNCT2 th)) >>
          (impl_tac >- (conj_tac >- decide_tac >> first_assum ACCEPT_TAC)) >>
          disch_then ACCEPT_TAC))) >>
  simp[] >>
  conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def, gas_marked_path_def] >>
      metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]) >>
  gvs[arithmeticTheory.ADD_COMM, locals_kept_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum `popped_kept _ _ _ r q` mp_tac >> simp[popped_kept_def]
QED
