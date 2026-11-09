(* Shared ADD entry and slice-frame transport for aggregate cons steps. *)
Theory bodyMemAggregateConsContinuation
Ancestors
  bodyMemAggregateAdd bodyMemAggregateSide exprSimProps freshWrites
  exprOperandVar exprLoweringProps emitHelperProps ASCIInumbers words
  compileEnv venomState context fragExec exprSimAggregateChildren
  exprSimHypsDefs loweringPosts bodyMemAggregatePath gasSummary
  bodyMemAggregateContinuation fragGasMode

Theorem aggregate_add_slice_entry_mem[local]:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  lookup_var x r = SOME (n2w b) /\ fn_has_code sm sn func /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts /\
  not_fresh_at sm x /\ alloca_inv r /\ alloca_history func r /\
  FLOOKUP r.vs_allocas aid = SOME (b,asz) /\
  off + type_memory_size tv <= asz /\ b + asz < dimword(:256) ==>
  ?d u. dst = Var d /\ not_fresh_at sn d /\
    lookup_var d u = SOME (n2w (b+off)) /\
    gas_marked_path T ctx func r 0 (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    vv_post ctx func ce cx e es sa sn s0 es' tvv vv u /\
    eval_operand dst u = SOME (n2w b + n2w off) /\
    u.vs_memory = r.vs_memory /\ u.vs_allocas = r.vs_allocas /\
    u.vs_alloca_next = r.vs_alloca_next /\
    (!z. not_fresh_at sm z ==> lookup_var z u = lookup_var z r) /\
    (vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r ==>
      vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv u) /\
    alloca_inv u /\ alloca_history func u /\
    FLOOKUP u.vs_allocas aid = SOME (b,asz) /\
    lookup_var x u = SOME (n2w b) /\
    w2n (n2w (b+off):bytes32) = b+off /\
    b+off+type_memory_size tv <= u.vs_alloca_next /\
    (!n lo k. local_region ce es'.scopes u n lo k <=>
      local_region ce es'.scopes r n lo k)
Proof
  strip_tac >>
  `local_ptrs_reserved ce sm` by
    metis_tac[compiler_ci_mono_reserved, cj 1 compile_expr_ci_mono, pairTheory.SND] >>
  `eval_operand (Var x) r = SOME (n2w b)` by simp[eval_operand_def] >>
  drule_all aggregate_tuple_add_marked_mem >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `dst = Var _` SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `eval_operand (Var d) q` >>
  `not_fresh_at sn d` by simp[Abbr `d`, not_fresh_at_def, toString_11] >>
  `alloca_inv q` by
    (irule aggregate_mem_path_alloca_inv >>
     qexistsl_tac [`ctx`, `func`, `0`, `r`] >> fs[gas_marked_path_def]) >>
  `w2n (n2w (b+off):bytes32) = b+off` by
    (`b+off < dimword(:256)` by decide_tac >> simp[w2n_n2w]) >>
  `b+off+type_memory_size tv <= q.vs_alloca_next` by
    metis_tac[aggregate_allocated_slice_capacity] >>
  `!n lo k. local_region ce es'.scopes q n lo k <=>
    local_region ce es'.scopes r n lo k` by
    (rpt gen_tac >> eq_tac >> strip_tac
     >- (irule local_region_frame >> conj_tac
         >- (qexists `func` >> fs[vv_post_def, stmt_state_rel_def, state_rel_def]) >>
         qexistsl_tac [`sm`, `es'.scopes`, `q`] >> simp[]) >>
     irule local_region_frame_fwd >>
     qexistsl_tac [`r`, `sm`, `es'.scopes`] >> simp[]) >>
  qexistsl_tac [`d`, `q`] >> fs[eval_operand_def, word_add_n2w]
QED

Theorem aggregate_slice_frame_transport[local]:
  u.vs_memory = r.vs_memory /\ u.vs_allocas = r.vs_allocas /\
  (!z. not_fresh_at sm z ==> lookup_var z u = lookup_var z r) /\
  (!z. not_fresh_at sm z ==> not_fresh_at sn z) /\
  (!n lo k. local_region ce es'.scopes u n lo k <=>
    local_region ce es'.scopes r n lo k) /\
  (!z a. not_fresh_at sn z /\ lookup_var z u = SOME a ==> lookup_var z q = SOME a) /\
  (!i a. FLOOKUP u.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
  (!i lo sz a k. FLOOKUP u.vs_allocas i = SOME (lo,sz) /\ i < N /\
    (!n b len. local_region ce es'.scopes u n b len ==> lo+sz <= b \/ b+len <= lo) /\
    lo <= a /\ a+k <= lo+sz /\ D a k ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k u.vs_memory) /\
  locals_kept ce es' u q ==>
  (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
  (!i a. FLOOKUP r.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
  (!i lo sz a k. FLOOKUP r.vs_allocas i = SOME (lo,sz) /\ i < N /\
    (!n b len. local_region ce es'.scopes r n b len ==> lo+sz <= b \/ b+len <= lo) /\
    lo <= a /\ a+k <= lo+sz /\ D a k ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
  locals_kept ce es' r q
Proof
  strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  fs[locals_kept_def] >> metis_tac[]
QED

Theorem aggregate_cons_slice_static[local]:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  local_ptrs_reserved ce sa /\ fn_has_code sm sb func /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0) marks (INL tvv) es' (OK r) /\
  expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sb /\
  fn_has_code sm sn func /\ fn_has_code sn su func /\ fn_has_code su sb func /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\ local_ptrs_reserved ce su /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  sn.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sn z) /\
  type_memory_size tv < 2 ** 64 /\ well_typed_expr env e /\
  (!v. read_result cx tvv (es' with gas_obs := []) = (INL v,es' with gas_obs := []) ==>
    value_has_type tv v /\ val_wf tv v)
Proof
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sb` by
    metis_tac[cj 1 compile_expr_ci_mono, ci_mono_emit_op,
              ci_mono_unwrap_value, ci_mono_compile_store_memory, pairTheory.SND] >>
  `fn_has_code sm sn func /\ fn_has_code sn su func /\ fn_has_code su sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\ local_ptrs_reserved ce su` by
    metis_tac[compiler_ci_mono_reserved] >>
  `!z. op = Var z ==> not_fresh_at su z` by
    metis_tac[aggregate_child_unwrap_var, ci_mono_def] >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sn z` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists `sm` >> fs[ci_mono_def] >>
     drule (cj 1 compiler_compile_var) >> simp[]) >>
  `type_memory_size tv < 2 ** 64` by
    (drule_all aggregate_child_memory_size_bound >> simp[]) >>
  `!v. read_result cx tvv (es' with gas_obs := []) = (INL v,es' with gas_obs := []) ==>
    value_has_type tv v /\ val_wf tv v` by
    (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`) aggregate_child_read_typed_mem >>
     disch_then (qspecl_then [`tv`, `env`, `ce`] mp_tac) >> simp[]) >>
  fs[ci_mono_def, cs_extends_def, expr_body_pre_def] >> decide_tac
QED

Theorem aggregate_cons_from_slice_mem_cursor:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  local_ptrs_reserved ce sa /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0) marks (INL tvv) es' (OK r) /\
  expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  alloca_history func r /\ alloca_inv r /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts /\
  not_fresh_at sm x /\ lookup_var x r = SOME (n2w b) /\
  FLOOKUP r.vs_allocas aid = SOME (b,asz) /\
  off + type_memory_size tv <= asz /\ b + asz < dimword(:256) /\
  (!n lo k. local_region ce es'.scopes r n lo k ==>
    lo+k <= b+off \/ b+off+type_memory_size tv <= lo) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)) /\
  P r /\ (!s t. s.vs_allocas = t.vs_allocas /\ P s ==> P t) /\
  (!d u. P u /\
    unwrap_value ce vv sn = (op,su) /\
    compile_store_memory ce op (Var d) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
    local_ptrs_reserved ce sn /\ local_ptrs_reserved ce su /\
    sa.cs_next_id <= sn.cs_next_id /\ sn.cs_next_var <= su.cs_next_var /\
    fn_has_code sn su func /\ fn_has_code su sb func /\ fn_inst_ids_distinct func /\
    (!z. vv_operand vv = Var z ==> not_fresh_at sn z) /\
    (!z. op = Var z ==> not_fresh_at su z) /\
    not_fresh_at sn d /\ lookup_var d u = SOME (n2w (b+off)) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    type_memory_bytes ce (expr_type e) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64 /\
    (!v. read_result cx tvv (es' with gas_obs := []) = (INL v,es' with gas_obs := []) ==>
      value_has_type tv v /\ val_wf tv v) /\
    vv_post ctx func ce cx e es sa sn s0 es' tvv vv u /\
    vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv u /\
    stmt_state_rel ctx func ce cx es' u /\
    (!n lo k. local_region ce es'.scopes u n lo k ==>
      lo+k <= w2n (n2w (b+off):bytes32) \/
      w2n (n2w (b+off):bytes32)+type_memory_size tv <= lo) /\
    (ce.ce_is_ctor ==> !name itv iv io.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
      regions_disjoint io (type_memory_size itv) (w2n (n2w (b+off):bytes32)) (type_memory_size tv)) /\
    well_typed_expr env e /\
    w2n (n2w (b+off):bytes32)+type_memory_size tv <= u.vs_alloca_next /\
    alloca_history func u /\
    (!t. gas_path_mem ctx func u 0 (OK t) ==> alloca_inv t) /\
    ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts ==>
    ?v q. gas_marked_exec T (ctx,func) (read_result cx tvv) (es',u) [] (INL v) es' (OK q) /\
      val_in_memory tv v (w2n (n2w (b+off):bytes32)) q.vs_memory /\
      stmt_state_rel ctx func ce cx es' q /\
      (!z a. not_fresh_at sn z /\ lookup_var z u = SOME a ==> lookup_var z q = SOME a) /\
      (!i a. FLOOKUP u.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
      (!i lo sz a k. FLOOKUP u.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
        (!n b len. local_region ce es'.scopes u n b len ==> lo+sz <= b \/ b+len <= lo) /\
        lo <= a /\ a+k <= lo+sz /\
        (a+k <= w2n (n2w (b+off):bytes32) \/
          w2n (n2w (b+off):bytes32)+type_memory_size tv <= a) ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k u.vs_memory) /\
      locals_kept ce es' u q /\
      q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func q /\ u.vs_alloca_next <= q.vs_alloca_next) ==>
  ?v q. gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r) [] (INL v) es' (OK q) /\
    val_in_memory tv v (b+off) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!i a. FLOOKUP r.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
    (!i lo sz a k. FLOOKUP r.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==> lo+sz <= b \/ b+len <= lo) /\
      lo <= a /\ a+k <= lo+sz /\ (a+k <= b+off \/ b+off+type_memory_size tv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' r q /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ r.vs_alloca_next <= q.vs_alloca_next /\
    lookup_var x q = SOME (n2w b) /\ FLOOKUP q.vs_allocas aid = SOME (b,asz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all aggregate_cons_slice_static >> strip_tac >>
  drule_all aggregate_add_slice_entry_mem >> strip_tac >> gvs[] >>
  `P u` by metis_tac[] >>
  `stmt_state_rel ctx func ce cx es' u` by fs[vv_post_def] >>
  qpat_x_assum `!d u. _` (qspecl_then [`d`, `u`] mp_tac) >>
  (impl_tac >- (simp[GSYM arithmeticTheory.ADD_ASSOC] >>
     conj_tac >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
     conj_tac >- metis_tac[] >>
     rpt strip_tac >> irule aggregate_mem_path_alloca_inv >>
     qexistsl_tac [`ctx`, `func`, `0`, `u`] >> simp[])) >> strip_tac >>
  `!z. not_fresh_at sm z ==> not_fresh_at sn z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sm` >> fs[ci_mono_def]) >>
  drule_at (Pat `locals_kept _ _ _ _`) aggregate_slice_frame_transport >>
  disch_then (qspecl_then [`sn`, `sm`, `r`, `sa.cs_next_id`,
    `\a k. a+k <= b+off \/ b+(off+type_memory_size tv) <= a`] mp_tac) >>
  (impl_tac >- (gvs[] >> rpt strip_tac >> first_x_assum irule >> metis_tac[])) >> strip_tac >>
  `u.vs_gas_readings = r.vs_gas_readings` by
    (drule gas_marked_path_ok_suffix >> simp[]) >>
  qexistsl_tac [`v`, `q`] >> simp[] >>
  conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >>
      metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]) >>
  gvs[]
QED
