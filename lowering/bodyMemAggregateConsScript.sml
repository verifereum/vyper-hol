(* One child, from its successful endpoint through ADD, unwrap and store. *)
Theory bodyMemAggregateCons
Ancestors
  bodyMemAggregateAdd bodyMemAggregateSide exprSimProps freshWrites
  exprOperandVar exprLoweringProps emitHelperProps ASCIInumbers words
  compileEnv loweringStateRelDefs venomState context fragExec exprSimAggregateChildren
  exprSimHypsDefs loweringPosts bodyMemAggregatePath gasSummary
  bodyMemAggregateContinuation fragGasMode

Theorem aggregate_tuple_cons_continuation_mem_cursor:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  local_ptrs_reserved ce sa /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tvv) es' (OK r) /\
  expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  alloca_history func r /\ alloca_inv r /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts /\
  not_fresh_at sm x /\ lookup_var x r = SOME (n2w b) /\
  FLOOKUP r.vs_allocas aid = SOME (b,asz) /\
  off + type_memory_size tv <= asz /\ b + asz < dimword (:256) /\
  (!n lo k. local_region ce es'.scopes r n lo k ==>
    lo + k <= b+off \/ b+off + type_memory_size tv <= lo) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)) ==>
  ?v q. gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
          [] (INL v) es' (OK q) /\
    val_in_memory tv v (b+off) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!i a. FLOOKUP r.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
    (!i lo sz a k.
      FLOOKUP r.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        lo + sz <= b \/ b + len <= lo) /\
      lo <= a /\ a + k <= lo + sz /\
      (a + k <= b+off \/ b+off + type_memory_size tv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' r q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ r.vs_alloca_next <= q.vs_alloca_next /\
    lookup_var x q = SOME (n2w b) /\ FLOOKUP q.vs_allocas aid = SOME (b,asz)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sb` by
    metis_tac[cj 1 compile_expr_ci_mono, ci_mono_emit_op,
              ci_mono_unwrap_value, ci_mono_compile_store_memory, pairTheory.SND] >>
  `fn_has_code sm sn func /\ fn_has_code sn su func /\ fn_has_code su sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\ local_ptrs_reserved ce su` by
    metis_tac[compiler_ci_mono_reserved] >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `eval_operand (Var x) r = SOME (n2w b)` by simp[eval_operand_def] >>
  drule_at (Pat `emit_op _ _ _ = _`) aggregate_tuple_add_marked_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspec_then `n2w b` mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  suspend "store"
QED

Resume aggregate_tuple_cons_continuation_mem_cursor[store]:
  rename1 `gas_marked_path T ctx func r 0 (OK tadd)` >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `dst = Var _` SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `eval_operand (Var d) tadd` >>
  `lookup_var d tadd = SOME (n2w (b+off))` by
    fs[eval_operand_def, word_add_n2w] >>
  `not_fresh_at sn d` by
    simp[Abbr `d`, not_fresh_at_def, toString_11] >>
  `!z. op = Var z ==> not_fresh_at su z` by
    metis_tac[aggregate_child_unwrap_var, ci_mono_def] >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sn z` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sm` >> fs[ci_mono_def] >>
     drule (cj 1 compiler_compile_var) >> simp[]) >>
  `sa.cs_next_id <= sn.cs_next_id /\ sn.cs_next_var <= su.cs_next_var` by
    (fs[ci_mono_def, cs_extends_def] >> decide_tac) >>
  `type_memory_size tv < 2 ** 64` by
    (drule_all aggregate_child_memory_size_bound >> simp[]) >>
  `!v. read_result cx tvv (es' with gas_obs := []) =
       (INL v,es' with gas_obs := []) ==> value_has_type tv v /\ val_wf tv v` by
    (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`) aggregate_child_read_typed_mem >>
     disch_then (qspecl_then [`tv`, `env`, `ce`] mp_tac) >> simp[]) >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `stmt_state_rel ctx func ce cx es' tadd` by fs[vv_post_def] >>
  `alloca_inv tadd` by
    (irule aggregate_mem_path_alloca_inv >>
     qexistsl_tac [`ctx`, `func`, `0`, `r`] >> fs[gas_marked_path_def]) >>
  `w2n (n2w (b+off) : bytes32) = b+off` by
    (`b+off < dimword (:256)` by decide_tac >> simp[w2n_n2w]) >>
  `w2n (n2w (b+off) : bytes32) + type_memory_size tv <= tadd.vs_alloca_next` by
    (irule aggregate_allocated_slice_capacity >> simp[] >>
     qexistsl_tac [`aid`, `asz`] >> simp[]) >>
  suspend "apply"
QED

Resume aggregate_tuple_cons_continuation_mem_cursor[apply]:
  `!n lo k. local_region ce es'.scopes tadd n lo k ==>
     local_region ce es'.scopes r n lo k` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >> fs[vv_post_def, stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sm`, `es'.scopes`, `tadd`] >> simp[]) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) aggregate_unwrap_store_slice_mem_cursor >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`n2w (b+off)`, `tv`, `env`] mp_tac) >>
  impl_tac >- (simp[] >> pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
                rpt conj_tac >> metis_tac[aggregate_mem_path_alloca_inv]) >>
  strip_tac >> suspend "join"
QED

Resume aggregate_tuple_cons_continuation_mem_cursor[join]:
  `!z. not_fresh_at sm z ==> not_fresh_at sn z` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sm` >> fs[ci_mono_def]) >>
  `tadd.vs_gas_readings = r.vs_gas_readings` by
    (drule gas_marked_path_ok_suffix >> simp[]) >>
  qexistsl_tac [`v`, `q`] >> simp[] >>
  conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >>
      metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
      qpat_x_assum `!i lo sz aa kk. _ ==> mem_bytes_at aa kk q.vs_memory = _` mp_tac >>
      simp[] >> disch_tac >> rpt gen_tac >> disch_tac >>
      qpat_x_assum `!i lo sz aa kk. _ ==> mem_bytes_at aa kk q.vs_memory = _` irule >>
      asm_rewrite_tac[] >> qexistsl_tac [`i`, `lo`, `sz`] >>
      qpat_x_assum `FLOOKUP r.vs_allocas i = _ /\ _` strip_assume_tac >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  `!n lo k. local_region ce es'.scopes r n lo k ==>
     local_region ce es'.scopes tadd n lo k` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     qexistsl_tac [`r`, `sm`, `es'.scopes`] >> simp[]) >>
  qpat_x_assum `locals_kept ce es' tadd q` mp_tac >>
  simp[locals_kept_def] >> metis_tac[]
QED

Finalise aggregate_tuple_cons_continuation_mem_cursor

Theorem aggregate_tuple_cons_continuation_mem:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  local_ptrs_reserved ce sa /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tvv) es' (OK r) /\
  expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  alloca_history func r /\ alloca_inv r /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts /\
  not_fresh_at sm x /\ lookup_var x r = SOME (n2w b) /\
  FLOOKUP r.vs_allocas aid = SOME (b,asz) /\
  off + type_memory_size tv <= asz /\ b + asz < dimword (:256) /\
  (!n lo k. local_region ce es'.scopes r n lo k ==>
    lo + k <= b+off \/ b+off + type_memory_size tv <= lo) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)) ==>
  ?v q. gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
          [] (INL v) es' (OK q) /\
    val_in_memory tv v (b+off) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!i a. FLOOKUP r.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
    (!i lo sz a k.
      FLOOKUP r.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        lo + sz <= b \/ b + len <= lo) /\
      lo <= a /\ a + k <= lo + sz /\
      (a + k <= b+off \/ b+off + type_memory_size tv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' r q /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ r.vs_alloca_next <= q.vs_alloca_next /\
    lookup_var x q = SOME (n2w b) /\ FLOOKUP q.vs_allocas aid = SOME (b,asz)
Proof
  disch_tac >> mp_tac aggregate_tuple_cons_continuation_mem_cursor >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> qexistsl_tac [`v`, `q`] >> fs[] >> first_assum ACCEPT_TAC
QED
