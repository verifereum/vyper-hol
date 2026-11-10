(* Consumer boundary for an aggregate element's marked read and store. *)
Theory bodyMemAggregateContinuation
Ancestors
  bodyMemAggregateStore bodyMemAggregateUnwrap exprSimMemUnwrap
  exprSimAggregateChildren exprSimMemDefs exprSimUnwrap exprSimUnwrapProps
  loweringPosts exprLowering compileEnv loweringStateRelDefs context fragGasPathMem gasSummary
  gasOutcome fragGasMode list

Theorem aggregate_rebased_marked_read_mem_capacity:
  post_value_type ce e = expr_type e /\
  unwrap_value ce vv sm = (op,su) /\
  local_ptrs_reserved ce sm /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (is_word_type (expr_type e) ==>
   ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  alloca_history func r /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
          [] (INL v) es' (OK u) /\
    expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
      su r es' v op u /\
    expr_store_bound cx (expr_type e) v op u /\
    (~is_word_type (expr_type e) /\ lowered_value_type ce e = expr_type e ==>
     !sw tvt. eval_operand op u = SOME sw /\
              evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
              type_memory_size tvt = 0 \/
              w2n sw + type_memory_size tvt <= u.vs_alloca_next) /\
    u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func u /\ r.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  drule vv_post_rebase >> strip_tac >>
  `local_ptrs_reserved ce (sa with cs_next_var := sm.cs_next_var)` by
    (qpat_x_assum `local_ptrs_reserved ce sm` mp_tac >>
     simp_tac (srw_ss()) [local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[]) >>
  qpat_x_assum `vv_post _ _ _ _ _ es _ _ _ _ _ _ _` kall_tac >>
  Cases_on `is_word_type (expr_type e)`
  >- (drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_marked_read_mem >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      impl_tac >- simp[] >> strip_tac >>
      qexistsl_tac [`v`, `u`] >> simp[]) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) aggregate_unwrap_value_marked_read_mem_capacity >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[]
QED

Theorem aggregate_unwrap_store_slice_mem_cursor:
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
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  stmt_state_rel ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  well_typed_expr env e /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
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
    stmt_state_rel ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
    (!aid off sz a k.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        off + sz <= b \/ b + len <= off) /\
      off <= a /\ a + k <= off + sz /\
      (a + k <= w2n w \/ w2n w + type_memory_size tv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' r q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ r.vs_alloca_next <= q.vs_alloca_next
Proof
  strip_tac >> (
  `post_value_type ce e = expr_type e` by
    metis_tac[exprSimHypsTheory.post_value_type_no_calls,
              loweringPostsTheory.post_value_type_lowered] >>
  drule_at (Pat `unwrap_value _ _ _ = _`) aggregate_rebased_marked_read_mem_capacity >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- (fs[] >> metis_tac[]) >> strip_tac >>
  `gas_path_mem ctx func r 0 (OK u)` by
    fs[gas_marked_exec_def, gas_marked_path_def] >>
  `alloca_inv u` by metis_tac[] >>
  `~u.vs_halted` by metis_tac[gas_path_mem_exec, fragGasPathTheory.gas_path_normal] >>
  `value_has_type tv v /\ val_wf tv v` by
    (qpat_x_assum `!v. read_result _ _ _ = _ ==> _` irule >>
     qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`) aggregate_store_rebased_slice_mem_cursor >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`w`, `tv`, `env`] mp_tac) >>
  impl_tac >- (fs[wordsTheory.dimword_def] >> rpt conj_tac >> metis_tac[]) >>
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
     `pure_frame ce func es sa s0 r /\
      (!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==>
         lookup_var z r = SOME a)` by
       (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        rewrite_tac[vv_post_def] >> strip_tac >> conj_tac
        >- (qpat_x_assum `~expr_has_effect e ==> _` irule >>
            first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `expr_post _ _ _ _ e _ _ _ _ _ _ _ u`
       (mp_then (Pos hd) mp_tac exprSimWordArgsTheory.expr_post_pure_frame) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `!aid a. FLOOKUP r.vs_allocas aid = SOME a ==>
        FLOOKUP u.vs_allocas aid = SOME a` by
       (qpat_x_assum `expr_post _ _ _ _ e _ _ _ _ _ _ _ u` mp_tac >>
        rewrite_tac[expr_post_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
     `pure_frame ce func es sa s0 u` by
       (match_mp_tac exprSimPropsTheory.pure_frame_trans >>
        qexistsl_tac [`es'`, `sa with cs_next_var := sm.cs_next_var`, `r`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     qspecl_then [`ce`, `func`, `es`, `sa`, `s0`, `u`, `q`, `b`, `asz`, `w2n w`,
                  `type_memory_size tv`] mp_tac aggregate_pure_frame_store >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> _` kall_tac >>
  qpat_x_assum `!a k. _ ==> mem_bytes_at a k q.vs_memory = mem_bytes_at a k u.vs_memory`
    kall_tac >>
  qpat_x_assum `~expr_has_effect e /\ _ ==> _` (fn pth =>
    qexistsl_tac [`v`, `q`] >> conj_tac >- ACCEPT_TAC pth) >>
  simp[] >>
  conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def, gas_marked_path_def] >>
      metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]) >>
  fs[arithmeticTheory.ADD_COMM] >>
  rpt conj_tac >> first_assum ACCEPT_TAC)
QED

Theorem aggregate_unwrap_store_slice_mem:
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
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  stmt_state_rel ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  well_typed_expr env e /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  w2n w + type_memory_size tv <= r.vs_alloca_next /\
  alloca_history func r /\
  (!u. gas_path_mem ctx func r 0 (OK u) ==> alloca_inv u) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v q. gas_marked_exec T (ctx,func) (read_result cx tvv) (es',r)
          [] (INL v) es' (OK q) /\
    val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
    (!aid off sz a k.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        off + sz <= b \/ b + len <= off) /\
      off <= a /\ a + k <= off + sz /\
      (a + k <= w2n w \/ w2n w + type_memory_size tv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' r q /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ r.vs_alloca_next <= q.vs_alloca_next
Proof
  disch_tac >> mp_tac aggregate_unwrap_store_slice_mem_cursor >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> qpat_x_assum `~expr_has_effect e /\ _ ==> _` kall_tac >>
  qexistsl_tac [`v`, `q`] >> fs[] >> first_assum ACCEPT_TAC
QED
