(* Compiler order and runtime entry transport for aggregate traversal. *)
Theory bodyMemAggregateTraversal
Ancestors
  bodyMemAggregateHeadContinuation bodyMemAggregatePostJoin
  bodyMemAggregateLoopBoundary exprLoweringProps compileEnv freshWrites
  exprSimAggregateChildren exprSimAggregateLoops exprSimHyps
  fragExec exprOperandVar gasSummary fragGasMode fragGasPath valueEncoding
  exprLowering exprSimWordArgs

Theorem aggregate_tuple_cons_order_mem[local]:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e) su = ((),ss) /\
  compile_make_tuple compile_expr ce args (Var x) tailoff ss = (out,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  not_fresh_at sa x /\ aid < sa.cs_next_id ==>
  ci_mono sa sm /\ ci_mono sm ss /\ ci_mono sa ss /\ ci_mono ss sb /\
  fn_has_code sa sm func /\ fn_has_code sm ss func /\ fn_has_code ss sb func /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce ss /\
  not_fresh_at ss x /\ aid < ss.cs_next_id
Proof
  strip_tac >>
  `ci_mono sa sm` by metis_tac[cj 1 compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su ss` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ci_mono ss sb` by
    metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm ss /\ ci_mono sa ss` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `cs_extends sa sm /\ cs_extends sm ss /\ cs_extends ss sb /\
   cs_extends sm sb /\ cs_extends sa ss` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sm func /\ fn_has_code sm ss func /\ fn_has_code ss sb func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce ss` by
    metis_tac[compiler_ci_mono_reserved] >>
  `not_fresh_at ss x` by metis_tac[not_fresh_at_mono, ci_mono_def] >>
  fs[ci_mono_def] >> decide_tac
QED

Theorem aggregate_tuple_tail_entry_mem[local]:
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type (e::args)) = SOME (htv::tvs) /\
  (!a st. MEM a (e::args) /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env a st) /\
  expr_body_pre ce cx env e es /\ body_inv tops ctx ce cx /\
  expr_sim_inv ce cx env es1 /\ body_exprs_mem_ok cx args /\
  fn_has_code ss sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce ss /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < ss.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at ss x /\ lookup_var x q = SOME (n2w b) /\
  FLOOKUP q.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list (htv::tvs) <= asz /\ b+asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off)
      (type_memory_size_list (htv::tvs))) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) es1 (OK t1) /\
  gas_marked_exec T (ctx,func) (read_result cx tv) (es1,t1)
    [] (INL v) es1 (OK q) /\
  stmt_state_rel ctx func ce cx es1 q /\ alloca_history func q /\
  q.vs_current_bb = ss.cs_current_bb /\ q.vs_inst_idx = LENGTH ss.cs_current_insts ==>
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es1 /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  body_inv tops ctx ce cx /\ body_exprs_mem_ok cx args /\
  fn_has_code ss sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce ss /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < ss.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at ss x /\ lookup_var x q = SOME (n2w b) /\
  FLOOKUP q.vs_allocas inst.inst_id = SOME (b,asz) /\
  (off + type_memory_size htv) + type_memory_size_list tvs <= asz /\
  b+asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+(off+type_memory_size htv))
      (type_memory_size_list tvs)) /\
  stmt_state_rel ctx func ce cx es1 q /\ alloca_history func q /\ ~q.vs_halted /\
  q.vs_current_bb = ss.cs_current_bb /\ q.vs_inst_idx = LENGTH ss.cs_current_insts
Proof
  strip_tac >> gvs[] >>
  `~q.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  drule_at (Pat `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _`)
    aggregate_tuple_marked_footprint_any >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ce.ce_is_ctor ==> _`)) >> strip_tac >>
  gvs[type_memory_size_def] >>
  rpt strip_tac >>
  qpat_x_assum `!name itv iv io. _ ==> regions_disjoint _ _ _ _` drule_all >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem aggregate_tuple_head_tail_mem[local]:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  expr_body_pre ce cx env e es /\ body_exprs_mem_ok cx (e::args) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e) su = ((),ss) /\
  ci_mono sa sm /\ ci_mono sa ss /\ local_ptrs_reserved ce sa /\ fn_has_code sm ss func /\
  fn_has_code ss sb func /\ local_ptrs_reserved ce ss /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  stmt_state_rel ctx func ce cx es s0 /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME htv /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type (e::args)) = SOME (htv::tvs) /\
  (!a st. MEM a (e::args) /\ expr_sim_inv ce cx env st ==> expr_body_pre ce cx env a st) /\
  off + type_memory_size_list (htv::tvs) <= asz /\ b+asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size_list (htv::tvs))) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) es1 (OK t1) /\ es1.gas_obs = [] /\
  vv_post ctx func ce cx e es sa sm s0 es1 tv vv t1 /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es1 tv vv t1 /\
  t1.vs_current_bb = sm.cs_current_bb /\
  t1.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t1 ==>
  ?v q. gas_marked_exec T (ctx,func) (read_result cx tv) (es1,t1) [] (INL v) es1 (OK q) /\
    val_in_memory htv v (b+off) q.vs_memory /\
    stmt_state_rel ctx func ce cx es1 q /\
    (!z a. not_fresh_at sm z /\ lookup_var z t1 = SOME a ==> lookup_var z q = SOME a) /\
    (!i a. FLOOKUP t1.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
    (!i lo sz a k. FLOOKUP t1.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
      (!name lb len. local_region ce es1.scopes t1 name lb len ==> lo+sz <= lb \/ lb+len <= lo) /\
      lo <= a /\ a+k <= lo+sz /\ (a+k <= b+off \/ b+off+type_memory_size htv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k t1.vs_memory) /\
    locals_kept ce es1 t1 q /\ q.vs_current_bb = ss.cs_current_bb /\
    q.vs_inst_idx = LENGTH ss.cs_current_insts /\
    alloca_history func q /\ t1.vs_alloca_next <= q.vs_alloca_next /\
    lookup_var x q = SOME (n2w b) /\ FLOOKUP q.vs_allocas inst.inst_id = SOME (b,asz) /\
    expr_sim_inv ce cx env es1 /\ body_exprs_mem_ok cx args /\
    value_has_type htv v /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    mem_bytes_at b asz t1.vs_memory = mem_bytes_at b asz s0.vs_memory /\
    OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
    (!a st. MEM a args /\ expr_sim_inv ce cx env st ==> expr_body_pre ce cx env a st) /\
    body_inv tops ctx ce cx /\ fn_has_code ss sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce ss /\ MEM inst (fn_insts func) /\
    inst.inst_outputs = [x] /\ inst.inst_id < ss.cs_next_id /\
    (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\ not_fresh_at ss x /\
    (off + type_memory_size htv) + type_memory_size_list tvs <= asz /\ b+asz < dimword (:256) /\
    (ce.ce_is_ctor ==> !name itv iv io.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
      regions_disjoint io (type_memory_size itv) (b+(off+type_memory_size htv))
        (type_memory_size_list tvs)) /\ ~q.vs_halted
Proof
  strip_tac >>
  `off + type_memory_size htv <= asz` by (fs[type_memory_size_def] >> decide_tac) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size htv)` by
    (rpt strip_tac >> qpat_x_assum `ce.ce_is_ctor ==> _` mp_tac >>
     simp[] >> disch_then drule_all >>
     simp[regions_disjoint_def, type_memory_size_def] >> decide_tac) >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) aggregate_body_head_continuation_mem >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP s0.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (qspec_then `args` mp_tac) >>
  (impl_tac >- (simp[] >> asm_rewrite_tac[])) >> strip_tac >>
  `not_fresh_at ss x /\ inst.inst_id < ss.cs_next_id` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  drule_at (Pat `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _`) aggregate_tuple_tail_entry_mem >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP q.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code ss sb _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ es1`)) >>
  disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
  disch_then (qspecl_then [`tvs`, `off`, `htv`, `args`] mp_tac) >>
  (impl_tac >- (simp[] >> asm_rewrite_tac[])) >> strip_tac >>
  qexistsl_tac [`v`, `q`] >> asm_rewrite_tac[]
QED

Theorem aggregate_tuple_tail_outcome_mem[local]:
  gas_marked_exec T (ctx,func) (read_result cx tv) (es1,t1) [] (INL v) es1 (OK q) /\
  es1.gas_obs = [] /\
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx args) (es1,q)
    (\res es2 r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es2 /\
      stmt_state_rel ctx func ce cx es2 r /\
      tuple_in_memory vs tvs (b+(off+type_memory_size htv)) r.vs_memory /\
      (!z w. not_fresh_at ss z /\ lookup_var z q = SOME w ==> lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP q.vs_allocas aid = SOME a ==> FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+(off+type_memory_size htv) \/
         b+(off+type_memory_size htv)+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory) /\
      (!aid p n. FLOOKUP q.vs_allocas aid = SOME (p,n) /\
        aid < ss.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es1.scopes q name lo sz ==> p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory) /\
      locals_kept ce es1 q r /\ alloca_history func r /\ q.vs_alloca_next <= r.vs_alloca_next)
    (\res es' exit. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) exit) /\
  vv_post ctx func ce cx e es sa sm s0 es1 tv vv t1 /\
  ci_mono sa sm /\ ci_mono sa ss /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es1 t1 /\ stmt_state_rel ctx func ce cx es1 q /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  FLOOKUP t1.vs_allocas inst.inst_id = SOME (b,asz) /\ inst.inst_id < sa.cs_next_id /\
  mem_bytes_at b asz t1.vs_memory = mem_bytes_at b asz s0.vs_memory /\
  value_has_type htv v /\ val_in_memory htv v (b+off) q.vs_memory /\
  off+type_memory_size htv <= asz /\
  (!z a. not_fresh_at sm z /\ lookup_var z t1 = SOME a ==> lookup_var z q = SOME a) /\
  (!i a. FLOOKUP t1.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
  (!i lo sz a k. FLOOKUP t1.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
    (!name lb len. local_region ce es1.scopes t1 name lb len ==>
      lo+sz <= lb \/ lb+len <= lo) /\
    lo <= a /\ a+k <= lo+sz /\
    (a+k <= b+off \/ b+off+type_memory_size htv <= a) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k t1.vs_memory) /\
  locals_kept ce es1 t1 q /\ s0.vs_alloca_next <= t1.vs_alloca_next /\
  t1.vs_alloca_next <= q.vs_alloca_next /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  expr_sim_inv ce cx env es1 /\ lookup_var x t1 = SOME (n2w b) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (read_result cx tv) (\v. bind (eval_exprs cx args) (\vs. return (v::vs)))) (es1,t1)
    (\res es2 r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es2 /\
      stmt_state_rel ctx func ce cx es2 r /\
      tuple_in_memory vs (htv::tvs) (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list (htv::tvs) <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==> p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es s0 r /\ alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next)
    (\res es' exit. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) exit)
Proof
  strip_tac >>
  `!name lo sz. local_region ce es1.scopes t1 name lo sz ==>
    b+asz <= lo \/ lo+sz <= b` by
    (rpt strip_tac >>
     `not_local_ptr ce es1.scopes x` by metis_tac[] >>
     qpat_assum `stmt_state_rel ctx func ce cx es1 t1`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _`) mp_tac
         (SRULE [] (Q.INST [`off` |-> `0`, `n` |-> `asz`] aggregate_alloca_slice_excludes_local))) >>
     disch_then (drule_at (Pat `FLOOKUP t1.vs_allocas _ = _`)) >>
     disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
     disch_then (drule_at (Pat `local_region _ _ _ _ _ _`)) >> simp[]) >>
  irule aggregate_tuple_value_bind_any >> goal_assum (drule_at Any) >>
  `es1 with gas_obs := [] = es1` by
    simp[vyperStateTheory.evaluation_state_component_equality] >> asm_rewrite_tac[] >>
  BETA_TAC >> irule aggregate_tuple_values_outcome_any >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ (eval_exprs _ _) _ _ _`)) >>
  conj_tac >- (simp[] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) aggregate_cons_success_post_mem >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ q.vs_memory`)) >>
  disch_then (drule_at (Pat `tuple_in_memory _ _ _ r.vs_memory`)) >>
  disch_then (qspec_then `ss` mp_tac) >>
  disch_then (qspecl_then [`sb`, `ee`, `env`, `asz`, `inst.inst_id`] mp_tac) >>
  (impl_tac >- (fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >> asm_rewrite_tac[])) >>
  strip_tac >> fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!p n. _ ==> mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory` irule >> simp[]) >>
  rpt strip_tac >> qpat_x_assum `!i p n. _ ==> mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory` irule >>
  asm_rewrite_tac[] >> qexists_tac `aid` >> simp[]
QED

Theorem aggregate_make_tuple_body_sim_mem:
  !args ce cx env off sa out sb es tvs func inst x b asz s0 ctx tops.
  compile_make_tuple compile_expr ce args (Var x) off sa = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==> expr_body_pre ce cx env e st) /\
  body_inv tops ctx ce cx /\ body_exprs_mem_ok cx args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b+asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size_list tvs)) /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==> p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es s0 r /\ alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next)
    (\res es' exit. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) exit)
Proof
  Induct_on `args`
  >- (rpt gen_tac >> strip_tac >> gvs[compile_make_tuple_def, comp_return_def] >>
      irule aggregate_tuple_nil_outcome_mem >> simp[val_in_memory_def, stmt_state_rel_gas_obs]) >>
  rpt gen_tac >> strip_tac >>
  `out = Var x` by metis_tac[compiler_make_tuple_result] >> gvs[] >>
  `expr_body_pre ce cx env h es` by metis_tac[listTheory.MEM] >>
  drule aggregate_mem_tuple_cons_compile >> strip_tac >>
  rename1 `compile_expr ce (expr_type h) h sa = (vv,sm)` >>
  rename1 `emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn)` >>
  rename1 `unwrap_value ce vv sn = (op,su)` >>
  rename1 `compile_store_memory ce op dst (expr_type h) (lowered_value_type ce h) su = ((),ss)` >>
  drule_all aggregate_tuple_cons_order_mem >> strip_tac >>
  drule_all aggregate_tuple_child_outcome_mem >> strip_tac >>
  rewrite_tac[aggregate_tuple_eval_cons] >>
  match_mp_tac (Q.SPEC `\tv ee r.
    vv_post ctx func ce cx h es sa sm s0 ee tv vv r /\
    vv_store_bound cx (expr_type h) (lowered_value_type ce h) ee tv vv r /\
    r.vs_current_bb = sm.cs_current_bb /\ r.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next`
    (Q.GEN `P` aggregate_tuple_bind_outcome_any)) >>
  conj_tac
  >- (irule aggregate_tuple_gas_outcome_mono >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `gas_marked_exec T _ (eval_expr cx h) _ marks (INL tv) es1 (OK t1)` >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) aggregate_tuple_head_tail_mem >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code ss sb _`)) >>
  disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP s0.vs_allocas _ = _`)) >>
  disch_then (qspecl_then [`t`, `args`] mp_tac) >>
  (impl_tac >- (simp[] >> asm_rewrite_tac[])) >> strip_tac >>
  `type_memory_bytes ce (expr_type h) = type_memory_size h'` by
    metis_tac[expr_sim_inv_memory_size] >>
  fs[] >>
  qpat_x_assum `!ce' cx' env' off' sa' out' sb' es' tvs' func' inst' x' b' asz' s0' ctx' tops'. _`
    (drule_at (Pat `compile_make_tuple _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ es1 q`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP q.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ es1`)) >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  (impl_tac >- (simp[] >> asm_rewrite_tac[])) >> strip_tac >>
  `FLOOKUP t1.vs_allocas inst.inst_id = SOME (b,asz) /\
   stmt_state_rel ctx func ce cx es1 t1` by (fs[loweringPostsTheory.vv_post_def] >> metis_tac[]) >>
  fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  drule_at (Pat `gas_outcome _ _ _ (eval_exprs _ _) _ _ _`)
    (SRULE [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] aggregate_tuple_tail_outcome_mem) >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ q.vs_memory`)) >>
  disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
  (impl_tac >- (simp[] >> asm_rewrite_tac[] >> fs[loweringPostsTheory.vv_post_def] >> metis_tac[])) >> simp[]
QED
