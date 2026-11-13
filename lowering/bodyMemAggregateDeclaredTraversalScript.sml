(* Declared-layout traversal, conditional on the shared head contract. *)
Theory bodyMemAggregateDeclaredTraversal
Ancestors
  bodyMemAggregateTraversal bodyMemArrayAdapters bodyMemStructFieldsBody
  valueEncoding exprLoweringProps freshWrites

(* Source sharing only: this quotation expands to a closed HOL antecedent. *)
val declared_head_contract = ``
  !tops ctx ce cx env es e args sa vv sm x off dst sn op su dty ss
   func inst s0 b asz htv marks tv es1 t1.
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  expr_body_pre ce cx env e es /\ body_exprs_mem_ok cx (e::args) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst dty (lowered_value_type ce e) su = ((),ss) /\
  arg_type_fits (expr_type e) dty /\ well_formed_type (get_tenv cx) dty /\
  ci_mono sa sm /\ local_ptrs_reserved ce sa /\ fn_has_code sm ss func /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  stmt_state_rel ctx func ce cx es s0 /\
  evaluate_type (get_tenv cx) dty = SOME htv /\
  off + type_memory_size htv <= asz /\ b+asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size htv)) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) es1 (OK t1) /\ es1.gas_obs = [] /\
  vv_post ctx func ce cx e es sa sm s0 es1 tv vv t1 /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es1 tv vv t1 /\
  t1.vs_current_bb = sm.cs_current_bb /\
  t1.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t1 ==>
  ?v q. (~expr_has_effect e /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
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
    gas_marked_exec T (ctx,func) (read_result cx tv) (es1,t1)
      [] (INL v) es1 (OK q) /\
    val_in_memory htv v (b+off) q.vs_memory /\
    stmt_state_rel ctx func ce cx es1 q /\
    (!z a. not_fresh_at sm z /\ lookup_var z t1 = SOME a ==> lookup_var z q = SOME a) /\
    (!i a. FLOOKUP t1.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
    (!i lo sz a k. FLOOKUP t1.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
      (!name lb len. local_region ce es1.scopes t1 name lb len ==>
        lo+sz <= lb \/ lb+len <= lo) /\
      lo <= a /\ a+k <= lo+sz /\ (a+k <= b+off \/ b+off+type_memory_size htv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k t1.vs_memory) /\
    locals_kept ce es1 es1 t1 q /\ q.vs_current_bb = ss.cs_current_bb /\
    q.vs_inst_idx = LENGTH ss.cs_current_insts /\
    alloca_history func q /\ t1.vs_alloca_next <= q.vs_alloca_next /\
    lookup_var x q = SOME (n2w b) /\
    FLOOKUP q.vs_allocas inst.inst_id = SOME (b,asz) /\
    expr_sim_inv ce cx env es1 /\ body_exprs_mem_ok cx args /\
    value_has_type htv v /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    mem_bytes_at b asz t1.vs_memory = mem_bytes_at b asz s0.vs_memory``;

Theorem aggregate_tuple_declared_head_tail_mem[local]:
  ^declared_head_contract ==>
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  expr_body_pre ce cx env e es /\ body_exprs_mem_ok cx (e::args) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst dty (lowered_value_type ce e) su = ((),ss) /\
  arg_type_fits (expr_type e) dty /\ well_formed_type (get_tenv cx) dty /\
  ci_mono sa sm /\ ci_mono sa ss /\ local_ptrs_reserved ce sa /\ fn_has_code sm ss func /\
  fn_has_code ss sb func /\ local_ptrs_reserved ce ss /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  stmt_state_rel ctx func ce cx es s0 /\
  evaluate_type (get_tenv cx) dty = SOME htv /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (dty::tys) = SOME (htv::tvs) /\
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
  ?v q. (~expr_has_effect e /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
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
    gas_marked_exec T (ctx,func) (read_result cx tv) (es1,t1) [] (INL v) es1 (OK q) /\
    val_in_memory htv v (b+off) q.vs_memory /\
    stmt_state_rel ctx func ce cx es1 q /\
    (!z a. not_fresh_at sm z /\ lookup_var z t1 = SOME a ==> lookup_var z q = SOME a) /\
    (!i a. FLOOKUP t1.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
    (!i lo sz a k. FLOOKUP t1.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
      (!name lb len. local_region ce es1.scopes t1 name lb len ==> lo+sz <= lb \/ lb+len <= lo) /\
      lo <= a /\ a+k <= lo+sz /\ (a+k <= b+off \/ b+off+type_memory_size htv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k t1.vs_memory) /\
    locals_kept ce es1 es1 t1 q /\ q.vs_current_bb = ss.cs_current_bb /\
    q.vs_inst_idx = LENGTH ss.cs_current_insts /\
    alloca_history func q /\ t1.vs_alloca_next <= q.vs_alloca_next /\
    lookup_var x q = SOME (n2w b) /\ FLOOKUP q.vs_allocas inst.inst_id = SOME (b,asz) /\
    expr_sim_inv ce cx env es1 /\ body_exprs_mem_ok cx args /\
    value_has_type htv v /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    mem_bytes_at b asz t1.vs_memory = mem_bytes_at b asz s0.vs_memory /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
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
  disch_then (assume_tac o SPEC_ALL) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `off + type_memory_size htv <= asz` by (fs[type_memory_size_def] >> decide_tac) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size htv)` by
    (rpt strip_tac >> qpat_x_assum `ce.ce_is_ctor ==> _` mp_tac >>
     simp[] >> disch_then drule_all >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def, type_memory_size_def] >> decide_tac) >>
  qpat_x_assum `body_inv _ _ _ _ /\ _ ==> ?v q. _` mp_tac >>
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
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then (mp_tac o SPEC_ALL) >>
  (impl_tac >- (simp[] >> asm_rewrite_tac[])) >> strip_tac >>
  qexistsl_tac [`v`, `q`] >> asm_rewrite_tac[]
QED
