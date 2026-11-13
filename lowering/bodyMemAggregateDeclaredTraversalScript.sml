(* Declared-layout traversal, conditional on the shared head contract. *)
Theory bodyMemAggregateDeclaredTraversal
Ancestors
  bodyMemAggregateTraversal bodyMemArrayAdapters bodyMemStructFieldsBody
  valueEncoding exprLoweringProps freshWrites exprLowering compileEnv
  bodyMemAggregateLoopBoundary exprSimAggregateLoops exprSimAggregateChildren
  exprSimHyps exprSimWordArgs exprOperandVar gasOutcome gasSummary fragExec fragGasMode

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

Theorem aggregate_declared_buffer_excludes_locals[local]:
  stmt_state_rel ctx func ce cx es s0 /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) ==>
  !name lo sz. local_region ce es.scopes s0 name lo sz ==>
    b+asz <= lo \/ lo+sz <= b
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)
    (SRULE [] (Q.INST [`off` |-> `0`, `n` |-> `asz`]
      exprSimAggregateLoopsTheory.aggregate_alloca_slice_excludes_local)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
  disch_then (drule_at (Pat `local_region _ _ _ _ _ _`)) >> simp[]
QED

(* The tail induction interface; args is intentionally the sole free parameter. *)
val declared_tuple_tail = ``
  !tys ce cx env off sa out sb es tvs func inst x b asz s0 ctx tops.
  compile_make_tuple compile_expr ce args tys (Var x) off sa = (out,sb) /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t) tys args /\
  EVERY (well_formed_type (get_tenv cx)) tys /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
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
      locals_kept ce es es' s0 r /\ alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\ FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\res es' exit. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) exit)``;

Theorem aggregate_declared_post_head_mem[local]:
  ^declared_tuple_tail ==>
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s0 /\
  compile_make_tuple compile_expr ce args tys (Var x) (off + type_memory_size htv) ss = (Var x,sb) /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t) tys args /\
  EVERY (well_formed_type (get_tenv cx)) tys /\
  ci_mono sa sm /\ ci_mono sa ss /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\ local_ptrs_reserved ce ss /\
  fn_has_code ss sb func /\ fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\ inst.inst_id < ss.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\ not_fresh_at ss x /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0) marks (INL tv) es1 (OK t1) /\
  es1.gas_obs = [] /\ vv_post ctx func ce cx e es sa sm s0 es1 tv vv t1 /\
  s0.vs_alloca_next <= t1.vs_alloca_next /\
  (~expr_has_effect e /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==> b+asz <= lb \/ lb+lsz <= b) ==>
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
       mem_bytes_at lb lsz q.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
     !p n. (p+n <= b \/ b+asz <= p) /\
       (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\ sa.cs_next_id <= i.inst_id /\
         FLOOKUP q.vs_allocas i.inst_id = SOME (c,sz) ==> regions_disjoint p n c sz) ==>
       mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory) /\
  gas_marked_exec T (ctx,func) (read_result cx tv) (es1,t1) [] (INL v) es1 (OK q) /\
  val_in_memory htv v (b+off) q.vs_memory /\ stmt_state_rel ctx func ce cx es1 q /\
  (!z a. not_fresh_at sm z /\ lookup_var z t1 = SOME a ==> lookup_var z q = SOME a) /\
  (!i a. FLOOKUP t1.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
  (!i lo sz a k. FLOOKUP t1.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
    (!name lb len. local_region ce es1.scopes t1 name lb len ==> lo+sz <= lb \/ lb+len <= lo) /\
    lo <= a /\ a+k <= lo+sz /\ (a+k <= b+off \/ b+off+type_memory_size htv <= a) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k t1.vs_memory) /\
  locals_kept ce es1 es1 t1 q /\ q.vs_current_bb = ss.cs_current_bb /\
  q.vs_inst_idx = LENGTH ss.cs_current_insts /\ alloca_history func q /\ ~q.vs_halted /\
  t1.vs_alloca_next <= q.vs_alloca_next /\ lookup_var x q = SOME (n2w b) /\
  FLOOKUP q.vs_allocas inst.inst_id = SOME (b,asz) /\
  expr_sim_inv ce cx env es1 /\ body_exprs_mem_ok cx args /\ value_has_type htv v /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  mem_bytes_at b asz t1.vs_memory = mem_bytes_at b asz s0.vs_memory /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  (!a st. MEM a args /\ expr_sim_inv ce cx env st ==> expr_body_pre ce cx env a st) /\
  (off+type_memory_size htv) + type_memory_size_list tvs <= asz /\ b+asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+(off+type_memory_size htv)) (type_memory_size_list tvs)) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (read_result cx tv) (\v. bind (eval_exprs cx args) (\vs. return (v::vs)))) (es1,t1)
    (\res es2 r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es2 /\
      stmt_state_rel ctx func ce cx es2 r /\ tuple_in_memory vs (htv::tvs) (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list (htv::tvs) <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\ aid < sa.cs_next_id /\
        (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==> p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es2 s0 r /\ alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next /\
      (~EXISTS expr_has_effect (e::args) ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p+n <= b \/ b+asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\ sa.cs_next_id <= i.inst_id /\
            FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==> regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\res es' exit. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) exit)
Proof
  disch_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!name lo sz. local_region ce es.scopes s0 name lo sz ==> b+asz <= lo \/ lo+sz <= b` by
    (`not_local_ptr ce es.scopes x` by metis_tac[] >>
     qpat_assum `stmt_state_rel ctx func ce cx es s0`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _`) mp_tac aggregate_declared_buffer_excludes_locals) >>
     disch_then (drule_at (Pat `FLOOKUP s0.vs_allocas _ = _`)) >>
     disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
     simp[]) >>
  `~expr_has_effect e ==>
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
       mem_bytes_at lb lsz q.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
     !p n. (p+n <= b \/ b+asz <= p) /\
       (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\ sa.cs_next_id <= i.inst_id /\
         FLOOKUP q.vs_allocas i.inst_id = SOME (c,sz) ==> regions_disjoint p n c sz) ==>
       mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (strip_tac >> qpat_x_assum `~expr_has_effect e /\ MAP FDOM _ = _ /\ _ ==> _` mp_tac >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  qpat_x_assum `!tys ce cx env off sa out sb es tvs func inst x b asz s0 ctx tops. _`
    (drule_at (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ es1 q`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP q.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ es1`)) >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  (impl_tac >- (simp[] >> asm_rewrite_tac[])) >> strip_tac >>
  `FLOOKUP t1.vs_allocas inst.inst_id = SOME (b,asz) /\
   stmt_state_rel ctx func ce cx es1 t1` by
    (fs[loweringPostsTheory.vv_post_def] >> metis_tac[]) >>
  fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  drule_at (Pat `gas_outcome _ _ _ (eval_exprs _ _) _ _ _`)
    (SRULE [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] aggregate_tuple_tail_outcome_mem) >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ q.vs_memory`)) >>
  disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
  (impl_tac >- (simp[] >> asm_rewrite_tac[] >> fs[loweringPostsTheory.vv_post_def] >> metis_tac[])) >> simp[]
QED

Theorem aggregate_make_tuple_body_declared_from_head_mem:
  ^declared_head_contract ==> !args. ^declared_tuple_tail
Proof
  disch_tac >> Induct_on `args`
  >- (rpt gen_tac >> strip_tac >> gvs[compile_make_tuple_def, comp_return_def] >>
      irule aggregate_tuple_nil_outcome_mem >> simp[valueEncodingDefsTheory.val_in_memory_def, stmt_state_rel_gas_obs]) >>
  pop_assum (fn ih =>
    rpt gen_tac >> strip_tac >> Cases_on `tys` >- fs[] >> gns[] >>
    `out = Var x` by metis_tac[compiler_make_tuple_result] >> gnvs[] >> assume_tac ih) >>
  rename1 `compile_make_tuple compile_expr ce (h::args) (dty::dtys) _ _ _ = _` >>
  `expr_body_pre ce cx env h es` by metis_tac[listTheory.MEM] >>
  drule exprSimAggregateLoopsTheory.compile_make_tuple_cons >> strip_tac >>
  rename1 `compile_expr ce (expr_type h) h sa = (vv,sm)` >>
  rename1 `emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn)` >>
  rename1 `unwrap_value ce vv sn = (op,su)` >>
  rename1 `compile_store_memory ce op dst dty (lowered_value_type ce h) su = ((),ss)` >>
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
      simp[] >> rpt strip_tac >> Cases_on `res` >>
      qpat_x_assum `expr_exit _ _` mp_tac >> simp[exprSimDefsTheory.expr_exit_def]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `gas_marked_exec T _ (eval_expr cx h) _ marks (INL tv) es1 (OK t1)` >>
  qpat_x_assum `arg_type_fits _ _ /\ _` (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  qpat_x_assum `?v. evaluate_type _ _ = _ /\ _` strip_assume_tac >> gnvs[] >>
  rename1 `evaluate_type (get_tenv cx) dty = SOME htv` >>
  rename1 `OPT_MMAP (evaluate_type (get_tenv cx)) dtys = SOME ttvs` >>
  suspend "declared_cons"
QED

Resume aggregate_make_tuple_body_declared_from_head_mem[declared_cons]:
  first_assum (mp_then (Pos hd)
    (drule_at (Pat `compile_expr _ _ _ _ = _`))
    (SRULE [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
      aggregate_tuple_declared_head_tail_mem)) >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code ss sb _`)) >>
  disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `arg_type_fits _ _`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP s0.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then (mp_tac o SPEC_ALL) >>
  (impl_tac >- (simp[] >> asm_rewrite_tac[])) >> strip_tac >>
  `type_memory_bytes ce dty = type_memory_size htv` by metis_tac[expr_sim_inv_memory_size] >>
  fs[] >> first_assum (mp_then (Pos hd)
    (drule_at (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`))
    (SRULE [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] aggregate_declared_post_head_mem)) >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ q.vs_memory`)) >>
  disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then (mp_tac o SPEC_ALL) >>
  qpat_x_assum `!tops' ctx' ce' cx' env' es' e args' sa' vv sm x' off' dst sn op su dty ss func' inst' s0' b' asz' htv marks tv es1 t1. _` kall_tac >>
  qpat_x_assum `!tys ce cx env off sa out sb es tvs func inst x b asz s0 ctx tops. _` kall_tac >>
  (impl_tac >- (simp[] >> asm_rewrite_tac[])) >> simp[]
QED

Finalise aggregate_make_tuple_body_declared_from_head_mem

Theorem aggregate_struct_fields_body_declared_from_head_mem:
  ^declared_head_contract ==>
  !fields tys ce cx env ty off sa out sb es tvs func inst x b asz s0 ctx tops.
  LIST_REL (\t (name,e).
    ALOOKUP (get_struct_fields ce.ce_struct_fields
      (case ty of StructT nsid => nsid_to_string nsid | _ => "")) name =
      SOME (t,type_memory_bytes ce t)) tys fields /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t) tys (MAP SND fields) /\
  EVERY (well_formed_type (get_tenv cx)) tys /\
  compile_struct_lit compile_expr ce ty fields (Var x) off sa = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e (MAP SND fields) /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  body_inv tops ctx ce cx /\ body_exprs_mem_ok cx (MAP SND fields) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size_list tvs)) /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx (MAP SND fields)) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
      fields_in_memory (ZIP (MAP FST fields,vs))
        (ZIP (MAP FST fields,tvs)) (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\ alloca_history func r /\
      s0.vs_alloca_next <= r.vs_alloca_next /\
      (~EXISTS expr_has_effect (MAP SND fields) ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  disch_then (mp_then (Pos hd) assume_tac aggregate_make_tuple_body_declared_from_head_mem) >>
  rpt gen_tac >> strip_tac >>
  drule exprSimAggregateLayoutTheory.compile_struct_lit_as_tuple >>
  disch_then (qspecl_then [`compile_expr`, `Var x`, `off`] assume_tac) >> gvs[] >>
  qpat_x_assum `!args. _` (drule_at (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME (_,_)`)) >>
  disch_then (qspecl_then [`es`, `func`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >> simp[] >>
  imp_res_tac listTheory.LIST_REL_LENGTH >>
  drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[] >> strip_tac >>
  irule struct_gas_outcome_post >> goal_assum (drule_at Any) >>
  BETA_TAC >> rpt strip_tac >> qexists_tac `vs` >> gvs[] >> simp[] >>
  conj_tac >- (irule struct_tuple_memory_post >> simp[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

val declared_array_elems = ``
  !args ce cx env elem_ty tv header idx off sa out sb es func inst x b asz s0 ctx tops.
  EVERY (\e. arg_type_fits (expr_type e) elem_ty) args /\
  well_formed_type (get_tenv cx) elem_ty /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  off = (if header then 32 else 0) + idx * type_memory_size tv /\
  compile_make_array_elems compile_expr ce args elem_ty
    (type_memory_bytes ce elem_ty) header (Var x) idx sa = (out,sb) /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==> expr_body_pre ce cx env e st) /\
  body_inv tops ctx ce cx /\ body_exprs_mem_ok cx args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + LENGTH args * type_memory_size tv <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off) (LENGTH args * type_memory_size tv)) /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\ elems_in_memory vs (b+off) tv r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\ aid < sa.cs_next_id /\
        (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==> p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\ alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\ sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==> regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\res es' exit. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) exit)``;

Theorem aggregate_make_array_elems_declared_from_head_mem[local]:
  ^declared_head_contract ==> ^declared_array_elems
Proof
  disch_then (mp_then (Pos hd) assume_tac aggregate_make_tuple_body_declared_from_head_mem) >>
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`args`, `idx`] (Q.INST [`cfn` |-> `compile_expr`,
    `buf` |-> `Var x`] compile_make_array_elems_as_tuple)) >> strip_tac >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (REPLICATE (LENGTH args) elem_ty) =
     SOME (REPLICATE (LENGTH args) tv)` by
    (Q.SPEC_TAC (`LENGTH args`, `n`) >> Induct >> gvs[rich_listTheory.REPLICATE]) >>
  `LIST_REL (\t e. arg_type_fits (expr_type e) t) (REPLICATE (LENGTH args) elem_ty) args` by
    gvs[listTheory.LIST_REL_EL_EQN, rich_listTheory.EL_REPLICATE, listTheory.EVERY_EL] >>
  `compile_make_tuple compile_expr ce args (REPLICATE (LENGTH args) elem_ty)
     (Var x) off sa = (out,sb)` by (gvs[] >> metis_tac[]) >>
  qpat_x_assum `!args. _` (drule_at (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME (_,_)`)) >>
  disch_then (qspecl_then [`es`, `func`] mp_tac) >>
  pure_rewrite_tac[exprSimAggregateEncodingTheory.type_memory_size_list_replicate] >>
  (impl_tac >- (gvs[rich_listTheory.EVERY_REPLICATE] >> simp[] >> first_assum ACCEPT_TAC)) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >> rpt (pop_assum kall_tac) >>
  pure_rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >> qexistsl_tac [`res`, `es_end`, `r`] >> gvs[] >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
      first_x_assum (qspec_then `[]` mp_tac) >> strip_tac >>
      drule vyperInterpreterTheory.eval_exprs_length >> strip_tac >> conj_tac
      >- (irule (iffLR exprSimAggregateEncodingTheory.tuple_in_memory_replicate_elems) >> metis_tac[]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >> metis_tac[]
QED

val declared_array_body = ``
  !args ce cx env elem_ty tv stride header sa out sb es func inst x b asz s0 ctx tops.
  EVERY (\e. arg_type_fits (expr_type e) elem_ty) args /\
  well_formed_type (get_tenv cx) elem_ty /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  stride = type_memory_size tv /\ type_memory_bytes ce elem_ty = type_memory_size tv /\
  compile_make_array compile_expr ce args elem_ty stride header (Var x) sa = (out,sb) /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==> expr_body_pre ce cx env e st) /\
  body_inv tops ctx ce cx /\ body_exprs_mem_ok cx args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  (if header then 32 else 0) + LENGTH args * type_memory_size tv <= asz /\
  b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) b
       ((if header then 32 else 0) + LENGTH args * type_memory_size tv)) /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
      elems_in_memory vs (b+(if header then 32 else 0)) tv r.vs_memory /\
      (header ==> mem_word_at b r.vs_memory = n2w (LENGTH args)) /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b \/ b+(if header then 32 else 0)+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\ aid < sa.cs_next_id /\
        (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==> p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\ alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\ sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==> regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\res es' exit. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) exit)``;

Theorem aggregate_array_header_from_declared_elems_mem[local]:
  ^declared_array_elems ==> ^declared_array_body
Proof
  disch_tac >> rpt gen_tac >> strip_tac >> reverse (Cases_on `header`)
  >- (gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
      `compile_make_array_elems compile_expr ce args elem_ty (type_memory_bytes ce elem_ty) F (Var x) 0 sa = (out,sb)` by simp[] >>
      qpat_x_assum `!args. _` (drule_at (Pat `compile_make_array_elems _ _ _ _ _ _ _ _ _ = _`)) >>
      disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = _`)) >>
      disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
      disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
      disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
      disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
      disch_then (mp_tac o SPEC_ALL) >> (impl_tac >- (simp[] >> asm_rewrite_tac[])) >> simp[]) >>
  gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def, AllCaseEqs()] >>
  Cases_on `emit_void MSTORE [Var x; Lit (n2w (LENGTH args))] sa` >>
  rename1 `emit_void MSTORE _ sa = (u,sm)` >> Cases_on `u` >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono sm sb` by
    (mp_tac (Q.SPECL [`args`, `0`] (Q.INST [`header` |-> `T`,
       `cfn` |-> `compile_expr`, `buf` |-> `Var x`] compile_make_array_elems_as_tuple)) >>
     strip_tac >> gvs[] >>
     metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  qabbrev_tac `sh = mstore b (n2w (LENGTH args)) s0 with vs_inst_idx := SUC s0.vs_inst_idx` >>
  `32 <= asz /\ not_local_ptr ce es.scopes x` by (simp[] >> decide_tac) >>
  `!name lo sz. local_region ce es.scopes s0 name lo sz ==> b + asz <= lo \/ lo + sz <= b` by
    (rpt strip_tac >>
     drule_all (SRULE [] (Q.INST [`off` |-> `0`, `n` |-> `asz`, `r` |-> `s0`]
       aggregate_alloca_slice_excludes_local)) >> decide_tac) >>
  drule bodyMemArrayHeaderTheory.array_header_mem_entry >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME (_,_)`)) >>
  disch_then (qspec_then `sh` mp_tac) >>
  (impl_tac >- (simp[Abbr `sh`] >> rpt strip_tac >> first_x_assum drule_all >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >> strip_tac >>
  suspend "header_elements"
QED

Resume aggregate_array_header_from_declared_elems_mem[header_elements]:
  `compile_make_array_elems compile_expr ce args elem_ty (type_memory_bytes ce elem_ty) T (Var x) 0 sm = (out,sb)` by simp[] >>
  qpat_x_assum `!args. _` (drule_at (Pat `compile_make_array_elems _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ sh`)) >>
  disch_then (drule_at (Pat `FLOOKUP sh.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (mp_tac o SPEC_ALL) >>
  (impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum drule_all >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >>
  strip_tac >> conj_tac >- simp[] >>
  irule bodyDeclMemoryComposeTheory.gas_outcome_zero_prefix_mem >>
  qexists_tac `sh` >> conj_tac >- fs[gas_marked_path_def] >>
  drule struct_gas_outcome_post >> disch_then irule >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt gen_tac >> strip_tac >>
  `!n lb lsz. local_region ce es.scopes s0 n lb lsz ==> asz + b <= lb \/ lb + lsz <= b` by
    (rpt strip_tac >>
     qpat_assum `!name lo sz. local_region ce es.scopes s0 name lo sz ==> b + asz <= lo \/ _`
       (drule_then mp_tac) >> decide_tac) >>
  pure_rewrite_tac [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  irule (SRULE [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] array_header_success_post) >>
  drule bodyMemArrayHeaderTheory.array_header_emit_entry >>
  disch_then (qspecl_then [`x`, `ce`] strip_assume_tac) >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (qexists_tac `sm` >> gvs[Abbr `sh`, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  gvs[Abbr `sh`, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise aggregate_array_header_from_declared_elems_mem

Theorem aggregate_make_array_body_declared_from_head_mem:
  ^declared_head_contract ==> ^declared_array_body
Proof
  disch_then (mp_then (Pos hd) mp_tac aggregate_make_array_elems_declared_from_head_mem) >>
  MATCH_ACCEPT_TAC aggregate_array_header_from_declared_elems_mem
QED
