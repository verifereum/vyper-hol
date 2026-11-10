(* Counted source-silent normalization of a widened conditional arm. *)
Theory bodyIfExpAggregateEndpoint
Ancestors
  bodyIfExpCompiledAggregate bodyIfExpSelectedEndpoint typedStorePathsMem
  gasSummary fragGasMode fragGasPathMem

Theorem ifexp_counted_conditional_of_read_mem[local]:
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0) marks (INL raw) ee (OK s) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  read_result cx raw (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
  ~s.vs_halted /\ gas_path_mem ctx func s n (OK u) ==>
  ?tv. gas_marked_exec T (ctx,func) (conditional_result cx raw)
    (ee with gas_obs := [],s) (REPLICATE n F) (INL tv)
    (ee with gas_obs := []) (OK u) /\
    read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := [])
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func) (read_result cx raw)
     (ee with gas_obs := [],s) [] (INL v) (ee with gas_obs := []) (OK s)` by
    (simp[gas_marked_exec_def, gas_marked_path_def] >>
     conj_tac
     >- (drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
     irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  drule_all ifexp_marked_conditional_of_read_mem >> strip_tac >>
  qexists_tac `tv` >> simp[] >>
  irule gas_marked_exec_no_source_read >>
  conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ (conditional_result _ _) _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def]) >>
  metis_tac[gas_marked_path_from_mem]
QED

Theorem ifexp_compiled_aggregate_marked_endpoint_mem:
  compile_expr ce ty e se = (vv,sa) /\
  compile_ifexp_arm ce dty sty vv sa = (op,sb) /\
  sty = lowered_value_type ce e /\ dty = expr_type e /\
  sty = post_value_type ce e /\ sty <> dty /\
  ~same_memory_layout ce sty dty /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  0 < type_memory_size stv /\ type_memory_size dtv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce se /\ local_ptrs_reserved ce origin /\
  local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes /\
  (!buf sm. compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) ==>
    (emitted_blocks sm sb <> [] ==>
      ?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0)) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0) marks (INL raw) ee (OK s) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  read_result cx raw (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
  vv_post ctx func ce cx e es origin sa s0 (ee with gas_obs := []) raw vv s /\
  vv_store_bound cx dty sty (ee with gas_obs := []) raw vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n tv u w.
    gas_marked_exec T (ctx,func) (conditional_result cx raw)
      (ee with gas_obs := [],s) (REPLICATE n F) (INL tv)
      (ee with gas_obs := []) (OK u) /\
    read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    gas_path_mem ctx func s n (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    expr_post ctx func ce cx (IfExp dty c a b) es origin sb s0
      (ee with gas_obs := []) v op u /\
    eval_operand op u = SOME w /\
    w2n w + type_memory_size dtv <= u.vs_alloca_next /\
    vv_store_bound cx dty dty (ee with gas_obs := []) tv
      (LocatedValue dty (mk_ptr op LocMemory)) u /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  drule_all ifexp_compiled_aggregate_arm_path_mem >>
  disch_then (qspecl_then [`c`,`b`,`a`] strip_assume_tac) >>
  drule_all ifexp_counted_conditional_of_read_mem >> strip_tac >>
  qexistsl_tac [`n`,`tv`,`u`,`w`] >> simp[] >>
  fs[exprSimMemDefsTheory.vv_store_bound_def] >> metis_tac[]
QED
