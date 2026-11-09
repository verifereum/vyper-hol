(* Body-aware child continuation through the shared ADD/slice boundary. *)
Theory bodyMemAggregateBodyCons
Ancestors
  bodyMemAggregateConsContinuation bodyMemAggregateSliceContinuation
  bodyMemAggregateCons words

Theorem aggregate_body_cons_continuation_mem_cursor:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
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
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tvv vv r /\
  alloca_history func r /\ alloca_inv r /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts /\
  not_fresh_at sm x /\ lookup_var x r = SOME (n2w b) /\
  aid < sa.cs_next_id /\ FLOOKUP r.vs_allocas aid = SOME (b,asz) /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`P` |-> `\u. FLOOKUP u.vs_allocas aid = SOME (b,asz)`]
    (SPEC_ALL aggregate_cons_from_slice_mem_cursor)) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (rpt strip_tac >> gvs[] >> first_x_assum irule >> metis_tac[]) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- (rpt strip_tac >> gvs[]) >>
    rpt gen_tac >> strip_tac >>
    drule_at (Pat `compile_store_memory _ _ (Var _) _ _ _ = _`)
      aggregate_body_unwrap_store_slice_mem_cursor >>
    disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
    disch_then (drule_at (Pat `FLOOKUP _ aid = SOME (b,asz)`)) >>
    disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
    disch_then (drule_at (Pat `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _`)) >>
    disch_then (qspecl_then [`n2w (b+off)`, `tv`, `env`] mp_tac) >>
    `w2n (n2w (b+off):bytes32) = b+off` by
      (`b+off < dimword(:256)` by decide_tac >> simp[w2n_n2w]) >>
    (impl_tac >- (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (rpt strip_tac >>
        qpat_x_assum `!n lo k. local_region ce es'.scopes u n lo k ==> _`
          (drule_then mp_tac) >> decide_tac) >> first_assum ACCEPT_TAC)) >>
    simp[])) >> simp[]
QED
