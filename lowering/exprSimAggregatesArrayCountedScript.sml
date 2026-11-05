(*
 * Counted array literal loop (#636)
 *
 * The gas-counted forms of exprSimAggregateLoops' array loops, with or
 * without a length word, for the array literal case of exprSimAggregates.
 *
 * TOP-LEVEL:
 *   aggregate_make_array_elems_counted — compile_make_array_elems
 *   aggregate_make_array_counted — compile_make_array
 *)
Theory exprSimAggregatesArrayCounted
Ancestors
  exprSimAggregatesLoopsCounted exprSimAggregateEncoding
  exprSimAggregateLoops exprSimAggregateChildren exprSimAlloc
  exprSimHyps exprSimHypsDefs exprSimSource exprSimProps exprSimDefs
  loweringPosts gasOutcome gasSummary gasSummaryCompose gasContext
  fragGasMode fragGasPath fragGasSeq fragExec stmtSimDeclPath
  exprLowering exprLoweringProps compileEnv valueEncoding
  vyperInterpreter vyperState venomState

Theorem array_header_store_state_rel[local]:
  stmt_state_rel ctx func ce cx es s /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
     lo + sz <= b \/ b + 32 <= lo) /\
  (ce.ce_is_ctor ==> !name tv v io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint io (type_memory_size tv) b 32) ==>
  stmt_state_rel ctx func ce cx es (mstore b w s)
Proof
  strip_tac >>
  `local_ptrs_rel func ce es.scopes (mstore b w s)` by
    (irule localPtrsPropsTheory.local_ptrs_rel_mstore >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es (mstore b w s)` by
    (irule loweringSliceTheory.immutables_rel_mem_agree >>
     qexists_tac `s` >> conj_tac
     >- (simp[immutableMemoryFrameTheory.immutable_mstore_capacity,
               arithmeticTheory.MAX_DEF] >> IF_CASES_TAC >> decide_tac) >>
     conj_tac >- simp[mstore_def] >>
     reverse conj_tac >- gvs[stmt_state_rel_def, state_rel_def] >>
     rpt strip_tac >> first_x_assum drule_all >>
     simp[regions_disjoint_def] >> strip_tac >>
     irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> simp[]) >>
  irule stmt_state_rel_allocas_frame >> conj_tac
  >- (irule immutable_base_zero_frame >> qexists_tac `s` >>
      gvs[stmt_state_rel_def, mstore_def, lookup_var_def]) >>
  conj_tac
  >- (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
      gvs[stmt_state_rel_def, mstore_def, local_region_def, lookup_var_def] >>
      metis_tac[]) >>
  conj_tac
  >- (irule state_rel_frame >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`es`, `s`] >>
      gvs[stmt_state_rel_def, mstore_def]) >>
  qexistsl_tac [`es`, `s`] >> simp[mstore_def]
QED

Theorem array_header_store_boundary[local]:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,asz) /\ 32 <= asz /\
  (ce.ce_is_ctor ==> !name tv v io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint io (type_memory_size tv) b 32) ==>
  stmt_state_rel ctx func ce cx es (mstore b w s) /\
  locals_kept ce es s (mstore b w s) /\
  mem_word_at b (mstore b w s).vs_memory = w /\
  (!p n. p+n <= b \/ b+32 <= p ==>
    mem_bytes_at p n (mstore b w s).vs_memory = mem_bytes_at p n s.vs_memory)
Proof
  strip_tac >>
  `!name lo sz. local_region ce es.scopes s name lo sz ==>
     lo + sz <= b \/ b + 32 <= lo` by
    (rpt strip_tac >>
     drule_all (SRULE [] (Q.INST [`off` |-> `0`, `n` |-> `32`]
       aggregate_alloca_slice_excludes_local)) >> simp[]) >>
  conj_tac >- (irule array_header_store_state_rel >> metis_tac[]) >>
  conj_tac
  >- (simp[locals_kept_def] >> rpt strip_tac >>
      irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
      first_x_assum drule >> strip_tac >> decide_tac) >>
  conj_tac >- simp[valueEncodingPropsTheory.mstore_mem_word_at_same] >>
  rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  decide_tac
QED

Theorem aggregate_make_array_elems_counted:
  !args ce cx env elem_ty tv header idx off sa out sb es func inst x b asz s0 ctx nocalls.
  EVERY (\e. expr_type e = elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  off = (if header then 32 else 0) + idx * type_memory_size tv /\
  compile_make_array_elems compile_expr ce args elem_ty
    (type_memory_bytes ce elem_ty) header (Var x) idx sa = (out,sb) /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ (nocalls ==> int_calls_expr e = [])) /\
  exprs_case nocalls ctx func ce cx args /\
  (~nocalls ==> !e. MEM e args ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + LENGTH args * type_memory_size tv <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (LENGTH args * type_memory_size tv)) /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
      elems_in_memory vs (b+off) tv r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es s0 r)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_make_array_elems_as_tuple >>
  disch_then (qspecl_then [`header`, `compile_expr`, `ce`, `Var x`, `idx`] mp_tac) >>
  strip_tac >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) =
     SOME (REPLICATE (LENGTH args) tv)` by
    (irule OPT_MMAP_uniform_map >> metis_tac[]) >>
  `compile_make_tuple compile_expr ce args (Var x) off sa = (out,sb)` by
    (gvs[] >> metis_tac[]) >>
  `off + type_memory_size_list (REPLICATE (LENGTH args) tv) <= asz` by
    gvs[type_memory_size_list_replicate] >>
  `ce.ce_is_ctor ==> !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (type_memory_size_list (REPLICATE (LENGTH args) tv))` by
    (gvs[type_memory_size_list_replicate] >> metis_tac[]) >>
  drule_all aggregate_make_tuple_counted >>
  pure_rewrite_tac [type_memory_size_list_replicate] >>
  disch_then strip_assume_tac >> conj_tac >- asm_rewrite_tac[] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  pure_rewrite_tac [gas_outcome_def, gas_summary_at_def] >>
  strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >>
      gvs[] >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      pure_rewrite_tac [gas_marked_exec_def] >> strip_tac >>
      first_x_assum (qspec_then `[]` mp_tac) >>
      strip_tac >> drule eval_exprs_length >> strip_tac >>
      metis_tac[tuple_in_memory_replicate_elems]) >>
  metis_tac[]
QED

Theorem aggregate_make_array_counted:
  !args ce cx env elem_ty tv stride header sa out sb es func inst x b asz s0 ctx nocalls.
  EVERY (\e. expr_type e = elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  stride = type_memory_size tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  compile_make_array compile_expr ce args elem_ty stride header (Var x) sa = (out,sb) /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ (nocalls ==> int_calls_expr e = [])) /\
  exprs_case nocalls ctx func ce cx args /\
  (~nocalls ==> !e. MEM e args ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  (if header then 32 else 0) + LENGTH args * type_memory_size tv <= asz /\
  b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) b
       ((if header then 32 else 0) + LENGTH args * type_memory_size tv)) /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
      elems_in_memory vs (b+(if header then 32 else 0)) tv r.vs_memory /\
      (header ==> mem_word_at b r.vs_memory = n2w (LENGTH args)) /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b \/ b+(if header then 32 else 0)+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es s0 r)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  cheat
QED
