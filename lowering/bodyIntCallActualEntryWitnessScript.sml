(* Administrative operands defined by the actual capture prefix. *)
Theory bodyIntCallActualEntryWitness
Ancestors
  bodyIntCallActualEntryReservation bodyIntCallActualEntryResource
  bodyIntCallPrologueResource bodyIntCallBodyTrace intCallCallee
  compileEnv loweringStateRelDefs context emitHelper exprLoweringProps finite_map list rich_list
  arithmetic venomState

Theorem internal_entry_prefix_operands:
  compile_internal_entry_prefix ce params has_rb st0 = ((stage_ce,caps,rpc),sc) /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory ==>
  ?t mr x.
    run_inst_seq (emitted_insts st0 sc) s0 = OK t /\
    rpc = Var x /\ not_fresh_at sc x /\
    lookup_var x t = SOME s0.vs_return_pc_token /\
    (has_rb ==> ?p. stage_ce.ce_return_buf =
       (case ce.ce_return_buf of SOME (MemLoc off sz) => SOME (PtrVar (Var p) sz)
         | _ => ce.ce_return_buf) /\
       not_fresh_at sc p /\ lookup_var p t = SOME (HD args)) /\
    mat_inv func stage_ce env sc t caller.vs_alloca_next mr /\
    mat_pending stage_ce env sc t caller.vs_alloca_next mr caps /\
    mat_frame st0 s0 t /\
    t.vs_alloca_next = caller.vs_alloca_next /\
    (!n1 n2 b1 sz1 b2 sz2.
      n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\ mr n2 = SOME (b2,sz2) ==>
      regions_disjoint b1 sz1 b2 sz2)
Proof
  strip_tac >> drule internal_entry_prefix_shapes >> strip_tac >>
  drule internal_entry_prefix_stages >> strip_tac >>
  drule_all internal_capture_materialization_entry >> strip_tac >>
  qexistsl [`t`, `mr`, `x`] >> simp[] >> conj_tac
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      qexists `p` >> gvs[] >> Cases_on `ce.ce_return_buf` >> simp[] >>
      rename1 `SOME loc` >> Cases_on `loc` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `t = s0 with vs_vars := _` SUBST1_TAC >>
      drule setup_callee_frontier >> simp[]) >>
  qpat_x_assum `!n1 n2 b1 sz1 b2 sz2. _` mp_tac >> simp[]
QED

(* Materialization and return scratch preserve the administrative prefix. *)
Theorem internal_entry_suffix_frame:
  materialize_internal_params ce caps sr = (ce2,sm) /\
  (case rt of
     SOME ty => if alloc_ce.ce_returns_count > 0 then
       do compile_alloc_buffer (type_memory_bytes alloc_ce ty); comp_return () od
       else comp_return ()
   | NONE => comp_return ()) sm = ((),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  ALL_DISTINCT (MAP FST caps) /\
  mat_inv func ce env sr s lo mr /\ mat_pending ce env sr s lo mr caps /\
  (!n1 n2 b1 sz1 b2 sz2.
    n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\ mr n2 = SOME (b2,sz2) ==>
    regions_disjoint b1 sz1 b2 sz2) /\
  s.vs_alloca_next + internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps)
    < dimword (:256) ==>
  ?u. run_inst_seq (emitted_insts sr st1) s = OK u /\
    mat_frame sr s u /\ sr.cs_next_var <= st1.cs_next_var
Proof
  strip_tac >> drule materialize_internal_params_shape >> strip_tac >>
  drule internal_scratch_shape >> strip_tac >>
  drule_all internal_prologue_segment_members >>
  disch_then (qspec_then `sr` strip_assume_tac) >>
  `!i. MEM i (DROP (LENGTH sr.cs_current_insts) sm.cs_current_insts) ==>
    MEM i (fn_insts func)` by fs[emitted_insts_def] >>
  drule_all materialize_run_compact >> strip_tac >>
  rename1 `mat_inv func ce2 env sm materialized lo mr` >>
  `run_inst_seq (emitted_insts sr sm) s = OK materialized` by
    gvs[emitted_insts_def] >>
  drule_all internal_scratch_materialization_inv >> strip_tac >>
  rename1 `mat_frame sm materialized landing` >>
  qexists `landing` >> conj_tac
  >- (irule run_entry_segments >> qexistsl [`sm`, `materialized`] >>
      simp[IS_PREFIX_APPEND]) >>
  conj_tac
  >- (irule mat_frame_trans >> qexistsl [`sm`, `materialized`] >>
      simp[] >> fs[not_fresh_at_def] >> decide_tac) >>
  decide_tac
QED

Theorem internal_entry_optional_reservation:
  (if ctor /\ 0 < n then
     do ar <- compile_fixed_region_with_id n; comp_return (SOME (SND ar).buf_operand) od
   else comp_return NONE) sc = (imm,sr) /\
  mat_inv func ce env sc t lo mr /\ mat_pending ce env sc t lo mr caps ==>
  ?u. run_inst_seq (emitted_insts sc sr) t = OK u /\
    mat_inv func ce env sr u lo mr /\ mat_pending ce env sr u lo mr caps /\
    mat_frame sc t u /\ u.vs_alloca_next = t.vs_alloca_next /\
    sc.cs_next_var <= sr.cs_next_var /\
    isPREFIX sc.cs_current_insts sr.cs_current_insts /\
    (!op. imm = SOME op ==> ?x. op = Var x /\ not_fresh_at sr x /\
      lookup_var x u = SOME 0w)
Proof
  strip_tac >> Cases_on `ctor /\ 0 < n`
  >- (gvs[comp_bind_def, comp_return_def] >> pairarg_tac >> gvs[] >>
      PairCases_on `ar` >>
      drule_all mat_fixed_region_assignment >> strip_tac >>
      drule compile_fixed_region_with_id_result >> strip_tac >>
      drule internal_fixed_region_shape >> strip_tac >>
      qexists `s'` >> simp[] >> conj_tac
      >- (drule immutableWordExecutionTheory.compile_fixed_region_execution >>
          disch_then (qspec_then `t` mp_tac) >> simp[] >>
          strip_tac >> gvs[update_var_def]) >>
      fs[eval_operand_def, not_fresh_at_def] >> metis_tac[]) >>
  gvs[comp_return_def] >> qexists `t` >>
  simp[emitted_insts_def, run_inst_seq_def, mat_frame_refl]
QED

Theorem internal_entry_administrative_stages:
  compile_internal_function_entry ce params has_rb ctor n rt st0 =
    ((ce2,rpc,imm),st1) ==>
  ?stage_ce caps sc sr sm.
    compile_internal_entry_prefix ce params has_rb st0 = ((stage_ce,caps,rpc),sc) /\
    (if ctor /\ 0 < n then
       do ar <- compile_fixed_region_with_id n; comp_return (SOME (SND ar).buf_operand) od
     else comp_return NONE) sc = (imm,sr) /\
    materialize_internal_params stage_ce caps sr = (ce2,sm) /\
    (case rt of
       SOME ty => if ce.ce_returns_count > 0 then
         do compile_alloc_buffer (type_memory_bytes ce ty); comp_return () od
         else comp_return ()
     | NONE => comp_return ()) sm = ((),st1)
Proof
  simp[compile_internal_function_entry_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_internal_entry_prefix _ _ _ _ = (prefix,_)` >>
  PairCases_on `prefix` >> gvs[] >>
  Cases_on `rt` >> Cases_on `ce.ce_returns_count > 0` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> fs[GREATER_DEF] >> metis_tac[]
QED

Theorem internal_entry_operand_landing:
  compile_internal_function_entry ce params has_rb ctor n rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u ==>
  (?x. rpc = Var x /\ not_fresh_at st1 x /\
       lookup_var x u = SOME s0.vs_return_pc_token) /\
  (has_rb ==> ?p.
    ce2.ce_return_buf =
      (case ce.ce_return_buf of SOME (MemLoc off sz) => SOME (PtrVar (Var p) sz)
       | _ => ce.ce_return_buf) /\
    not_fresh_at st1 p /\ lookup_var p u = SOME (HD args)) /\
  (!op. imm = SOME op ==> ?x. op = Var x /\ not_fresh_at st1 x /\
    lookup_var x u = SOME 0w)
Proof
  strip_tac >> drule internal_entry_administrative_stages >> strip_tac >>
  drule internal_entry_prefix_shapes >> strip_tac >>
  drule_all internal_entry_prefix_operands >> strip_tac >>
  rename1 `mat_inv func stage_ce env sc captured _ mr` >>
  drule_all internal_entry_optional_reservation >> strip_tac >>
  rename1 `mat_frame sc captured reserved` >>
  `ALL_DISTINCT (MAP FST caps)` by fs[internal_args_rel_def] >>
  `reserved.vs_alloca_next +
    internal_stack_size stage_ce (MAP (\c. (FST c,FST (SND c))) caps) < dimword (:256)` by
    (simp[] >> metis_tac[internal_stack_size_vars]) >>
  drule_all internal_entry_suffix_frame >> strip_tac >>
  rename1 `mat_frame sr reserved landing` >>
  drule internal_scratch_shape >> strip_tac >>
  drule materialize_internal_params_shape >> strip_tac >>
  `isPREFIX sr.cs_current_insts st1.cs_current_insts` by
    metis_tac[IS_PREFIX_TRANS, IS_PREFIX_APPEND] >>
  `isPREFIX sc.cs_current_insts st1.cs_current_insts` by
    metis_tac[IS_PREFIX_TRANS] >>
  `run_inst_seq (emitted_insts st0 st1) s0 = OK landing` by
    (irule run_entry_segments >> qexistsl [`sc`, `captured`] >> simp[] >>
     irule run_entry_segments >> qexistsl [`sr`, `reserved`] >> simp[]) >>
  `landing = u` by gvs[] >> gvs[] >>
  suspend "lookups"
QED

Resume internal_entry_operand_landing[lookups]:
  `!p. not_fresh_at sc p ==> not_fresh_at sr p /\ not_fresh_at st1 p` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!p. not_fresh_at sr p ==> not_fresh_at st1 p` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!p. not_fresh_at sc p ==> lookup_var p landing = lookup_var p captured` by
    (fs[mat_frame_def] >> metis_tac[]) >>
  `!p. not_fresh_at sr p ==> lookup_var p landing = lookup_var p reserved` by
    fs[mat_frame_def] >>
  rpt conj_tac >- metis_tac[] >- metis_tac[] >> metis_tac[]
QED

Finalise internal_entry_operand_landing
