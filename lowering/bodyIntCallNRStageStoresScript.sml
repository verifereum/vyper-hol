(* Stores publish a declared-type snapshot at their own counted endpoint.
   Allocation and type conversion are inputs, not hidden staging invariants. *)
Theory bodyIntCallNRStageStores
Ancestors
  bodyIntCallFamCallIntStageStore bodyIntCallAggregateStoreFrame
  exprSimIfExpWidenedBytesCounted placeMemoryCopyEffect
  context compileEnv exprLoweringProps loweringStateRelDefs venomState
  valueEncoding freshWrites finite_map words list

(* Common certificate transport.  The byte frame is for the whole allocated
   capacity, including padding, rather than only the represented value. *)
Theorem intcall_stage_snapshot_landing[local]:
  typed_copy_effect ctx func sa sb s u (w2n dw) n /\
  n <= MAX 32 (type_memory_size tv) /\
  val_in_memory tv v (w2n dw) u.vs_memory /\ val_wf tv v /\
  eval_operand dst s = SOME dw /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sb.cs_next_var /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,MAX 32 (type_memory_size tv)) /\
  start.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  w2n dw + MAX 32 (type_memory_size tv) <= s.vs_alloca_next /\
  w2n dw + MAX 32 (type_memory_size tv) < dimword (:256) ==>
  gas_marked_path F ctx func s 0 (OK u) /\
  typed_copy_effect ctx func sa sb s u (w2n dw) (MAX 32 (type_memory_size tv)) /\
  val_in_memory tv v (w2n dw) u.vs_memory /\ val_wf tv v /\
  eval_operand dst u = SOME dw /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  FLOOKUP u.vs_allocas aid = SOME (w2n dw,MAX 32 (type_memory_size tv)) /\
  start.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  w2n dw + MAX 32 (type_memory_size tv) <= u.vs_alloca_next /\
  w2n dw + MAX 32 (type_memory_size tv) < dimword (:256) /\
  u.vs_alloca_next = s.vs_alloca_next /\
  (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op u = eval_operand op s)
Proof
  strip_tac >>
  `typed_copy_effect ctx func sa sb s u (w2n dw) (MAX 32 (type_memory_size tv))` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op u = eval_operand op s` by
    (Cases_on `op` >>
     gvs[typed_copy_effect_def, venom_state_component_equality,
         eval_operand_def, lookup_var_def]) >>
  `!x. dst = Var x ==> not_fresh_at sb x` by
    metis_tac[not_fresh_at_mono] >>
  gvs[typed_copy_effect_def, venom_state_component_equality] >> metis_tac[]
QED

Theorem intcall_stage_word_snapshot:
  compile_store_memory ce src dst dty sty sa = ((),sb) /\
  is_word_type sty /\ is_word_type dty /\
  evaluate_type tenv dty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  eval_operand src s = SOME (typed_val_to_w256 tv v) /\
  eval_operand dst s = SOME dw /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  type_memory_bytes ce dty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    regions_disjoint b sz (w2n dw) (type_memory_size tv)) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n dw) (type_memory_size tv)) /\
  sa.cs_next_var <= sb.cs_next_var /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,MAX 32 (type_memory_size tv)) /\
  start.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  w2n dw + MAX 32 (type_memory_size tv) <= s.vs_alloca_next /\
  w2n dw + MAX 32 (type_memory_size tv) < dimword (:256) ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    typed_copy_effect ctx func sa sb s u (w2n dw) (MAX 32 (type_memory_size tv)) /\
    stmt_state_rel ctx func ce cx es u /\
    val_in_memory tv v (w2n dw) u.vs_memory /\ val_wf tv v /\
    eval_operand dst u = SOME dw /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    FLOOKUP u.vs_allocas aid = SOME (w2n dw,MAX 32 (type_memory_size tv)) /\
    start.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    w2n dw + MAX 32 (type_memory_size tv) <= u.vs_alloca_next /\
    w2n dw + MAX 32 (type_memory_size tv) < dimword (:256) /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op u = eval_operand op s)
Proof
  strip_tac >>
  `compile_store_memory ce src dst dty dty sa = ((),sb)` by
    (gvs[compile_store_memory_def]) >>
  mp_tac (Q.INST [`P` |-> `\b n. regions_disjoint b n (w2n dw) (type_memory_size tv)`,
    `reserved` |-> `\op:operand. F`, `sty` |-> `dty`, `stv` |-> `tv`,
    `dtv` |-> `tv`, `sw` |-> `typed_val_to_w256 tv v`]
    (SPEC_ALL protected_compatible_store_state_landing)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `typed_copy_effect ctx func sa sb s u (w2n dw) (type_memory_size tv)` by
    (simp[typed_copy_effect_def, regions_disjoint_def]) >>
  `type_memory_size tv <= MAX 32 (type_memory_size tv)` by simp[] >>
  drule_all intcall_stage_snapshot_landing >> strip_tac >>
  qexists_tac `u` >> simp[]
QED

Theorem intcall_stage_bytes_snapshot:
  compile_store_bytestring src dst sa = ((),sb) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  type_memory_size tv < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,MAX 32 (type_memory_size tv)) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    b+sz <= w2n dw \/ w2n dw+MAX 32 (type_memory_size tv) <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n dw) (MAX 32 (type_memory_size tv))) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  sa.cs_next_var <= sb.cs_next_var /\
  start.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  w2n dw + MAX 32 (type_memory_size tv) <= s.vs_alloca_next /\
  w2n dw + MAX 32 (type_memory_size tv) < dimword (:256) ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    typed_copy_effect ctx func sa sb s u (w2n dw) (MAX 32 (type_memory_size tv)) /\
    stmt_state_rel ctx func ce cx es u /\
    val_in_memory tv v (w2n dw) u.vs_memory /\ val_wf tv v /\
    eval_operand dst u = SOME dw /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    FLOOKUP u.vs_allocas aid = SOME (w2n dw,MAX 32 (type_memory_size tv)) /\
    start.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    w2n dw + MAX 32 (type_memory_size tv) <= u.vs_alloca_next /\
    w2n dw + MAX 32 (type_memory_size tv) < dimword (:256) /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op u = eval_operand op s)
Proof
  strip_tac >>
  `type_memory_size tv <= MAX 32 (type_memory_size tv)` by simp[] >>
  drule_all bytestring_store_allocated_counted_frame >> strip_tac >>
  `typed_copy_effect ctx func sa sb s t (w2n dw) (MAX 32 (type_memory_size tv))` by
    (gvs[typed_copy_effect_def, venom_state_component_equality] >> metis_tac[]) >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `MAX 32 (type_memory_size tv) <= MAX 32 (type_memory_size tv)` by simp[] >>
  drule_all intcall_stage_snapshot_landing >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

(* The conditional metadata obligation is exactly the public store interface:
   compatible copies do not require a structural widening derivation. *)
Theorem intcall_stage_aggregate_snapshot:
  compile_store_memory ce src dst dty sty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  value_has_type dtv v /\ value_has_type stv v /\ val_wf dtv v /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  (if is_word_type sty then sw = typed_val_to_w256 stv v
   else val_in_memory stv v (w2n sw) s.vs_memory) /\
  type_memory_size dtv + 64 < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    regions_disjoint b sz (w2n dw) (type_memory_size dtv)) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n dw) (type_memory_size dtv)) /\
  (~(dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) ==>
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    (!ty tv. evaluate_type tenv ty = SOME tv ==>
      type_memory_bytes ce ty = type_memory_size tv) /\
    type_widens_to tenv sty dty /\ val_wf dtv v /\ val_wf stv v /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256)) /\
  sa.cs_next_var <= sb.cs_next_var /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,MAX 32 (type_memory_size dtv)) /\
  start.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  w2n dw + MAX 32 (type_memory_size dtv) <= s.vs_alloca_next /\
  w2n dw + MAX 32 (type_memory_size dtv) < dimword (:256) ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    typed_copy_effect ctx func sa sb s u (w2n dw) (MAX 32 (type_memory_size dtv)) /\
    stmt_state_rel ctx func ce cx es u /\
    val_in_memory dtv v (w2n dw) u.vs_memory /\ val_wf dtv v /\
    eval_operand dst u = SOME dw /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    FLOOKUP u.vs_allocas aid = SOME (w2n dw,MAX 32 (type_memory_size dtv)) /\
    start.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    w2n dw + MAX 32 (type_memory_size dtv) <= u.vs_alloca_next /\
    w2n dw + MAX 32 (type_memory_size dtv) < dimword (:256) /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op u = eval_operand op s)
Proof
  strip_tac >> drule_all intcall_stage_store_effect >> strip_tac >>
  `type_memory_size dtv <= MAX 32 (type_memory_size dtv)` by simp[] >>
  drule_all intcall_stage_snapshot_landing >> strip_tac >>
  qexists_tac `u` >> simp[]
QED
