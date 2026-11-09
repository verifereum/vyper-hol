(* Actual value footprints remain separated from a later allocation site. *)
Theory bodyIntCallFamCallIntAllocationGeometry
Ancestors
  bodyIntCallFamCallIntStageAllocation

Theorem intcall_vv_at_footprint_location:
  vv_at ce cx ty a b es r vv s /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand (vv_operand vv) s = SOME w /\
  (case vv of StackValue _ _ => ~is_word_type ty
            | LocatedValue _ p => p.ptr_location = LocMemory) ==>
  (?aid lb len. FLOOKUP s.vs_allocas aid = SOME (lb,len) /\
    aid < b.cs_next_id /\ lb <= w2n w /\
    w2n w + val_footprint tv v <= lb+len) \/
  (?name lb len. local_region ce es.scopes s name lb len /\
    lb <= w2n w /\ w2n w + val_footprint tv v <= lb+len) \/
  val_footprint tv v = 0
Proof
  Cases_on `vv` >>
  simp[loweringPostsTheory.vv_at_def, contextTheory.vv_operand_def,
       loweringPostsTheory.expr_val_at_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem intcall_vv_at_allocation_disjoint:
  vv_at ce cx ty a sa es r vv s /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand (vv_operand vv) s = SOME w /\
  (case vv of StackValue _ _ => ~is_word_type ty
            | LocatedValue _ p => p.ptr_location = LocMemory) /\
  val_footprint tv v <> 0 /\
  stmt_state_rel ctx func ce cx es u /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (dst,sz) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
    regions_disjoint dst sz lb len) ==>
  regions_disjoint (w2n w) (val_footprint tv v) dst sz
Proof
  strip_tac >> drule_all intcall_vv_at_footprint_location >> strip_tac
  >- (irule intcall_stage_allocation_old_window >> metis_tac[])
  >- (first_x_assum drule >>
      simp[compileEnvTheory.regions_disjoint_def] >> decide_tac)
  >> simp[compileEnvTheory.regions_disjoint_def]
QED

(* A zero-sized value need not have an ordered address with respect to the
   destination: regions_disjoint is an ordering predicate even at size zero.
   The nonzero guard above is intentional; empty byte ranges frame trivially. *)
