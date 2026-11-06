Theory bodyPtrPrecompileBuiltinsRecoveryPostFrame
Ancestors exprSimPrecompiles exprLoweringProps localPtrsProps
          venomMemDefs compileEnv venomInst

Theorem registered_allocation_local_regions:
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_rel fn cenv es.scopes s /\ MEM inst (fn_insts fn) /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) ==>
  !name lo sz. local_region cenv es.scopes s name lo sz ==>
    regions_disjoint b n lo sz
Proof
  strip_tac >> `alloca_inv s` by fs[stmt_state_rel_def] >>
  rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
  goal_assum drule >> simp[] >> metis_tac[]
QED

Theorem registered_allocation_old_regions:
  stmt_state_rel ctx fn cenv cx es s /\
  FLOOKUP s.vs_allocas id = SOME (b,n) /\ sf.cs_next_id <= id ==>
  !aid lo sz. aid < sf.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (lo,sz) ==>
    regions_disjoint b n lo sz
Proof
  rpt strip_tac >> `id <> aid` by decide_tac >>
  irule state_allocations_disjoint >> goal_assum drule >> metis_tac[]
QED

(* Immutable regions already have exactly the required registered-allocation
   interface: use precompile_alloca_immutable_disjoint directly. *)
