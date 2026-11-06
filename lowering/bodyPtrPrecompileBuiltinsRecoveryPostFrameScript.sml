Theory bodyPtrPrecompileBuiltinsRecoveryPostFrame
Ancestors exprSimPrecompiles exprLoweringProps localPtrsProps
          venomMemDefs compileEnv venomInst exprSimAlloc exprSimHash
          valueEncodingProps allocaFootprint exprSimProps loweringPosts

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

Theorem registered_word_store_state:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,32) /\
  (!name lo sz. local_region cenv es.scopes s name lo sz ==>
     regions_disjoint b 32 lo sz) ==>
  stmt_state_rel ctx fn cenv cx es (mstore b w s) /\
  mem_word_at b (mstore b w s).vs_memory = w
Proof
  strip_tac >> conj_tac
  >- (irule literal_mstore_state_rel >>
      reverse conj_tac >- simp[] >>
      qexistsl [`b`,`inst`,`32`] >> simp[] >>
      gvs[regions_disjoint_def]) >>
  simp[mstore_mem_word_at_same]
QED

Theorem registered_word_store_wb_frame:
  stmt_state_rel ctx fn cenv cx es s /\
  FLOOKUP s.vs_allocas id = SOME (b,32) /\ sf.cs_next_id <= id /\
  (!name lo sz. local_region cenv es.scopes s name lo sz ==>
     regions_disjoint b 32 lo sz) ==>
  wb_frame cenv es sf s (mstore b w s)
Proof
  strip_tac >> simp[wb_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule mstore_region_frame >>
      qexistsl [`b`,`32`] >> simp[] >>
      irule state_allocations_disjoint >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> decide_tac) >>
  irule locals_kept_regions >> rpt strip_tac >>
  irule mstore_region_frame >> qexistsl [`b`,`32`] >> simp[] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem wb_frame_counter_weaken:
  wb_frame cenv es sb s t /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id ==>
  wb_frame cenv es sa s t
Proof
  simp[wb_frame_def, not_fresh_at_def] >> rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]
QED
