(* Return storage is separate from every later staged memory argument. *)
Theory bodyIntCallStageReturn
Ancestors
  bodyIntCallStageEndpoint bodyIntCallStageAllocation bodyIntCallStageOwned
  allocaSiteResource venomState loweringHalt
  exprSimConvertBytes loweringPosts venomMemDefs compileEnv

Theorem staged_arg_old_allocation_disjoint:
  staged_arg ce func es a sm t (ty,tv,v,F,op) /\
  alloca_inv t /\ rid < a.cs_next_id /\
  FLOOKUP t.vs_allocas rid = SOME (rb,cap) /\
  eval_operand op t = SOME w /\ rsz <= cap ==>
  compileEnv$regions_disjoint rb rsz (w2n w) (type_memory_size tv)
Proof
  simp[staged_arg_def] >> strip_tac >>
  `rid <> aid` by decide_tac >>
  gvs[venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.allocas_non_overlapping_def,
      loweringStateRelDefsTheory.regions_disjoint_def] >>
  first_x_assum (drule_at Any) >>
  disch_then (qspec_then `inst.inst_id` mp_tac) >> simp[] >> decide_tac
QED

Theorem staged_return_frame:
  wb_frame ce es es sm s t /\ not_fresh_at sm x /\
  eval_operand (Var x) s = SOME w /\
  FLOOKUP s.vs_allocas rid = SOME (rb,cap) /\
  alloca_inv t /\ rsz <= cap ==>
  eval_operand (Var x) t = SOME w /\
  FLOOKUP t.vs_allocas rid = SOME (rb,cap) /\
  rb + rsz <= t.vs_alloca_next
Proof
  simp[wb_frame_def, venomStateTheory.eval_operand_def] >> strip_tac >>
  `FLOOKUP t.vs_allocas rid = SOME (rb,cap)` by metis_tac[] >>
  drule_all alloca_site_registered_below >> strip_tac >>
  simp[]
QED

