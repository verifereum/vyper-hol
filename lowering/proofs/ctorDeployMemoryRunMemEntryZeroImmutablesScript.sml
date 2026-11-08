Theory ctorDeployMemoryRunMemEntryZeroImmutables
Ancestors
  loweringStateRelDefs
  ctorDeployMemoryRunMemEntrySourceDefaults
  ctorDeployLoweringEntryImmutableMemory immutableRelation compileVyper
  ctorDeployDefs e2eDeployDefs compileEnv

Theorem ctor_source_zero_memory_immutables:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
  immutable_section_layout cenv tops /\
  (!p. p < imm_len tops ==>
    mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 []) ==>
  immutables_rel cenv tx.target NONE T (es0 with outcomes := SOME os) actual
Proof
  strip_tac >> drule_all ctor_source_start_immutables >> strip_tac >>
  irule deploy_ctor_zero_memory_immutables >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[deploy_source_ok_def]
QED

Theorem ctor_source_zero_memory_location:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
  immutable_section_layout cenv tops /\
  (!p. p < imm_len tops ==>
    mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 []) /\
  FLOOKUP cenv.ce_module_vars (NONE,name) = SOME (ImmutableLoc off) /\
  ALOOKUP es0.immutables tx.target = SOME imms /\
  FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) ==>
  off + type_memory_size tv <= imm_len tops /\
  immutable_value_admissible tv v /\
  val_in_memory tv v off actual.vs_memory /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at off (type_memory_size tv) actual.vs_memory)
Proof
  strip_tac >>
  drule_all ctor_source_start_immutables >> strip_tac >>
  `immutables_rel cenv tx.target NONE T es0 actual` by
    (irule deploy_ctor_zero_memory_immutables >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     gvs[deploy_source_ok_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `immutable_value_admissible tv v /\
   val_in_memory tv v off actual.vs_memory /\
   immutable_value_bytes_rel tv v
     (mem_bytes_at off (type_memory_size tv) actual.vs_memory)` by
    (gvs[immutables_rel_def] >> metis_tac[]) >>
  simp[] >>
  gvs[immutable_section_layout_def] >>
  first_x_assum drule >> strip_tac >>
  `MEM (VariableDecl vis Immutable name ty slot) tops` by simp[] >>
  `ALOOKUP es0.immutables tx.target = SOME imms` by simp[] >>
  drule_all ctor_source_start_immutable_default >> strip_tac >>
  gvs[imm_len_def] >>
  simp[compute_immutables_len_append, compute_immutables_len_def]
QED
