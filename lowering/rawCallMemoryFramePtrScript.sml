(* Clean return-buffer writes may remove old taint.  Robust local values
   survive because their occupied region, not all memory, is unchanged. *)
Theory rawCallMemoryFramePtr
Ancestors
  robustCopyTransportPtr valueEncodingProps bodyPtrDefs pred_set ptrDiscipline
  venomInst finite_map localPtrsProps loweringSlice venomMemProps vyperCallOutcome

Theorem robust_val_clean_write_frame:
  val_wf tv v /\
  (p + val_footprint tv v <= dst \/ dst + LENGTH bytes <= p) /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==> val_in_memory tv v p mem) ==>
  !mem. mem_agree_outside
    (dirty DIFF {i | dst <= i /\ i < dst + LENGTH bytes})
    (write_memory_with_expansion dst bytes s).vs_memory mem ==>
    val_in_memory tv v p mem
Proof
  rpt strip_tac >> (
  irule robust_val_in_memory_exterior_frame >> simp[] >>
  qexistsl_tac [`s.vs_memory`, `(write_memory_with_expansion dst bytes s).vs_memory`,
    `dirty`, `dirty DIFF {i | dst <= i /\ i < dst + LENGTH bytes}`,
    `{i | dst <= i /\ i < dst + LENGTH bytes}`] >>
  simp[] >> rpt strip_tac >>
  irule write_memory_mem_bytes_at_disjoint >> decide_tac)
QED

Theorem oracle_call_memory_taint:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  (step_taint inst s t tn).t_mem =
    tn.t_mem DIFF range_bytes (step_writes inst s t)
Proof
  strip_tac >>
  `new_site_bytes s t = {}` by
    (simp[new_site_bytes_def, EXTENSION, finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]) >>
  simp[step_taint_def, mem_taint_def, written_taint_def] >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[] >>
  namedCases_on `rest` ["", "b rest2"] >> simp[] >>
  namedCases_on `rest2` ["", "c rest3"] >> simp[] >>
  Cases_on `rest3` >> simp[]
QED

(* Only the memory window and local pointer lookups matter here; oracle
   account updates and pc advancement are deliberately abstracted away. *)
Theorem local_ptrs_rel_clean_write_frame:
  local_ptrs_rel func cenv scopes s /\
  (!name entry p sz. lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p u = lookup_var p s) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  u.vs_memory = (write_memory_with_expansion dst bytes s).vs_memory /\
  (!name a len. local_region cenv scopes s name a len ==>
    regions_disjoint dst (LENGTH bytes) a len) ==>
  local_ptrs_rel func cenv scopes u
Proof
  strip_tac >> irule local_ptrs_rel_frame >> qexists_tac `s` >> simp[] >>
  reverse conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> irule val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`sz`, `s.vs_memory`] >> simp[] >>
  `local_region cenv scopes s name (w2n w) sz` by
    (simp[compileEnvTheory.local_region_def] >> metis_tac[]) >>
  qpat_x_assum `!name a len. local_region _ _ _ _ _ _ ==> _` drule >>
  simp[compileEnvTheory.regions_disjoint_def] >> strip_tac >>
  sym_tac >> irule write_memory_mem_bytes_at_disjoint >> simp[]
QED

Theorem immutables_rel_runtime_write_frame:
  immutables_rel cenv addr src F es s /\
  u.vs_data_section = s.vs_data_section /\
  u.vs_memory = (write_memory_with_expansion dst bytes s).vs_memory ==>
  immutables_rel cenv addr src F es u
Proof
  strip_tac >> irule immutables_rel_mem_agree >> qexists_tac `s` >>
  simp[venomMemPropsTheory.LENGTH_write_memory_with_expansion]
QED

Theorem oracle_adoption_locals:
  (SND (adopt_call_outcome rq outcome es)).scopes = es.scopes /\
  (SND (adopt_call_outcome rq outcome es)).immutables = es.immutables
Proof
  Cases_on `rq.cr_static` >> Cases_on `outcome.co_success` >>
  Cases_on `rq.cr_kind = MessageCall` >>
  simp[vyperCallOutcomeTheory.adopt_call_outcome_equation]
QED

(* The oracle's record update changes only effects and memory.  Freshness
   discharges local lookup preservation even after writing the status word. *)
Theorem oracle_write_semantic_frame:
  local_ptrs_rel func cenv es.scopes s /\
  immutables_rel cenv addr src F es s /\
  t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_data_section = s.vs_data_section /\
  t.vs_memory = (write_memory_with_expansion dst bytes s).vs_memory /\
  not_scope_ptr cenv es.scopes out /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint dst (LENGTH bytes) a len) ==>
  local_ptrs_rel func cenv es.scopes t /\
  immutables_rel cenv addr src F es t /\
  local_ptrs_rel func cenv es.scopes
    ((update_var out result t) with vs_inst_idx := pc) /\
  immutables_rel cenv addr src F es
    ((update_var out result t) with vs_inst_idx := pc)
Proof
  strip_tac >> rpt conj_tac
  >- (irule local_ptrs_rel_clean_write_frame >>
      qexistsl_tac [`bytes`, `dst`, `s`] >> simp[venomStateTheory.lookup_var_def] >>
      metis_tac[])
  >- (irule immutables_rel_runtime_write_frame >>
      qexistsl_tac [`bytes`, `dst`, `s`] >> simp[])
  >- (irule local_ptrs_rel_clean_write_frame >>
      qexistsl_tac [`bytes`, `dst`, `s`] >>
      simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
        finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt strip_tac >> fs[compileEnvTheory.not_scope_ptr_def] >> metis_tac[]) >>
  irule immutables_rel_runtime_write_frame >>
  qexistsl_tac [`bytes`, `dst`, `s`] >> simp[venomStateTheory.update_var_def]
QED

Theorem oracle_take_adoption_locals:
  take_call_outcome target calldata value_opt es = (INL (rq,outcome),es1) ==>
  (SND (adopt_call_outcome rq outcome es1)).scopes = es.scopes /\
  (SND (adopt_call_outcome rq outcome es1)).immutables = es.immutables
Proof
  strip_tac >> drule vyperCallOutcomeTheory.take_call_outcome_frame >>
  strip_tac >> simp[oracle_adoption_locals] >>
  fs[vyperStateTheory.evaluation_state_component_equality]
QED
