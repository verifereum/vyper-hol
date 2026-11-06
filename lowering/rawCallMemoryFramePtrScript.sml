(* Clean return-buffer writes may remove old taint.  Robust local values
   survive because their occupied region, not all memory, is unchanged. *)
Theory rawCallMemoryFramePtr
Ancestors
  robustCopyTransportPtr valueEncodingProps bodyPtrDefs pred_set ptrDiscipline
  venomInst finite_map

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
