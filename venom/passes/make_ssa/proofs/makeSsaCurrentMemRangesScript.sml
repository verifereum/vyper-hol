Theory makeSsaCurrentMemRanges
Ancestors
  makeSsaCurrentOrdinary unitMemInv contextCodegenRel codegenRel
  makeSsaCurrentDefs stateFrame venomExecSemantics list pair

Theorem current_dret_memory_ranges_agree:
  inst.inst_opcode = DRET /\ inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st' ==>
  source_memory_read_ranges inst st = source_memory_read_ranges inst' st' /\
  source_memory_write_ranges inst st = source_memory_write_ranges inst' st'
Proof
  strip_tac >>
  `parse_dret_shape inst' = parse_dret_shape inst`
    by (irule current_parse_dret_shape >> qexists_tac `rs` >> simp[]) >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st`
    by (simp[] >> irule current_eval_operands_subset >> metis_tac[]) >>
  `st.vs_call_entry_fmp = st'.vs_call_entry_fmp`
    by (qpat_x_assum `execution_frame _ = _`
          (mp_tac o AP_TERM ``\s:venom_state. s.vs_call_entry_fmp``) >>
        simp[execution_frame_def]) >>
  simp[source_memory_write_ranges_def, source_memory_read_ranges_def,
       dret_memory_read_ranges_def]
QED

Theorem current_source_memory_write_ranges_agree:
  inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st' ==>
  source_memory_write_ranges inst st = source_memory_write_ranges inst' st'
Proof
  strip_tac >> Cases_on `inst.inst_opcode = DRET`
  >- metis_tac[current_dret_memory_ranges_agree] >>
  drule_all current_rename_operands_pointwise >> strip_tac >>
  Cases_on `inst.inst_opcode` >> simp[source_memory_write_ranges_def] >>
  qpat_x_assum `execution_frame _ = _` kall_tac >>
  qpat_x_assum `current_name_agree _ _ _ _` kall_tac >>
  map_every (fn q => Cases_on q >>
    gvs[current_rename_operands_map, LIST_REL_def,
        fixed_source_write_range_def, sized_source_write_range_def])
    [`inst.inst_operands`, `TL inst.inst_operands`,
     `TL (TL inst.inst_operands)`, `TL (TL (TL inst.inst_operands))`,
     `TL (TL (TL (TL inst.inst_operands)))`,
     `TL (TL (TL (TL (TL inst.inst_operands))))`,
     `TL (TL (TL (TL (TL (TL inst.inst_operands)))))`,
     `TL (TL (TL (TL (TL (TL (TL inst.inst_operands))))))`]
QED

Theorem current_eval_renamed_index:
  execution_frame st = execution_frame st' /\
  current_name_agree rs (venomInst$operand_vars allops) st st' /\
  (!op. MEM op ops ==> MEM op allops) /\ n < LENGTH ops ==>
  eval_operand (EL n (rename_current_operands rs ops)) st' =
  eval_operand (EL n ops) st
Proof
  strip_tac >> simp[current_rename_operands_el] >>
  irule current_eval_operand_occurrence >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexists_tac `allops` >> metis_tac[EL_MEM]
QED

Theorem current_log_memory_read_ranges_agree:
  inst.inst_opcode = LOG /\ inst'.inst_opcode = LOG /\
  inst.inst_operands = Lit tc :: rest /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st' ==>
  source_memory_read_ranges inst st = source_memory_read_ranges inst' st'
Proof
  strip_tac >> reverse (Cases_on `LENGTH rest = w2n tc + 2`)
  >- simp[source_memory_read_ranges_def, rename_current_operands_def] >>
  `eval_operand (EL 0 (rename_current_operands rs (REVERSE rest))) st' =
   eval_operand (EL 0 (REVERSE rest)) st` by
    (irule current_eval_renamed_index >>
     conj_tac >- simp[] >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     qexists_tac `inst.inst_operands` >> gvs[]) >>
  `eval_operand (EL 1 (rename_current_operands rs (REVERSE rest))) st' =
   eval_operand (EL 1 (REVERSE rest)) st` by
    (irule current_eval_renamed_index >>
     conj_tac >- simp[] >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     qexists_tac `inst.inst_operands` >> gvs[]) >>
  `eval_operands (rename_current_operands rs (DROP 2 (REVERSE rest))) st' =
   eval_operands (DROP 2 (REVERSE rest)) st` by
    (irule current_eval_operands_subset >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     qexists_tac `inst.inst_operands` >> gvs[] >>
     rpt strip_tac >> drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
  qpat_x_assum `eval_operand (EL 0 _) _ = _`
    (assume_tac o REWRITE_RULE [EL]) >>
  simp[source_memory_read_ranges_def, rename_current_operands_def,
       GSYM current_rename_operands_reverse, GSYM current_rename_operands_drop,
       memory_range_of_operands_def]
QED

Theorem current_source_memory_read_ranges_agree:
  inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st' ==>
  source_memory_read_ranges inst st = source_memory_read_ranges inst' st'
Proof
  strip_tac >> Cases_on `inst.inst_opcode = DRET`
  >- metis_tac[current_dret_memory_ranges_agree] >>
  Cases_on `inst.inst_opcode = LOG`
  >- (Cases_on `inst.inst_operands`
      >- simp[source_memory_read_ranges_def, rename_current_operands_def] >>
      rename1 `inst.inst_operands = h::rest` >> Cases_on `h`
      >- (irule current_log_memory_read_ranges_agree >>
          asm_rewrite_tac[] >> conj_tac >- metis_tac[] >>
          qexists_tac `rs` >> asm_rewrite_tac[]) >>
      simp[source_memory_read_ranges_def, rename_current_operands_def]) >>
  drule_all current_rename_operands_pointwise >> strip_tac >>
  Cases_on `inst.inst_opcode` >> simp[source_memory_read_ranges_def] >>
  qpat_x_assum `execution_frame _ = _` kall_tac >>
  qpat_x_assum `current_name_agree _ _ _ _` kall_tac >>
  map_every (fn q => Cases_on q >>
    gvs[current_rename_operands_map, LIST_REL_def, memory_range_of_operands_def])
    [`inst.inst_operands`, `TL inst.inst_operands`,
     `TL (TL inst.inst_operands)`, `TL (TL (TL inst.inst_operands))`,
     `TL (TL (TL (TL inst.inst_operands)))`,
     `TL (TL (TL (TL (TL inst.inst_operands))))`,
     `TL (TL (TL (TL (TL (TL inst.inst_operands)))))`,
     `TL (TL (TL (TL (TL (TL (TL inst.inst_operands))))))`]
QED

Theorem current_inst_mem_ranges_agree:
  inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st' ==>
  inst_mem_ranges inst st = inst_mem_ranges inst' st'
Proof
  strip_tac >>
  drule_all current_source_memory_read_ranges_agree >> strip_tac >>
  drule_all current_source_memory_write_ranges_agree >> strip_tac >>
  simp[inst_mem_ranges_def]
QED
