Theory makeSsaCurrentRetainedContext
Ancestors
  makeSsaCurrentRetainedEffect makeSsaCurrentWfSsa removeUnusedProofs
  venomExecProps venomWf venomInst list

Theorem current_retained_block_count:
  !bbs bb P. MEM bb bbs ==>
  LENGTH (FILTER P bb.bb_instructions) <=
    LENGTH (FILTER P (fn_insts_blocks bbs))
Proof
  Induct >> simp[fn_insts_blocks_def] >> rpt strip_tac >> gvs[] >>
  simp[listTheory.FILTER_APPEND_DISTRIB] >>
  first_x_assum drule >> disch_then (qspec_then `P` mp_tac) >> simp[]
QED

Theorem current_retained_original_effect:
  wf_function fn /\ fn_phi_outputs_single_def fn /\
  lookup_block h fn.fn_blocks = SOME old /\
  k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_outputs = [x] ==>
  phi_eff (SOME p) x old.bb_instructions =
    resolve_phi p (EL k old.bb_instructions).inst_operands
Proof
  strip_tac >>
  `MEM old fn.fn_blocks /\ MEM (EL k old.bb_instructions) old.bb_instructions` by
    metis_tac[lookup_block_MEM, listTheory.MEM_EL] >>
  `LENGTH (FILTER (\i. MEM x i.inst_outputs) (fn_insts fn)) <= 1` by
    (fs[fn_phi_outputs_single_def_def] >> metis_tac[listTheory.MEM]) >>
  `LENGTH (FILTER (\i. MEM x i.inst_outputs) old.bb_instructions) <= 1` by
    (drule current_retained_block_count >>
     disch_then (qspec_then `\i. MEM x i.inst_outputs` mp_tac) >>
     fs[fn_insts_def] >> decide_tac) >>
  irule current_retained_index_effect >> simp[] >> gen_tac >> strip_tac >>
  conj_tac
  >- (fs[wf_function_def, bb_well_formed_def] >> metis_tac[]) >>
  strip_tac >>
  `i = k` by (irule (INST_TYPE [alpha |-> ``:instruction``] current_retained_filter_unique_index) >>
    qexistsl [`\j. MEM x j.inst_outputs`, `old.bb_instructions`] >> simp[]) >>
  decide_tac
QED

Theorem current_retained_context_before:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  q < LENGTH new.bb_instructions /\
  (EL q new.bb_instructions).inst_opcode = PHI /\
  (EL q new.bb_instructions).inst_outputs = [y] ==>
  !i. i < q ==> (EL i new.bb_instructions).inst_opcode = PHI /\
    ~MEM y (EL i new.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `ssa_form (fn with fn_blocks := renamed)` by
    metis_tac[current_wf_phi_context_ssa_form] >>
  gen_tac >> strip_tac >> conj_tac
  >- metis_tac[current_wf_phi_context_prefix_order] >>
  strip_tac >>
  `i = q` by
    (irule ssa_form_no_dup_in_block >>
     qexistsl [`new`, `fn with fn_blocks := renamed`, `y`] >>
     simp[] >> metis_tac[lookup_block_MEM, arithmeticTheory.LESS_TRANS]) >>
  decide_tac
QED

Theorem current_retained_context_effect:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  q < LENGTH new.bb_instructions /\
  (EL q new.bb_instructions).inst_opcode = PHI /\
  (EL q new.bb_instructions).inst_outputs = [y] ==>
  phi_eff (SOME p) y new.bb_instructions =
    resolve_phi p (EL q new.bb_instructions).inst_operands /\
  (simplify_current_phi (EL q new.bb_instructions) = EL q new.bb_instructions ==>
   phi_eff (SOME p) y (simplify_current_phi_block new).bb_instructions =
     resolve_phi p (EL q new.bb_instructions).inst_operands)
Proof
  strip_tac >>
  `!i. i < q ==> (EL i new.bb_instructions).inst_opcode = PHI /\
    ~MEM y (EL i new.bb_instructions).inst_outputs` by
    metis_tac[current_retained_context_before] >>
  conj_tac
  >- (irule current_retained_index_effect >> simp[]) >>
  strip_tac >> irule current_retained_index_cleanup_effect >> simp[]
QED

Theorem current_retained_original_at_effect:
  current_wf_phi_context s fn renamed s' A H events /\
  current_wf_original_phi_at fn A renamed h k q slots /\
  lookup_block h fn.fn_blocks = SOME old /\
  (EL k old.bb_instructions).inst_outputs = [x] ==>
  phi_eff (SOME p) x old.bb_instructions =
    resolve_phi p (EL k old.bb_instructions).inst_operands
Proof
  strip_tac >>
  `wf_function fn /\ fn_phi_outputs_single_def fn` by
    fs[current_wf_phi_context_def] >>
  `k < LENGTH old.bb_instructions /\ (EL k old.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_original_phi_at_def] >> metis_tac[]) >>
  metis_tac[current_retained_original_effect]
QED
