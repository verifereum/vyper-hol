Theory gasShadowUnitExtract
Ancestors
  gasShadowUnit gasShadowState gasShadowModuleDefs vyperCompiler venomInst
  list pair

Theorem gas_shadow_mk_raw_function:
  !bs cs name. LIST_REL gas_shadow_block bs cs ==>
    gas_shadow_function (mk_raw_function name bs) (mk_raw_function name cs)
Proof
  simp[gas_shadow_function_def, mk_raw_function_def]
QED

Theorem gas_shadow_mk_internal_function:
  !bs cs name buf rc. LIST_REL gas_shadow_block bs cs ==>
    gas_shadow_function (mk_internal_function name bs buf rc)
      (mk_internal_function name cs buf rc)
Proof
  simp[gas_shadow_function_def, mk_internal_function_def, mk_raw_function_def]
QED

Theorem gas_shadow_mk_venom_context:
  !fs gs entry. LIST_REL gas_shadow_function fs gs ==>
    gas_shadow_context (mk_venom_context fs entry) (mk_venom_context gs entry)
Proof
  simp[gas_shadow_context_def, mk_venom_context_def]
QED

Theorem gas_shadow_split_blocks_at:
  !bs cs label. LIST_REL gas_shadow_block bs cs ==>
    OPTREL (\(p,s) (q,t). LIST_REL gas_shadow_block p q /\ LIST_REL gas_shadow_block s t)
      (split_blocks_at label bs) (split_blocks_at label cs)
Proof
  Induct >> Cases_on `cs` >> simp[split_blocks_at_def] >>
  rpt gen_tac >> strip_tac >>
  `h.bb_label = h'.bb_label` by gvs[gas_shadow_block_def] >>
  simp[split_blocks_at_def] >> IF_CASES_TAC >- simp[] >>
  first_x_assum drule >> disch_then (qspec_then `label` mp_tac) >>
  Cases_on `split_blocks_at label bs` >> Cases_on `split_blocks_at label t` >>
  simp[] >> PairCases_on `x` >> PairCases_on `x'` >> simp[]
QED

Theorem gas_shadow_package_internal_blocks:
  !ds bs cs. LIST_REL gas_shadow_block bs cs ==>
    OPTREL (\(p,fs) (q,gs). LIST_REL gas_shadow_block p q /\ LIST_REL gas_shadow_function fs gs)
      (package_internal_blocks ds bs) (package_internal_blocks ds cs)
Proof
  Induct >> simp[package_internal_blocks_def] >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  drule gas_shadow_split_blocks_at >> disch_then (qspec_then `h0` mp_tac) >>
  Cases_on `split_blocks_at h0 bs` >> Cases_on `split_blocks_at h0 cs` >>
  simp[package_internal_blocks_def] >>
  PairCases_on `x` >> PairCases_on `x'` >> simp[] >> strip_tac >>
  first_x_assum drule >>
  Cases_on `package_internal_blocks ds x1` >>
  Cases_on `package_internal_blocks ds x'1` >> simp[] >>
  PairCases_on `x` >> PairCases_on `x'` >>
  simp[gas_shadow_mk_internal_function]
QED

Theorem gas_shadow_internal_fn_descriptors[simp]:
  !ints. internal_fn_descriptors (MAP gas_shadow_internal_package ints) =
    internal_fn_descriptors ints
Proof
  Induct >> simp[internal_fn_descriptors_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[internal_fn_descriptors_def, gas_shadow_internal_package_def]
QED

Theorem gas_shadow_extract_context_with_internals:
  !s t entry ints. gas_shadow_state s t ==>
    OPTREL (\(c,d) (c',d'). gas_shadow_context c c' /\ d = d')
      (extract_context_with_internals entry ints s)
      (extract_context_with_internals entry (MAP gas_shadow_internal_package ints) t)
Proof
  rpt gen_tac >> strip_tac >>
  `LIST_REL gas_shadow_block
     (REVERSE s.cs_blocks ++ [<| bb_label := s.cs_current_bb;
                                bb_instructions := s.cs_current_insts |>])
     (REVERSE t.cs_blocks ++ [<| bb_label := t.cs_current_bb;
                                bb_instructions := t.cs_current_insts |>])`
    by gvs[gas_shadow_state_def, gas_shadow_block_def] >>
  drule gas_shadow_package_internal_blocks >>
  disch_then (qspec_then `internal_fn_descriptors ints` mp_tac) >>
  simp[extract_context_with_internals_def] >>
  qmatch_goalsub_abbrev_tac `package_internal_blocks ds bs` >>
  qabbrev_tac `cs = REVERSE t.cs_blocks ++
    [<| bb_label := t.cs_current_bb; bb_instructions := t.cs_current_insts |>]` >>
  Cases_on `package_internal_blocks ds bs` >>
  Cases_on `package_internal_blocks ds cs` >> simp[] >>
  PairCases_on `x` >> PairCases_on `x'` >> simp[] >> strip_tac >>
  gvs[gas_shadow_state_def] >>
  irule gas_shadow_mk_venom_context >>
  simp[gas_shadow_mk_raw_function]
QED

Theorem gas_shadow_install_immutable_reservation:
  gas_shadow_context c d ==>
  gas_shadow_context (install_immutable_reservation n c)
                     (install_immutable_reservation n d)
Proof
  simp[gas_shadow_context_def, install_immutable_reservation_def] >>
  strip_tac >>
  qpat_x_assum `_ = c` mp_tac >>
  disch_then (fn th => once_rewrite_tac[GSYM th]) >> simp[]
QED
