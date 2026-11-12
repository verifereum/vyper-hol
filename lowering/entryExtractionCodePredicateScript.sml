Theory entryExtractionCodePredicate
Ancestors
  entryCodePredicate entryDallocaCoverage vyperCompiler venomInst unitShapeDefs list

Theorem entry_code_split_blocks:
  split_blocks_at label blocks = SOME (prefix,suffix) /\
  EVERY (\b. EVERY P b.bb_instructions) blocks ==>
  EVERY (\b. EVERY P b.bb_instructions) prefix /\
  EVERY (\b. EVERY P b.bb_instructions) suffix
Proof
  qid_spec_tac `prefix` >> Induct_on `blocks` >>
  simp[split_blocks_at_def] >> rpt gen_tac >>
  Cases_on `h.bb_label = label` >>
  gvs[split_blocks_at_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem entry_code_package_blocks:
  package_internal_blocks descriptors blocks = SOME (entry_blocks,functions) /\
  EVERY (\b. EVERY P b.bb_instructions) blocks ==>
  EVERY (\b. EVERY P b.bb_instructions) entry_blocks /\
  EVERY (\f. EVERY P (fn_insts f)) functions
Proof
  map_every qid_spec_tac [`blocks`, `entry_blocks`, `functions`] >>
  Induct_on `descriptors`
  >- simp[package_internal_blocks_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[package_internal_blocks_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_all entry_code_split_blocks >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  simp[mk_internal_function_def, fn_insts_def, mk_raw_function_def,
       EVERY_MEM, MEM_fn_insts_blocks_iff] >>
  qpat_x_assum `EVERY (\b. EVERY P b.bb_instructions) fn_blocks` mp_tac >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem entry_code_extracted_context:
  extract_context_with_internals label internal_fns st = SOME (ctx,data) /\
  entry_code_pred P st ==>
  !f. MEM f ctx.ctx_functions ==> EVERY P (fn_insts f)
Proof
  simp[extract_context_with_internals_def, entry_code_pred_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule entry_code_package_blocks >>
  disch_then (qspec_then `P` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[mk_venom_context_def] >> rpt strip_tac >> gvs[]
  >- (simp[fn_insts_def, mk_raw_function_def, EVERY_MEM,
           MEM_fn_insts_blocks_iff] >>
      qpat_x_assum `EVERY (\b. EVERY P b.bb_instructions) entry_blocks` mp_tac >>
      simp[EVERY_MEM] >> metis_tac[]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem entry_code_extracted_fmp_room:
  extract_context_with_internals label internal_fns st = SOME (ctx,data) /\
  entry_code_pred (\i. i.inst_opcode <> DALLOCA) st /\
  MEM func ctx.ctx_functions ==> fmp_room ctx func s
Proof
  strip_tac >> irule context_without_dalloca_fmp_room >>
  simp[] >> qpat_x_assum `MEM func ctx.ctx_functions` kall_tac >>
  gen_tac >> strip_tac >> drule_all entry_code_extracted_context >>
  simp[EVERY_MEM, EXISTS_MEM]
QED
