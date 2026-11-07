Theory bodyPtrPopContextPackaging
Ancestors vyperCompiler bodyPtrPopCompilerBoundary bodyPtrPopBoundaryContract
  compileEnv venomInst list

Theorem pop_split_blocks_at_every:
  !blocks label prefix suffix.
    EVERY P blocks /\ split_blocks_at label blocks = SOME (prefix,suffix) ==>
    EVERY P prefix /\ EVERY P suffix
Proof
  Induct >> simp[split_blocks_at_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h.bb_label = label` >> gvs[] >>
  gvs[AllCaseEqs()] >> first_x_assum drule_all >> simp[]
QED

Theorem pop_package_internal_blocks_every:
  !ds blocks entry fs.
    EVERY P blocks /\ package_internal_blocks ds blocks = SOME (entry,fs) ==>
    EVERY P entry /\ EVERY (\f. EVERY P f.fn_blocks) fs
Proof
  Induct >> simp[package_internal_blocks_def] >> rpt gen_tac >>
  PairCases_on `h` >> simp[package_internal_blocks_def] >> strip_tac >>
  gvs[AllCaseEqs()] >> drule_all pop_split_blocks_at_every >> strip_tac >>
  first_x_assum drule_all >> simp[mk_internal_function_metadata]
QED

Theorem pop_extract_context_every:
  EVERY P (REVERSE st.cs_blocks ++
    [<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|>]) /\
  extract_context_with_internals label packages st = SOME (ctx,data) ==>
  EVERY (\f. EVERY P f.fn_blocks) ctx.ctx_functions
Proof
  simp[extract_context_with_internals_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_at (Pat `package_internal_blocks _ _ = _`) pop_package_internal_blocks_every >>
  simp[] >> simp[mk_venom_context_def, mk_raw_function_def]
QED

Theorem pop_extract_context_boundary:
  pop_comp_boundary st /\
  extract_context_with_internals label packages st = SOME (ctx,data) ==>
  EVERY (\f. EVERY (\bb. ~occurs5 pop_guarded5 bb.bb_instructions) f.fn_blocks)
    ctx.ctx_functions
Proof
  rpt strip_tac >> drule_at (Pat `extract_context_with_internals _ _ _ = _`)
    pop_extract_context_every >> disch_then irule >>
  gvs[pop_comp_boundary_def, pop_boundary_clean_windows]
QED
