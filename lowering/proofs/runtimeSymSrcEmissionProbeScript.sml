(* Generic instruction predicates suffice: reuse state_insts rather than
   introduce a second compiler-state invariant.  These boundaries include
   finalized blocks and separately packaged internal functions. *)
Theory runtimeSymSrcEmissionProbe
Ancestors
  loweringShapeDefs vyperCompiler compileEnv list venomInst venomState

Theorem runtime_sym_emit:
  EVERY P (state_insts (SND (emit inst st))) <=>
  EVERY P (state_insts st) /\ P inst
Proof
  simp[state_insts_def, all_blocks_def, emit_def, MAP_APPEND,
       FLAT_APPEND, EVERY_APPEND]
QED

Theorem runtime_sym_new_block:
  state_insts (SND (new_block label st)) = state_insts st
Proof
  simp[state_insts_def, all_blocks_def, new_block_def, MAP_APPEND,
       FLAT_APPEND, APPEND_ASSOC]
QED

Theorem runtime_sym_split_blocks:
  !blocks label pre post.
    split_blocks_at label blocks = SOME (pre,post) ==>
    blocks = pre ++ post
Proof
  Induct >> simp[split_blocks_at_def] >> rpt gen_tac >>
  Cases_on `h.bb_label = label` >> simp[] >>
  Cases_on `split_blocks_at label blocks` >> simp[] >>
  PairCases_on `x` >> simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem runtime_sym_package_blocks:
  !descs blocks entry functions.
    package_internal_blocks descs blocks = SOME (entry,functions) /\
    EVERY P (FLAT (MAP (\bb. bb.bb_instructions) blocks)) ==>
    EVERY P (FLAT (MAP (\bb. bb.bb_instructions) entry)) /\
    EVERY (\fn. EVERY P (fn_insts fn)) functions
Proof
  Induct >> simp[package_internal_blocks_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[package_internal_blocks_def] >>
  Cases_on `split_blocks_at h0 blocks` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `package_internal_blocks descs x1` >> simp[] >>
  PairCases_on `x` >> simp[] >> rpt strip_tac >> gvs[] >>
  drule runtime_sym_split_blocks >> strip_tac >> gvs[] >>
  fs[MAP_APPEND, FLAT_APPEND, EVERY_APPEND] >>
  first_x_assum drule_all >>
  simp[mk_internal_function_def, mk_raw_function_def, fn_insts_def, EVERY_fn_insts_blocks, EVERY_FLAT, EVERY_MAP]
QED

Theorem runtime_sym_extract:
  extract_context_with_internals entry_label internal_fns st = SOME (ctx,data) /\
  EVERY P (state_insts st) ==>
  !fn. MEM fn ctx.ctx_functions ==> EVERY P (fn_insts fn)
Proof
  simp[extract_context_with_internals_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule runtime_sym_package_blocks >>
  disch_then (qspec_then `P` mp_tac) >>
  fs[state_insts_def, all_blocks_def, EVERY_FLAT, EVERY_MAP] >>
  strip_tac >>
  gvs[mk_venom_context_def, mk_raw_function_def, fn_insts_def,
      EVERY_fn_insts_blocks, EVERY_FLAT, EVERY_MAP, EVERY_MEM] >>
  metis_tac[unitShapeDefsTheory.MEM_fn_insts_blocks_iff]
QED
