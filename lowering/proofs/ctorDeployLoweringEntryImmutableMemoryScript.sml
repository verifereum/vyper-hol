Theory ctorDeployLoweringEntryImmutableMemory
Ancestors
  loweringStateRelDefs valueEncodingDefs
  ctorDeployLoweringNoCtor ctorDeployLoweringEntrySourceFrame
  immutableSectionRel immutableRelation loweringSlice valueEncodingProps
  valueEncodingProofs compileEnv ctorDeployLoweringDefs ctorDeployDefs
  valueEncoding immutableEncoding list rich_list

Theorem deploy_ctor_start_zero_section:
  !tops am tx mut nr body am_c es0.
  deploy_typing_ok tops am tx /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) ==>
  immutables_section_rel tops
    (case ALOOKUP am_c.immutables tx.target of SOME m => m | NONE => [])
    (REPLICATE (imm_len tops) 0w)
Proof
  rpt gen_tac >> strip_tac >> fs[deploy_ctor_start_def] >>
  irule no_ctor_initialized_zero_section >>
  goal_assum $ drule_at Any >> simp[] >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem deploy_ctor_section_memory_relation:
  immutable_section_layout cenv tops /\
  immutables_section_rel tops imms section /\
  ALOOKUP es.immutables addr = SOME imms /\
  mem_bytes_at 0 (LENGTH section) ss.vs_memory = section ==>
  immutables_rel cenv addr NONE T es ss
Proof
  strip_tac >> simp[immutables_rel_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `immutable_section_layout _ _`
    (mp_tac o REWRITE_RULE [immutable_section_layout_def]) >>
  disch_then drule >> strip_tac >>
  drule_all immutables_section_rel_lookup >> strip_tac >>
  `mem_bytes_at byte_offset (type_memory_size tv) section =
   mem_bytes_at byte_offset (type_memory_size tv) ss.vs_memory` by
    (irule (cj 1 mem_bytes_at_agree_window) >>
     qexistsl [`LENGTH section`, `0`] >> gvs[mem_bytes_at_def, TAKE_APPEND]) >>
  gvs[] >>
  irule val_in_memory_mem_agree >>
  conj_tac >- metis_tac[immutable_admissible_val_wf] >>
  qexistsl [`type_memory_size tv`, `section`] >>
  simp[immutable_admissible_val_wf]
QED

Theorem deploy_ctor_prefix_bytes_agree:
  (!p. p < cap ==> mem_bytes_at p 1 mem = mem_bytes_at p 1 mem') ==>
  mem_bytes_at 0 cap mem = mem_bytes_at 0 cap mem'
Proof
  strip_tac >> irule LIST_EQ >> simp[LENGTH_mem_bytes_at_proof] >>
  rpt strip_tac >> first_x_assum drule >>
  disch_then (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
  simp[EL_mem_bytes_at]
QED

Theorem deploy_ctor_empty_zero_section:
  mem_bytes_at 0 cap ([]:word8 list) = REPLICATE cap 0w
Proof
  simp[mem_bytes_at_def]
QED

Theorem deploy_ctor_zero_prefix_section:
  (!p. p < cap ==> mem_bytes_at p 1 ss.vs_memory = mem_bytes_at p 1 []) ==>
  mem_bytes_at 0 cap ss.vs_memory = REPLICATE cap 0w
Proof
  strip_tac >>
  `mem_bytes_at 0 cap ss.vs_memory = mem_bytes_at 0 cap []` by
    (irule deploy_ctor_prefix_bytes_agree >> simp[]) >>
  simp[deploy_ctor_empty_zero_section]
QED

Theorem deploy_ctor_zero_memory_immutables:
  !tops am tx mut nr body am_c es0 cenv addr ss es.
  deploy_typing_ok tops am tx /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
  immutable_section_layout cenv tops /\ addr = tx.target /\
  es.immutables = am_c.immutables /\
  (!p. p < imm_len tops ==>
    mem_bytes_at p 1 ss.vs_memory = mem_bytes_at p 1 []) ==>
  immutables_rel cenv addr NONE T es ss
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_start_zero_section >> strip_tac >>
  drule deploy_ctor_zero_prefix_section >> strip_tac >>
  Cases_on `ALOOKUP es.immutables addr`
  >- simp[immutables_rel_def] >>
  irule deploy_ctor_section_memory_relation >>
  qexistsl [`x`, `REPLICATE (imm_len tops) 0w`, `tops`] >> gvs[]
QED
