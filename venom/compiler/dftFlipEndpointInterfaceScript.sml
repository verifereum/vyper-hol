Theory dftFlipEndpointInterface
Ancestors
  dftFlipContextRuntime dftFlipOccurrenceProbe dftPositionalRuntime
  dftOriginalScheduleRuntime dftDefs dftStructural venomExecSemantics
  venomInst dftOccurrenceMachine dftRelationalEdit list option

Theorem dft_flip_indexed_functions:
  LIST_REL dft_flip_function C.ctx_functions D.ctx_functions /\
  dft_pos_functions C D f g ==> dft_flip_function f g
Proof
  simp[dft_pos_functions_def, LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem dft_flip_indexed_blocks:
  LIST_REL dft_flip_function C.ctx_functions D.ctx_functions /\
  dft_pos_blocks C D f g b b' ==> dft_flip_block b b'
Proof
  simp[dft_pos_blocks_def, LIST_REL_EL_EQN, dft_flip_function_def] >>
  metis_tac[]
QED

Theorem dft_flip_indexed_function_lookup:
  LIST_REL dft_flip_function C.ctx_functions D.ctx_functions ==>
  OPTREL (dft_pos_functions C D)
    (lookup_function nm C.ctx_functions) (lookup_function nm D.ctx_functions)
Proof
  strip_tac >> simp[lookup_function_def] >> irule dft_rel_find >> conj_tac
  >- metis_tac[dft_flip_indexed_functions, dft_flip_function_name] >>
  irule dft_pos_functions_list >> metis_tac[LIST_REL_LENGTH]
QED

Theorem dft_flip_indexed_blocks_list:
  LIST_REL dft_flip_function C.ctx_functions D.ctx_functions /\
  dft_pos_functions C D f g ==>
  LIST_REL (dft_pos_blocks C D f g) f.fn_blocks g.fn_blocks
Proof
  strip_tac >>
  `dft_flip_function f g` by metis_tac[dft_flip_indexed_functions] >>
  `LENGTH g.fn_blocks = LENGTH f.fn_blocks` by
    metis_tac[dft_flip_function_def, LIST_REL_LENGTH] >>
  simp[LIST_REL_EL_EQN, dft_pos_blocks_def] >>
  fs[dft_pos_functions_def] >> metis_tac[]
QED

Theorem dft_flip_indexed_block_lookup:
  LIST_REL dft_flip_function C.ctx_functions D.ctx_functions /\
  dft_pos_functions C D f g ==>
  OPTREL (dft_pos_blocks C D f g)
    (lookup_block lbl f.fn_blocks) (lookup_block lbl g.fn_blocks)
Proof
  strip_tac >> simp[lookup_block_def] >> irule dft_rel_find >> conj_tac
  >- metis_tac[dft_flip_indexed_blocks, dft_flip_block_def] >>
  irule dft_flip_indexed_blocks_list >> simp[]
QED

Theorem dft_flip_indexed_interface:
  LIST_REL dft_flip_function C.ctx_functions D.ctx_functions ==>
  dft_rel_interface C D (dft_pos_functions C D) (dft_pos_blocks C D)
Proof
  strip_tac >> simp[dft_rel_interface_def] >> rpt conj_tac
  >- metis_tac[dft_flip_indexed_function_lookup]
  >- metis_tac[dft_flip_indexed_functions, dft_flip_setup,
       dft_flip_indexed_block_lookup] >>
  metis_tac[dft_flip_indexed_blocks, dft_flip_block_def, dft_flip_phis]
QED

Theorem dft_flip_indexed_instructions:
  LIST_REL dft_flip_function C.ctx_functions D.ctx_functions /\
  dft_pos_functions C D f g /\ dft_pos_blocks C D f g b b' ==>
  LIST_REL flip_rel b.bb_instructions b'.bb_instructions
Proof
  metis_tac[dft_flip_indexed_blocks, dft_flip_block_def]
QED

Theorem dft_flip_indexed_entry_root:
  j < LENGTH C.ctx_functions ==>
  dft_flip_occ_rel (dft_pos_functions C D) (dft_pos_blocks C D)
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] n))
Proof
  simp[dft_flip_occ_rel_def, dft_occ_init_def, dft_rel_core_def,
    dft_pos_functions_def] >> metis_tac[]
QED

Theorem dft_fn_block_update:
  dft_fn f = f with fn_blocks := (dft_fn f).fn_blocks
Proof
  simp[dft_fn_def] >> pairarg_tac >> simp[]
QED

Theorem dft_original_dft_metadata[local]:
  dft_original_function f m /\ g = dft_fn f ==>
  g = m with fn_blocks := g.fn_blocks
Proof
  strip_tac >>
  `m = f with fn_blocks := m.fn_blocks` by fs[dft_original_function_def] >>
  qpat_x_assum `m = _` SUBST_ALL_TAC >> simp[] >>
  once_rewrite_tac[dft_fn_block_update] >> simp[]
QED

Theorem dft_normalized_flip_functions:
  dft_original_context C M /\
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions D.ctx_functions /\
  LIST_REL (\m g. LIST_REL (\b c. b.bb_label = c.bb_label /\
    LIST_REL flip_rel b.bb_instructions c.bb_instructions) m.fn_blocks g.fn_blocks)
    M.ctx_functions D.ctx_functions ==>
  LIST_REL dft_flip_function M.ctx_functions D.ctx_functions
Proof
  simp[dft_original_context_def, LIST_REL_EL_EQN] >> strip_tac >>
  simp[dft_flip_function_def, LIST_REL_EL_EQN, dft_flip_block_def] >>
  rpt strip_tac
  >- metis_tac[dft_original_dft_metadata] >>
  metis_tac[]
QED

Theorem dft_flip_entry_label:
  dft_flip_function f g ==> fn_entry_label f = fn_entry_label g
Proof
  simp[dft_flip_function_def] >> strip_tac >>
  Cases_on `f.fn_blocks` >> Cases_on `g.fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def, dft_flip_block_def]
QED

Theorem dft_flip_indexed_missing_function:
  LIST_REL dft_flip_function C.ctx_functions D.ctx_functions ==>
  (lookup_function nm C.ctx_functions = NONE <=>
   lookup_function nm D.ctx_functions = NONE)
Proof
  strip_tac >> drule dft_flip_indexed_function_lookup >>
  disch_then (qspec_then `nm` mp_tac) >>
  Cases_on `lookup_function nm C.ctx_functions` >>
  Cases_on `lookup_function nm D.ctx_functions` >> simp[]
QED

Theorem dft_flip_indexed_entry_label:
  LIST_REL dft_flip_function C.ctx_functions D.ctx_functions /\
  dft_pos_functions C D f g ==> fn_entry_label f = fn_entry_label g
Proof
  metis_tac[dft_flip_indexed_functions, dft_flip_entry_label]
QED

Theorem dft_flip_indexed_lookup_roots:
  LIST_REL dft_flip_function C.ctx_functions D.ctx_functions /\
  lookup_function nm C.ctx_functions = SOME f /\
  lookup_function nm D.ctx_functions = SOME g ==>
  dft_flip_occ_rel (dft_pos_functions C D) (dft_pos_blocks C D)
    (dft_occ_init (DftOpen (DftEnter f 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter g 0 s) [] n))
Proof
  strip_tac >>
  `dft_pos_functions C D f g` by
    (drule dft_flip_indexed_function_lookup >>
     disch_then (qspec_then `nm` mp_tac) >> simp[]) >>
  simp[dft_flip_occ_rel_def, dft_occ_init_def, dft_rel_core_def]
QED

Theorem dft_flip_indexed_missing_entry_label:
  LIST_REL dft_flip_function C.ctx_functions D.ctx_functions /\
  dft_pos_functions C D f g ==>
  (fn_entry_label f = NONE <=> fn_entry_label g = NONE)
Proof
  metis_tac[dft_flip_indexed_entry_label]
QED
