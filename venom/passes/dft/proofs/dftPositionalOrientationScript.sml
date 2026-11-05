Theory dftPositionalOrientation
Ancestors
  dftPositionalRuntime dftPositionalEdit venomInst list rich_list

Theorem dft_pos_runtime_ready_reverse:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post ==>
  dft_pos_runtime_ready D fi bi pre y x post
Proof
  rw[dft_pos_runtime_ready_def] >>
  simp[dft_pos_edit_ctx_def, dft_pos_edit_fn_def, dft_pos_replace_el]
QED

Theorem dft_pos_replace_restore[local]:
  k < LENGTH xs ==>
  dft_pos_replace k (EL k xs) (dft_pos_replace k v xs) = xs
Proof
  strip_tac >> irule LIST_EQ >> simp[dft_pos_replace_el] >>
  rpt strip_tac >> Cases_on `x = k` >> simp[]
QED

Theorem dft_pos_edit_fn_reverse:
  bi < LENGTH f.fn_blocks /\
  (EL bi f.fn_blocks).bb_instructions = pre ++ [x;y] ++ post ==>
  dft_pos_edit_fn bi pre y x post (dft_pos_edit_fn bi pre x y post f) = f
Proof
  strip_tac >>
  simp[dft_pos_edit_fn_def, dft_pos_replace_el] >>
  `((EL bi f.fn_blocks) with bb_instructions := pre ++ [x;y] ++ post) =
    EL bi f.fn_blocks` by simp[venomInstTheory.basic_block_component_equality] >>
  simp[dft_pos_replace_restore]
QED

Theorem dft_pos_edit_ctx_reverse:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post ==>
  C = dft_pos_edit_ctx fi bi pre y x post D
Proof
  strip_tac >> fs[dft_pos_runtime_ready_def] >> gvs[] >>
  simp[dft_pos_edit_ctx_def, dft_pos_replace_el] >>
  `dft_pos_edit_fn bi pre y x post
    (dft_pos_edit_fn bi pre x y post (EL fi C.ctx_functions)) = EL fi C.ctx_functions` by
    (irule dft_pos_edit_fn_reverse >> simp[]) >>
  simp[dft_pos_replace_restore]
QED

Theorem dft_pos_functions_reverse:
  D = dft_pos_edit_ctx fi bi pre x y post C ==>
  (dft_pos_functions C D f g <=> dft_pos_functions D C g f)
Proof
  simp[dft_pos_functions_def, dft_pos_edit_ctx_def] >> metis_tac[]
QED

Theorem dft_pos_blocks_reverse:
  D = dft_pos_edit_ctx fi bi pre x y post C ==>
  (dft_pos_blocks C D f g b b' <=> dft_pos_blocks D C g f b' b)
Proof
  strip_tac >>
  `dft_pos_functions C D f g ==> LENGTH g.fn_blocks = LENGTH f.fn_blocks` by
    (gvs[] >> metis_tac[dft_pos_edit_blocks_length]) >>
  `dft_pos_functions D C g f ==> LENGTH g.fn_blocks = LENGTH f.fn_blocks` by
    metis_tac[dft_pos_functions_reverse] >>
  simp[dft_pos_blocks_def] >> eq_tac >> rpt strip_tac >>
  `dft_pos_functions C D f g /\ dft_pos_functions D C g f` by
    (fs[dft_pos_functions_def, dft_pos_edit_ctx_def] >> metis_tac[]) >>
  qexistsl [`j`,`k`] >> gvs[dft_pos_edit_ctx_def]
QED
