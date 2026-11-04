Theory dftPositionalEdit
Ancestors
  dftOriginalScheduleRuntime dftEditLabels dftRunRel o1PassContract venomInst
  list rich_list

Definition dft_pos_replace_def:
  dft_pos_replace k v xs =
    if k < LENGTH xs then TAKE k xs ++ [v] ++ DROP (SUC k) xs else xs
End

Theorem dft_pos_replace_lupdate:
  !xs k v. dft_pos_replace k v xs = LUPDATE v k xs
Proof
  Induct >> Cases_on `k` >> simp[dft_pos_replace_def, LUPDATE_def] >>
  rpt strip_tac >> Cases_on `n < LENGTH xs` >> gvs[dft_pos_replace_def] >>
  metis_tac[]
QED

Theorem dft_pos_replace_length[simp]:
  LENGTH (dft_pos_replace k v xs) = LENGTH xs
Proof simp[dft_pos_replace_lupdate]
QED

Theorem dft_pos_replace_el:
  EL j (dft_pos_replace k v xs) =
    if j = k /\ k < LENGTH xs then v else EL j xs
Proof simp[dft_pos_replace_lupdate, EL_LUPDATE]
QED

Theorem dft_pos_replace_list_rel:
  LIST_REL R xs ys /\ k < LENGTH ys /\ R (EL k xs) v ==>
  LIST_REL R xs (dft_pos_replace k v ys)
Proof
  simp[LIST_REL_EL_EQN, dft_pos_replace_el] >> rpt strip_tac >>
  Cases_on `n = k` >> simp[]
QED

Definition dft_pos_edit_fn_def:
  dft_pos_edit_fn bi pre x y post g =
    g with fn_blocks := dft_pos_replace bi
      ((EL bi g.fn_blocks) with bb_instructions := pre ++ [y;x] ++ post)
      g.fn_blocks
End

Definition dft_pos_edit_ctx_def:
  dft_pos_edit_ctx fi bi pre x y post C =
    C with ctx_functions := dft_pos_replace fi
      (dft_pos_edit_fn bi pre x y post (EL fi C.ctx_functions))
      C.ctx_functions
End

Theorem dft_pos_edit_fn_selected:
  bi < LENGTH g.fn_blocks ==>
  EL bi (dft_pos_edit_fn bi pre x y post g).fn_blocks =
    (EL bi g.fn_blocks) with bb_instructions := pre ++ [y;x] ++ post
Proof simp[dft_pos_edit_fn_def, dft_pos_replace_el]
QED

Theorem dft_pos_edit_fn_other:
  j <> bi ==>
  EL j (dft_pos_edit_fn bi pre x y post g).fn_blocks = EL j g.fn_blocks
Proof simp[dft_pos_edit_fn_def, dft_pos_replace_el]
QED

Theorem dft_pos_edit_ctx_selected:
  fi < LENGTH C.ctx_functions ==>
  EL fi (dft_pos_edit_ctx fi bi pre x y post C).ctx_functions =
    dft_pos_edit_fn bi pre x y post (EL fi C.ctx_functions)
Proof simp[dft_pos_edit_ctx_def, dft_pos_replace_el]
QED

Theorem dft_pos_edit_ctx_other:
  j <> fi ==>
  EL j (dft_pos_edit_ctx fi bi pre x y post C).ctx_functions =
    EL j C.ctx_functions
Proof simp[dft_pos_edit_ctx_def, dft_pos_replace_el]
QED

Theorem dft_pos_edit_duplicate_isolation:
  j <> bi /\ EL j g.fn_blocks = EL bi g.fn_blocks ==>
  EL j (dft_pos_edit_fn bi pre x y post g).fn_blocks = EL bi g.fn_blocks
Proof metis_tac[dft_pos_edit_fn_other]
QED

Theorem dft_pos_edit_original_function:
  dft_original_function f g /\ bi < LENGTH g.fn_blocks /\
  (EL bi g.fn_blocks).bb_instructions = pre ++ [x;y] ++ post /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  schedule_edges (EL bi f.fn_blocks).bb_instructions dft_must_order
    (pre ++ [y;x] ++ post) ==>
  dft_original_function f (dft_pos_edit_fn bi pre x y post g)
Proof
  strip_tac >> fs[dft_original_function_def] >>
  simp[dft_original_function_def, dft_pos_edit_fn_def] >> conj_tac
  >- (qpat_x_assum `g = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  irule dft_pos_replace_list_rel >> simp[] >>
  irule dft_original_block_swap >> simp[] >>
  fs[LIST_REL_EL_EQN]
QED

Theorem dft_pos_edit_original_context:
  dft_original_context Corig C /\ fi < LENGTH C.ctx_functions /\
  bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
  (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;y] ++ post /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  schedule_edges (EL bi (EL fi Corig.ctx_functions).fn_blocks).bb_instructions
    dft_must_order (pre ++ [y;x] ++ post) ==>
  dft_original_context Corig (dft_pos_edit_ctx fi bi pre x y post C)
Proof
  strip_tac >> fs[dft_original_context_def] >>
  simp[dft_original_context_def, dft_pos_edit_ctx_def] >> conj_tac
  >- (qpat_x_assum `C = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  irule dft_pos_replace_list_rel >> simp[] >>
  irule dft_pos_edit_original_function >> simp[] >>
  fs[LIST_REL_EL_EQN]
QED

Theorem dft_pos_replace_exists:
  k < LENGTH xs /\ (P v <=> P (EL k xs)) ==>
  ((?w. MEM w (dft_pos_replace k v xs) /\ P w) <=>
   (?w. MEM w xs /\ P w))
Proof
  simp[dft_pos_replace_lupdate, MEM_EL] >>
  rpt strip_tac >> eq_tac >> rpt strip_tac >> gvs[] >>
  Cases_on `n = k` >> gvs[EL_LUPDATE] >> metis_tac[EL_LUPDATE]
QED

Theorem dft_pos_edit_fn_insts_mem:
  bi < LENGTH g.fn_blocks /\
  (EL bi g.fn_blocks).bb_instructions = pre ++ [x;y] ++ post ==>
  (MEM i (fn_insts (dft_pos_edit_fn bi pre x y post g)) <=>
   MEM i (fn_insts g))
Proof
  strip_tac >> simp[fn_insts_def, fn_insts_blocks_MEM, dft_pos_edit_fn_def] >>
  ho_match_mp_tac dft_pos_replace_exists >> simp[] >> metis_tac[]
QED

Theorem dft_pos_edit_ctx_labels_bound:
  fi < LENGTH C.ctx_functions /\
  bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
  (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;y] ++ post /\
  ctx_labels_bound C L ==>
  ctx_labels_bound (dft_pos_edit_ctx fi bi pre x y post C) L
Proof
  simp[ctx_labels_bound_def, dft_pos_edit_ctx_def] >> rpt strip_tac >>
  fs[dft_pos_replace_lupdate] >>
  drule MEM_LUPDATE_E >> strip_tac >> gvs[] >>
  metis_tac[dft_pos_edit_fn_insts_mem, MEM_EL]
QED

Theorem dft_pos_replace_outside:
  LENGTH xs <= k ==> dft_pos_replace k v xs = xs
Proof
  simp[dft_pos_replace_def]
QED

Theorem dft_pos_edit_fn_metadata:
  dft_pos_edit_fn bi pre x y post g =
    g with fn_blocks := (dft_pos_edit_fn bi pre x y post g).fn_blocks
Proof
  simp[dft_pos_edit_fn_def]
QED

Theorem dft_pos_edit_ctx_metadata:
  dft_pos_edit_ctx fi bi pre x y post C =
    C with ctx_functions := (dft_pos_edit_ctx fi bi pre x y post C).ctx_functions
Proof
  simp[dft_pos_edit_ctx_def]
QED

Theorem dft_pos_edit_fn_block_labels:
  !bs bi pre x y post.
  MAP (\b. b.bb_label)
    (dft_pos_replace bi ((EL bi bs) with bb_instructions := pre ++ [y;x] ++ post) bs) =
  MAP (\b. b.bb_label) bs
Proof
  Induct >> Cases_on `bi` >>
  simp[dft_pos_replace_lupdate, LUPDATE_def] >>
  fs[dft_pos_replace_lupdate]
QED
