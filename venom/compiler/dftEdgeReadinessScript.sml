Theory dftEdgeReadiness
Ancestors
  dftPositionalRuntime dftPositionalEdit dftNormalizedEndpoint
  dftScheduleOrder venomEffects venomInst list rich_list

Theorem dft_invoke_pair_ordered:
  x.inst_opcode = INVOKE /\ y.inst_opcode = INVOKE ==> dft_must_order x y
Proof
  strip_tac >> simp[dft_must_order_def, write_effects_def, read_effects_def,
    empty_effects_def] >> EVAL_TAC
QED

Theorem dft_pos_edit_fn_inverse:
  bi < LENGTH f.fn_blocks /\
  (EL bi f.fn_blocks).bb_instructions = pre ++ [x;y] ++ post ==>
  dft_pos_edit_fn bi pre y x post (dft_pos_edit_fn bi pre x y post f) = f
Proof
  strip_tac >>
  `((EL bi f.fn_blocks) with bb_instructions := pre ++ [x;y] ++ post) =
    EL bi f.fn_blocks` by
    (qpat_x_assum `_.bb_instructions = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  simp[dft_pos_edit_fn_def, dft_pos_replace_el, dft_pos_replace_lupdate,
    EL_LUPDATE] >>
  `LUPDATE (EL bi f.fn_blocks) bi
    (LUPDATE ((EL bi f.fn_blocks) with bb_instructions := pre ++ [y;x] ++ post)
      bi f.fn_blocks) = f.fn_blocks` by
    (irule LIST_EQ >> simp[EL_LUPDATE] >> rpt strip_tac >>
     IF_CASES_TAC >> gvs[]) >> simp[]
QED

Theorem dft_pos_edit_ctx_inverse:
  fi < LENGTH C.ctx_functions /\
  bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
  (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;y] ++ post ==>
  dft_pos_edit_ctx fi bi pre y x post (dft_pos_edit_ctx fi bi pre x y post C) = C
Proof
  strip_tac >>
  `dft_pos_edit_fn bi pre y x post
    (dft_pos_edit_fn bi pre x y post (EL fi C.ctx_functions)) =
    EL fi C.ctx_functions` by metis_tac[dft_pos_edit_fn_inverse] >>
  simp[dft_pos_edit_ctx_def, dft_pos_replace_el, dft_pos_replace_lupdate,
    EL_LUPDATE] >>
  `LUPDATE (EL fi C.ctx_functions) fi
    (LUPDATE (dft_pos_edit_fn bi pre x y post (EL fi C.ctx_functions))
      fi C.ctx_functions) = C.ctx_functions` by
    (irule LIST_EQ >> simp[EL_LUPDATE] >> rpt strip_tac >>
     IF_CASES_TAC >> gvs[]) >> simp[]
QED

Theorem dft_pos_runtime_ready_reverse:
  dft_pos_runtime_ready C fi bi pre x y post ==>
  dft_pos_runtime_ready (dft_pos_edit_ctx fi bi pre x y post C)
    fi bi pre y x post
Proof
  simp[dft_pos_runtime_ready_def, dft_pos_edit_ctx_def,
    dft_pos_edit_fn_def, dft_pos_replace_el]
QED

Theorem dft_pos_runtime_ready_inverse:
  dft_pos_runtime_ready C fi bi pre x y post ==>
  dft_pos_edit_ctx fi bi pre y x post (dft_pos_edit_ctx fi bi pre x y post C) = C
Proof
  simp[dft_pos_runtime_ready_def] >> metis_tac[dft_pos_edit_ctx_inverse]
QED

Theorem dft_normalized_edge_readiness:
  dft_original_context C M /\
  LIST_REL dft_fallible_order_kept C.ctx_functions M.ctx_functions /\
  dft_original_context C A /\ dft_original_context C B /\
  dft_pos_context_edge (dft_pos_provenance_guard C M) A B ==>
  ?fi bi pre x y post.
    B = dft_pos_edit_ctx fi bi pre x y post A /\
    dft_pos_runtime_ready A fi bi pre x y post /\
    dft_pos_runtime_ready B fi bi pre y x post /\
    A = dft_pos_edit_ctx fi bi pre y x post B /\
    ~dft_must_order x y /\
    ~(x.inst_opcode = INVOKE /\ y.inst_opcode = INVOKE) /\
    abort_compatible x.inst_opcode y.inst_opcode
Proof
  strip_tac >> drule_all dft_normalized_provenance_edge >> strip_tac >>
  `dft_pos_runtime_ready A fi bi pre x y post` by
    (simp[dft_pos_runtime_ready_def] >> conj_tac >> strip_tac >> gvs[is_pseudo_def]) >>
  metis_tac[dft_pos_runtime_ready_reverse, dft_pos_runtime_ready_inverse,
    dft_invoke_pair_ordered]
QED
