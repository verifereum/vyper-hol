(* Bound-label preservation for context, ABI and builtin helpers. *)
Theory helperBoundLabels
Ancestors
  boundLabelRules context compileEnv

Theorem bound_labels_imm_load_word:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_imm_load_word is_ctor imm off s))))
Proof
  Cases_on `is_ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, bound_labels_emit_op] >>
  strip_tac >> irule bound_labels_bind >> simp[bound_labels_emit_op]
QED

Theorem bound_labels_imm_store_word:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_imm_store_word imm off v s))))
Proof
  Cases_on `imm` >> simp[compile_imm_store_word_def, bound_labels_emit_void] >>
  strip_tac >> irule bound_labels_bind >>
  simp[bound_labels_emit_op, bound_labels_emit_void]
QED

Theorem bound_labels_ptr_load:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_ptr_load is_ctor imm loc op s))))
Proof
  Cases_on `loc` >>
  simp[compile_ptr_load_def, bound_labels_emit_op, bound_labels_imm_load_word]
QED

Theorem bound_labels_ptr_store:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_ptr_store is_ctor imm loc dst v s))))
Proof
  Cases_on `loc` >> Cases_on `is_ctor` >>
  simp[compile_ptr_store_def, bound_labels_emit_void, bound_labels_imm_store_word]
QED

Theorem bound_labels_copy_memory:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_copy_memory dst src n s))))
Proof
  Cases_on `n` >>
  simp[compile_copy_memory_def, comp_return_def, bound_labels_emit_void]
QED

Theorem bound_labels_fresh_label_bind[local]:
  (!l t. compiler_label l /\
     EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
     EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (g l t))))) ==>
  !s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (comp_bind (fresh_label suffix) g s))))
Proof
  rpt strip_tac >> irule bound_labels_bind_result >>
  reverse conj_tac >- simp[] >>
  qexists_tac `\l t. compiler_label l /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t))` >>
  simp[] >> qx_gen_tac `t` >> strip_tac >>
  Cases_on `fresh_label suffix t` >>
  drule bound_labels_fresh_label >> simp[]
QED

Theorem bound_labels_word_copy_loop:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_word_copy_loop src dst n ld st ctor s))))
Proof
  strip_tac >> simp[compile_word_copy_loop_def] >>
  irule bound_labels_fresh_label_bind >> simp[] >> rpt strip_tac >>
  irule bound_labels_fresh_label_bind >> simp[] >> rpt strip_tac >>
  irule bound_labels_fresh_label_bind >> simp[] >> rpt strip_tac >>
  rpt (FIRST [
    CHANGED_TAC (simp[bound_labels_emit_inst, bound_labels_emit_op,
      bound_labels_ptr_load, bound_labels_ptr_store, bound_labels_new_block,
      cj 4 bound_labels_primitives]),
    gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED
