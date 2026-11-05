(* Opcode-independent rules for labels bound by compiler computations. *)
Theory boundLabelRules
Ancestors
  loweringShapeDefs compileEnv emitHelper list rich_list

Theorem bound_labels_new_block:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) /\ P l ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (new_block l s))))
Proof
  simp[new_block_def, all_blocks_def, EVERY_APPEND]
QED

Theorem bound_labels_primitives:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (comp_return x s)))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (comp_get s)))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (emit inst s)))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (fresh_var s)))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (fresh_id s)))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (fresh_label suffix s))))
Proof
  simp[comp_return_def, comp_get_def, emit_def, fresh_var_def,
       fresh_id_def, fresh_label_def, all_blocks_def]
QED

Theorem bound_labels_fresh_label:
  fresh_label suffix s = (l,t) ==>
  compiler_label l /\
  (EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
   EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)))
Proof
  simp[fresh_label_def] >> strip_tac >> gvs[] >>
  simp[compiler_label_def, emitHelperPropsTheory.fresh_label_output_in_future,
       all_blocks_def]
QED

Theorem bound_labels_bind_result:
  (!s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
       Q (FST (f s)) (SND (f s))) /\
  (!x s. Q x s ==>
       EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (g x s))))) ==>
  !s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
      EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (comp_bind f g s))))
Proof
  rpt strip_tac >> simp[comp_bind_def] >> pairarg_tac >> gvs[] >>
  metis_tac[pairTheory.FST, pairTheory.SND]
QED

Theorem bound_labels_bind:
  (!s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
       EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f s))))) /\
  (!x s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
       EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (g x s))))) ==>
  !s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
      EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (comp_bind f g s))))
Proof
  rpt strip_tac >> simp[comp_bind_def] >> pairarg_tac >> gvs[] >>
  metis_tac[pairTheory.SND]
QED

Theorem bound_labels_ignore_bind:
  (!s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
       EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f s))))) /\
  (!s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
       EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (g s))))) ==>
  !s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
      EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (comp_ignore_bind f g s))))
Proof
  simp[comp_ignore_bind_def] >> rpt strip_tac >>
  irule bound_labels_bind >> simp[]
QED

Theorem bound_labels_fresh_block:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (comp_bind (fresh_label suffix) new_block s))))
Proof
  strip_tac >> irule bound_labels_bind_result >>
  reverse conj_tac >- simp[] >> qexists_tac `\l t. compiler_label l /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t))` >>
  simp[] >> conj_tac
  >- metis_tac[bound_labels_new_block] >>
  qx_gen_tac `t` >> strip_tac >> Cases_on `fresh_label suffix t` >>
  drule bound_labels_fresh_label >> simp[]
QED

Theorem bound_labels_set:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (comp_set t s))))
Proof
  simp[comp_set_def]
QED

Theorem bound_labels_data_section:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (emit_data_section l s))))
Proof
  simp[emit_data_section_def, all_blocks_def]
QED

Theorem bound_labels_data_item:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (emit_data_item item s))))
Proof
  Cases_on `s.cs_data_sections` >> simp[emit_data_item_def, all_blocks_def]
QED

Theorem bound_labels_emit_op:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (emit_op opc ops s))))
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
       fresh_var_def, emit_def, comp_return_def, all_blocks_def]
QED

Theorem bound_labels_emit_inst:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (emit_inst opc ops outs s))))
Proof
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, all_blocks_def]
QED

Theorem bound_labels_emit_void:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (emit_void opc ops s))))
Proof
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def, all_blocks_def]
QED

Theorem bound_labels_fresh_vars:
  !n s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (fresh_vars n s))))
Proof
  Induct >> simp[fresh_vars_def, comp_return_def] >> rpt strip_tac >>
  simp[comp_bind_def, fresh_var_def] >> pairarg_tac >> simp[comp_return_def] >>
  first_x_assum (qspec_then `s with cs_next_var := s.cs_next_var + 1` mp_tac) >>
  gvs[all_blocks_def]
QED

Theorem bound_labels_emit_multi_op:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (emit_multi_op opc ops n s))))
Proof
  strip_tac >> simp[emit_multi_op_def, comp_bind_def] >> pairarg_tac >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >> pairarg_tac >>
  `EVERY P (MAP (\bb. bb.bb_label) (all_blocks cs'))` by
    metis_tac[bound_labels_fresh_vars, pairTheory.SND] >>
  gvs[] >> metis_tac[bound_labels_emit_inst, pairTheory.SND]
QED

Theorem bound_labels_jmp_if_not_terminated:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (emit_jmp_if_not_terminated target s))))
Proof
  simp[emit_jmp_if_not_terminated_def, comp_bind_def, comp_get_def] >>
  Cases_on `block_is_terminated s` >>
  simp[comp_return_def, bound_labels_emit_inst]
QED

Theorem pair_let_snd_preserves:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND p))) /\
  (!x t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (g (x,t)))))) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (g p))))
Proof
  Cases_on `p` >> simp[]
QED
