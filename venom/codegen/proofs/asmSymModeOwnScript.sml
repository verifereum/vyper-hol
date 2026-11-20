(* Relocated mode correspondence assembled from subject interfaces. *)
Theory asmSymModeOwn
Ancestors asmSymModeInterfaceOwn asmSymRelocLabelsOwn asmSymExceptionalOwn
  asmSymBridge fnPlanPlaceRevertPostamble codegenSymRel

val result_rel = mk_var ("R", type_of ``asm_sym_rel p env``);
val result_body = subst [``asm_sym_rel p env`` |-> result_rel]
  (lhs (concl asm_sym_step_rel_core_canonical));
val result_vars = result_rel :: List.map (fn name =>
  List.find (fn v => fst (dest_var v) = name) (free_vars result_body)
  |> valOf) ["sr", "cr"];
val _ = Parse.temp_overload_on
  ("bridge_result", list_mk_abs (result_vars, result_body));

Theorem asm_sym_inst_step_mode:
  asm_static_wf p /\ code_labels_agree p lo /\
  asm_sym_rel_own lo p env own cs ss /\ MEM ai p ==>
  bridge_result (asm_sym_rel_own lo p env own)
    (if allow_own then sym_step_own p env own ai ss
     else sym_step p env ai ss)
    (asm_step lo (build_offset_to_pc p) ai cs)
Proof
  strip_tac >> irule asm_sym_inst_step_mode_from_interfaces >>
  simp[] >>
  `asm_data_env_lo_ok lo p env own` by fs[asm_sym_rel_own_def] >>
  metis_tac[asm_push_label_lookup_reloc, sym_jump_dest_conc_reloc,
            asm_sym_exceptional_op_own]
QED

Theorem asm_sym_step_mode_replay:
  asm_static_wf p /\ code_labels_agree p lo /\
  asm_sym_rel_own lo p env own cs ss /\
  asm_block_at p cs.as_pc [ai] /\
  asm_step lo (build_offset_to_pc p) ai cs = AsmOK cs' /\
  (!msg. (if allow_own then sym_step_own p env own ai ss
          else sym_step p env ai ss) <> SymBad msg) ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
    asm_sym_rel_own lo p env own cs' ss'
Proof
  strip_tac >> irule asm_sym_step_mode_replay_from_interfaces >>
  simp[] >>
  `asm_data_env_lo_ok lo p env own` by fs[asm_sym_rel_own_def] >>
  metis_tac[asm_push_label_lookup_reloc, sym_jump_dest_conc_reloc,
            asm_sym_exceptional_op_own]
QED

Theorem asm_sym_steps_mode_sim:
  asm_static_wf p /\ code_labels_agree p lo /\
  asm_sym_rel_own lo p env own cs ss /\
  sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
  ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
    asm_sym_rel_own lo p env own cs' ss'
Proof
  strip_tac >>
  `asm_data_env_lo_ok lo p env own` by fs[asm_sym_rel_own_def] >>
  irule asm_sym_steps_mode_from_interfaces >> simp[] >>
  metis_tac[asm_push_label_lookup_reloc, sym_jump_dest_conc_reloc,
            asm_sym_exceptional_op_own]
QED
