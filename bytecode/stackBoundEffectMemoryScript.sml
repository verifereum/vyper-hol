(* Memory effects preserve the checked frame's control and operand stack. *)
Theory stackBoundEffectMemory
Ancestors
  stackBoundEffectCore vfmExecution vfmState vfmContext list pair arithmetic

Theorem sb_eff_memory_neutral[simp]:
  sb_eff_neutral (memory_expansion_info off sz) /\
  sb_eff_neutral (expand_memory amount) /\
  sb_eff_neutral (read_memory off sz) /\
  sb_eff_neutral (write_memory off bytes)
Proof
  rw[sb_eff_neutral_def, memory_expansion_info_def, expand_memory_def,
     read_memory_def, write_memory_def, bind_def,
     get_current_context_def, set_current_context_def, return_def] >>
  gvs[AllCaseEqs(), sb_eff_frame_def] >>
  Cases_on `s.contexts` >> gvs[]
QED

Theorem sb_eff_copy_to_memory_neutral:
  (case source of NONE => T | SOME f => sb_eff_neutral f) ==>
  sb_eff_neutral (copy_to_memory gas off sourceOff sz source)
Proof
  Cases_on `source`
  >- (simp[copy_to_memory_def] >> pairarg_tac >>
      simp[sb_eff_neutral_bind, sb_eff_neutral_ignore_bind]) >>
  strip_tac >> gvs[] >> simp[copy_to_memory_def] >>
  irule sb_eff_neutral_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >>
  irule sb_eff_neutral_ignore_bind >> conj_tac >- simp[] >>
  irule sb_eff_neutral_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >>
  simp[sb_eff_neutral_bind, sb_eff_neutral_ignore_bind]
QED
