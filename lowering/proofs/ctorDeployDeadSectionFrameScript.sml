(* imm_section_dead is fixed by the immutables section's live bytes. *)
Theory ctorDeployDeadSectionFrame
Ancestors
  ctorDeployDeadSection ctorDeployDefs immutableSectionRel immutableValue
  immutableEncoding valueEncoding compileVyper structFieldsProps entryStateRel
  list rich_list

Theorem imm_section_dead_frame:
  !tops sec1 sec2.
    struct_args_unique tops /\
    LENGTH sec2 = LENGTH sec1 /\
    (!j. j < LENGTH sec1 /\ ~imm_section_dead tops sec1 j ==>
         EL j sec2 = EL j sec1) ==>
    imm_section_dead tops sec2 = imm_section_dead tops sec1
Proof
  cheat
QED
