(* immutables_section_rel ignores the immutables section's dead bytes. *)
Theory ctorDeployDeadSectionRel
Ancestors
  ctorDeployDeadSection ctorDeployDefs immutableSectionRel immutableValue
  immutableEncoding valueEncoding compileVyper structFieldsProps entryStateRel
  list rich_list

(* A section related to the immutables stays related when its dead bytes
   change, provided each immutable's recorded type is its declared one. *)
Theorem immutables_section_rel_dead:
  !tops imms sec1 sec2.
    immutables_section_rel tops imms sec1 /\
    (!pre vis name ty slot post tv v.
       tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
       FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) ==>
       evaluate_type (type_env tops) ty = SOME tv) /\
    LENGTH sec2 = LENGTH sec1 /\
    (!j. j < LENGTH sec1 /\ ~imm_section_dead tops sec1 j ==>
         EL j sec2 = EL j sec1) ==>
    immutables_section_rel tops imms sec2
Proof
  cheat
QED
