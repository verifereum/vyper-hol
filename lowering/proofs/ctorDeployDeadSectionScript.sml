(* The immutables section's dead bytes (imm_section_dead) are fixed by its
 * live bytes, and immutables_section_rel ignores them.
 *)
Theory ctorDeployDeadSection
Ancestors
  ctorDeployDefs immutableSectionRel immutableValue valueEncoding
  structFieldsProps entryStateRel list rich_list

(* mem_dead_bytes reads only the length words its value's live bytes hold. *)
Theorem mem_dead_bytes_frame:
  !sec1 sec2 off tv.
    LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size tv /\ j < LENGTH sec1 /\
         ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
    mem_dead_bytes sec2 off tv = mem_dead_bytes sec1 off tv
Proof
  cheat
QED

Theorem mem_dead_bytes_range:
  !sec off tv i.
    mem_dead_bytes sec off tv i ==> off <= i /\ i < off + type_memory_size tv
Proof
  cheat
QED

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
