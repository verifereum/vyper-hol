(* Diagnostic witness for the abstract body invariant's metadata clauses. *)
Theory typedCopyMetadataWitness
Ancestors
  context typedCopyDomain compileEnv valueEncoding vyperValue vyperAST finite_map list pair

Definition widening_cycle_tenv_def:
  widening_cycle_tenv = FEMPTY |+
    (((SOME 0),"Unused"), StructArgs [("self",StructT (SOME 0,"Unused"))])
End

Definition widening_cycle_env_def:
  widening_cycle_env = (ARB:compile_env) with ce_struct_fields :=
    FEMPTY |+ ("0.Unused",[("self",StructT (SOME 0,"Unused"),32)])
End

Theorem widening_cycle_metadata_consistent:
  sfields_tenv_consistent widening_cycle_env.ce_struct_fields widening_cycle_tenv
Proof
  simp[widening_cycle_env_def, widening_cycle_tenv_def,
       sfields_tenv_consistent_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[nsid_to_string_def] >> EVAL_TAC
QED

Theorem widening_cycle_metadata_sizes:
  !name fields.
    FLOOKUP widening_cycle_env.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv.
      evaluate_type widening_cycle_tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields
Proof
  simp[widening_cycle_env_def, widening_cycle_tenv_def,
       FLOOKUP_UPDATE, evaluate_type_def, DOMSUB_FUPDATE_THM]
QED

Theorem widening_cycle_metadata_not_acyclic:
  ~acyclic_struct_metadata widening_cycle_env.ce_struct_fields
Proof
  simp[widening_cycle_env_def, acyclic_struct_metadata_def,
       FEVERY_DEF, type_rank_def, get_struct_fields_def,
       nsid_to_string_def, FLOOKUP_UPDATE, DOMSUB_FUPDATE_THM] >> EVAL_TAC
QED

Theorem widening_array_copy_rejects_unused_metadata:
  compile_store_memory_typed widening_cycle_env (Lit 256w)
    (ArrayT (BaseT (BytesT (Dynamic 64))) (Fixed 1)) (Lit 128w)
    (ArrayT (BaseT (BytesT (Dynamic 32))) (Fixed 1)) =
  emit_void INVALID []
Proof
  simp[Once compile_store_memory_typed_def,
       is_word_type_def, is_bytestring_type_def,
       widening_cycle_metadata_not_acyclic]
QED
