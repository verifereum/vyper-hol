(* Staging writes use the shared store dispatcher, including its direct
   word and bytestring branches. *)
Theory bodyIntCallFamCallIntStageAdapters
Ancestors
  bodyIntCallFamCallIntTransport bodyIntCallFamCallIntStageStore
  exprLowering context compileEnv
Libs
  monadsyntax

Theorem intcall_stage_write:
  (if is_word_type ty then emit_void MSTORE [dst; src]
   else if (case ty of BaseT (BytesT (Dynamic _)) => T
                      | BaseT (StringT _) => T | _ => F) then
     do compile_store_bytestring src dst; return () od
   else compile_store_memory ce src dst ty sty) =
  compile_store_memory ce src dst ty sty
Proof
  `((case ty of BaseT (BytesT (Dynamic _)) => T
             | BaseT (StringT _) => T | _ => F) = is_bytestring_type ty)` by
    (Cases_on `ty` >> simp[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >> simp[is_bytestring_type_def]) >>
  simp[compile_store_memory_def] >>
  Cases_on `is_word_type ty` >> simp[] >>
  Cases_on `is_bytestring_type ty` >> simp[] >>
  simp[FUN_EQ_THM, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  gen_tac >> pairarg_tac >> simp[] >> Cases_on `v` >> simp[]
QED

