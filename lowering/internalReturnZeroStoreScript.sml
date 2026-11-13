(* A direct compatible store with zero source footprint emits no instructions. *)
Theory internalReturnZeroStore
Ancestors
  bodyDeclCopyMemory valueCopyBytes contextProps exprSimProps
  context compileEnv valueEncoding

Theorem compile_compatible_zero_store:
  evaluate_type tenv ty = SOME tv /\ evaluate_type tenv sty = SOME stv /\
  ~is_word_type ty /\ value_has_type tv v /\ value_has_type stv v /\
  (ty = sty \/ is_bytestring_type ty /\ is_bytestring_type sty) /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  val_store_size stv v = 0 ==>
  compile_store_memory cenv src dst ty sty sa = ((),sa)
Proof
  strip_tac >>
  `val_store_size tv v = 0` by
    (Cases_on `ty = sty` >> gvs[] >>
     metis_tac[bytestring_val_store_size_eq]) >>
  `type_memory_size tv = 0` by
    (qspec_then `tv` (qspec_then `v` mp_tac) val_store_size_pos >> simp[] >> decide_tac) >>
  `~is_bytestring_type ty` by
    (strip_tac >> qspecl_then [`cenv`, `ty`] mp_tac bytestring_memory_bytes_positive >> simp[]) >>
  `ty = sty` by metis_tac[] >>
  simp[compile_store_memory_def, compile_copy_memory_zero]
QED
