(* Goal-directed scalar representation tactics for the Log consumers.
   No theorem values are manufactured or cached here. *)
structure logWidenTacticsLib =
struct
open HolKernel boolLib bossLib
open supportedTypesTheory vyperValueTheory compileEnvTheory
     valueCopyBytesTheory valueTypingMemoryPropsTheory
     exprSimDefsTheory exprSimPropsTheory loweringPostsTheory
     stmtSimLogArgsTheory

fun scalar_evaluate ty =
  qpat_x_assum ([QUOTE "type_memory_bytes _ ("] @ ty @ [QUOTE ") < dimword (:256)"]) mp_tac >>
  qpat_x_assum ([QUOTE "supported_scalar_type ("] @ ty @ [QUOTE ")"]) mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  Cases_on ty >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[supported_word_type_def, supported_string_type_def,
      evaluate_type_def, type_memory_bytes_def, type_slot_size_def,
      vfmConstantsTheory.word_size_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >>
       gvs[supported_word_type_def, supported_string_type_def,
           evaluate_type_def, type_memory_bytes_def, type_slot_size_def,
           vfmConstantsTheory.word_size_def]) >>
  gvs[supported_int_width_def] >>
  rename1 `cap < dimword (:256)` >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >>
  (impl_tac >- decide_tac) >>
  disch_then (qspec_then `cap+31` strip_assume_tac) >> decide_tac

fun scalar_transport cases =
  rename1 `event_arg_compatible dst src` >>
  `src = dst \/ (is_bytestring_type src /\ is_bytestring_type dst)` by
    (drule (CONJUNCT1 cases) >> strip_tac >>
     gvs[supported_scalar_type_def, supported_word_type_def,
         supported_string_type_def, is_bytestring_type_def]) >>
  Cases_on `src = dst` >- gvs[] >>
  gvs[] >>
  rename1 `evaluate_type (get_tenv cx) src = SOME stv` >>
  rename1 `evaluate_type (get_tenv cx) dst = SOME dtv` >>
  rename1 `value_has_type stv v` >>
  `val_footprint stv v = val_footprint dtv v` by
    metis_tac[bytestring_val_footprint_eq] >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[value_has_type_memory_wf] >>
  `~is_word_type src /\ ~is_word_type dst` by
    metis_tac[is_bytestring_word_type] >>
  `?sbt. stv = BaseTV sbt` by metis_tac[bytestring_type_value] >>
  `?dbt. dtv = BaseTV dbt` by metis_tac[bytestring_type_value] >>
  gvs[log_arg_rel_def] >>
  conj_tac >-
    (fs[expr_val_rel_def] >>
     metis_tac[bytestring_val_in_memory_transfer]) >>
  conj_tac >-
    (fs[expr_val_at_def] >> rpt strip_tac >> gvs[] >>
     metis_tac[local_val_at_base, arithmeticTheory.LESS_EQ_REFL]) >>
  fs[log_arg_clear_def] >> rpt strip_tac >>
  metis_tac[local_val_at_base, arithmeticTheory.LESS_EQ_REFL]

end
