(* Tuple reconstruction is shared across old and allocator-effect interfaces. *)
structure typedCopyTupleLib =
struct
open HolKernel boolLib bossLib
open typedCopyBytesFieldsPtrTheory tupleMemoryLayoutTheory typedCopyAgreementTheory
     arithmeticTheory listTheory

fun prepare sum_prefix =
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `compile_typed_copy_fields cenv (Var dst) (Var src) dts sts 0 0 sa = ((),sz)` by
    (drule compile_store_memory_typed_valid >>
     disch_then (qspecl_then [`TupleT sts`, `Var src`, `TupleT dts`, `Var dst`] mp_tac) >>
     simp[compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def] >>
     metis_tac[]) >>
  `(!i. SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) =
         SUM (MAP type_memory_size (TAKE i dtvs))) /\
   (!i. SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) =
         SUM (MAP type_memory_size (TAKE i stvs)))` by
    (conj_tac >> irule sum_prefix >> asm_rewrite_tac[] >> metis_tac[]) >>
  `!i. i < LENGTH dts ==> !m.
     mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory (EL i stvs) (EL i vals)
       (w2n a + SUM (MAP (type_memory_bytes cenv) (TAKE i sts))) m` by
    (rpt strip_tac >> asm_rewrite_tac[] >> irule tuple_in_memory_element >>
     asm_rewrite_tac[] >> metis_tac[valueEncodingPropsTheory.val_in_memory_tuple]) >>
  suspend "premises";

val premises =
  markerLib.RESUME_TAC >>
  `!i. i < LENGTH dts ==>
      is_bytestring_type (EL i sts) /\ is_bytestring_type (EL i dts) /\
      evaluate_type tenv (EL i sts) = SOME (EL i stvs) /\
      evaluate_type tenv (EL i dts) = SOME (EL i dtvs) /\
      value_has_type (EL i stvs) (EL i vals) /\ value_has_type (EL i dtvs) (EL i vals) /\
      val_wf (EL i stvs) (EL i vals) /\ val_wf (EL i dtvs) (EL i vals) /\
      ((?bs. EL i vals = BytesV bs /\ EL i lens = LENGTH bs) \/
       (?str. EL i vals = StringV str /\ EL i lens = LENGTH str)) /\
      32+32*((EL i lens+31) DIV 32) <= type_memory_bytes cenv (EL i dts) /\
      32+32*((EL i lens+31) DIV 32) <= type_memory_bytes cenv (EL i sts) /\
      type_memory_size (EL i dtvs) <= type_memory_bytes cenv (EL i dts) /\
      type_memory_size (EL i stvs) <= type_memory_bytes cenv (EL i sts) /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) < dtotal /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) +
        (32+32*((EL i lens+31) DIV 32)) <= dtotal /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) < stotal /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) +
        (32+32*((EL i lens+31) DIV 32)) <= stotal /\
      w2n b + SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) < dimword(:256) /\
      w2n a + SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) < dimword(:256) /\
      EL i lens+31 < dimword(:256) /\ 32+32*((EL i lens+31) DIV 32) < dimword(:256) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory (EL i stvs) (EL i vals)
          (w2n a + SUM (MAP (type_memory_bytes cenv) (TAKE i sts))) m)` by
    (qx_gen_tac `i` >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH dts ==> is_bytestring_type _ /\ _`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac,
       rpt strip_tac >> first_x_assum irule >> asm_rewrite_tac[]]) >>
  suspend "copy";

fun copy (fields, tuple_from_elements) =
  markerLib.RESUME_TAC >>
  qpat_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac fields) >>
  disch_then (qspecl_then [`dtvs`, `stvs`, `vals`, `lens`, `tenv`] mp_tac) >>
  pure_rewrite_tac[ADD_CLAUSES] >> disch_then drule_all >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  qpat_x_assum `!i. i < LENGTH dts ==> is_bytestring_type _ /\ _` kall_tac >>
  qpat_x_assum `!i. i < LENGTH dts ==> is_bytestring_type _ /\ _` kall_tac >>
  conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  rewrite_tac[valueEncodingPropsTheory.val_in_memory_tuple] >>
  irule tuple_from_elements >> asm_rewrite_tac[] >> qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH dts ==> !m. _ ==> val_in_memory (EL i dtvs) _ _ _`
    (qspec_then `i` mp_tac) >>
  asm_rewrite_tac[] >> disch_then irule >> asm_rewrite_tac[];
end
