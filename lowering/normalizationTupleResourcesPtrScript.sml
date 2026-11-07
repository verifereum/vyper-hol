(* Pure semantic resources for immediate bytestring tuple normalization. *)
Theory normalizationTupleResourcesPtr
Ancestors normalizationTupleBytesPtr tupleMemoryLayout vyperTypeValues
  abiTupleValueEncoding

Theorem bytestring_payload_resources:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v ==>
  ?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
         (?str. v = StringV str /\ len = LENGTH str)) /\
    val_wf tv v /\ 32+32*((len+31) DIV 32) <= type_memory_size tv
Proof
  strip_tac >>
  `val_wf tv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  drule_all valueCopyBytesTheory.bytestring_type_value >>
  strip_tac >> Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def] >>
  simp[valueTypingMemoryPropsTheory.value_has_type_memory_wf,
    valueEncodingTheory.type_memory_size_def, vfmConstantsTheory.word_size_def] >>
  irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]
QED

Theorem tuple_layout_resources:
  evaluate_type tenv (TupleT tys) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vals)) /\
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv) ==>
  LENGTH tys = LENGTH tvs /\ LENGTH vals = LENGTH tys /\
  val_wf (TupleTV tvs) (ArrayV (TupleV vals)) /\
  SUM (MAP (type_memory_bytes cenv) tys) = type_memory_size_list tvs /\
  (!i. i < LENGTH tys ==>
    evaluate_type tenv (EL i tys) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vals) /\
    val_wf (EL i tvs) (EL i vals) /\
    type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs))
Proof
  strip_tac >> drule vyperTypeValuesTheory.evaluate_type_TupleT_cases >>
  strip_tac >> gvs[] >>
  `val_wf (TupleTV tvs) (ArrayV (TupleV vals))` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  gvs[vyperTypingTheory.value_has_type_def,
    abiTupleValueEncodingTheory.abi_values_have_types,
    listTheory.LIST_REL_EL_EQN] >>
  conj_tac >- (
    first_x_assum (qspec_then `TupleT tys` mp_tac) >>
    simp[compileEnvTheory.type_memory_bytes_def,
      valueEncodingTheory.type_memory_size_def] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  rpt strip_tac >> metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]
QED

Theorem mapped_prefix_element_bound:
  !xs i. i < LENGTH xs ==>
  SUM (MAP (f:'a -> num) (TAKE i xs)) + f (EL i xs) <= SUM (MAP f xs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `i` >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem tuple_bytestring_resources:
  !tenv sts stvs dts dtvs vals cenv N S.
  evaluate_type tenv (TupleT sts) = SOME (TupleTV stvs) /\
  evaluate_type tenv (TupleT dts) = SOME (TupleTV dtvs) /\
  value_has_type (TupleTV stvs) (ArrayV (TupleV vals)) /\
  value_has_type (TupleTV dtvs) (ArrayV (TupleV vals)) /\
  EVERY is_bytestring_type sts /\ EVERY is_bytestring_type dts /\
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv) /\
  N = type_memory_bytes cenv (TupleT dts) /\
  S = val_footprint (TupleTV stvs) (ArrayV (TupleV vals)) /\
  N < dimword(:256) ==>
  ?lens.
    LENGTH sts = LENGTH dts /\ LENGTH stvs = LENGTH dts /\
    LENGTH dtvs = LENGTH dts /\ LENGTH vals = LENGTH dts /\ LENGTH lens = LENGTH dts /\
    val_wf (TupleTV stvs) (ArrayV (TupleV vals)) /\
    val_wf (TupleTV dtvs) (ArrayV (TupleV vals)) /\
    SUM (MAP (type_memory_bytes cenv) dts) = N /\
    SUM (MAP (type_memory_bytes cenv) sts) = S /\
    (!i. i < LENGTH dts ==>
      is_bytestring_type (EL i sts) /\ is_bytestring_type (EL i dts) /\
      evaluate_type tenv (EL i sts) = SOME (EL i stvs) /\
      evaluate_type tenv (EL i dts) = SOME (EL i dtvs) /\
      value_has_type (EL i stvs) (EL i vals) /\ value_has_type (EL i dtvs) (EL i vals) /\
      val_wf (EL i stvs) (EL i vals) /\ val_wf (EL i dtvs) (EL i vals) /\
      ((?bs. EL i vals = BytesV bs /\ EL i lens = LENGTH bs) \/
       (?str. EL i vals = StringV str /\ EL i lens = LENGTH str)) /\
      32+32*((EL i lens+31) DIV 32) <= type_memory_bytes cenv (EL i dts) /\
      32+32*((EL i lens+31) DIV 32) <= type_memory_bytes cenv (EL i sts) /\
      type_memory_bytes cenv (EL i dts) = type_memory_size (EL i dtvs) /\
      type_memory_bytes cenv (EL i sts) = type_memory_size (EL i stvs) /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) < N /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) + 32+32*((EL i lens+31) DIV 32) <= N /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) < S /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) + 32+32*((EL i lens+31) DIV 32) <= S /\
      EL i lens+31 < dimword(:256) /\ 32+32*((EL i lens+31) DIV 32) < dimword(:256))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuple_layout_resources >> strip_tac >>
  qpat_x_assum `evaluate_type _ (TupleT dts) = _` kall_tac >>
  drule_all tuple_layout_resources >> strip_tac >>
  qexists `MAP (\v. case v of BytesV bs => LENGTH bs | StringV str => LENGTH str | _ => 0) vals` >>
  gvs[exprSimTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def,
    compileEnvTheory.type_memory_bytes_def, listTheory.EVERY_EL] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> gvs[] >>
  qx_gen_tac `i` >> strip_tac >>
  `is_bytestring_type (EL i sts) /\ is_bytestring_type (EL i dts)` by simp[] >>
  qpat_assum `!i. _ ==> evaluate_type tenv (EL i sts) = _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!i. _ ==> evaluate_type tenv (EL i dts) = _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all bytestring_payload_resources >> strip_tac >>
  qpat_x_assum `evaluate_type tenv (EL i dts) = _` kall_tac >>
  drule_all bytestring_payload_resources >> strip_tac >>
  gvs[listTheory.EL_MAP] >>
  `SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) +
    type_memory_bytes cenv (EL i dts) <= SUM (MAP (type_memory_bytes cenv) dts)` by
    (irule mapped_prefix_element_bound >> simp[]) >>
  `SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) +
    type_memory_bytes cenv (EL i sts) <= SUM (MAP (type_memory_bytes cenv) sts)` by
    (irule mapped_prefix_element_bound >> simp[]) >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >> gvs[] >>
  qmatch_goalsub_abbrev_tac `k+31` >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `k+31` strip_assume_tac) >>
  `(k+31) MOD 32 < 32` by simp[] >> decide_tac
QED
