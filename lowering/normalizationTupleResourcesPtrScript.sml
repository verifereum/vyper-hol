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

(* Consumer boundary: source resources come from the typed expression endpoint. *)
Theorem compile_alloc_tuple_bytes_endpoint_ptr:
  !ctx func cenv cx env e es sa sb s0 es' vals root s n buf sc sd
   stvs sts dts tn PG G R.
    expr_sim_inv cenv cx env es /\
    IS_SOME (type_stmt env (TupleT dts) (Return (SOME e))) /\
    expr_type e = TupleT sts /\ expr_type e <> TupleT dts /\
    EVERY is_bytestring_type sts /\ EVERY is_bytestring_type dts /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME (TupleTV stvs) /\
    value_has_type (TupleTV stvs) (ArrayV (TupleV vals)) /\
    ptr_val_ok cx (expr_type e) (ArrayV (TupleV vals)) (Var root) G tn s /\
    expr_post ctx func cenv cx e es sa sb s0 es' (ArrayV (TupleV vals)) (Var root) s /\
    fresh_vars_wrt sb s /\ fn_inst_ids_distinct func /\ not_fresh_at sb root /\
    compile_alloc_buffer n sb = (buf,sc) /\
    compile_store_memory_typed cenv buf.buf_operand (TupleT dts)
      (Var root) (TupleT sts) sc = ((),sd) /\ fn_has_code sb sd func /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv) /\
    n = type_memory_bytes cenv (TupleT dts) /\ n < dimword(:256) ==>
    ?dtvs out b Gf tnf sf.
      evaluate_type (get_tenv cx) (TupleT dts) = SOME (TupleTV dtvs) /\
      buf.buf_operand = Var out /\ b+n < dimword(:256) /\
      frag_exec_ptr cx ctx PG sb sd
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      lookup_var out sf = SOME (n2w b) /\ ptr_covers Gf tnf out sf n /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory (TupleTV dtvs) (ArrayV (TupleV vals)) b m) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!q. not_fresh_at sb q ==>
        lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q)) /\
      (!ft fv p. val_wf ft fv /\
        (p+type_memory_size ft <= b \/ b+n <= p) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ft fv p m) ==>
        !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> val_in_memory ft fv p m)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typedCopyPtrTheory.typed_return_normalization_layout >> strip_tac >>
  drule vyperTypeValuesTheory.evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  qpat_assum `evaluate_type _ (TupleT sts) = _`
    (mp_then Any mp_tac (SRULE [] tuple_bytestring_resources)) >>
  disch_then (qspecl_then [`dts`, `tvs`, `vals`, `cenv`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `~is_word_type (TupleT sts)` by simp[compileEnvTheory.is_word_type_def] >>
  `dts <> []` by (strip_tac >> gvs[]) >>
  `0 < val_footprint (TupleTV stvs) (ArrayV (TupleV vals))` by
    (`0 < LENGTH dts` by (Cases_on `dts` >> gvs[]) >>
     qpat_assum `!i. i < LENGTH dts ==> _` (drule_then strip_assume_tac) >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx es' s /\
   expr_val_at cenv cx (TupleT sts) sa sb es' (ArrayV (TupleV vals)) (Var root) s` by
    gvs[exprSimTheory.expr_post_def] >>
  `?a. lookup_var root s = SOME a` by
    (qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [exprSimTheory.expr_val_at_def]) >>
     disch_then (qspec_then `TupleTV stvs` mp_tac) >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `eval_operand (Var root) s = SOME a` by simp[venomStateTheory.eval_operand_def] >>
  `ptr_covers G tn root s (val_footprint (TupleTV stvs) (ArrayV (TupleV vals)))` by
    (`val_footprint (TupleTV stvs) (ArrayV (TupleV vals)) <> 0 /\
      val_footprint (TupleTV stvs) (ArrayV (TupleV vals)) <=
        val_footprint (TupleTV stvs) (ArrayV (TupleV vals))` by decide_tac >>
     drule_all representationCleanPtrTheory.ptr_val_ok_read_covers >> simp[]) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (TupleTV stvs) (ArrayV (TupleV vals)) (w2n a) m` by
    (fs[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def] >>
     metis_tac[]) >>
  `s.vs_alloca_next < dimword(:256)` by
    (irule exprLoweringPropsTheory.alloca_room_next_lt >>
     fs[exprLoweringPropsTheory.stmt_state_rel_def] >> metis_tac[]) >>
  `!i. i < LENGTH dts ==>
    w2n a + SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) < dimword(:256)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i < LENGTH dts ==> _` (drule_then strip_assume_tac) >>
     `w2n a <= w2n a + SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) /\
      w2n a + SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) <
        w2n a + val_footprint (TupleTV stvs) (ArrayV (TupleV vals))` by decide_tac >>
     drule_all allocationPtrTheory.expr_val_at_below_frontier >> decide_tac) >>
  irule normalizationTupleBytesPtrTheory.compile_alloc_tuple_bytes_robust_frag_ptr >>
  asm_rewrite_tac[] >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lookup_var _ _ = _`)) >>
  qexists `lens` >> simp[] >> gen_tac >> strip_tac >>
  qpat_assum `!i. i < LENGTH dts ==> is_bytestring_type _ /\ _`
    (drule_then strip_assume_tac) >> decide_tac
QED
