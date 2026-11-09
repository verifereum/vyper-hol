Theory typedCopyTuplePtr
Ancestors
  typedCopyBytesFieldsPtr tupleMemoryLayout typedCopyAgreement arithmetic list

Theorem tuple_in_memory_from_elements:
  !tvs vals base mem.
    LENGTH vals = LENGTH tvs /\
    (!i. i < LENGTH tvs ==>
      val_in_memory (EL i tvs) (EL i vals)
        (base + SUM (MAP type_memory_size (TAKE i tvs))) mem) ==>
    tuple_in_memory vals tvs base mem
Proof
  Induct >> Cases_on `vals` >> simp[valueEncodingTheory.val_in_memory_def] >>
  rpt gen_tac >> strip_tac >>
  simp[Once valueEncodingTheory.val_in_memory_def] >>
  conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum irule >> simp[] >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  simp_tac (srw_ss()) [EL, TL, TAKE_def, MAP, SUM] >>
  `base' + (type_memory_size h' + SUM (MAP type_memory_size (TAKE i tvs))) =
   base' + (SUM (MAP type_memory_size (TAKE i tvs)) + type_memory_size h')`
    by decide_tac >>
  asm_rewrite_tac[]
QED

Theorem sum_map_take_pointwise:
  !xs ys f g.
    LENGTH xs = LENGTH ys /\
    (!i. i < LENGTH xs ==> f (EL i xs) = g (EL i ys)) ==>
    !n. SUM (MAP f (TAKE n xs)) = SUM (MAP g (TAKE n ys))
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `n` >> simp[] >>
  `f h' = g h` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[] >> first_x_assum irule >> simp[] >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem compile_store_memory_typed_tuple_bytes_frag_ptr:
  !dts sts dtvs stvs vals lens tenv cx ctx PG R cenv dst src sa sz
   a b G tn s dtotal stotal.
    LENGTH sts = LENGTH dts /\ LENGTH dtvs = LENGTH dts /\
    LENGTH stvs = LENGTH dts /\ LENGTH vals = LENGTH dts /\
    LENGTH lens = LENGTH dts /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    compile_store_memory_typed cenv (Var dst) (TupleT dts)
      (Var src) (TupleT sts) sa = ((),sz) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s dtotal /\ ptr_covers G tn src s stotal /\
    (w2n b+dtotal <= w2n a \/ w2n a+stotal <= w2n b) /\
    SUM (MAP (type_memory_bytes cenv) dts) <= dtotal /\
    SUM (MAP (type_memory_bytes cenv) sts) <= stotal /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (TupleTV stvs) (ArrayV (TupleV vals)) (w2n a) m) /\
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
      SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) < dtotal /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) +
        (32+32*((EL i lens+31) DIV 32)) <= dtotal /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) < stotal /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) +
        (32+32*((EL i lens+31) DIV 32)) <= stotal /\
      w2n b + SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) < dimword(:256) /\
      w2n a + SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) < dimword(:256) /\
      EL i lens+31 < dimword(:256) /\ 32+32*((EL i lens+31) DIV 32) < dimword(:256)) ==>
    cs_extends sa sz /\
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sz
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p)) /\
      (!i. ~(w2n b <= i /\
             i < w2n b+SUM (MAP (type_memory_bytes cenv) dts)) ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
      (!i. ~(w2n b <= i /\
             i < w2n b+SUM (MAP (type_memory_bytes cenv) dts)) ==>
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory (TupleTV dtvs) (ArrayV (TupleV vals)) (w2n b) m) /\
      (!ft fv p. val_wf ft fv /\
        (p+type_memory_size ft <= w2n b \/
         w2n b+SUM (MAP (type_memory_bytes cenv) dts) <= p) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ft fv p m) ==>
        !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> val_in_memory ft fv p m)
Proof
  typedCopyTupleLib.prepare sum_map_take_pointwise
QED

Resume compile_store_memory_typed_tuple_bytes_frag_ptr[premises]:
  typedCopyTupleLib.premises
QED

Resume compile_store_memory_typed_tuple_bytes_frag_ptr[copy]:
  typedCopyTupleLib.copy
    (compile_bytestring_fields_frag_ptr, tuple_in_memory_from_elements)
QED

Finalise compile_store_memory_typed_tuple_bytes_frag_ptr
