(* Effect-bearing field copying shares execution proof code with its ancestor. *)
Theory typedCopyBytesFieldsEffectsPtr
Ancestors typedCopyBytesFieldsPtr typedCopyOffsetEffectsPtr typedCopyRobustEffectsPtr

Theorem compile_bytestring_field_effects_frag_ptr:
  !cx ctx PG R cenv dst src doff soff sa sb sc sd dp sp G tn s a b
   dtotal stotal n len tenv sty dty stv dtv v.
    compile_with_byte_offset (Var dst) doff sa = (dp,sb) /\
    compile_with_byte_offset (Var src) soff sb = (sp,sc) /\
    compile_store_memory_typed cenv dp dty sp sty sc = ((),sd) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s dtotal /\ ptr_covers G tn src s stotal /\
    doff < dtotal /\ doff+n <= dtotal /\
    soff < stotal /\ soff+n <= stotal /\
    w2n b+doff < dimword(:256) /\ w2n a+soff < dimword(:256) /\
    n = 32+32*((len+31) DIV 32) /\
    len+31 < dimword(:256) /\ n < dimword(:256) /\
    is_bytestring_type sty /\ is_bytestring_type dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a+soff) m) ==>
    cs_extends sa sd /\
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sd
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      (!i. ~(w2n b+doff <= i /\ i < w2n b+doff+n) ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
      (!i. ~(w2n b+doff <= i /\ i < w2n b+doff+n) ==>
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b+doff) m) /\
      (!ft fv p. val_wf ft fv /\
        (p+type_memory_size ft <= w2n b+doff \/ w2n b+doff+n <= p) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          val_in_memory ft fv p m) ==>
        !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
          val_in_memory ft fv p m)
Proof
  typedCopyBytesFieldsLib.field
    (compile_with_byte_offset_effects_frag_ptr,
     compile_store_bytestring_robust_effects_frag_ptr, byte_offset_next_var)
QED

Resume compile_bytestring_field_effects_frag_ptr[destination_offset]:
  typedCopyBytesFieldsLib.destination_offset byte_offset_next_var
QED

Resume compile_bytestring_field_effects_frag_ptr[package]:
  typedCopyBytesFieldsLib.package compile_bytestring_field_shape
QED

Resume compile_bytestring_field_effects_frag_ptr[old_vars]:
  typedCopyBytesFieldsLib.old_vars byte_offset_next_var
QED

Finalise compile_bytestring_field_effects_frag_ptr

Theorem compile_bytestring_fields_effects_frag_ptr:
  !dts sts dtvs stvs vals lens tenv cx ctx PG R cenv dst src sa sz
   a b G tn s dtotal stotal doff soff.
    LENGTH sts = LENGTH dts /\ LENGTH dtvs = LENGTH dts /\
    LENGTH stvs = LENGTH dts /\ LENGTH vals = LENGTH dts /\
    LENGTH lens = LENGTH dts /\
    compile_typed_copy_fields cenv (Var dst) (Var src) dts sts doff soff sa = ((),sz) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s dtotal /\ ptr_covers G tn src s stotal /\
    (w2n b+dtotal <= w2n a \/ w2n a+stotal <= w2n b) /\
    doff + SUM (MAP (type_memory_bytes cenv) dts) <= dtotal /\
    soff + SUM (MAP (type_memory_bytes cenv) sts) <= stotal /\
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
      type_memory_size (EL i dtvs) <= type_memory_bytes cenv (EL i dts) /\
      type_memory_size (EL i stvs) <= type_memory_bytes cenv (EL i sts) /\
      doff + SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) < dtotal /\
      doff + SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) +
        (32+32*((EL i lens+31) DIV 32)) <= dtotal /\
      soff + SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) < stotal /\
      soff + SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) +
        (32+32*((EL i lens+31) DIV 32)) <= stotal /\
      w2n b + (doff + SUM (MAP (type_memory_bytes cenv) (TAKE i dts))) < dimword(:256) /\
      w2n a + (soff + SUM (MAP (type_memory_bytes cenv) (TAKE i sts))) < dimword(:256) /\
      EL i lens+31 < dimword(:256) /\ 32+32*((EL i lens+31) DIV 32) < dimword(:256) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory (EL i stvs) (EL i vals)
          (w2n a + (soff + SUM (MAP (type_memory_bytes cenv) (TAKE i sts)))) m)) ==>
    cs_extends sa sz /\
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sz
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p)) /\
      (!i. ~(w2n b+doff <= i /\
             i < w2n b+(doff + SUM (MAP (type_memory_bytes cenv) dts))) ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
      (!i. ~(w2n b+doff <= i /\
             i < w2n b+(doff + SUM (MAP (type_memory_bytes cenv) dts))) ==>
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!i. i < LENGTH dts ==> !m.
        mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory (EL i dtvs) (EL i vals)
          (w2n b+(doff + SUM (MAP (type_memory_bytes cenv) (TAKE i dts)))) m) /\
      (!ft fv p. val_wf ft fv /\
        (p+type_memory_size ft <= w2n b+doff \/
         w2n b+(doff+SUM (MAP (type_memory_bytes cenv) dts)) <= p) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ft fv p m) ==>
        !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> val_in_memory ft fv p m)
Proof
  Induct_on `dts`
  >- (rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
      qpat_x_assum `_ \/ _` kall_tac >>
      gvs[Once contextTheory.compile_store_memory_typed_def, compileEnvTheory.comp_return_def] >>
      conj_tac >- simp[compileEnvTheory.cs_extends_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >> simp[] >>
      simp[bodyPtrDefsTheory.frag_exec_ptr_def] >> rpt strip_tac >> disj1_tac >>
      rpt strip_tac >> qexists_tac `fuel` >> simp[]) >>
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  namedCases_on `sts` ["", "st sts"] >> gnvs[] >>
  namedCases_on `dtvs` ["", "dtv dtvs"] >> gnvs[] >>
  namedCases_on `stvs` ["", "stv stvs"] >> gnvs[] >>
  namedCases_on `vals` ["", "v vals"] >> gnvs[] >>
  namedCases_on `lens` ["", "len lens"] >> gnvs[] >>
  rename1 `compile_typed_copy_fields cenv (Var dst) (Var src)
    (dt::dts) (st::sts) doff soff sa = ((),sz)` >>
  qpat_x_assum `!i. i < SUC (LENGTH dts) ==> _` mp_tac >>
  simp[Once arithmeticTheory.FORALL_NUM, listTheory.TAKE_def] >>
  disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> Cases_on `_0` >> suspend "head"
QED

Resume compile_bytestring_fields_effects_frag_ptr[head]:
  typedCopyBytesFieldsLib.fields_head compile_bytestring_field_effects_frag_ptr
QED

Resume compile_bytestring_fields_effects_frag_ptr[field_endpoint]:
  typedCopyBytesFieldsLib.fields_endpoint
    (compile_bytestring_field_shape, byte_offset_next_var)
QED

Resume compile_bytestring_fields_effects_frag_ptr[tail]:
  typedCopyBytesFieldsLib.fields_tail
QED

Resume compile_bytestring_fields_effects_frag_ptr[fields_package]:
  typedCopyBytesFieldsLib.fields_package true
QED

Resume compile_bytestring_fields_effects_frag_ptr[fields_memory]:
  typedCopyBytesFieldsLib.fields_memory
QED

Resume compile_bytestring_fields_effects_frag_ptr[fields_elements]:
  typedCopyBytesFieldsLib.fields_elements
QED

Finalise compile_bytestring_fields_effects_frag_ptr
