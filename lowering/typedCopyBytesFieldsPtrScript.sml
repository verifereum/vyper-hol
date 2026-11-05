(* Concrete bytestring fields with independent source and destination offsets. *)
Theory typedCopyBytesFieldsPtr
Ancestors
  typedCopyFieldsPtr typedCopyBytesRobustPtr typedCopyOffsetPtr
  typedCopyAgreement exprLoweringProps contextCodegenRelProps
  bodyPtrDefs fragExecPtr words finite_map list arithmetic
  contextCodegenRel compileEnv abiEncoderInput

Theorem byte_offset_next_var[local]:
  !root off sa op sb.
    compile_with_byte_offset (Var root) off sa = (op,sb) ==>
    sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> Cases_on `off = 0` >>
  simp[contextTheory.compile_with_byte_offset_def,
       emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem compile_bytestring_field_shape[local]:
  !src dst sa sb.
    compile_store_bytestring src dst sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`src`, `dst`, `sa`] mp_tac ci_mono_compile_store_bytestring >>
     simp[ci_mono_def]) >> simp[] >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp[contextTheory.compile_store_bytestring_def,
       contextTheory.compile_bytestring_copy_len_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[cs_extends_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem compile_bytestring_field_frag_ptr:
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
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  drule_all compile_with_byte_offset_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`]
    strip_assume_tac) >>
  rename1 `lookup_var p s1 = SOME (n2w (w2n b+doff))` >>
  rename1 `ptr_covers G1 tn1 p s1 n` >>
  `not_fresh_at sb src /\ lookup_var src s1 = SOME a /\
   ptr_covers G1 tn1 src s1 stotal` by
    (qpat_assum `!q. not_fresh_at sa q ==> _` (qspec_then `src` strip_assume_tac) >>
     conj_tac >-
       (`sa.cs_next_var <= sb.cs_next_var` by metis_tac[byte_offset_next_var] >>
        fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     simp[] >> gvs[ptr_covers_def]) >>
  qpat_x_assum `compile_with_byte_offset (Var src) soff sb = _` assume_tac >>
  drule_all compile_with_byte_offset_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  rename1 `lookup_var q s2 = SOME (n2w (w2n a+soff))` >>
  rename1 `ptr_covers G2 tn2 q s2 n` >>
  `not_fresh_at sc p /\ lookup_var p s2 = SOME (n2w (w2n b+doff)) /\
   ptr_covers G2 tn2 p s2 n` by suspend "destination_offset" >>
  `compile_store_bytestring (Var q) (Var p) sc = ((),sd)` by
    (gvs[typedCopyAgreementTheory.compile_store_memory_typed_bytes]) >>
  `!m. mem_agree_outside tn2.t_mem s2.vs_memory m ==>
     val_in_memory stv v (w2n (n2w (w2n a+soff):bytes32)) m` by
    (gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  drule_all compile_store_bytestring_robust_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  suspend "package"
QED

Resume compile_bytestring_field_frag_ptr[destination_offset]:
  markerLib.RESUME_TAC >> (
  qpat_assum `!q. not_fresh_at sb q ==> _` (qspec_then `p` strip_assume_tac) >>
  conj_tac >-
    (`sb.cs_next_var <= sc.cs_next_var` by metis_tac[byte_offset_next_var] >>
     gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  simp[] >> gvs[ptr_covers_def])
QED

Resume compile_bytestring_field_frag_ptr[package]:
  markerLib.RESUME_TAC >> (
  drule compile_bytestring_field_shape >> strip_tac >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  conj_tac >-
    (irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sa sb _ _ _` (irule_at Any) >>
     simp[] >> conj_tac >- metis_tac[cs_extends_trans] >>
     irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sb sc _ _ _` (irule_at Any) >> simp[]) >>
  qpat_x_assum `frag_exec_ptr _ _ _ sa sb _ _ _` kall_tac >>
  qpat_x_assum `frag_exec_ptr _ _ _ sb sc _ _ _` kall_tac >>
  qpat_x_assum `frag_exec_ptr _ _ _ sc sd _ _ _` kall_tac >>
  qpat_x_assum `sf.vs_memory = _` kall_tac >>
  qpat_x_assum `n = _` kall_tac >>
  qpat_x_assum `(?bs. _) \/ _` kall_tac >>
  gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
      AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  asm_rewrite_tac[] >> suspend "old_vars")
QED

Resume compile_bytestring_field_frag_ptr[old_vars]:
  markerLib.RESUME_TAC >> (
  `sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var` by
    metis_tac[byte_offset_next_var] >>
  qx_gen_tac `z` >> strip_tac >>
  `not_fresh_at sb z /\ not_fresh_at sc z` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qpat_x_assum `!q. not_fresh_at sa q ==> _` (qspec_then `z` mp_tac) >>
  qpat_x_assum `!q. not_fresh_at sb q ==> _` (qspec_then `z` mp_tac) >>
  qpat_x_assum `!q. not_fresh_at sc q ==> _` (qspec_then `z` mp_tac) >>
  simp[])
QED

Finalise compile_bytestring_field_frag_ptr

Theorem compile_bytestring_fields_frag_ptr:
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
      gvs[Once contextTheory.compile_store_memory_typed_def, comp_return_def] >>
      conj_tac >- simp[cs_extends_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >> simp[] >>
      simp[frag_exec_ptr_def] >> rpt strip_tac >> disj1_tac >>
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
  simp[Once contextTheory.compile_store_memory_typed_def, comp_bind_def,
       comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >>
  Cases_on `_0` >>
  qpat_assum `compile_with_byte_offset (Var dst) doff sa = _`
    (mp_then Any mp_tac
      (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] compile_bytestring_field_frag_ptr)) >>
  disch_then drule >> disch_then drule >>
  disch_then (mp_tac o SRULE []) >>
  qpat_assum `ptr_covers G tn dst s dtotal`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `ptr_covers G tn src s stotal`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `lookup_var dst s = SOME b`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `lookup_var src s = SOME a`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `evaluate_type tenv st = SOME stv`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `evaluate_type tenv dt = SOME dtv`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `value_has_type stv v`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] mp_tac) >>
  disch_then (qspec_then `len` mp_tac) >>
  (impl_tac >-
    (qpat_x_assum `!sts dtvs stvs vals lens tenv cx ctx PG R cenv dst src sa sz a b G tn s dtotal stotal doff soff. _` kall_tac >>
     qpat_x_assum `!i. i < LENGTH dts ==> _` kall_tac >>
     asm_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM] >> decide_tac)) >>
  strip_tac >>
  rename1 `frag_exec_ptr cx ctx PG sa sm _
    (\g t v. g = G1 /\ t = tn1 /\ v = s1) R` >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_x_assum `!sts dtvs stvs vals lens tenv cx ctx PG R cenv dst src sa sz a b G tn s dtotal stotal doff soff. _` kall_tac >>
     qpat_x_assum `!i. i < LENGTH dts ==> _` kall_tac >>
     `compile_store_bytestring src_ptr dst_ptr cs'' = ((),sm)` by
       metis_tac[typedCopyAgreementTheory.compile_store_memory_typed_bytes] >>
     drule compile_bytestring_field_shape >> strip_tac >>
     metis_tac[byte_offset_next_var, LESS_EQ_TRANS]) >>
  `not_fresh_at sm dst /\ not_fresh_at sm src /\
   lookup_var dst s1 = SOME b /\ lookup_var src s1 = SOME a /\
   ptr_covers G1 tn1 dst s1 dtotal /\ ptr_covers G1 tn1 src s1 stotal` by
    (qpat_x_assum `!sts dtvs stvs vals lens tenv cx ctx PG R cenv dst src sa sz a b G tn s dtotal stotal doff soff. _` kall_tac >>
     qpat_x_assum `!i. i < LENGTH dts ==> _` kall_tac >>
     conj_tac >- metis_tac[not_fresh_at_def, LESS_EQ_TRANS] >>
     conj_tac >- metis_tac[not_fresh_at_def, LESS_EQ_TRANS] >>
     full_simp_tac std_ss [ptr_covers_def] >> metis_tac[optionTheory.SOME_11]) >>
  `!i. i < LENGTH dts ==> !m.
     mem_agree_outside tn1.t_mem s1.vs_memory m ==>
     val_in_memory (EL i stvs') (EL i vals')
       (w2n a + (soff + type_memory_bytes cenv st +
         SUM (MAP (type_memory_bytes cenv) (TAKE i sts)))) m` by
    (qx_gen_tac `i` >> strip_tac >>
     qpat_x_assum `!sts dtvs stvs vals lens tenv cx ctx PG R cenv dst src sa sz a b G tn s dtotal stotal doff soff. _` kall_tac >>
     qpat_x_assum `!i. i < LENGTH dts ==> _` (qspec_then `i` mp_tac) >>
     asm_simp_tac bool_ss [] >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
     `SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) +
        type_memory_bytes cenv (EL i sts) <=
        SUM (MAP (type_memory_bytes cenv) sts)` by
       (irule abi_encoder_prefix_sum_bound >> asm_rewrite_tac[]) >>
     qpat_x_assum `!ft fv p. _` (qspec_then `EL i stvs'` mp_tac) >>
     disch_then (qspec_then `EL i vals'` mp_tac) >>
     disch_then (qspec_then
       `w2n a + (soff + type_memory_bytes cenv st +
          SUM (MAP (type_memory_bytes cenv) (TAKE i sts)))` mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     (impl_tac >- decide_tac) >>
     (impl_tac >-
       (`w2n a + (soff + type_memory_bytes cenv st +
           SUM (MAP (type_memory_bytes cenv) (TAKE i sts))) =
         soff + (SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) +
           (w2n a + type_memory_bytes cenv st))` by decide_tac >>
        asm_rewrite_tac[])) >>
     simp[]) >>
  qpat_x_assum `!sts dtvs stvs vals lens tenv cx ctx PG R cenv dst src sa sz a b G tn s dtotal stotal doff soff. _`
    (qspecl_then [`sts`, `dtvs'`, `stvs'`, `vals'`, `lens'`, `tenv`,
                  `cx`, `ctx`, `PG`, `R`] mp_tac) >>
  disch_then (mp_tac o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  qpat_assum `compile_typed_copy_fields _ _ _ _ _ _ _ sm = _`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `ptr_covers G1 tn1 dst s1 dtotal`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `ptr_covers G1 tn1 src s1 stotal`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `lookup_var dst s1 = SOME b`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `lookup_var src s1 = SOME a`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  (impl_tac >-
    (ntac 8 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- decide_tac >>
     conj_tac >- decide_tac >>
     qx_gen_tac `i` >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH dts ==> is_bytestring_type _ /\ _`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
     qpat_x_assum `!i. i < LENGTH dts ==> !m. _`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
     ntac 13 (conj_tac >- first_assum ACCEPT_TAC) >>
     ntac 8 (conj_tac >- decide_tac) >>
     `soff + type_memory_bytes cenv st +
        (SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) + w2n a) =
      w2n a + (soff + type_memory_bytes cenv st +
        SUM (MAP (type_memory_bytes cenv) (TAKE i sts)))` by decide_tac >>
     asm_rewrite_tac[])) >>
  strip_tac >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  conj_tac >- metis_tac[frag_exec_ptr_seq] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (qx_gen_tac `p` >> strip_tac >>
     `not_fresh_at sm p` by metis_tac[not_fresh_at_def, LESS_EQ_TRANS] >>
     metis_tac[]) >>
  conj_tac >-
    (qx_gen_tac `i` >> strip_tac >>
     `mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s1.vs_memory` by
       (qpat_x_assum `!i. _ ==> mem_bytes_at _ _ sf.vs_memory = _`
          (qspec_then `i` mp_tac) >>
        (impl_tac >- decide_tac) >> simp[]) >>
     `mem_bytes_at i 1 s1.vs_memory = mem_bytes_at i 1 s.vs_memory` by
       (qpat_x_assum `!i. _ ==> mem_bytes_at _ _ s1.vs_memory = _`
          (qspec_then `i` mp_tac) >>
        (impl_tac >- decide_tac) >> simp[]) >>
     metis_tac[]) >>
  conj_tac >-
    (qx_gen_tac `i` >> strip_tac >>
     `i IN tnf.t_mem <=> i IN tn1.t_mem` by
       (qpat_x_assum `!i. _ ==> (i IN tnf.t_mem <=> _)`
          (qspec_then `i` mp_tac) >>
        (impl_tac >- decide_tac) >> simp[]) >>
     `i IN tn1.t_mem <=> i IN tn.t_mem` by
       (qpat_x_assum `!i. _ ==> (i IN tn1.t_mem <=> _)`
          (qspec_then `i` mp_tac) >>
        (impl_tac >- decide_tac) >> simp[]) >>
     metis_tac[]) >>
  conj_tac >-
    (qx_gen_tac `i` >> strip_tac >> Cases_on `i`
     >- (pure_rewrite_tac [listTheory.EL, listTheory.TAKE_def,
                           listTheory.MAP, listTheory.SUM, ADD_CLAUSES] >>
         qpat_x_assum `!ft fv p. _ ==> _ ==> _ ==> !m.
           mem_agree_outside tnf.t_mem _ _ ==> _`
           (qspecl_then [`dtv`, `v`, `doff + w2n b`] mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         (impl_tac >- decide_tac) >>
         (impl_tac >-
           (`doff + w2n b = w2n b + doff` by decide_tac >> asm_rewrite_tac[])) >>
         simp[]) >>
     rename1 `SUC j < SUC (LENGTH dts)` >>
     simp_tac (srw_ss()) [listTheory.EL, listTheory.TAKE_def,
                       listTheory.MAP, listTheory.SUM, listTheory.TL] >>
     qpat_x_assum `!i. i < LENGTH dts ==> !m.
       mem_agree_outside tnf.t_mem _ _ ==> _`
       (qspec_then `j` mp_tac) >>
     (impl_tac >- decide_tac) >>
     `doff + (type_memory_bytes cenv dt +
        SUM (MAP (type_memory_bytes cenv) (TAKE j dts)) + w2n b) =
      doff + type_memory_bytes cenv dt +
        (SUM (MAP (type_memory_bytes cenv) (TAKE j dts)) + w2n b)` by decide_tac >>
     asm_rewrite_tac[]) >>
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  qpat_x_assum `!ft fv p. _ ==> _ ==> _ ==> !m.
    mem_agree_outside tnf.t_mem _ _ ==> _`
    (qspecl_then [`ft`, `fv`, `p`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- decide_tac) >>
  (impl_tac >-
    (qpat_x_assum `!ft fv p. _ ==> _ ==> _ ==> !m.
       mem_agree_outside tn1.t_mem _ _ ==> _`
       (qspecl_then [`ft`, `fv`, `p`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     (impl_tac >- decide_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[])) >>
  simp[]
QED
