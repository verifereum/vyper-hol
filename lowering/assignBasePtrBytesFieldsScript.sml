(* Counted normalization for concrete lists of bytestring fields. *)
Theory assignBasePtrBytesFields
Ancestors assignBasePtrTypedBytesField assignBasePtrFieldsCompose
  exprLoweringProps contextCodegenRelProps
  context compileEnv bodyPtrDefs fragExec fragGasPathPtr abiEncoderInput
  words finite_map list arithmetic

Theorem assign_base_bytestring_fields_counted:
  !dts sts dtvs stvs vals lens tenv ctx PG D fn cenv dst src sa sz
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
          (w2n a + (soff + SUM (MAP (type_memory_bytes cenv) (TAKE i sts)))) m)) /\
    fn_has_code sa sz fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx ==>
    cs_extends sa sz /\
    ?Gf tnf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
      sf.vs_current_bb = sz.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sz.cs_current_insts /\ ~sf.vs_halted /\
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
  rpt gen_tac >>
  map_every qid_spec_tac [`soff`, `doff`, `s`, `tn`, `G`, `sz`, `sa`,
    `lens`, `vals`, `stvs`, `dtvs`, `sts`, `dts`] >>
  Induct_on `dts`
  >- (rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
      qpat_x_assum `_ \/ _` kall_tac >>
      gvs[Once compile_store_memory_typed_def, comp_return_def] >>
      simp[cs_extends_refl] >> qexistsl_tac [`G`, `tn`, `s`] >>
      simp[cj 1 gas_path_ptr_rules]) >>
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  namedCases_on `sts` ["", "st sts"] >> gnvs[] >>
  namedCases_on `dtvs` ["", "dtv dtvs"] >> gnvs[] >>
  namedCases_on `stvs` ["", "stv stvs"] >> gnvs[] >>
  namedCases_on `vals` ["", "v vals"] >> gnvs[] >>
  namedCases_on `lens` ["", "len lens"] >> gnvs[] >>
  rename1 `compile_typed_copy_fields cenv (Var dst) (Var src)
    (dt::dts) (st::sts) doff soff sa = ((),sz)` >>
  qpat_x_assum `!i. i < SUC (LENGTH dts) ==> _` mp_tac >>
  simp[Once FORALL_NUM, TAKE_def] >>
  disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> Cases_on `_0` >>
  suspend "head"
QED

Resume assign_base_bytestring_fields_counted[head]:
  rename1 `compile_store_memory_typed cenv dst_ptr dt src_ptr st sc = ((),sm)` >>
  `cs_extends sa cs' /\ cs_extends cs' sc /\
   sa.cs_next_var <= cs'.cs_next_var /\ cs'.cs_next_var <= sc.cs_next_var` by
    (qpat_assum `compile_with_byte_offset (Var dst) _ _ = _`
       (mp_then Any strip_assume_tac assignBasePtrFieldOffsetsTheory.assign_base_offset_extends) >>
     qpat_assum `compile_with_byte_offset (Var src) _ _ = _`
       (mp_then Any strip_assume_tac assignBasePtrFieldOffsetsTheory.assign_base_offset_extends) >>
     simp[]) >>
  `ci_mono sc sm /\ ci_mono sm sz` by
    (qpat_x_assum `!sts dtvs stvs vals lens sa sz G tn s doff soff. _` kall_tac >>
     qpat_x_assum `!i. i < LENGTH dts ==> _` kall_tac >>
     metis_tac[ci_mono_typed_memory_family, pairTheory.SND]) >>
  `cs_extends sa sm /\ cs_extends sm sz /\ sa.cs_next_var <= sm.cs_next_var` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n a+soff) m` by
    (simp_tac bool_ss [ADD_COMM] >> first_assum ACCEPT_TAC) >>
  drule_all (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) []
    (Q.INST [`n` |-> `32+32*((len+31) DIV 32)`]
      (SPEC_ALL assign_base_typed_bytestring_field_counted))) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> suspend "tail"
QED

Resume assign_base_bytestring_fields_counted[tail]:
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` >>
  `not_fresh_at sm dst /\ not_fresh_at sm src /\
   lookup_var dst s1 = SOME b /\ lookup_var src s1 = SOME a /\
   ptr_covers G1 tn1 dst s1 dtotal /\ ptr_covers G1 tn1 src s1 stotal` by
    (qpat_x_assum `!sts dtvs stvs vals lens sa sz G tn s doff soff. _` kall_tac >>
     qpat_x_assum `!i. i < LENGTH dts ==> _` kall_tac >>
     `not_fresh_at sm dst /\ not_fresh_at sm src` by
       metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
     qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `dst` mp_tac) >>
     qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `src` mp_tac) >>
     simp[] >> rpt strip_tac >> fs[ptr_covers_def] >> metis_tac[]) >>
  `!i. i < LENGTH dts ==> !m.
     mem_agree_outside tn1.t_mem s1.vs_memory m ==>
     val_in_memory (EL i stvs') (EL i vals')
       (w2n a + (soff + type_memory_bytes cenv st +
          SUM (MAP (type_memory_bytes cenv) (TAKE i sts)))) m` by
    suspend "source_frame" >>
  suspend "invoke_tail"
QED

Resume assign_base_bytestring_fields_counted[source_frame]:
  qpat_x_assum `!sts dtvs stvs vals lens sa sz G tn s doff soff. _` kall_tac >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH dts ==> _` (qspec_then `i` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) +
   type_memory_bytes cenv (EL i sts) <= SUM (MAP (type_memory_bytes cenv) sts)` by
    (irule abi_encoder_prefix_sum_bound >> simp[]) >>
  qpat_x_assum `!ft fv p. _` (qspecl_then
    [`EL i stvs'`, `EL i vals'`,
     `w2n a + (soff + type_memory_bytes cenv st +
       SUM (MAP (type_memory_bytes cenv) (TAKE i sts)))`] mp_tac) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- decide_tac >>
     qpat_x_assum `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory (EL i stvs') _ _ _` mp_tac >>
     simp_tac bool_ss [AC ADD_ASSOC ADD_COMM])) >>
  simp_tac bool_ss []
QED

Resume assign_base_bytestring_fields_counted[invoke_tail]:
  qpat_x_assum `!sts dtvs stvs vals lens sa sz G tn s doff soff. _`
    (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ dst _ _`)) >>
  disch_then (qspecl_then [`dtvs'`, `stvs'`, `vals'`, `lens'`] mp_tac) >>
  (impl_tac >- suspend "tail_premises") >>
  strip_tac >> suspend "package"
QED

Resume assign_base_bytestring_fields_counted[tail_premises]:
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- decide_tac
  >- decide_tac
  >- suspend "tail_indexed"
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >> first_assum ACCEPT_TAC
QED

Resume assign_base_bytestring_fields_counted[tail_indexed]:
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH dts ==> is_bytestring_type _ /\ _`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  qpat_x_assum `!i. i < LENGTH dts ==> !m. _` (qspec_then `i` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_tac >>
  ntac 13 (conj_tac >- first_assum ACCEPT_TAC) >>
  ntac 8 (conj_tac >- decide_tac) >>
  pop_assum mp_tac >> simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED

Resume assign_base_bytestring_fields_counted[package]:
  conj_tac >- metis_tac[cs_extends_trans] >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  conj_tac
  >- (qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
        (mp_then Any mp_tac gas_path_ptr_then) >>
      disch_then drule >> simp_tac bool_ss [ADD_CLAUSES]) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  conj_tac >- suspend "old_vars" >>
  conj_tac >- suspend "memory_frame" >>
  conj_tac >- suspend "taint_frame" >>
  conj_tac >- suspend "destination_fields" >>
  suspend "exterior_representation"
QED

Resume assign_base_bytestring_fields_counted[old_vars]:
  qx_gen_tac `p` >> strip_tac >>
  `not_fresh_at sm p` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `p` mp_tac) >>
  qpat_assum `!p. not_fresh_at sm p ==> _` (qspec_then `p` mp_tac) >>
  simp_tac bool_ss [] >> metis_tac[]
QED

Resume assign_base_bytestring_fields_counted[memory_frame]:
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. _ ==> mem_bytes_at _ _ sf.vs_memory = _`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  qpat_x_assum `!i. _ ==> mem_bytes_at _ _ s1.vs_memory = _`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  metis_tac[]
QED

Resume assign_base_bytestring_fields_counted[taint_frame]:
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. _ ==> (i IN tnf.t_mem <=> _)`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  qpat_x_assum `!i. _ ==> (i IN tn1.t_mem <=> _)`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  metis_tac[]
QED

Resume assign_base_bytestring_fields_counted[destination_fields]:
  qx_gen_tac `i` >> strip_tac >> Cases_on `i`
  >- (pure_rewrite_tac [EL, TAKE_def, MAP, SUM, ADD_CLAUSES] >>
      qpat_x_assum `!ft fv p. _ ==> !m. mem_agree_outside tnf.t_mem _ _ ==> _`
        (qspecl_then [`dtv`, `v`, `doff+w2n b`] mp_tac) >>
      (impl_tac >-
        (conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- decide_tac >> first_assum ACCEPT_TAC)) >>
      simp_tac bool_ss [listTheory.HD, listTheory.MAP, listTheory.SUM,
                        ADD_CLAUSES]) >>
  rename1 `SUC j < SUC (LENGTH dts)` >>
  simp_tac (srw_ss()) [EL, TAKE_def, MAP, SUM, TL] >>
  qpat_x_assum `!i. i < LENGTH dts ==> !m.
    mem_agree_outside tnf.t_mem _ _ ==> _` (qspec_then `j` mp_tac) >>
  (impl_tac >- decide_tac) >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED

Resume assign_base_bytestring_fields_counted[exterior_representation]:
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `!m. mem_agree_outside tn1.t_mem s1.vs_memory m ==>
       val_in_memory ft fv p m` by
    (qpat_x_assum `!ft fv p. _ ==> !m. mem_agree_outside tn1.t_mem _ _ ==> _`
       (qspecl_then [`ft`, `fv`, `p`] mp_tac) >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- decide_tac >> first_assum ACCEPT_TAC)) >>
     simp_tac bool_ss []) >>
  qpat_x_assum `!ft fv p. _ ==> !m. mem_agree_outside tnf.t_mem _ _ ==> _`
    (qspecl_then [`ft`, `fv`, `p`] mp_tac) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- decide_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss []
QED

Finalise assign_base_bytestring_fields_counted
