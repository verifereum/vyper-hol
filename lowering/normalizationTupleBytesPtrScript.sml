(* Allocation and whole-tuple bytestring normalization. *)
Theory normalizationTupleBytesPtr
Ancestors normalizationAllocExecPtr typedCopyTupleEffectsPtr

Theorem alloca_step_exterior_effects:
  step_inst_base (mk_inst id ALLOCA [Lit sz] [out]) s = OK s1 /\
  FLOOKUP s1.vs_allocas id = SOME (b,n) ==>
  s1.vs_memory = s.vs_memory /\
  (step_taint (mk_inst id ALLOCA [Lit sz] [out]) s s1 tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id ALLOCA [Lit sz] [out]) s s1 tn).t_trans = tn.t_trans /\
  (!j. ~(b <= j /\ j < b+n) ==>
    (j IN (step_taint (mk_inst id ALLOCA [Lit sz] [out]) s s1 tn).t_mem <=>
     j IN tn.t_mem))
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, venomInstTheory.mk_inst_def,
    venomStateTheory.eval_operand_def, venomExecSemanticsTheory.exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.set_var_taint_def,
    venomInstTheory.mk_inst_def, ptrDisciplineTheory.adopt_reset_def,
    ptrDisciplineTheory.store_taint_def, ptrDisciplineTheory.mem_taint_def,
    ptrDisciplineTheory.new_site_bytes_def, ptrDisciplineTheory.step_writes_def,
    ptrDisciplineTheory.written_taint_def, codegenRelTheory.source_memory_write_ranges_def,
    ptrDisciplineTheory.range_bytes_def] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >>
  eq_tac >> rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_DEF]
QED

Theorem alloca_step_robust_exterior_frame:
  step_inst_base (mk_inst id ALLOCA [Lit sz] [out]) s = OK s1 /\
  FLOOKUP s1.vs_allocas id = SOME (b,n) /\ val_wf ft fv /\
  (p+type_memory_size ft <= b \/ b+n <= p) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ft fv p m) ==>
  !m. mem_agree_outside
    (step_taint (mk_inst id ALLOCA [Lit sz] [out]) s s1 tn).t_mem
    s1.vs_memory m ==> val_in_memory ft fv p m
Proof
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  drule_all alloca_step_exterior_effects >> disch_then (qspec_then `tn` strip_assume_tac) >>
  `val_footprint ft fv <= type_memory_size ft` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  rpt strip_tac >> irule robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl [`s.vs_memory`, `s1.vs_memory`, `tn.t_mem`,
    `(step_taint (mk_inst id ALLOCA [Lit sz] [out]) s s1 tn).t_mem`,
    `{j | b <= j /\ j < b+n}`] >>
  simp[] >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem compile_alloc_tuple_bytes_effects_frag_ptr:
  !ctx func cenv cx e es sa sb s0 es' vals root s n buf sc sd
   stvs dtvs sts dts lens a tn PG G R.
    expr_post ctx func cenv cx e es sa sb s0 es' (ArrayV (TupleV vals)) (Var root) s /\
    fresh_vars_wrt sb s /\ fn_inst_ids_distinct func /\
    compile_alloc_buffer n sb = (buf,sc) /\
    compile_store_memory_typed cenv buf.buf_operand (TupleT dts)
      (Var root) (TupleT sts) sc = ((),sd) /\ fn_has_code sb sd func /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME (TupleTV stvs) /\
    ~is_word_type (expr_type e) /\ val_wf (TupleTV stvs) (ArrayV (TupleV vals)) /\
    n < dimword(:256) /\ not_fresh_at sb root /\ lookup_var root s = SOME a /\
    ptr_covers G tn root s (val_footprint (TupleTV stvs) (ArrayV (TupleV vals))) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (TupleTV stvs) (ArrayV (TupleV vals)) (w2n a) m) /\
    LENGTH sts = LENGTH dts /\ LENGTH dtvs = LENGTH dts /\
    LENGTH stvs = LENGTH dts /\ LENGTH vals = LENGTH dts /\ LENGTH lens = LENGTH dts /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    SUM (MAP (type_memory_bytes cenv) dts) <= n /\
    SUM (MAP (type_memory_bytes cenv) sts) <=
      val_footprint (TupleTV stvs) (ArrayV (TupleV vals)) /\
    (!i. i < LENGTH dts ==>
      is_bytestring_type (EL i sts) /\ is_bytestring_type (EL i dts) /\
      evaluate_type (get_tenv cx) (EL i sts) = SOME (EL i stvs) /\
      evaluate_type (get_tenv cx) (EL i dts) = SOME (EL i dtvs) /\
      value_has_type (EL i stvs) (EL i vals) /\ value_has_type (EL i dtvs) (EL i vals) /\
      val_wf (EL i stvs) (EL i vals) /\ val_wf (EL i dtvs) (EL i vals) /\
      ((?bs. EL i vals = BytesV bs /\ EL i lens = LENGTH bs) \/
       (?str. EL i vals = StringV str /\ EL i lens = LENGTH str)) /\
      32+32*((EL i lens+31) DIV 32) <= type_memory_bytes cenv (EL i dts) /\
      32+32*((EL i lens+31) DIV 32) <= type_memory_bytes cenv (EL i sts) /\
      type_memory_bytes cenv (EL i dts) = type_memory_size (EL i dtvs) /\
      type_memory_bytes cenv (EL i sts) = type_memory_size (EL i stvs) /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) < n /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) +
        (32+32*((EL i lens+31) DIV 32)) <= n /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) <
        val_footprint (TupleTV stvs) (ArrayV (TupleV vals)) /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) +
        (32+32*((EL i lens+31) DIV 32)) <=
        val_footprint (TupleTV stvs) (ArrayV (TupleV vals)) /\
      w2n a + SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) < dimword(:256) /\
      EL i lens+31 < dimword(:256) /\ 32+32*((EL i lens+31) DIV 32) < dimword(:256)) ==>
    ?out b Gf tnf sf.
      buf.buf_operand = Var out /\ b+n < dimword(:256) /\
      (?sAlloc.
        step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK sAlloc /\
        FLOOKUP sAlloc.vs_allocas sb.cs_next_id = SOME (b,n) /\
        sf.vs_allocas = sAlloc.vs_allocas /\
        sf.vs_alloca_next = sAlloc.vs_alloca_next) /\
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
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `ci_mono sb sc` by
    (mp_tac (Q.SPECL [`n`, `sb`] exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >>
     simp[]) >>
  `ci_mono sc sd` by
    (mp_tac (Q.SPECL [`cenv`, `buf.buf_operand`, `TupleT dts`, `Var root`, `TupleT sts`, `sc`]
      (CONJUNCT1 exprLoweringPropsTheory.ci_mono_typed_memory_family)) >> simp[]) >>
  `cs_extends sb sc /\ cs_extends sc sd` by
    gvs[exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code sb sc func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `eval_operand (Var root) s = SOME a` by simp[venomStateTheory.eval_operand_def] >>
  drule_all normalizationAllocPtrTheory.compile_alloc_buffer_expr_resources >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  qpat_x_assum `i = mk_inst _ _ _ _` SUBST_ALL_TAC >>
  qabbrev_tac `sA = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `frag_exec_ptr cx ctx PG sb sc
    (\g t v. g = G /\ t = tn /\ v = s)
    (\g t v. g = G1 /\ t = tn1 /\ v = sA) R` by
    (gvs[] >> simp[Abbr `sA`] >> irule compile_alloc_buffer_step_frag_ptr >> simp[]) >>
  `!q. not_fresh_at sb q ==>
    lookup_var q sA = lookup_var q s /\ FLOOKUP G1 q = FLOOKUP G q /\
    op_taint tn1 (Var q) = op_taint tn (Var q)` by
    (drule loweringHaltTheory.compile_alloc_buffer_emission >> strip_tac >>
     `~not_fresh_at sb out` by gvs[] >>
     rpt strip_tac >> `q <> out` by metis_tac[] >>
     drule alloca_step_old_register_frame >>
     disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
     qpat_x_assum `!q. q <> out ==> _` (qspec_then `q` mp_tac) >>
     simp[Abbr `sA`, venomStateTheory.lookup_var_def]) >>
  `not_fresh_at sc root` by
    (gvs[compileEnvTheory.not_fresh_at_def, exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `lookup_var root sA = SOME a /\ lookup_var out sA = SOME (n2w b) /\
   ptr_covers G1 tn1 root sA (val_footprint (TupleTV stvs) (ArrayV (TupleV vals))) /\
   ptr_covers G1 tn1 out sA n` by suspend "resources" >>
  `w2n (n2w b:256 word) = b` by
    (simp[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  Cases_on `dts = []` >- suspend "empty" >>
  `0 < n /\ 0 < val_footprint (TupleTV stvs) (ArrayV (TupleV vals))` by
    (qpat_x_assum `!i. i < LENGTH dts ==> _` (qspec_then `0` mp_tac) >>
     simp[] >> (impl_tac >- (Cases_on `dts` >> gvs[])) >>
     strip_tac >> decide_tac) >>
  `b+n <= w2n a \/ w2n a+val_footprint (TupleTV stvs) (ArrayV (TupleV vals)) <= b`
    by suspend "disjoint" >> (
  `!m. mem_agree_outside tn1.t_mem sA.vs_memory m ==>
    val_in_memory (TupleTV stvs) (ArrayV (TupleV vals)) (w2n a) m` by
    (simp[Abbr `sA`] >> metis_tac[]) >>
  `not_fresh_at sc out` by
    (drule loweringHaltTheory.compile_alloc_buffer_emission >> strip_tac >> gvs[]) >>
  qpat_x_assum `buf.buf_operand = Var out` SUBST_ALL_TAC >>
  drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)
    compile_store_memory_typed_tuple_bytes_effects_frag_ptr >>
  disch_then (drule_at (Pat `lookup_var out _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var root _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ out _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ root _ _`)) >>
  disch_then (qspecl_then [`dtvs`, `stvs`, `vals`, `lens`, `get_tenv cx`, `cx`, `ctx`, `PG`, `R`] mp_tac) >>
  (impl_tac >- suspend "copy_premises") >>
  strip_tac >> qexistsl [`out`, `b`, `Gf`, `tnf`, `sf`] >>
  asm_rewrite_tac[] >>
  conj_tac >- (qexists_tac `s1` >> simp[Abbr `sA`]) >>
  conj_tac >- suspend "compose" >>
  conj_tac >- suspend "lookup" >>
  conj_tac >- suspend "covers" >>
  conj_tac >- suspend "representation" >>
  suspend "frame")
QED

Resume compile_alloc_tuple_bytes_effects_frag_ptr[resources]:
  `ptr_covers G1 tn1 root s1 (val_footprint (TupleTV stvs) (ArrayV (TupleV vals)))` by
    metis_tac[] >>
  qpat_x_assum `!p k. ptr_covers _ _ _ _ _ ==> _` kall_tac >>
  qpat_x_assum `G1 = _` kall_tac >> qpat_x_assum `tn1 = _` kall_tac >>
  gvs[Abbr `sA`, venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
    bodyPtrDefsTheory.ptr_covers_def]
QED
Resume compile_alloc_tuple_bytes_effects_frag_ptr[disjoint]:
  Cases_on `b+n <= w2n a` >> simp[] >>
  Cases_on `w2n a+val_footprint (TupleTV stvs) (ArrayV (TupleV vals)) <= b` >> simp[] >>
  `w2n a <= MAX b (w2n a) /\
   MAX b (w2n a) < w2n a+val_footprint (TupleTV stvs) (ArrayV (TupleV vals)) /\
   b <= MAX b (w2n a) /\ MAX b (w2n a) < b+n` by
    (simp_tac (srw_ss()) [arithmeticTheory.MAX_DEF] >>
     Cases_on `b <= w2n a` >> simp[] >> decide_tac) >>
  metis_tac[]
QED
Resume compile_alloc_tuple_bytes_effects_frag_ptr[copy_premises]:
  markerLib.RESUME_TAC >> (
  asm_rewrite_tac[] >> qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH dts ==> _` (qspec_then `i` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >> simp[] >> decide_tac)
QED
Resume compile_alloc_tuple_bytes_effects_frag_ptr[compose]:
  markerLib.RESUME_TAC >> (
  irule fragExecPtrTheory.frag_exec_ptr_seq >>
  qexists_tac `\g t v. g = G1 /\ t = tn1 /\ v = sA` >>
  qexists_tac `sc` >> asm_rewrite_tac[])
QED
Resume compile_alloc_tuple_bytes_effects_frag_ptr[covers]:
  markerLib.RESUME_TAC >> (
  qpat_assum `!p. not_fresh_at sc p ==> _` (qspec_then `out` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qpat_x_assum `G1 = _` kall_tac >> qpat_x_assum `tn1 = _` kall_tac >>
  qpat_x_assum `ptr_covers G1 tn1 out sA n` mp_tac >>
  simp[bodyPtrDefsTheory.ptr_covers_def, venomStateTheory.eval_operand_def])
QED
Resume compile_alloc_tuple_bytes_effects_frag_ptr[frame]:
  markerLib.RESUME_TAC >> (
  drule_all alloca_step_exterior_effects >> disch_then (qspec_then `tn` strip_assume_tac) >>
  rpt conj_tac
  >- metis_tac[]
  >- metis_tac[]
  >- (qx_gen_tac `q` >> strip_tac >>
      `not_fresh_at sc q` by
        (gvs[compileEnvTheory.not_fresh_at_def, exprLoweringPropsTheory.ci_mono_def] >>
         metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      qpat_assum `!p. not_fresh_at sc p ==> _` (qspec_then `q` mp_tac) >>
      qpat_assum `!q. not_fresh_at sb q ==> _` (qspec_then `q` mp_tac) >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `!m. mem_agree_outside tn1.t_mem sA.vs_memory m ==> val_in_memory ft fv p m` by
    (simp_tac (srw_ss()) [Abbr `sA`] >>
     qpat_x_assum `tn1 = _` SUBST_ALL_TAC >> rpt strip_tac >>
     irule alloca_step_robust_exterior_frame >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_x_assum `!ft fv p. _` (qspecl_then [`ft`, `fv`, `p`] mp_tac) >>
  simp[] >> (impl_tac >- decide_tac) >> metis_tac[])
QED
Resume compile_alloc_tuple_bytes_effects_frag_ptr[lookup]:
  markerLib.RESUME_TAC >> (
  qpat_assum `!p. not_fresh_at sc p ==> _` (qspec_then `out` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >> asm_rewrite_tac[])
QED
Resume compile_alloc_tuple_bytes_effects_frag_ptr[representation]:
  markerLib.RESUME_TAC >> (rpt strip_tac >> metis_tac[])
QED
Resume compile_alloc_tuple_bytes_effects_frag_ptr[empty]:
  `sts = [] /\ dtvs = [] /\ stvs = [] /\ vals = [] /\ lens = []` by gvs[] >>
  `sd = sc` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once contextTheory.compile_store_memory_typed_def,
       compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def,
       compileEnvTheory.comp_return_def] >>
     simp[Once contextTheory.compile_store_memory_typed_def, compileEnvTheory.comp_return_def]) >>
  drule_all alloca_step_exterior_effects >> disch_then (qspec_then `tn` strip_assume_tac) >>
  qexistsl [`out`, `b`, `G1`, `tn1`, `sA`] >>
  qpat_x_assum `G1 = _` kall_tac >>
  gvs[valueEncodingTheory.val_in_memory_def] >>
  rpt gen_tac >> strip_tac >>
  simp_tac (srw_ss()) [Abbr `sA`] >> rpt strip_tac >>
  irule alloca_step_robust_exterior_frame >> asm_rewrite_tac[] >> metis_tac[]
QED
Finalise compile_alloc_tuple_bytes_effects_frag_ptr

(* Compatibility projection; the execution witness is constructed only above. *)
Theorem compile_alloc_tuple_bytes_robust_frag_ptr:
  !ctx func cenv cx e es sa sb s0 es' vals root s n buf sc sd
   stvs dtvs sts dts lens a tn PG G R.
    expr_post ctx func cenv cx e es sa sb s0 es' (ArrayV (TupleV vals)) (Var root) s /\
    fresh_vars_wrt sb s /\ fn_inst_ids_distinct func /\
    compile_alloc_buffer n sb = (buf,sc) /\
    compile_store_memory_typed cenv buf.buf_operand (TupleT dts)
      (Var root) (TupleT sts) sc = ((),sd) /\ fn_has_code sb sd func /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME (TupleTV stvs) /\
    ~is_word_type (expr_type e) /\ val_wf (TupleTV stvs) (ArrayV (TupleV vals)) /\
    n < dimword(:256) /\ not_fresh_at sb root /\ lookup_var root s = SOME a /\
    ptr_covers G tn root s (val_footprint (TupleTV stvs) (ArrayV (TupleV vals))) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (TupleTV stvs) (ArrayV (TupleV vals)) (w2n a) m) /\
    LENGTH sts = LENGTH dts /\ LENGTH dtvs = LENGTH dts /\
    LENGTH stvs = LENGTH dts /\ LENGTH vals = LENGTH dts /\ LENGTH lens = LENGTH dts /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    SUM (MAP (type_memory_bytes cenv) dts) <= n /\
    SUM (MAP (type_memory_bytes cenv) sts) <=
      val_footprint (TupleTV stvs) (ArrayV (TupleV vals)) /\
    (!i. i < LENGTH dts ==>
      is_bytestring_type (EL i sts) /\ is_bytestring_type (EL i dts) /\
      evaluate_type (get_tenv cx) (EL i sts) = SOME (EL i stvs) /\
      evaluate_type (get_tenv cx) (EL i dts) = SOME (EL i dtvs) /\
      value_has_type (EL i stvs) (EL i vals) /\ value_has_type (EL i dtvs) (EL i vals) /\
      val_wf (EL i stvs) (EL i vals) /\ val_wf (EL i dtvs) (EL i vals) /\
      ((?bs. EL i vals = BytesV bs /\ EL i lens = LENGTH bs) \/
       (?str. EL i vals = StringV str /\ EL i lens = LENGTH str)) /\
      32+32*((EL i lens+31) DIV 32) <= type_memory_bytes cenv (EL i dts) /\
      32+32*((EL i lens+31) DIV 32) <= type_memory_bytes cenv (EL i sts) /\
      type_memory_bytes cenv (EL i dts) = type_memory_size (EL i dtvs) /\
      type_memory_bytes cenv (EL i sts) = type_memory_size (EL i stvs) /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) < n /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i dts)) +
        (32+32*((EL i lens+31) DIV 32)) <= n /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) <
        val_footprint (TupleTV stvs) (ArrayV (TupleV vals)) /\
      SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) +
        (32+32*((EL i lens+31) DIV 32)) <=
        val_footprint (TupleTV stvs) (ArrayV (TupleV vals)) /\
      w2n a + SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) < dimword(:256) /\
      EL i lens+31 < dimword(:256) /\ 32+32*((EL i lens+31) DIV 32) < dimword(:256)) ==>
    ?out b Gf tnf sf.
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
  drule_all compile_alloc_tuple_bytes_effects_frag_ptr >>
  disch_then (qspecl_then [`PG`, `R`] strip_assume_tac) >>
  qexistsl_tac [`out`, `b`, `Gf`, `tnf`, `sf`] >> asm_rewrite_tac[]
QED
