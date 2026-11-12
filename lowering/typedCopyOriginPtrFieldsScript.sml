(* The joint typed memory copies of tuples and structs, field by field. *)
Theory typedCopyOriginPtrFields
Ancestors
  typedCopyOriginPtrBase placeTypedCopyRecursivePath fragGasOriginPtr fragGasSeqPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline typedMemoryCopy robustCopyTransportPtr
  context compileEnv valueEncodingDefs valueEncoding

Theorem typed_copy_origin_ptr_fields_path_from_offset:
  (!cenv ctx dty sty dtv stv v xd xs doff soff dtotal stotal
     sa s1 s2 sb dp sp lo explicit func PG s G tn dw sw.
    typed_copy_origin_ptr_entry cenv ctx dty sty dtv stv v /\
    compile_with_byte_offset (Var xd) doff sa = (dp,s1) /\
    compile_with_byte_offset (Var xs) soff s1 = (sp,s2) /\
    compile_store_memory_typed cenv dp dty sp sty s2 = ((),sb) /\
    not_fresh_at sa xs /\ not_fresh_at sa xd /\
    lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory stv v (w2n sw + soff) mem) /\
    doff + type_memory_size dtv <= dtotal /\
    soff + type_memory_size stv <= stotal /\
    w2n sw + soff + type_memory_size stv < dimword (:256) /\
    w2n dw + doff + type_memory_size dtv < dimword (:256) /\
    (type_memory_size stv = 0 \/
     w2n sw + soff + type_memory_size stv <= s.vs_alloca_next) /\
    (type_memory_size dtv = 0 \/
     w2n dw + doff + type_memory_size dtv <= s.vs_alloca_next) /\
    (w2n sw + soff + type_memory_size stv <= w2n dw + doff \/
     w2n dw + doff + type_memory_size dtv <= w2n sw + soff) /\
    ptr_covers G tn xs s stotal /\ ptr_covers G tn xd s dtotal /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t Gf tnf.
      gas_origin_ptr_path
        (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
            d_ret := K {} |>,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tnf) /\
      val_in_memory dtv v (w2n dw + doff) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw + doff) (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!i. ~(w2n dw + doff <= i /\
              i < w2n dw + doff + type_memory_size dtv) ==>
           (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
         val_in_memory dtv v (w2n dw + doff) mem) /\
      (!p. not_fresh_at sa p ==>
         FLOOKUP Gf p = FLOOKUP G p /\
         op_taint tnf (Var p) = op_taint tn (Var p))) ==>
  (!cenv ctx dtys stys dtvs stvs vs xd xs doff soff dtotal stotal
     sa sb lo explicit func PG s G tn dw sw.
    LENGTH stys = LENGTH dtys /\ LENGTH dtvs = LENGTH dtys /\
    LENGTH stvs = LENGTH dtys /\ LENGTH vs = LENGTH dtys /\
    (!i. i < LENGTH dtys ==>
      type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs) /\
      type_memory_bytes cenv (EL i stys) = type_memory_size (EL i stvs) /\
      typed_copy_origin_ptr_entry cenv ctx (EL i dtys) (EL i stys)
        (EL i dtvs) (EL i stvs) (EL i vs)) /\
    tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
    compile_typed_copy_fields cenv (Var xd) (Var xs)
      dtys stys doff soff sa = ((),sb) /\
    not_fresh_at sa xs /\ not_fresh_at sa xd /\
    lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       tuple_in_memory vs stvs (w2n sw + soff) mem) /\
    doff + type_memory_size_list dtvs <= dtotal /\
    soff + type_memory_size_list stvs <= stotal /\
    w2n sw + soff + type_memory_size_list stvs < dimword (:256) /\
    w2n dw + doff + type_memory_size_list dtvs < dimword (:256) /\
    (type_memory_size_list stvs = 0 \/
     w2n sw + soff + type_memory_size_list stvs <= s.vs_alloca_next) /\
    (type_memory_size_list dtvs = 0 \/
     w2n dw + doff + type_memory_size_list dtvs <= s.vs_alloca_next) /\
    (w2n sw + soff + type_memory_size_list stvs <= w2n dw + doff \/
     w2n dw + doff + type_memory_size_list dtvs <= w2n sw + soff) /\
    ptr_covers G tn xs s stotal /\ ptr_covers G tn xd s dtotal /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t Gf tnf.
      gas_origin_ptr_path
        (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
            d_ret := K {} |>,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tnf) /\
      tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw + doff)
        (type_memory_size_list dtvs) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!i. ~(w2n dw + doff <= i /\
              i < w2n dw + doff + type_memory_size_list dtvs) ==>
           (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
         tuple_in_memory vs dtvs (w2n dw + doff) mem) /\
      (!p. not_fresh_at sa p ==>
         FLOOKUP Gf p = FLOOKUP G p /\
         op_taint tnf (Var p) = op_taint tn (Var p)))
Proof
  disch_then (mk_asm "offset") >>
  map_every qx_gen_tac [`cenv`, `ctx`] >> Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_store_memory_typed_def, comp_return_def,
          val_in_memory_def, type_memory_size_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >>
      simp[gas_origin_ptr_path_rules]) >>
  first_x_assum (mk_asm "ih") >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  namedCases_on `stys` ["", "sty stys"]
  >- (qpat_x_assum `LENGTH [] = LENGTH (_::_)` mp_tac >> simp[]) >>
  namedCases_on `dtvs` ["", "dtv dtvs"]
  >- (qpat_x_assum `LENGTH [] = LENGTH (_::_)` mp_tac >> simp[]) >>
  namedCases_on `stvs` ["", "stv stvs"]
  >- (qpat_x_assum `LENGTH [] = LENGTH (_::_)` mp_tac >> simp[]) >>
  namedCases_on `vs` ["", "v vs"]
  >- (qpat_x_assum `LENGTH [] = LENGTH (_::_)` mp_tac >> simp[]) >>
  rename1 `compile_typed_copy_fields cenv (Var xd) (Var xs)
    (dty::dtys) (sty::stys) doff soff sa = ((),sb)` >>
  gnvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  qpat_assum `!i. i < SUC (LENGTH dtys) ==> _`
    (qspec_then `0` mp_tac) >>
  simp_tac std_ss [listTheory.EL, listTheory.HD] >>
  strip_tac >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rpt (qpat_x_assum `_ /\ _` strip_assume_tac) >>
  rename1 `compile_store_memory_typed cenv dp dty sp sty sc2 = (u,sc)` >>
  Cases_on `u` >>
  `ci_mono sa sc /\ ci_mono sc sb` by
    (asm_x "ih" kall_tac >> asm_x "offset" kall_tac >>
     `ci_mono sa cs' /\ ci_mono cs' sc2` by
       metis_tac[typed_copy_offset_mono] >>
     `ci_mono sc2 sc /\ ci_mono sc sb` by
       metis_tac[cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family,
                 cj 2 exprLoweringPropsTheory.ci_mono_typed_memory_family,
                 pairTheory.SND] >>
     gvs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[compileEnvTheory.cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `cs_extends sa sc /\ cs_extends sc sb` by
    gvs[exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    (asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  asm "offset" (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_with_byte_offset (Var xd) _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_with_byte_offset (Var xs) _ _ = _`)) >>
  disch_then (drule_at (Pat `typed_copy_origin_ptr_entry _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xs _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xd _ _`)) >>
  disch_then (qspecl_then [`lo`, `explicit`, `func`, `PG`] mp_tac) >>
  disch_then (drule_at (Pat `lookup_var xs _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var xd _ = _`)) >>
  (impl_tac >- (asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
    simp[] >> rpt conj_tac >> decide_tac)) >>
  strip_tac >>
  `!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
     tuple_in_memory vs' stvs' (w2n sw + soff + type_memory_size stv) mem` by
    (`!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
       val_in_memory (TupleTV stvs') (ArrayV (TupleV vs'))
         (w2n sw + soff + type_memory_size stv) mem`
       suffices_by (simp_tac (srw_ss()) [val_in_memory_def]) >>
     rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[val_wf_def] >>
     qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
       `{i | w2n dw + doff <= i /\ i < w2n dw + doff + type_memory_size dtv}`] >>
     asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
     simp[val_wf_def, val_in_memory_def, loweringPostsTheory.val_footprint_def,
       type_memory_size_def] >>
     gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `lookup_var xs t = SOME sw /\ lookup_var xd t = SOME dw /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
     gvs[typed_copy_state_frame_def, venomStateTheory.venom_state_component_equality]) >>
  `not_fresh_at sc xs /\ not_fresh_at sc xd` by
    (asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,
               exprLoweringPropsTheory.ci_mono_def]) >>
  `ptr_covers Gf tnf xs t stotal /\ ptr_covers Gf tnf xd t dtotal` by
    (asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
     gvs[ptr_covers_def] >> metis_tac[]) >>
  `allocas_from lo t` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     pure_rewrite_tac [allocas_from_def] >> asm_rewrite_tac []) >>
  qpat_x_assum `ptr_covers G tn xs s stotal` kall_tac >>
  qpat_x_assum `ptr_covers G tn xd s dtotal` kall_tac >>
  qpat_x_assum `lookup_var xs s = SOME sw` kall_tac >>
  qpat_x_assum `lookup_var xd s = SOME dw` kall_tac >>
  asm "ih" (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xs _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xd _ _`)) >>
  disch_then (drule_at (Pat `lookup_var xs _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var xd _ = _`)) >>
  disch_then (qspecl_then [`dtvs'`, `stvs'`, `vs'`, `lo`, `explicit`, `func`, `PG`] mp_tac) >>
  (impl_tac >-
    (asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
     `!i. i < LENGTH dtys ==>
       type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs') /\
       type_memory_bytes cenv (EL i stys) = type_memory_size (EL i stvs') /\
       typed_copy_origin_ptr_entry cenv ctx (EL i dtys) (EL i stys)
         (EL i dtvs') (EL i stvs') (EL i vs')` by
       (rpt strip_tac >>
        qpat_x_assum `!i. i < SUC (LENGTH dtys) ==> _`
          (qspec_then `SUC i` mp_tac) >> simp[]) >>
     qpat_x_assum `!i. i < SUC (LENGTH dtys) ==> _` kall_tac >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       (qpat_x_assum `!i. i < LENGTH dtys ==> _` kall_tac >>
        asm_rewrite_tac [allocas_from_def, arithmeticTheory.ADD_ASSOC] >> decide_tac)])) >>
  strip_tac >> asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
  qpat_x_assum `!i. i < SUC (LENGTH dtys) ==> _` kall_tac >>
  `!mem. mem_agree_outside tnf'.t_mem t'.vs_memory mem ==>
     val_in_memory dtv v (w2n dw + doff) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`t.vs_memory`, `t'.vs_memory`, `tnf.t_mem`, `tnf'.t_mem`,
       `{i | w2n dw + (doff + type_memory_size dtv) <= i /\
             i < w2n dw + (doff + type_memory_size dtv) + type_memory_size_list dtvs'}`] >>
     `loweringPosts$val_footprint dtv v <= type_memory_size dtv` by
       metis_tac[exprSimPropsTheory.val_footprint_le] >>
     simp[] >>
     gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `typed_copy_state_frame sa (w2n dw + doff)
     (type_memory_size dtv + type_memory_size_list dtvs') s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> conj_tac
     >- (irule typed_copy_state_frame_subinterval >>
         goal_assum (drule_at Any) >> decide_tac) >>
     irule typed_copy_state_frame_subinterval >>
     qexistsl_tac [`w2n dw + (doff + type_memory_size dtv)`,
                  `type_memory_size_list dtvs'`] >>
     simp[] >> irule typed_copy_state_frame_mono >>
     goal_assum (drule_at Any) >>
     metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`t'`, `Gf'`, `tnf'`] >>
  conj_tac
  >- metis_tac[gas_origin_ptr_path_append, listTheory.APPEND_NIL] >>
  `val_in_memory dtv v (w2n dw + doff) t'.vs_memory` by
    (qpat_assum `!mem. _ ==> val_in_memory dtv v _ mem`
       (qspec_then `t'.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def]) >>
  rule_assum_tac (SIMP_RULE (srw_ss())
    [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_x_assum `!i. _ ==> (i IN tnf.t_mem <=> i IN tn.t_mem)`
        (qspec_then `i` mp_tac) >>
      (impl_tac >- decide_tac) >> disch_tac >>
      qpat_x_assum `!i. _ ==> (i IN tnf'.t_mem <=> i IN tnf.t_mem)`
        (qspec_then `i` mp_tac) >>
      (impl_tac >- decide_tac) >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at sc p` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,
              exprLoweringPropsTheory.ci_mono_def] >>
  metis_tac[]
QED

Theorem typed_copy_origin_ptr_tuple_entry:
  !cenv tenv ctx dtys sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (TupleT dtys) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (TupleT dtys) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (TupleT dtys) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_origin_ptr_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_origin_ptr_entry cenv ctx (TupleT dtys) sty dtv stv v
Proof
  cheat
QED

Theorem typed_copy_origin_ptr_struct_entry:
  !cenv tenv ctx name sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (StructT name) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (StructT name) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (StructT name) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_origin_ptr_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_origin_ptr_entry cenv ctx (StructT name) sty dtv stv v
Proof
  cheat
QED
