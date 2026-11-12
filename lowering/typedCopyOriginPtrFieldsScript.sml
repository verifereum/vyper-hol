(* The joint typed memory copies of tuples and structs, field by field. *)
Theory typedCopyOriginPtrFields
Ancestors
  typedCopyOriginPtrBase placeTypedCopyRecursivePath fragGasOriginPtr fragGasSeqPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline typedMemoryCopy vyperTypeDefaults

Libs
  vyperValueTheory vyperTypingTheory vyperASTTheory listTheory vyperTypeSystemTheory
  valueEncodingDefsTheory valueEncodingTheory contextTheory compileEnvTheory

Theorem tuple_val_wf_LIST_REL:
  !tvs vs. LENGTH vs = LENGTH tvs ==>
    (tuple_val_wf vs tvs <=> LIST_REL val_wf tvs vs)
Proof
  Induct >> Cases_on `vs` >> simp[val_wf_def]
QED

Theorem typed_copy_origin_ptr_tuple_entry_from_fields:
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
         op_taint tnf (Var p) = op_taint tn (Var p))) ==>

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
  disch_then (mk_asm "fields") >>
  rpt gen_tac >> strip_tac >>
  `?stys. sty = TupleT stys` by metis_tac[typed_copy_tuple_widening] >> gvs[] >>
  `LIST_REL (type_widens_to tenv) stys dtys` by
    (`!ss ds. (ss = ds \/ arg_types_fit ss ds) /\
         (?tvs. OPT_MMAP (evaluate_type tenv) ds = SOME tvs) ==>
         LIST_REL (type_widens_to tenv) ss ds` suffices_by
       (strip_tac >> drule typed_copy_tuple_widening >>
        gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
        metis_tac[]) >>
     Induct >> Cases_on `ds` >>
     simp[arg_type_fits_def, OPT_MMAP_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     simp[type_widens_to_def, well_formed_type_def] >> metis_tac[]) >>
  gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `LENGTH stys = LENGTH dtys /\ LENGTH tvs' = LENGTH dtys /\
   LENGTH tvs = LENGTH dtys /\ LENGTH l = LENGTH dtys /\
   (!i. i < LENGTH dtys ==>
     type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i tvs') /\
     type_memory_bytes cenv (EL i stys) = type_memory_size (EL i tvs) /\
     typed_copy_origin_ptr_entry cenv ctx (EL i dtys) (EL i stys)
       (EL i tvs') (EL i tvs) (EL i l))` by
    (gvs[vyperMiscTheory.OPT_MMAP_SOME_IFF, LIST_REL_EL_EQN,
         EVERY_MAP, EVERY_EL, LENGTH_MAP] >>
     `LENGTH l = LENGTH dtys` by
       metis_tac[values_have_types_length, LENGTH_MAP] >> simp[] >>
     rpt strip_tac >> simp[EL_MAP] >>
     `evaluate_type tenv (EL i dtys) = SOME (THE (evaluate_type tenv (EL i dtys))) /\
      evaluate_type tenv (EL i stys) = SOME (THE (evaluate_type tenv (EL i stys)))` by
       (`IS_SOME (evaluate_type tenv (EL i dtys)) /\
         IS_SOME (evaluate_type tenv (EL i stys))` by metis_tac[] >>
        Cases_on `evaluate_type tenv (EL i dtys)` >>
        Cases_on `evaluate_type tenv (EL i stys)` >> gvs[])
     >- (irule typed_copy_memory_size >> qexists_tac `tenv` >>
         simp[] >> metis_tac[EVERY_EL])
     >- (irule typed_copy_memory_size >> qexists_tac `tenv` >>
         simp[] >> metis_tac[EVERY_EL]) >>
     qpat_x_assum `!cd cs cdt cst cv. _` irule >>
     (conj_tac >- metis_tac[typedCopyDomainTheory.member_rank_lt_tuple, MEM_EL]) >>
     gvs[val_wf_def, tuple_val_wf_LIST_REL,
         vyperTypeDefaultsTheory.values_have_types_LIST_REL,
         LIST_REL_EL_EQN, EL_MAP]) >>
  pure_rewrite_tac[typed_copy_origin_ptr_entry_def] >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  asm "fields" (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  simp[val_in_memory_def, type_memory_size_def] >>
  disch_then irule >>
  gnvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  conj_tac >- (qexists_tac `type_memory_size_list tvs'` >> simp[]) >>
  qexistsl_tac [`type_memory_size_list tvs`, `tvs`] >>
  simp[]
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
