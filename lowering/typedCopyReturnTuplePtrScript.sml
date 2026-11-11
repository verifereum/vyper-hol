(* Tuple constructor for the counted pointer-safe typed copy. *)
Theory typedCopyReturnTuplePtr
Ancestors typedCopyReturnFieldsPtr typedCopyReturnFieldSemantics
  typedCopyLayoutPtr typedMemoryCopy context compileEnv

Theorem typed_copy_return_tuple_step:
  !ce tenv D ctx PG dts sty dtv stv v.
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty (TupleT dts) /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv (TupleT dts) = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  (!cd cs cdt cst cv.
    type_rank ce.ce_struct_fields cd < type_rank ce.ce_struct_fields (TupleT dts) ==>
    type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
    evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
    value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
    !dp sp sc sd fn G tn s dw sw.
    compile_store_memory_typed ce (Var dp) cd (Var sp) cs sc = ((),sd) /\
    not_fresh_at sc dp /\ not_fresh_at sc sp /\
    lookup_var dp s = SOME dw /\ lookup_var sp s = SOME sw /\
    w2n dw + type_memory_size cdt < dimword(:256) /\
    w2n sw + type_memory_size cst < dimword(:256) /\
    regions_disjoint (w2n sw) (type_memory_size cst) (w2n dw) (type_memory_size cdt) /\
    ptr_covers G tn dp s (type_memory_size cdt) /\
    ptr_covers G tn sp s (type_memory_size cst) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory cst cv (w2n sw) m) /\
    fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\
    s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = sd.cs_current_bb /\
      t.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sc (w2n dw) (type_memory_size cdt) s t /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==> val_in_memory cdt cv (w2n dw) m) /\
      (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size cdt) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tm.t_mem <=> i IN tn.t_mem)) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))) ==>
  !dst src sa sb fn G tn s dw sw.
  compile_store_memory_typed ce (Var dst) (TupleT dts) (Var src) sty sa = ((),sb) /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\
  lookup_var dst s = SOME dw /\ lookup_var src s = SOME sw /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  w2n sw + type_memory_size stv < dimword(:256) /\
  regions_disjoint (w2n sw) (type_memory_size stv) (w2n dw) (type_memory_size dtv) /\
  ptr_covers G tn dst s (type_memory_size dtv) /\
  ptr_covers G tn src s (type_memory_size stv) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory stv v (w2n sw) m) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==> val_in_memory dtv v (w2n dw) m) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `?sts. sty = TupleT sts` by metis_tac[typed_copy_tuple_widening] >> gvs[] >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
      vyperValueTheory.evaluate_types_OPT_MMAP] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def] >>
  `LIST_REL (type_widens_to tenv) sts dts` by
    (irule typed_copy_tuple_children_widen >>
     conj_tac >- metis_tac[] >>
     drule typed_copy_tuple_widening >> simp[] >> strip_tac >> simp[]) >>
  suspend "tuple"
QED

Resume typed_copy_return_tuple_step[tuple]:
  qabbrev_tac `eligible = \cd cs cdt cst cv.
    MEM cd dts /\ type_widens_to tenv cs cd /\
    evaluate_type tenv cs = SOME cst /\ evaluate_type tenv cd = SOME cdt /\
    value_has_type cst cv /\ value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv` >>
  `LENGTH sts = LENGTH dts /\ LENGTH tvs' = LENGTH dts /\
   LENGTH tvs = LENGTH dts /\ LENGTH l = LENGTH dts /\
   (!i. i < LENGTH dts ==>
     type_memory_bytes ce (EL i dts) = type_memory_size (EL i tvs') /\
     type_memory_bytes ce (EL i sts) = type_memory_size (EL i tvs) /\
     val_wf (EL i tvs') (EL i l) /\ val_wf (EL i tvs) (EL i l) /\
     eligible (EL i dts) (EL i sts) (EL i tvs') (EL i tvs) (EL i l))` by
    (irule typed_copy_return_fields_semantics >>
     ntac 4 (conj_tac >- gvs[valueEncodingTheory.val_wf_def]) >>
     qexists_tac `tenv` >> simp[Abbr `eligible`] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def,
       is_word_type_def, is_bytestring_type_def] >>
  strip_tac >> suspend "execute"
QED

Resume typed_copy_return_tuple_step[execute]:
  drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
    typed_copy_return_fields_counted >>
  disch_then (qspec_then `eligible` mp_tac) >>
  disch_then (qspec_then `D` mp_tac) >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qspecl_then [`tvs'`, `tvs`, `l`] mp_tac) >>
  disch_then (qspec_then `fn` mp_tac) >>
  disch_then (qspec_then `G` mp_tac) >>
  disch_then (qspec_then `tn` mp_tac) >>
  disch_then (qspecl_then [`s`, `dw`, `sw`] mp_tac) >>
  (impl_tac >- suspend "premises") >>
  strip_tac >> suspend "finish"
QED

Resume typed_copy_return_tuple_step[premises]:
  simp[Once valueEncodingTheory.type_memory_size_def] >>
  conj_tac >- suspend "child" >>
  fs[valueEncodingTheory.type_memory_size_def,
     valueEncodingProofsTheory.type_memory_size_list_sum] >>
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  rpt strip_tac >> irule tuple_in_memory_robust_element >> simp[] >>
  qpat_x_assum `!m. mem_agree_outside _ _ m ==> _` mp_tac >>
  simp[valueEncodingTheory.val_in_memory_def] >> metis_tac[]
QED

Resume typed_copy_return_tuple_step[finish]:
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t)` >>
  qexistsl_tac [`H`, `tm`, `t`] >>
  simp[valueEncodingTheory.type_memory_size_def,
       valueEncodingProofsTheory.type_memory_size_list_sum] >>
  rpt strip_tac >> irule typedCopyReturnFieldLayoutPtrTheory.typed_copy_fields_robust_tuple >> simp[] >>
  qexistsl_tac [`t.vs_memory`, `tm.t_mem`] >> simp[] >>
  rpt gen_tac >> strip_tac >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  simp[]
QED

Resume typed_copy_return_tuple_step[child]:
  rpt gen_tac >> simp[Abbr `eligible`] >> strip_tac >>
  `type_rank ce.ce_struct_fields dt < type_rank ce.ce_struct_fields (TupleT dts)` by
    metis_tac[typedCopyDomainTheory.member_rank_lt_tuple] >>
  qpat_x_assum `!cd cs cdt cst cv. _` drule >>
  disch_then (drule_at (Pat `type_widens_to _ _ _`)) >>
  disch_then (qspecl_then [`dtv`, `stv`, `v`] mp_tac) >> simp[]
QED

Finalise typed_copy_return_tuple_step
