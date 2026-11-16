(* Zero physical buffers need neither a variable operand nor source coverage. *)
Theory bodyFullStructLitZeroStore
Ancestors
  bodyPtrDefs wideningZeroLayout valueEncodingProofs
  valueCopyBytes contextProps fragGasOriginPtr typedMemoryCopy

Theorem structlit_zero_physical_store_path:
  compile_store_memory cenv src (Var xd) dty sty sa = ((),sb) /\
  ~is_word_type dty /\ (is_bytestring_type dty ==> is_bytestring_type sty) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  type_memory_size stv = 0 /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xd /\ eval_operand src s = SOME sw /\ op_taint tn src = {} /\
  lookup_var xd s = SOME dw /\
  (!mem. bodyPtrDefs$mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory stv v (w2n sw) mem) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
  bodyPtrDefs$ptr_covers G tn xd s (type_memory_size dtv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. bodyPtrDefs$mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory dtv v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `sty = dty` by metis_tac[type_widens_to_zero_layout] >> gvs[] >>
  `~is_bytestring_type dty` by
    (strip_tac >> drule bytestring_memory_bytes_positive >>
     disch_then (qspec_then `cenv` mp_tac) >> simp[]) >>
  `sb = sa` by
    gvs[contextTheory.compile_store_memory_def, compile_copy_memory_zero] >>
  gvs[] >> qexistsl_tac [`s`, `G`, `tn`] >>
  simp[gas_origin_ptr_path_rules, typed_copy_state_frame_def, typed_copy_frame_def,
       return_zero_wf_memory, venomStateTheory.venom_state_component_equality]
QED
