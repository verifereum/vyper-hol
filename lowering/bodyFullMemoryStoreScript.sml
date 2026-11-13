(* The aggregate-store dispatch retains one joint copy endpoint. *)
Theory bodyFullMemoryStore
Ancestors
  bodyFullMemoryCopy typedCopyOriginPtr typedMemoryCopy
  memoryLayoutDefs memoryLayoutSource memoryLayoutRel memoryValueEncoding
  context compileEnv bodyPtrDefs fragGasOriginPtr
  valueEncoding valueEncodingDefs venomState

Theorem body_full_memory_store_path:
  compile_store_memory cenv (Var xs) (Var xd) dty sty sa = ((),sb) /\
  ~is_word_type dty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `(dty = sty \/ tuple_memory_layout_eq dty sty) /\ ~is_bytestring_type dty`
  >- suspend "flat" >>
  `is_bytestring_type dty ==> is_bytestring_type sty` by
    metis_tac[typed_copy_bytestring_source] >>
  `compile_store_memory_typed cenv (Var xd) dty (Var xs) sty sa = ((),sb)` by
    (Cases_on `is_bytestring_type dty`
     >- (gvs[compile_store_memory_def] >>
         once_rewrite_tac[compile_store_memory_typed_def] >> simp[]) >>
     gvs[compile_store_memory_def]) >>
  drule_all compile_store_memory_typed_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[] >>
  fs[typed_copy_state_frame_def] >> metis_tac[]
QED

Resume body_full_memory_store_path[flat]:
  `compile_copy_memory (Var xd) (Var xs) (type_memory_size dtv) sa = ((),sb)` by
    gvs[compile_store_memory_def] >>
  `tuple_memory_layout_eq dty sty ==>
    memory_layout_key dty = memory_layout_key sty` by
    (Cases_on `dty` >> Cases_on `sty` >>
     simp[tuple_memory_layout_eq_def,memory_layout_key_tuple]) >>
  `memory_layout_key dty = memory_layout_key sty` by metis_tac[] >>
  `memory_layout_rel dtv stv` by metis_tac[memory_layout_key_evaluated] >>
  `type_memory_size dtv = type_memory_size stv` by fs[memory_layout_rel_def] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory dtv v (w2n sw) mem` by
    (rpt strip_tac >> irule memory_value_rel_val_in_memory >> simp[] >>
     irule memory_layout_rel_value >> qexists_tac `stv` >> simp[] >>
     irule val_in_memory_memory_value_rel >> simp[]) >>
  irule body_full_memory_copy_path >> simp[] >>
  qexistsl_tac [`sw`,`xd`,`xs`] >> fs[]
QED

Finalise body_full_memory_store_path
