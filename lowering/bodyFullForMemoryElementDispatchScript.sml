Theory bodyFullForMemoryElementDispatch
Ancestors
  bodyFullForArray stmtLowering compileEnv memLocDefs venomInst venomState
  typedMemoryCopy typedCopyDomain localValueStoreProps valueCopyBytes
  eventTopicValueProps valueTypingMemoryProps valueEncoding valueEncodingDefs
  vfmConstants vyperValue vyperTyping vyperTypeSystem
  memoryLayoutSource memoryLayoutRel layoutStoreProps
  fragGasOriginPtr reasonCopySourcePtr allocationPtr ptrDiscipline context
  bodyPtrDefs finite_map list arithmetic pred_set words

(* Select the store used for a live memory child. The write extent can be
   smaller than the saved item allocation, which remains covered in full. *)
Theorem for_memory_element_dispatch_joint_frame:
  compile_iter_elem_copy c (Var xs) (Var xd) bytes LocMemory F dty sty sa = ((),sb) /\
  EL k vs = Value v /\
  acyclic_struct_metadata c.ce_struct_fields /\
  sfields_tenv_consistent c.ce_struct_fields tenv /\
  (!name fields. FLOOKUP c.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  type_memory_bytes c dty = type_memory_size dtv /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  (0 < type_memory_size stv \/ ~(dty = sty \/ tuple_memory_layout_eq dty sty) ==>
    not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
    ptr_covers G tn xs s (type_memory_size stv)) /\
  not_fresh_at sa xd /\ lookup_var xd s = SOME dw /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,capacity) /\
  ptr_covers G tn xd s capacity /\ type_memory_size dtv <= capacity /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
  (w2n sw + type_memory_size stv <= w2n dw \/ w2n dw + type_memory_size dtv <= w2n sw) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n t Gf tnf.
    n <= capacity /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) n s t /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    FLOOKUP t.vs_allocas aid = SOME (w2n dw,capacity) /\
    lookup_var xd t = SOME dw /\ ptr_covers Gf tnf xd t capacity
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type dty` >- suspend "word" >>
  Cases_on `is_bytestring_type dty` >- suspend "bytestring" >>
  Cases_on `dty = sty \/ tuple_memory_layout_eq dty sty` >- suspend "bulk" >>
  suspend "relayout"
QED

Resume for_memory_element_dispatch_joint_frame[word]:
  `sty = dty` by (drule_all typed_copy_word_widening >> simp[]) >>
  `type_memory_size stv = 32 /\ type_memory_size dtv = 32` by
    (drule_all evaluated_word_memory_size >> fs[]) >>
  `not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\ ptr_covers G tn xs s 32` by fs[] >>
  `w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next` by fs[] >>
  `32 <= capacity` by fs[] >>
  drule_all for_memory_word_element_joint_frame >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`32`,`t`,`Gf`,`tnf`] >> simp[]
QED

Resume for_memory_element_dispatch_joint_frame[bytestring]:
  `is_bytestring_type sty` by (drule_all typed_copy_bytestring_source >> simp[]) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm
                    (qx_choose_then `len` (CONJUNCTS_THEN ASSUME_TAC)))
    `?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
            (?str. v = StringV str /\ len = LENGTH str)) /\
           val_memory_size v = 32 + 32 * word_size len`
  >- (drule_all bytestring_type_value >> strip_tac >> Cases_on `v` >>
      fs[value_has_type_def, val_memory_size_def] >> metis_tac[]) >>
  qabbrev_tac `n = 32 + 32 * word_size len` >>
  `n <= type_memory_size stv /\ n <= type_memory_size dtv` by
    metis_tac[bytestring_value_size_bound] >>
  `0 < n` by simp[Abbr `n`] >>
  `len <= 32 * word_size len` by simp[word_size_capacity] >>
  `len+31 < dimword (:256) /\ n < dimword (:256) /\ n <= capacity /\
   w2n sw+n < dimword (:256) /\ w2n dw+n < dimword (:256) /\
   w2n sw+n <= s.vs_alloca_next /\ w2n dw+n <= s.vs_alloca_next` by
    (qpat_assum `Abbrev (n = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     decide_tac) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `w2n sw+n <= w2n dw \/ w2n dw+n <= w2n sw`
  >- decide_tac >>
  `0 < type_memory_size stv` by decide_tac >>
  `not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
   ptr_covers G tn xs s (type_memory_size stv)` by fs[] >>
  `ptr_covers G tn xs s n` by (irule ptr_covers_mono >> metis_tac[]) >>
  `n = 32 + 32 * ((len+31) DIV 32)` by simp[Abbr `n`, word_size_def] >>
  drule_all for_memory_bytes_element_joint_frame >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`n`,`t`,`Gf`,`tnf`] >> asm_rewrite_tac[]
QED

Resume for_memory_element_dispatch_joint_frame[bulk]:
  `type_memory_size stv = type_memory_size dtv` by
    (drule bulk_store_layout_keys >> strip_tac >>
     drule_all memory_layout_key_evaluated >> simp[memory_layout_rel_def]) >>
  qabbrev_tac `n = type_memory_size dtv` >>
  `compile_iter_elem_copy c (Var xs) (Var xd) n LocMemory F dty sty sa = ((),sb)` by
    (qpat_assum `compile_iter_elem_copy _ _ _ bytes _ _ _ _ _ = _` mp_tac >>
     simp[NoAsms, compile_iter_elem_copy_def]) >>
  qpat_x_assum `compile_iter_elem_copy _ _ _ bytes _ _ _ _ _ = _` kall_tac >>
  `n <= capacity` by simp[] >>
  `(0 < n ==>
      not_fresh_at sa xs /\ not_fresh_at sa xd /\ lookup_var xs s = SOME sw /\
      ptr_covers G tn xs s n /\
      w2n sw + n < dimword (:256) /\ w2n dw + n < dimword (:256) /\
      w2n sw + n <= s.vs_alloca_next /\ w2n dw + n <= s.vs_alloca_next /\
      (w2n sw + n <= w2n dw \/ w2n dw + n <= w2n sw) /\
      allocas_from lo s /\ lo <= s.vs_alloca_next /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func)` by
    (disch_tac >> fs[]) >>
  `n = type_memory_size dtv` by simp[Abbr `n`] >>
  qpat_x_assum `type_memory_bytes c dty = n` (assume_tac o SYM) >>
  drule_all for_memory_bulk_element_joint_frame >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`n`,`t`,`Gf`,`tnf`] >> asm_rewrite_tac[]
QED

Resume for_memory_element_dispatch_joint_frame[relayout]:
  `not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
   ptr_covers G tn xs s (type_memory_size stv)` by fs[] >>
  `dty <> sty /\ ~tuple_memory_layout_eq dty sty` by fs[] >>
  drule_all for_memory_relayout_element_joint_frame >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`type_memory_size dtv`,`t`,`Gf`,`tnf`] >> asm_rewrite_tac[]
QED

Finalise for_memory_element_dispatch_joint_frame
