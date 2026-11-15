(* Joint offset-prefix application of a recursive member store. *)
Theory fullStoreSlotsMemberStep
Ancestors
  fullStoreSlotsMembers fullStoreSlotsMemberFrame
  typedCopyOriginPtrBase fragGasOriginPtr context emitHelper exprLoweringProps
  loweringStateRelDefs compileEnv venomState ptrDiscipline venomInst
  finite_map list arithmetic words stateFrame stmtLoweringMono
  typedMemoryCopy fragExec pair

Theorem store_slots_member_code:
  compile_lit_byte_offset (Var root) mo sa = (src,sb) /\
  compile_lit_byte_offset dst so sb = (slot,sc) /\
  compile_store_slots cenv src slot ty tr sc = ((),sd) /\
  fn_has_code sa sd func ==>
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_has_code sc sd func /\
  (!p. not_fresh_at sa p ==> not_fresh_at sb p /\ not_fresh_at sc p)
Proof
  strip_tac >>
  `ci_mono sa sb /\ ci_mono sb sc /\ ci_mono sc sd` by
    metis_tac[ci_mono_compile_lit_byte_offset,cj 1 ci_mono_compile_store_slots,SND] >>
  `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd` by
    metis_tac[ci_mono_def] >>
  `fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_has_code sc sd func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  simp[] >> rpt strip_tac >>
  metis_tac[ci_mono_def,freshWritesTheory.not_fresh_at_mono,LESS_EQ_TRANS]
QED

Theorem store_slots_member_offsets_origin_ptr:
  compile_lit_byte_offset (Var root) mo sa = (src,sb) /\
  compile_lit_byte_offset dst so sb = (slot,sc) /\
  not_fresh_at sa root /\ (!x. dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var root s = SOME sw /\ ptr_covers G tn root s capacity /\
  mo + n <= capacity /\ w2n sw + mo < dimword(:256) /\
  eval_operand dst s = SOME dw /\ op_taint tn dst = {} ==>
  ?out Gf tf u. src = Var out /\ not_fresh_at sc out /\
    (!x. slot = Var x ==> not_fresh_at sc x) /\
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~u.vs_halted /\
    lookup_var out u = SOME (sw+n2w mo) /\ ptr_covers Gf tf out u n /\
    eval_operand slot u = SOME (dw+n2w so) /\ op_taint tf slot = {} /\
    op_prov Gf slot = op_prov G dst /\
    execution_frame u = execution_frame s /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `ci_mono sa sb /\ ci_mono sb sc` by
    metis_tac[ci_mono_compile_lit_byte_offset,SND] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sb p` by
    metis_tac[ci_mono_def,freshWritesTheory.not_fresh_at_mono] >>
  drule_all store_slots_source_offset_origin_ptr >>
  disch_then (qx_choose_then `out` (qx_choose_then `Gp`
    (qx_choose_then `tp` (qx_choose_then `p` strip_assume_tac)))) >> gvs[] >>
  `not_fresh_at sb out` by
    (qpat_assum `compile_lit_byte_offset (Var root) _ _ = _`
       (mp_then Any mp_tac placeStoreSlotsTheory.store_slots_lit_offset_fresh) >> simp[]) >>
  `not_fresh_at sc out` by
    metis_tac[ci_mono_def,freshWritesTheory.not_fresh_at_mono] >>
  `!x. slot = Var x ==> not_fresh_at sc x` by
    (drule_at (Pat `compile_lit_byte_offset dst _ _ = _`)
       placeStoreSlotsTheory.store_slots_lit_offset_fresh >> simp[]) >>
  `eval_operand dst p = SOME dw /\ op_taint tp dst = {} /\
   op_prov Gp dst = op_prov G dst` by
    (Cases_on `dst` >> gvs[eval_operand_def,op_taint_def,op_prov_def]) >>
  `allocas_from lo p` by metis_tac[allocas_from_def] >>
  drule_all store_slots_clean_offset_origin_ptr >>
  disch_then (qspec_then `Gp` (qx_choose_then `Gf`
    (qx_choose_then `tf` (qx_choose_then `u` strip_assume_tac)))) >>
  qexistsl_tac [`Gf`,`tf`,`u`] >> simp[] >>
  conj_tac >- (rpt gen_tac >> metis_tac[gas_origin_ptr_path_append,APPEND_NIL]) >>
  conj_tac >- (gvs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  fs[execution_frame_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem store_slots_member_step_origin_ptr:
  (!root slot tr sa sb func s sw dw writes G tn.
    compile_store_slots cenv (Var root) slot ty tr sa = ((),sb) /\
    not_fresh_at sa root /\ (!x. slot = Var x ==> not_fresh_at sa x) /\
    lookup_var root s = SOME sw /\ eval_operand slot s = SOME dw /\
    op_prov G slot = NONE /\ op_taint tn slot = {} /\ ptr_covers G tn root s (val_store_size tv v) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n sw) m) /\
    w2n sw + type_memory_size tv < dimword(:256) /\
    w2n dw + type_slot_size tv <= dimword(:256) /\
    encode_value tv v = SOME writes /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
    w2n sw + val_store_size tv v <= s.vs_alloca_next ==>
    ?Gf tf u ks.
      (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,Gf,tf)) /\
      store_copy_normalize s u =
        FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
          (mload (w2n sw+32*j) s) q) s ks /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      (if tr then tf.t_trans else tf.t_stor) =
        FOLDL (\ta j. key_update ta (dw+n2w j)
          (mem_word_taint tn.t_mem (w2n sw+32*j)))
          (if tr then tn.t_trans else tn.t_stor) ks /\
      (if tr then tf.t_stor else tf.t_trans) =
        (if tr then tn.t_stor else tn.t_trans) /\
      (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
      u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts) /\
  compile_lit_byte_offset (Var root) mo sa = (src,sb) /\
  compile_lit_byte_offset dst so sb = (slot,sc) /\
  compile_store_slots cenv src slot ty tr sc = ((),sd) /\
  not_fresh_at sa root /\ (!x. dst = Var x ==> not_fresh_at sa x) /\
  lookup_var root s = SOME sw /\ ptr_covers G tn root s capacity /\
  mo + val_store_size tv v <= capacity /\
  eval_operand dst s = SOME dw /\ op_prov G dst = NONE /\
  op_taint tn dst = {} /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n sw+mo) m) /\
  w2n sw+mo+type_memory_size tv < dimword(:256) /\
  w2n dw+so < dimword(:256) /\
  w2n dw+so+type_slot_size tv <= dimword(:256) /\
  w2n sw+mo+val_store_size tv v <= s.vs_alloca_next /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sd func /\ fn_inst_ids_distinct func /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p tp u Gf tf ks.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    execution_frame p = execution_frame s /\
    tp.t_mem = tn.t_mem /\ tp.t_imm = tn.t_imm /\
    tp.t_stor = tn.t_stor /\ tp.t_trans = tn.t_trans /\
    store_copy_normalize p u =
      FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w so+n2w j)
        (mload (w2n sw+mo+32*j) p) q) p ks /\
    u.vs_memory = p.vs_memory /\ tf.t_mem = tp.t_mem /\ tf.t_imm = tp.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) =
      FOLDL (\ta j. key_update ta (dw+n2w so+n2w j)
        (mem_word_taint tp.t_mem (w2n sw+mo+32*j)))
        (if tr then tp.t_trans else tp.t_stor) ks /\
    (if tr then tf.t_stor else tf.t_trans) =
      (if tr then tp.t_stor else tp.t_trans) /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all store_slots_member_code >> strip_tac >>
  `w2n sw+mo < dimword(:256)` by decide_tac >>
  drule_all store_slots_member_offsets_origin_ptr >>
  disch_then (qx_choose_then `out` (qx_choose_then `Gp`
    (qx_choose_then `tp` (qx_choose_then `p` strip_assume_tac)))) >> gvs[] >>
  `p.vs_memory = s.vs_memory /\ p.vs_alloca_next = s.vs_alloca_next /\
   p.vs_allocas = s.vs_allocas /\ p.vs_labels = s.vs_labels /\
   p.vs_call_ctx = s.vs_call_ctx` by
    gvs[execution_frame_def,venom_state_component_equality] >>
  `w2n (sw+n2w mo) = w2n sw+mo /\
   w2n (dw+n2w so) = w2n dw+so` by
    (simp[w2n_add_2] >> decide_tac) >>
  `allocas_from lo p` by metis_tac[allocas_from_def] >>
  qpat_x_assum `!root slot tr sa sb func s sw dw G tn. _` drule >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  simp[eval_operand_def] >> disch_then drule_all >>
  disch_then (qx_choose_then `Gu` (qx_choose_then `tu`
    (qx_choose_then `u` (qx_choose_then `ks` strip_assume_tac)))) >>
  qexistsl_tac [`p`,`tp`,`u`,`Gu`,`tu`,`ks`] >>
  conj_tac >- (rpt gen_tac >> metis_tac[gas_origin_ptr_path_append,APPEND_NIL]) >>
  fs[execution_frame_def] >> rpt strip_tac >> metis_tac[]
QED
