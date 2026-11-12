(* Counted indexed child execution and robust array-prefix advancement. *)
Theory typedCopyReturnIndexBodyPtr
Ancestors typedCopyReturnIndexAddressPtr typedCopyReturnArrayLayoutPtr
  typedCopyReturnBasePtr typedCopyRobustTransportPtr typedMemoryCopy
  exprSimBufferStore emitHelperProps stmtFragPtr fragGasPathPtr
  compileEnv bodyPtrDefs venomState words finite_map list arithmetic

Theorem typed_copy_exterior_singleton[local]:
  (!j. j < off \/ off + len <= j ==>
    mem_byte_at mem' j = mem_byte_at mem j /\ (j IN tn' <=> j IN tn)) ==>
  (!j. ~(off <= j /\ j < off + len) ==>
    mem_bytes_at j 1 mem' = mem_bytes_at j 1 mem /\ (j IN tn' <=> j IN tn))
Proof
  strip_tac >> gen_tac >> strip_tac >>
  first_x_assum (qspec_then `j` mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >> simp[] >>
  irule LIST_EQ >> simp[buffer_window_byte]
QED

Theorem typed_copy_index_body_counted:
  !ce tenv sty dty stv dtv D ctx PG.
  (!sc sd sp dp fn G tn s a b v.
    compile_store_memory_typed ce (Var dp) dty (Var sp) sty sc = ((),sd) /\
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    not_fresh_at sc sp /\ not_fresh_at sc dp /\ fn_has_code sc sd fn /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sc.cs_current_bb /\
    s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    lookup_var sp s = SOME a /\ lookup_var dp s = SOME b /\
    w2n a + type_memory_size stv < dimword(:256) /\
    w2n b + type_memory_size dtv < dimword(:256) /\
    regions_disjoint (w2n a) (type_memory_size stv) (w2n b) (type_memory_size dtv) /\
    op_taint tn (Var sp) = {} /\ op_taint tn (Var dp) = {} /\
    (type_memory_size stv <> 0 ==> ptr_covers G tn sp s (type_memory_size stv)) /\
    (type_memory_size dtv <> 0 ==> ptr_covers G tn dp s (type_memory_size dtv)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a) m) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = sd.cs_current_bb /\
      t.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sc (w2n b) (type_memory_size dtv) s t /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        val_in_memory dtv v (w2n b) m) /\
      (!j. j < w2n b \/ w2n b + type_memory_size dtv <= j ==>
        mem_byte_at t.vs_memory j = mem_byte_at s.vs_memory j /\
        (j IN tm.t_mem <=> j IN tn.t_mem)) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!p. not_fresh_at sc p ==> lookup_var p t = lookup_var p s /\
        FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))) ==>
  !sb c1 c2 c3 si se ctr so doff src dst sp dp fn G tn s a b f i N src_span dst_span.
    emit_op MUL [Var ctr;Lit (n2w (type_memory_size stv))] sb = (Var so,c1) /\
    emit_op MUL [Var ctr;Lit (n2w (type_memory_size dtv))] c1 = (Var doff,c2) /\
    emit_op ADD [Var src;Var so] c2 = (Var sp,c3) /\
    emit_op ADD [Var dst;Var doff] c3 = (Var dp,si) /\
    compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se) /\
    fn_has_code sb c1 fn /\ fn_has_code c1 c2 fn /\
    fn_has_code c2 c3 fn /\ fn_has_code c3 si fn /\ fn_has_code si se fn /\
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    (!j. j < N ==> value_has_type stv (f j) /\ value_has_type dtv (f j) /\
      val_wf stv (f j) /\ val_wf dtv (f j)) /\
    not_fresh_at sb ctr /\ not_fresh_at sb src /\ not_fresh_at sb dst /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
    (src_span <> 0 ==> ptr_covers G tn src s src_span) /\
    (dst_span <> 0 ==> ptr_covers G tn dst s dst_span) /\
    N * type_memory_size stv <= src_span /\ N * type_memory_size dtv <= dst_span /\ i < N /\
    w2n a + src_span < dimword(:256) /\ w2n b + dst_span < dimword(:256) /\
    regions_disjoint (w2n a) src_span (w2n b) dst_span /\
    (!j. j < N ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv (f j) (w2n a + j * type_memory_size stv) m) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      typed_copy_index_prefix f dtv (w2n b) N i m) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = se.cs_current_bb /\
      t.vs_inst_idx = LENGTH se.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sb (w2n b) dst_span s t /\
      (!j. j < N ==> !m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        val_in_memory stv (f j) (w2n a + j * type_memory_size stv) m) /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        typed_copy_index_prefix f dtv (w2n b) N (SUC i) m) /\
      (!j. j < w2n b \/ w2n b + dst_span <= j ==>
        mem_byte_at t.vs_memory j = mem_byte_at s.vs_memory j /\
        (j IN tm.t_mem <=> j IN tn.t_mem)) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!p. not_fresh_at sb p ==> lookup_var p t = lookup_var p s /\
        FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  `i * type_memory_size stv + type_memory_size stv <= src_span /\
   i * type_memory_size dtv + type_memory_size dtv <= dst_span` by
    (conj_tac >> irule LESS_EQ_TRANS >>
     first_assum (irule_at (Pos last)) >>
     simp[GSYM MULT_CLAUSES] >> irule LESS_MONO_MULT >> decide_tac) >>
  drule_all typed_copy_index_address_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 H1 tm1 (OK u)` >>
  `u.vs_memory = s.vs_memory` by gvs[venom_state_component_equality] >>
  `w2n (n2w (w2n a + i * type_memory_size stv):256 word) =
      w2n a + i * type_memory_size stv /\
   w2n (n2w (w2n b + i * type_memory_size dtv):256 word) =
      w2n b + i * type_memory_size dtv` by (conj_tac >> simp[]) >>
  `regions_disjoint (w2n a + i * type_memory_size stv) (type_memory_size stv)
     (w2n b + i * type_memory_size dtv) (type_memory_size dtv)` by
    (fs[regions_disjoint_def] >> decide_tac) >>
  `value_has_type stv (f i) /\ value_has_type dtv (f i) /\
   val_wf stv (f i) /\ val_wf dtv (f i)` by simp[] >>
  `w2n a + i * type_memory_size stv + type_memory_size stv < dimword(:256) /\
   w2n b + i * type_memory_size dtv + type_memory_size dtv < dimword(:256)` by decide_tac >>
  `(!m. mem_agree_outside tm1.t_mem u.vs_memory m ==>
     val_in_memory stv (f i) (w2n a + i * type_memory_size stv) m)` by simp[] >>
  qpat_x_assum `!sc sd sp dp fn G tn s a b v. _`
    (qspecl_then [`si`,`se`,`sp`,`dp`] mp_tac) >>
  disch_then (drule_at (Pat `lookup_var sp _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`fn`,`H1`,`tm1`,`f i`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `sb.cs_next_var <= si.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >> decide_tac) >>
  qexistsl_tac [`H`,`tm`,`t`] >>
  conj_tac >- metis_tac[gas_path_ptr_then,ADD] >> simp[] >>
  conj_tac >- suspend "frame" >>
  conj_tac >- suspend "source" >>
  conj_tac >- suspend "prefix" >>
  conj_tac >- suspend "exterior" >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED

Resume typed_copy_index_body_counted[frame]:
  irule typed_copy_state_frame_trans >> qexists_tac `u` >> conj_tac
  >- (gvs[typed_copy_state_frame_def,typed_copy_frame_def,
          venom_state_component_equality]) >>
  irule typed_copy_state_frame_subinterval >>
  qexistsl_tac [`w2n b + i * type_memory_size dtv`,`type_memory_size dtv`] >>
  simp[] >> gvs[typed_copy_state_frame_def] >> metis_tac[not_fresh_at_mono]
QED

Resume typed_copy_index_body_counted[source]:
  drule (ONCE_REWRITE_RULE[ADD_COMM] typed_copy_exterior_singleton) >> disch_tac >>
  rpt strip_tac >> irule robust_representation_exterior_frame >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`w2n b + i * type_memory_size dtv`,`s.vs_memory`,`t.vs_memory`,
    `type_memory_size dtv`,`tn.t_mem`,`tm.t_mem`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  `j * type_memory_size stv + type_memory_size stv <= src_span` by
    (drule typed_copy_array_subinterval >>
     disch_then (qspecl_then [`0`,`type_memory_size stv`] mp_tac) >>
     simp[] >> decide_tac) >>
  fs[regions_disjoint_def] >> decide_tac
QED

Resume typed_copy_index_body_counted[prefix]:
  drule (ONCE_REWRITE_RULE[ADD_COMM] typed_copy_exterior_singleton) >> disch_tac >>
  rpt strip_tac >> irule typed_copy_index_prefix_robust_step >>
  conj_tac >- (rpt strip_tac >> metis_tac[LESS_TRANS]) >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`,`t.vs_memory`,`tn.t_mem`,`tm.t_mem`] >>
  simp[ADD_COMM] >> metis_tac[]
QED

Resume typed_copy_index_body_counted[exterior]:
  rpt strip_tac >>
  `j < w2n b + i * type_memory_size dtv \/
   type_memory_size dtv + (w2n b + i * type_memory_size dtv) <= j` by decide_tac >>
  metis_tac[]
QED

Finalise typed_copy_index_body_counted
