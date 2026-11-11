(* Counted heterogeneous field copies, separated from metadata and rank. *)
Theory typedCopyReturnFieldsPtr
Ancestors typedCopyReturnFieldAddressPtr typedCopyReturnFieldLayoutPtr
  assignBasePtrFieldsCompose assignBasePtrFieldOffsets assignBasePtrByteOffset fragExec
  exprLoweringProps exprSimTypedAlloc exprSimBufferStore
  typedMemoryCopy typedCopyRobustTransportPtr appendStorageGhostPtr
  contextCodegenRelProps fragGasPathPtr bodyPtrDefs compileEnv stmtFragPtr
  words finite_map list arithmetic venomState

Theorem typed_copy_address_state_frame[local]:
  (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) ==>
  typed_copy_state_frame sa off len s u
Proof
  strip_tac >> simp[typed_copy_state_frame_def] >>
  gvs[venom_state_component_equality]
QED

Theorem typed_copy_field_frame_accumulate[local]:
  sa.cs_next_var <= sc.cs_next_var /\
  typed_copy_state_frame sa off len s u /\
  typed_copy_state_frame sc (off+delta) n u t /\
  delta+n <= len ==>
  typed_copy_state_frame sa off len s t
Proof
  strip_tac >> irule typed_copy_state_frame_trans >> qexists_tac `u` >>
  simp[] >> irule typed_copy_state_frame_subinterval >>
  qexistsl_tac [`off+delta`, `n`] >> simp[] >>
  gvs[typed_copy_state_frame_def] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem typed_copy_return_field_path[local]:
  !ce dt st dtv stv v D ctx PG.
  (!dp sp sc sd fn G tn s dw sw.
    compile_store_memory_typed ce (Var dp) dt (Var sp) st sc = ((),sd) /\
    not_fresh_at sc dp /\ not_fresh_at sc sp /\
    lookup_var dp s = SOME dw /\ lookup_var sp s = SOME sw /\
    w2n dw + type_memory_size dtv < dimword(:256) /\
    w2n sw + type_memory_size stv < dimword(:256) /\
    regions_disjoint (w2n sw) (type_memory_size stv)
      (w2n dw) (type_memory_size dtv) /\
    ptr_covers G tn dp s (type_memory_size dtv) /\
    ptr_covers G tn sp s (type_memory_size stv) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n sw) m) /\
    fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\
    s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = sd.cs_current_bb /\
      t.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sc (w2n dw) (type_memory_size dtv) s t /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        val_in_memory dtv v (w2n dw) m) /\
      (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tm.t_mem <=> i IN tn.t_mem)) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))) ==>
  !dst src doff soff sa sm sc sd dop sop fn G tn s dw sw dtot stot.
    compile_with_byte_offset (Var dst) doff sa = (dop,sm) /\
    compile_with_byte_offset (Var src) soff sm = (sop,sc) /\
    compile_store_memory_typed ce dop dt sop st sc = ((),sd) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var dst s = SOME dw /\ lookup_var src s = SOME sw /\
    ptr_covers G tn dst s dtot /\ ptr_covers G tn src s stot /\
    doff + type_memory_size dtv <= dtot /\
    soff + type_memory_size stv <= stot /\
    w2n dw + dtot < dimword(:256) /\ w2n sw + stot < dimword(:256) /\
    regions_disjoint (w2n sw) stot (w2n dw) dtot /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n sw+soff) m) /\
    fn_has_code sa sd fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = sd.cs_current_bb /\
      t.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sa (w2n dw) dtot s t /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        val_in_memory dtv v (w2n dw+doff) m) /\
      (!i. ~(w2n dw+doff <= i /\
              i < w2n dw+doff+type_memory_size dtv) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tm.t_mem <=> i IN tn.t_mem)) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  `ci_mono sc sd` by metis_tac[typed_return_store_mono] >>
  `cs_extends sa sc /\ sa.cs_next_var <= sc.cs_next_var` by
    metis_tac[assign_base_offset_extends, cs_extends_trans, LESS_EQ_TRANS] >>
  `cs_extends sc sd` by gvs[exprLoweringPropsTheory.ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `w2n dw+doff < dimword(:256) /\ w2n sw+soff < dimword(:256)` by decide_tac >>
  drule_all typed_copy_field_addresses_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 Gm tm (OK u)` >>
  `u.vs_memory = s.vs_memory` by fs[venom_state_component_equality] >>
  `w2n (n2w (w2n dw+doff):256 word) = w2n dw+doff /\
   w2n (n2w (w2n sw+soff):256 word) = w2n sw+soff` by simp[] >>
  `regions_disjoint (w2n sw+soff) (type_memory_size stv)
     (w2n dw+doff) (type_memory_size dtv)` by
    (fs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `w2n dw+doff+type_memory_size dtv < dimword(:256) /\
   w2n sw+soff+type_memory_size stv < dimword(:256)` by decide_tac >>
  gvs[] >>
  qpat_x_assum `!dp sp sc sd fn G tn s dw sw. _` drule >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`fn`, `Gm`, `tm`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >> rename1 `gas_path_ptr D 0 ctx fn PG Gm tm u 0 H tf (OK t)` >>
  qexistsl_tac [`H`, `tf`, `t`] >>
  conj_tac
  >- (qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
        (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  simp[] >> conj_tac >- suspend "frame" >>
  simp[] >> rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED

Resume typed_copy_return_field_path[frame]:
  irule typed_copy_field_frame_accumulate >>
  qexistsl_tac [`doff`, `type_memory_size dtv`, `sc`, `u`] >> simp[] >>
  irule typed_copy_address_state_frame >> metis_tac[]
QED

Finalise typed_copy_return_field_path

Theorem typed_copy_fields_source_frame[local]:
  !tvs vs src dst len tn mem tn' mem'.
    (!i. i < LENGTH tvs ==> val_wf (EL i tvs) (EL i vs)) /\
    regions_disjoint src (SUM (MAP type_memory_size tvs)) dst len /\
    (!i. i < LENGTH tvs ==> !m. mem_agree_outside tn mem m ==>
      val_in_memory (EL i tvs) (EL i vs)
        (src + SUM (MAP type_memory_size (TAKE i tvs))) m) /\
    (!x. ~(dst <= x /\ x < dst+len) ==>
      mem_bytes_at x 1 mem' = mem_bytes_at x 1 mem /\
      (x IN tn' <=> x IN tn)) ==>
    !i. i < LENGTH tvs ==> !m. mem_agree_outside tn' mem' m ==>
      val_in_memory (EL i tvs) (EL i vs)
        (src + SUM (MAP type_memory_size (TAKE i tvs))) m
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  irule robust_representation_exterior_frame >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`dst`, `mem`, `mem'`, `len`, `tn`, `tn'`] >>
  rpt conj_tac >- metis_tac[] >- metis_tac[] >- metis_tac[] >>
  drule tupleMemoryLayoutTheory.tuple_element_interval >>
  fs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem typed_copy_return_fields_counted:
  !ce R D ctx PG dts sts dtvs stvs vs dst src sa sb fn G tn s dw sw.
  LENGTH sts = LENGTH dts /\ LENGTH dtvs = LENGTH dts /\
  LENGTH stvs = LENGTH dts /\ LENGTH vs = LENGTH dts /\
  (!i. i < LENGTH dts ==>
    type_memory_bytes ce (EL i dts) = type_memory_size (EL i dtvs) /\
    type_memory_bytes ce (EL i sts) = type_memory_size (EL i stvs) /\
    val_wf (EL i dtvs) (EL i vs) /\ val_wf (EL i stvs) (EL i vs) /\
    R (EL i dts) (EL i sts) (EL i dtvs) (EL i stvs) (EL i vs)) /\
  (!dt st dtv stv v. R dt st dtv stv v ==>
    !dp sp sc sd fn G tn s dw sw.
    compile_store_memory_typed ce (Var dp) dt (Var sp) st sc = ((),sd) /\
    not_fresh_at sc dp /\ not_fresh_at sc sp /\
    lookup_var dp s = SOME dw /\ lookup_var sp s = SOME sw /\
    w2n dw + type_memory_size dtv < dimword(:256) /\
    w2n sw + type_memory_size stv < dimword(:256) /\
    regions_disjoint (w2n sw) (type_memory_size stv)
      (w2n dw) (type_memory_size dtv) /\
    ptr_covers G tn dp s (type_memory_size dtv) /\
    ptr_covers G tn sp s (type_memory_size stv) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n sw) m) /\
    fn_has_code sc sd fn /\ s.vs_current_bb = sc.cs_current_bb /\
    s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = sd.cs_current_bb /\
      t.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sc (w2n dw) (type_memory_size dtv) s t /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        val_in_memory dtv v (w2n dw) m) /\
      (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tm.t_mem <=> i IN tn.t_mem)) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))) /\
  compile_typed_copy_fields ce (Var dst) (Var src) dts sts 0 0 sa = ((),sb) /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\
  lookup_var dst s = SOME dw /\ lookup_var src s = SOME sw /\
  ptr_covers G tn dst s (SUM (MAP type_memory_size dtvs)) /\
  ptr_covers G tn src s (SUM (MAP type_memory_size stvs)) /\
  w2n dw + SUM (MAP type_memory_size dtvs) < dimword(:256) /\
  w2n sw + SUM (MAP type_memory_size stvs) < dimword(:256) /\
  regions_disjoint (w2n sw) (SUM (MAP type_memory_size stvs))
    (w2n dw) (SUM (MAP type_memory_size dtvs)) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  (!i. i < LENGTH dts ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (EL i stvs) (EL i vs)
      (w2n sw + SUM (MAP type_memory_size (TAKE i stvs))) m) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    typed_copy_state_frame sa (w2n dw) (SUM (MAP type_memory_size dtvs)) s t /\
    (!i. i < LENGTH dts ==> !m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      val_in_memory (EL i dtvs) (EL i vs)
        (w2n dw + SUM (MAP type_memory_size (TAKE i dtvs))) m) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + SUM (MAP type_memory_size dtvs)) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `field_inv = \ds ss doff soff sc H tm t.
    ?k. k <= LENGTH dts /\ ds = DROP k dts /\ ss = DROP k sts /\
      doff = SUM (MAP type_memory_size (TAKE k dtvs)) /\
      soff = SUM (MAP type_memory_size (TAKE k stvs)) /\
      sa.cs_next_var <= sc.cs_next_var /\
      typed_copy_state_frame sa (w2n dw) (SUM (MAP type_memory_size dtvs)) s t /\
      (!i. i < k ==> !m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        val_in_memory (EL i dtvs) (EL i vs)
          (w2n dw + SUM (MAP type_memory_size (TAKE i dtvs))) m) /\
      (!i. ~(w2n dw <= i /\ i < w2n dw + SUM (MAP type_memory_size dtvs)) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tm.t_mem <=> i IN tn.t_mem)) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))` >>
  drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
    assign_base_typed_copy_fields_counted >>
  disch_then (qspecl_then [`D`, `ctx`, `PG`, `field_inv`] mp_tac) >>
  (impl_tac >- suspend "callback") >>
  simp[] >> strip_tac >>
  `field_inv dts sts 0 0 sa G tn s` by
    (simp[Abbr `field_inv`] >> qexists_tac `0` >> simp[]) >>
  qpat_x_assum `!fn G tn s. _` drule_all >> strip_tac >>
  suspend "finish"
QED

Resume typed_copy_return_fields_counted[callback]:
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `ci_mono c d` by metis_tac[typed_return_store_mono] >>
  `cs_extends a c /\ a.cs_next_var <= c.cs_next_var` by
    metis_tac[assign_base_offset_extends, cs_extends_trans, LESS_EQ_TRANS] >>
  `cs_extends a d /\ a.cs_next_var <= d.cs_next_var` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >> simp[] >>
  qx_gen_tac `f` >> qx_gen_tac `G0` >> qx_gen_tac `tn0` >> qx_gen_tac `s0` >>
  strip_tac >> gvs[Abbr `field_inv`] >>
  qpat_assum `_::_ = DROP _ dts` (mp_tac o SYM) >>
  disch_then (mp_then Any strip_assume_tac DROP_EQ_CONS) >>
  qpat_assum `_::_ = DROP _ sts` (mp_tac o SYM) >>
  disch_then (mp_then Any strip_assume_tac DROP_EQ_CONS) >>
  qpat_assum `!i. i < LENGTH dts ==> _ /\ _` (qspec_then `k` assume_tac) >>
  gvs[] >>
  `not_fresh_at a dst /\ not_fresh_at a src` by
    metis_tac[not_fresh_at_mono] >>
  `lookup_var dst s0 = SOME dw /\ lookup_var src s0 = SOME sw` by metis_tac[] >>
  `ptr_covers G0 tn0 dst s0 (SUM (MAP type_memory_size dtvs)) /\
   ptr_covers G0 tn0 src s0 (SUM (MAP type_memory_size stvs))` by
    metis_tac[ptr_covers_old_transport] >>
  `SUM (MAP type_memory_size (TAKE k dtvs)) + type_memory_size (EL k dtvs)
     <= SUM (MAP type_memory_size dtvs) /\
   SUM (MAP type_memory_size (TAKE k stvs)) + type_memory_size (EL k stvs)
     <= SUM (MAP type_memory_size stvs)` by
    metis_tac[tupleMemoryLayoutTheory.tuple_element_interval] >>
  `!i. i < LENGTH stvs ==> !m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
    val_in_memory (EL i stvs) (EL i vs)
      (w2n sw + SUM (MAP type_memory_size (TAKE i stvs))) m` by
    (rpt strip_tac >>
     irule typed_copy_fields_source_frame >>
     conj_tac >- metis_tac[] >> simp[] >>
     qexistsl_tac [`w2n dw`, `SUM (MAP type_memory_size dtvs)`,
       `s.vs_memory`, `s0.vs_memory`, `tn.t_mem`, `tn0.t_mem`] >>
     simp[] >> metis_tac[]) >>
  `R (EL k dts) (EL k sts) (EL k dtvs) (EL k stvs) (EL k vs)` by metis_tac[] >>
  suspend "field_apply"
QED

Resume typed_copy_return_fields_counted[field_apply]:
  `?H tm t.
    gas_path_ptr D 0 ctx f PG G0 tn0 s0 0 H tm (OK t) /\
    t.vs_current_bb = d.cs_current_bb /\
    t.vs_inst_idx = LENGTH d.cs_current_insts /\ ~t.vs_halted /\
    typed_copy_state_frame a (w2n dw) (SUM (MAP type_memory_size dtvs)) s0 t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      val_in_memory (EL k dtvs) (EL k vs)
        (w2n dw + SUM (MAP type_memory_size (TAKE k dtvs))) m) /\
    (!i. ~(w2n dw + SUM (MAP type_memory_size (TAKE k dtvs)) <= i /\
      i < w2n dw + SUM (MAP type_memory_size (TAKE k dtvs)) + type_memory_size (EL k dtvs)) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s0.vs_memory /\
      (i IN tm.t_mem <=> i IN tn0.t_mem)) /\
    tm.t_stor = tn0.t_stor /\ tm.t_trans = tn0.t_trans /\ tm.t_imm = tn0.t_imm /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s0 /\
      FLOOKUP H x = FLOOKUP G0 x /\ op_taint tm (Var x) = op_taint tn0 (Var x))`
    suffices_by suspend "field_result" >>
  irule typed_copy_return_field_path >>
  ntac 7 (conj_tac >- metis_tac[ADD_COMM]) >>
  qexistsl_tac [`ce`, `dp`, `dst`, `EL k dts`, `c`, `b`,
    `SUM (MAP type_memory_size (TAKE k stvs))`, `sp`, `src`, `EL k sts`,
    `SUM (MAP type_memory_size stvs)`, `EL k stvs`, `sw`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "child_contract" >>
  metis_tac[ADD_COMM]
QED

Resume typed_copy_return_fields_counted[child_contract]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!dt' st' dtv stv v. _` drule >>
  disch_then (mp_tac o SIMP_RULE bool_ss [ADD_COMM, DE_MORGAN_THM]) >>
  simp_tac bool_ss [ADD_COMM, DE_MORGAN_THM] >>
  disch_then irule >> metis_tac[ADD_COMM]
QED

Resume typed_copy_return_fields_counted[finish]:
  gvs[Abbr `field_inv`] >>
  `k' = LENGTH dts` by decide_tac >>
  gvs[] >> goal_assum (drule_at Any) >> simp[] >> gvs[]
QED

Resume typed_copy_return_fields_counted[field_result]:
  strip_tac >>
  qexistsl_tac [`H`, `tm`, `t`] >> simp[] >>
  qexists_tac `SUC k` >>
  simp[rich_listTheory.TAKE_SUC_BY_TAKE, MAP_SNOC, SUM_SNOC] >>
  conj_tac >-
    (irule typed_copy_state_frame_trans >> qexists_tac `s0` >>
     simp[] >> fs[typed_copy_state_frame_def] >> metis_tac[not_fresh_at_mono]) >>
  conj_tac >- suspend "prefix_result" >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED

Resume typed_copy_return_fields_counted[prefix_result]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [Once ADD_COMM] >>
  irule typed_copy_fields_prefix_step >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`k`, `s0.vs_memory`, `t.vs_memory`, `tn0.t_mem`, `tm.t_mem`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (rpt strip_tac >>
     qpat_assum `!i. i < k ==> _` drule >> metis_tac[ADD_COMM]) >>
  conj_tac >-
    (rpt strip_tac >>
     `i' < LENGTH dts` by decide_tac >>
     qpat_assum `!i. i < LENGTH dts ==> _ /\ _` drule >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- decide_tac >>
  first_assum ACCEPT_TAC
QED

Finalise typed_copy_return_fields_counted
