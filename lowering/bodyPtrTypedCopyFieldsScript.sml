(* Robust prefix/suffix composition for independently laid out fields. *)
Theory bodyPtrTypedCopyFields
Ancestors
  bodyPtrTypedCopyBoundary assignBasePtrFieldsCompose assignBasePtrFieldOffsets
  typedCopyTuplePtr typedCopyLayoutPtr bodyPtrSubscriptMemoryRebuild
  abiEncoderInput typedMemoryCopy typedCopyRobustTransportPtr
  valueEncodingProps valueEncodingDefs exprSimProps list rich_list arithmetic
  pred_set bodyPtrTypedCopyFieldsCompose bodyPtrTypedCopyFieldStep
  contextCodegenRelProps compileEnv

(* A write to field k preserves the completed destination prefix.  This
   boundary uses semantic sizes; sum_map_take_pointwise transports compiler
   offsets to these sums without identifying source and destination strides. *)
Theorem typed_fields_robust_prefix_frame:
  !tvs vs k addr tn tf mem mem'.
    LENGTH vs = LENGTH tvs /\ k < LENGTH tvs /\
    (!i. i < k ==> val_wf (EL i tvs) (EL i vs)) /\
    (!i. ~(addr + SUM (MAP type_memory_size (TAKE k tvs)) <= i /\
      i < addr + SUM (MAP type_memory_size (TAKE k tvs)) +
        type_memory_size (EL k tvs)) ==>
      mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem /\
      (i IN tf <=> i IN tn)) /\
    (!j. j < k ==> !m. mem_agree_outside tn mem m ==>
      val_in_memory (EL j tvs) (EL j vs)
        (addr + SUM (MAP type_memory_size (TAKE j tvs))) m) ==>
    !j. j < k ==> !m. mem_agree_outside tf mem' m ==>
      val_in_memory (EL j tvs) (EL j vs)
        (addr + SUM (MAP type_memory_size (TAKE j tvs))) m
Proof
  rpt strip_tac >>
  `SUM (MAP type_memory_size (TAKE j tvs)) + type_memory_size (EL j tvs) <=
    SUM (MAP type_memory_size (TAKE k tvs))` by
    (irule sum_take_element_before >> simp[]) >>
  irule robust_representation_exterior_frame >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`addr + SUM (MAP type_memory_size (TAKE k tvs))`,
    `mem`, `mem'`, `type_memory_size (EL k tvs)`, `tn`, `tf`] >>
  simp[] >> metis_tac[]
QED

(* Any destination write disjoint from the source window preserves its
   remaining fields.  Empty windows need no artificial ordering premise. *)
Theorem typed_fields_robust_suffix_frame:
  !tvs vs k src dst n tn tf mem mem'.
    LENGTH vs = LENGTH tvs /\
    (!j. k <= j /\ j < LENGTH tvs ==> val_wf (EL j tvs) (EL j vs)) /\
    (SUM (MAP type_memory_size tvs) <> 0 /\ n <> 0 ==>
      src + SUM (MAP type_memory_size tvs) <= dst \/ dst+n <= src) /\
    (!i. ~(dst <= i /\ i < dst+n) ==>
      mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem /\
      (i IN tf <=> i IN tn)) /\
    (!j. k <= j /\ j < LENGTH tvs ==> !m.
      mem_agree_outside tn mem m ==>
      val_in_memory (EL j tvs) (EL j vs)
        (src + SUM (MAP type_memory_size (TAKE j tvs))) m) ==>
    !j. k <= j /\ j < LENGTH tvs ==> !m.
      mem_agree_outside tf mem' m ==>
      val_in_memory (EL j tvs) (EL j vs)
        (src + SUM (MAP type_memory_size (TAKE j tvs))) m
Proof
  rpt strip_tac >>
  `val_wf (EL j tvs) (EL j vs)` by metis_tac[] >>
  drule val_footprint_le >> strip_tac >>
  `SUM (MAP type_memory_size (TAKE j tvs)) +
    type_memory_size (EL j tvs) <= SUM (MAP type_memory_size tvs)` by
    (irule abi_encoder_prefix_sum_bound >> simp[]) >>
  irule robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`mem`, `mem'`, `tn`, `tf`,
    `{i | dst <= i /\ i < dst+n}`] >>
  simp[]
QED

(* The two layouts are independent: offsets advance by their own sizes. *)
Theorem typed_fields_copy_robust:
  !ce dts sts.
  (!i. i < LENGTH dts ==>
   !tenv dtv stv v dst src sa sb ctx fn D PG G tn s a b.
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). sz = type_memory_bytes ce fty /\
        (!tv. evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv)) fields) /\
    type_widens_to tenv (EL i sts) (EL i dts) /\
    evaluate_type tenv (EL i sts) = SOME stv /\
    evaluate_type tenv (EL i dts) = SOME dtv /\
    type_memory_bytes ce (EL i sts) = type_memory_size stv /\
    type_memory_bytes ce (EL i dts) = type_memory_size dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    compile_store_memory_typed ce (Var dst) (EL i dts) (Var src) (EL i sts) sa = ((),sb) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (type_memory_bytes ce (EL i sts)) /\
    ptr_covers G tn dst s (type_memory_bytes ce (EL i dts)) /\
    w2n a + type_memory_bytes ce (EL i sts) < dimword(:256) /\
    w2n b + type_memory_bytes ce (EL i dts) < dimword(:256) /\
    (type_memory_bytes ce (EL i sts) <> 0 /\ type_memory_bytes ce (EL i dts) <> 0 ==>
      w2n a + type_memory_bytes ce (EL i sts) <= w2n b \/
      w2n b + type_memory_bytes ce (EL i dts) <= w2n a) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a) m) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    cs_extends sa sb /\
    ?H tf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK sf) /\
      sf.vs_current_bb = sb.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
      typed_copy_state_frame sa (w2n b) (type_memory_bytes ce (EL i dts)) s sf /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!j. ~(w2n b <= j /\ j < w2n b + type_memory_bytes ce (EL i dts)) ==>
        (j IN tf.t_mem <=> j IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b) m)) ==>
  !tenv dtvs stvs vs dst src doff soff sa sb ctx fn D PG G tn s a b dtot stot.
    LENGTH sts = LENGTH dts /\ LENGTH dtvs = LENGTH dts /\
    LENGTH stvs = LENGTH dts /\ LENGTH vs = LENGTH dts /\
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). sz = type_memory_bytes ce fty /\
        (!tv. evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv)) fields) /\
    (!i. i < LENGTH dts ==>
      type_widens_to tenv (EL i sts) (EL i dts) /\
      evaluate_type tenv (EL i sts) = SOME (EL i stvs) /\
      evaluate_type tenv (EL i dts) = SOME (EL i dtvs) /\
      type_memory_bytes ce (EL i sts) = type_memory_size (EL i stvs) /\
      type_memory_bytes ce (EL i dts) = type_memory_size (EL i dtvs) /\
      value_has_type (EL i stvs) (EL i vs) /\
      value_has_type (EL i dtvs) (EL i vs) /\
      val_wf (EL i stvs) (EL i vs) /\ val_wf (EL i dtvs) (EL i vs)) /\
    compile_typed_copy_fields ce (Var dst) (Var src) dts sts doff soff sa = ((),sb) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s stot /\ ptr_covers G tn dst s dtot /\
    soff + SUM (MAP (type_memory_bytes ce) sts) <= stot /\
    doff + SUM (MAP (type_memory_bytes ce) dts) <= dtot /\
    w2n a + stot < dimword(:256) /\ w2n b + dtot < dimword(:256) /\
    (SUM (MAP (type_memory_bytes ce) sts) <> 0 /\
     SUM (MAP (type_memory_bytes ce) dts) <> 0 ==>
      w2n a + soff + SUM (MAP (type_memory_bytes ce) sts) <= w2n b + doff \/
      w2n b + doff + SUM (MAP (type_memory_bytes ce) dts) <= w2n a + soff) /\
    (!i. i < LENGTH dts ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (EL i stvs) (EL i vs)
        (w2n a + soff + SUM (MAP type_memory_size (TAKE i stvs))) m) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    cs_extends sa sb /\
    ?H tf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK sf) /\
      sf.vs_current_bb = sb.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
      typed_copy_state_frame sa (w2n b + doff)
        (SUM (MAP (type_memory_bytes ce) dts)) s sf /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!i. ~(w2n b + doff <= i /\
        i < w2n b + doff + SUM (MAP (type_memory_bytes ce) dts)) ==>
        (i IN tf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
        tuple_in_memory vs dtvs (w2n b + doff) m)
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  `cs_extends sa sb` by
    (qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
     qspecl_then [`ce`, `Var dst`, `Var src`] mp_tac
       (cj 2 externalEntryShapeTheory.typed_memory_family_labels) >>
     disch_then (qspecl_then [`dts`, `sts`, `doff`, `soff`, `sa`] mp_tac) >>
     strip_tac >> disch_then SUBST_ALL_TAC >> fs[]) >>
  simp[] >>
  `!k. SUM (MAP (type_memory_bytes ce) (TAKE k dts)) =
         SUM (MAP type_memory_size (TAKE k dtvs))` by
    (irule sum_map_take_pointwise >> simp[] >> metis_tac[]) >>
  `!k. SUM (MAP (type_memory_bytes ce) (TAKE k sts)) =
         SUM (MAP type_memory_size (TAKE k stvs))` by
    (irule sum_map_take_pointwise >> simp[] >> metis_tac[]) >>
  qabbrev_tac `field_inv = \ds ss offd offs sc H tm u.
    ?k. k <= LENGTH dts /\ ds = DROP k dts /\ ss = DROP k sts /\
      offd = doff + SUM (MAP (type_memory_bytes ce) (TAKE k dts)) /\
      offs = soff + SUM (MAP (type_memory_bytes ce) (TAKE k sts)) /\
      cs_extends sa sc /\ sa.cs_next_var <= sc.cs_next_var /\
      typed_copy_state_frame sa (w2n b + doff)
        (SUM (MAP (type_memory_bytes ce) dts)) s u /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!i. ~(w2n b + doff <= i /\
        i < w2n b + doff + SUM (MAP (type_memory_bytes ce) dts)) ==>
        (i IN tm.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p u = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
        op_taint tm (Var p) = op_taint tn (Var p)) /\
      (!j. j < k ==> !m. mem_agree_outside tm.t_mem u.vs_memory m ==>
        val_in_memory (EL j dtvs) (EL j vs)
          (w2n b + doff + SUM (MAP type_memory_size (TAKE j dtvs))) m) /\
      (!j. k <= j /\ j < LENGTH dts ==> !m.
        mem_agree_outside tm.t_mem u.vs_memory m ==>
        val_in_memory (EL j stvs) (EL j vs)
          (w2n a + soff + SUM (MAP type_memory_size (TAKE j stvs))) m)` >>
  `field_inv dts sts doff soff sa G tn s` by
    (simp[Abbr `field_inv`] >> qexists_tac `0` >> simp[cs_extends_refl] >> gvs[]) >>
  qspec_then `ce` mp_tac typed_copy_fields_counted_for_function >>
  disch_then (qspecl_then [`Var dst`, `Var src`, `D`, `ctx`] mp_tac) >>
  disch_then (qspecl_then [`PG`, `field_inv`, `fn`] mp_tac) >>
  (impl_tac >- suspend "step") >>
  disch_then (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> disch_then (drule_all_then strip_assume_tac) >>
  suspend "finish"
QED

Resume typed_fields_copy_robust[step]:
  rpt gen_tac >> strip_tac >>
  `cs_extends a' b' /\ cs_extends b' c /\ cs_extends c d` by
    (conj_tac >- metis_tac[assignBasePtrFieldOffsetsTheory.assign_base_offset_extends] >>
     conj_tac >- metis_tac[assignBasePtrFieldOffsetsTheory.assign_base_offset_extends] >>
     qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     qspecl_then [`ce`, `dp`, `dt`, `sp`, `st`, `c`] mp_tac
       (cj 1 externalEntryShapeTheory.typed_memory_family_labels) >>
     strip_tac >> disch_then SUBST_ALL_TAC >> fs[]) >>
  `cs_extends a' d` by metis_tac[cs_extends_trans] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `field_inv (dt::ds) (st::ss) _ _ _ _ _ _` mp_tac >>
  simp[Abbr `field_inv`] >> strip_tac >>
  `k < LENGTH dts /\ EL k dts = dt /\ DROP (SUC k) dts = ds /\
   EL k sts = st /\ DROP (SUC k) sts = ss` by
    metis_tac[fragExecTheory.DROP_EQ_CONS] >>
  `not_fresh_at a' dst /\ not_fresh_at a' src` by
    (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `lookup_var src s' = SOME a /\ lookup_var dst s' = SOME b` by
    metis_tac[] >>
  `ptr_covers G' tn' src s' stot /\ ptr_covers G' tn' dst s' dtot` by
    (conj_tac >> irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`G`, `s`, `tn`] >> simp[] >> metis_tac[]) >>
  `SUM (MAP (type_memory_bytes ce) (TAKE k dts)) +
      type_memory_bytes ce (EL k dts) <= SUM (MAP (type_memory_bytes ce) dts) /\
   SUM (MAP (type_memory_bytes ce) (TAKE k sts)) +
      type_memory_bytes ce (EL k sts) <= SUM (MAP (type_memory_bytes ce) sts)` by
    (conj_tac >> irule abi_encoder_prefix_sum_bound >> simp[]) >>
  `doff' + type_memory_bytes ce dt <= dtot /\
   soff' + type_memory_bytes ce st <= stot` by
    (qpat_assum `!k. SUM (MAP (type_memory_bytes ce) (TAKE k dts)) = _`
       (qspec_then `k` assume_tac) >>
     qpat_assum `!k. SUM (MAP (type_memory_bytes ce) (TAKE k sts)) = _`
       (qspec_then `k` assume_tac) >> gvs[] >> decide_tac) >>
  `(type_memory_bytes ce st <> 0 /\ type_memory_bytes ce dt <> 0 ==>
    w2n a + soff' + type_memory_bytes ce st <= w2n b + doff' \/
    w2n b + doff' + type_memory_bytes ce dt <= w2n a + soff')` by
    (qpat_assum `!k. SUM (MAP (type_memory_bytes ce) (TAKE k dts)) = _`
       (qspec_then `k` assume_tac) >>
     qpat_assum `!k. SUM (MAP (type_memory_bytes ce) (TAKE k sts)) = _`
       (qspec_then `k` assume_tac) >> gvs[] >> decide_tac) >>
  qpat_assum `!i. i < LENGTH dts ==> !tenv dtv stv v dst src sa sb ctx fn D PG G tn s a b. _`
    (qspec_then `k` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (mp_then Any mp_tac typed_field_copy_step) >>
  simp[] >>
  disch_then (fn th =>
    qpat_assum `compile_with_byte_offset (Var dst) doff' a' = _`
      (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `compile_with_byte_offset (Var src) soff' b' = _`
      (mp_then Any mp_tac th)) >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`tenv`, `EL k dtvs`, `EL k stvs`, `EL k vs`] mp_tac) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (fn th => qpat_assum `ptr_covers G' tn' src s' stot`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `ptr_covers G' tn' dst s' dtot`
    (mp_then Any mp_tac th)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (qspecl_then [`D`, `PG`, `a`, `b`] mp_tac) >>
  (impl_tac >- (gvs[] >> rpt conj_tac >> gvs[])) >>
  strip_tac >>
  `a'.cs_next_var <= b'.cs_next_var /\ b'.cs_next_var <= c.cs_next_var /\
   c.cs_next_var <= d.cs_next_var` by
    metis_tac[typedCopyOperandFramesTheory.compile_with_byte_offset_next_var,
      typedCopyVarFlowTheory.compile_store_memory_typed_next_var] >>
  `typed_copy_state_frame sa (doff' + w2n b)
     (type_memory_size (EL k dtvs)) s' sf` by
    (qpat_assum `typed_copy_state_frame a' _ _ s' sf` mp_tac >>
     pure_rewrite_tac[typed_copy_state_frame_def] >> strip_tac >>
     simp[] >> rpt strip_tac >>
     `not_fresh_at a' x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     metis_tac[]) >>
  `typed_copy_state_frame sa (w2n b + doff)
     (SUM (MAP (type_memory_bytes ce) dts)) s' sf` by
    (irule typed_copy_state_frame_subinterval >>
     qexistsl_tac [`doff' + w2n b`, `type_memory_size (EL k dtvs)`] >>
     gvs[] >> decide_tac) >>
  `typed_copy_state_frame sa (w2n b + doff)
     (SUM (MAP (type_memory_bytes ce) dts)) s sf` by
    (irule typed_copy_state_frame_trans >> qexists_tac `s'` >> simp[]) >>
  qexistsl_tac [`H`, `tf`, `sf`] >> simp[] >>
  qexists_tac `SUC k` >>
  simp[typedNormalizeFieldsTheory.normalize_prefix_step] >>
  gvs[] >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  conj_tac >- (rpt strip_tac >>
    `~(doff + SUM (MAP type_memory_size (TAKE k dtvs)) + w2n b <= i /\
       i < doff + SUM (MAP type_memory_size (TAKE k dtvs)) +
         (type_memory_size (EL k dtvs) + w2n b))` by decide_tac >>
    qpat_x_assum `!j. _ ==> (j IN tf.t_mem <=> _)` (qspec_then `i` mp_tac) >>
    qpat_x_assum `!j. _ ==> (j IN tn'.t_mem <=> _)` (qspec_then `i` mp_tac) >>
    `~(doff + w2n b <= i /\
       i < doff + w2n b + SUM (MAP (type_memory_bytes ce) dts))` by decide_tac >>
    pop_assum mp_tac >>
    qpat_x_assum `~(_ /\ _)` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >>
    simp[]) >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at a' p` by
      (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
    metis_tac[]) >>
  `!i. ~(doff + (SUM (MAP type_memory_size (TAKE k dtvs)) + w2n b) <= i /\
      i < doff + (SUM (MAP type_memory_size (TAKE k dtvs)) + w2n b) +
        type_memory_size (EL k dtvs)) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s'.vs_memory /\
      (i IN tf.t_mem <=> i IN tn'.t_mem)` by
    (gen_tac >> disch_tac >> conj_tac >-
      (qpat_x_assum `typed_copy_state_frame a' _ _ s' sf` mp_tac >>
       pure_rewrite_tac[typed_copy_state_frame_def, typed_copy_frame_def] >>
       strip_tac >> first_x_assum irule >> decide_tac) >>
     qpat_x_assum `!i. _ ==> (i IN tf.t_mem <=> _)` (qspec_then `i` mp_tac) >>
     pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> disch_tac >> Cases_on `j = k` >- simp[] >>
     `j < k` by decide_tac >>
     `doff + (SUM (MAP type_memory_size (TAKE j dtvs)) + w2n b) =
       (doff + w2n b) + SUM (MAP type_memory_size (TAKE j dtvs))` by decide_tac >>
     pop_assum SUBST1_TAC >>
     gen_tac >> disch_tac >> irule typed_fields_robust_prefix_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`k`, `s'.vs_memory`, `sf.vs_memory`, `tf.t_mem`, `tn'.t_mem`] >>
     simp[]) >>
  rpt gen_tac >> disch_tac >>
  `soff + (SUM (MAP type_memory_size (TAKE j stvs)) + w2n a) =
    (soff + w2n a) + SUM (MAP type_memory_size (TAKE j stvs))` by decide_tac >>
  pop_assum SUBST1_TAC >>
  gen_tac >> disch_tac >> irule typed_fields_robust_suffix_frame >>
  simp[] >>
  qexistsl_tac [`doff + (SUM (MAP type_memory_size (TAKE k dtvs)) + w2n b)`,
    `k`, `s'.vs_memory`, `sf.vs_memory`, `type_memory_size (EL k dtvs)`,
    `tf.t_mem`, `tn'.t_mem`] >>
  simp[] >>
  `SUM (MAP type_memory_size stvs) = SUM (MAP (type_memory_bytes ce) sts)` by
    (qpat_x_assum `!k. _ = SUM (MAP type_memory_size (TAKE k stvs))`
       (qspec_then `LENGTH sts` mp_tac) >>
     `TAKE (LENGTH dts) stvs = stvs` by
       (irule TAKE_LENGTH_TOO_LONG >> simp[]) >> simp[]) >>
  rpt strip_tac >> decide_tac
QED

Resume typed_fields_copy_robust[finish]:
  qpat_x_assum `field_inv [] [] _ _ _ _ _ _` mp_tac >>
  simp[Abbr `field_inv`] >> strip_tac >>
  `k = LENGTH dts` by (fs[DROP_EQ_NIL] >> decide_tac) >>
  gvs[] >> qexistsl_tac [`G'`, `tn'`, `u`] >> simp[] >>
  rpt strip_tac >> simp[tuple_in_memory_from_elements]
QED

Finalise typed_fields_copy_robust
