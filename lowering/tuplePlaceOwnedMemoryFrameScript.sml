Theory tuplePlaceOwnedMemoryFrame
Ancestors
  tuplePlaceMemoryFrame tuplePlaceTypedSize tuplePlaceStaging
  tuplePlacePrimitiveSize aggregateStoreSizePath tuplePlaceChildSize
  placeMemoryStoreEffect placeMemoryCopyEffect placeMemoryTypedPrimitive
  placeMemoryPrimitiveForward placeMemoryChildForward memoryLocalRhsProps
  compileEnv venomState vyperTypeSystem context
  tuplePlaceStore placeMemoryStaging placeMemoryLiveRegion placeMemoryTypedForward
  placeMemoryTypeInterfaces exprSimHyps valueEncodingTyping vyperTypeArgFits
  stmtLowering loweringPosts stmtSimDefs fragGasMode exprLoweringProps
  placeMemoryProtectedFrame abiBuiltinEncodeReusedInput
  placeMemoryStagingFrame freshWrites exprSimProps exprSimHypsDefs exprSimAlloc
  loweringHalt abiTupleProps rich_list fragExec
  placeStoreMemory placeMemoryStateRebuild placeStore abiValueEncoding
  valueEncodingProps exprLowering

Theorem tuple_place_nonword_size_effect[local]:
  ~is_word_type dty /\ ~is_word_type sty /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw) u.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  type_memory_size dtv + 64 < dimword (:256) /\
  type_memory_size stv + 64 < dimword (:256) /\
  eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
  (!x. dp = Var x ==> not_fresh_at a x) /\
  (!x. sp = Var x ==> not_fresh_at a x) /\
  fn_has_code a b func /\ ~u.vs_halted /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  cenv.ce_target CapMcopy /\
  tuple_place_child_size_forward cenv tenv ctx func dty /\
  (dty <> sty /\ ~is_bytestring_type dty ==>
    w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  compile_store_memory cenv sp dp dty sty a = ((),b) ==>
  ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv)
Proof
  strip_tac >> Cases_on `dty = sty`
  >- suspend "same" >>
  Cases_on `is_bytestring_type dty`
  >- suspend "bytes" >>
  `compile_store_memory_typed cenv dp dty sp sty a = ((),b)` by
    gvs[compile_store_memory_def] >>
  `w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw` by metis_tac[] >>
  irule tuple_place_child_size_forward_apply >> simp[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[SF SFY_ss]
QED

Resume tuple_place_nonword_size_effect[same]:
  gvs[] >>
  drule compile_store_memory_same_type_size_forward >>
  disch_then (qspec_then `v` mp_tac) >>
  disch_then (drule_at (Pat `eval_operand sp _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  simp[] >> disch_then (qspecl_then [`func`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[typed_copy_effect_def] >>
  conj_tac
  >- (qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = u`
        (mp_tac o Q.AP_TERM `\z. z with <|vs_prev_bb := u.vs_prev_bb;
          vs_current_bb := u.vs_current_bb|>`) >> simp[]) >>
  qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = u`
    (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Resume tuple_place_nonword_size_effect[bytes]:
  `is_bytestring_type sty` by
    (gvs[type_widens_to_def] >>
     metis_tac[memoryLocalRhsPropsTheory.arg_type_fits_bytestring_source]) >>
  `compile_store_memory_typed cenv dp dty sp sty a = ((),b)` by
    (simp[Once compile_store_memory_typed_def] >>
     gvs[compile_store_memory_def]) >>
  drule_all tuple_place_bytestring_size_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[typed_copy_effect_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED
Finalise tuple_place_nonword_size_effect

Theorem tuple_place_owned_memory_forward_frame[local]:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    loc = LocMemory /\ ~is_word_type dty /\
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty (type_memory_bytes cenv dty) sa = ((),sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
       evaluate_type (get_tenv cx) dty = SOME dtv ==>
       type_memory_size stv = 0 \/
       w2n sw + type_memory_size stv <= w2n w \/
       w2n w + type_memory_size dtv <= w2n sw \/ sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0. p = MemoryPlace id path /\
       lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==> !sw. eval_operand op s = SOME sw ==>
       0 < type_memory_size stv /\ type_memory_size stv + 64 < dimword (:256) /\
       w2n sw + type_memory_size stv < dimword (:256) /\
       ?aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
         aid < sa.cs_next_id /\ b <= w2n sw /\
         w2n sw + type_memory_size stv <= b+len) /\
    (loc = LocMemory ==> !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
       w2n w + type_memory_size dtv < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
       0 < type_memory_size dtv /\ type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==> 0 < type_slot_size dtv) /\
    stmt_state_rel ctx func cenv cx ee s /\ write_place cx p v ee = (INL (),ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?dtv r t.
      evaluate_type (get_tenv cx) dty = SOME dtv /\
      val_in_memory dtv v (w2n w) t.vs_memory /\
      stmt_state_rel ctx func cenv cx ee r /\
      gas_marked_path F ctx func s 0 (OK t) /\
      (t with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
        vs_prev_bb := r.vs_prev_bb; vs_current_bb := r.vs_current_bb;
        vs_inst_idx := r.vs_inst_idx|>) = r /\
      t.vs_allocas = r.vs_allocas /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
      (!name b len. local_region cenv ee.scopes s name b len ==>
         local_region cenv ee.scopes r name b len) /\
      (!name b len a n. local_region cenv ee.scopes r name b len /\
         b <= a /\ a+n <= b+len /\
         (a+n <= w2n w \/ w2n w+type_memory_size dtv <= a) ==>
         mem_bytes_at a n t.vs_memory = mem_bytes_at a n r.vs_memory) /\
      LENGTH r.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (cenv.ce_is_ctor ==> !nm tv iv off.
        FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
          | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (tv,iv) ==>
        mem_bytes_at off (type_memory_size tv) t.vs_memory =
        mem_bytes_at off (type_memory_size tv) r.vs_memory) /\
      r.vs_memory = s.vs_memory /\
      (!aid b len a n. aid < sa.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= a /\ a+n <= b+len /\
        (a+n <= w2n w \/ w2n w+type_memory_size dtv <= a) ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) dty = SOME dtv` >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[cj 1 value_has_type_val_wf] >>
  `type_memory_bytes cenv sty = type_memory_size stv /\
   type_memory_bytes cenv dty = type_memory_size dtv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `~is_word_type sty` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  `?sw. eval_operand op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory` by gvs[expr_val_rel_def] >>
  qpat_x_assum `~is_word_type sty ==> _` mp_tac >> simp[] >> strip_tac >>
  `tuple_place_child_size_forward cenv (get_tenv cx) ctx func dty` by
    (irule tuple_place_rank_size_forward >> simp[] >>
     `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
       type_memory_bytes cenv ty = type_memory_size tv` by
       metis_tac[expr_sim_inv_memory_size] >>
     fs[expr_sim_inv_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all memory_place_live_region >> strip_tac >>
  `immutable_alloca_sep func cenv cx ee s` by metis_tac[stmt_state_rel_def] >>
  `cenv.ce_is_ctor ==> !nm tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (tv,iv) ==>
    off + type_memory_size tv <= w2n w \/ w2n w + type_memory_size dtv <= off` by
    (rpt strip_tac >>
     qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
     simp[immutable_alloca_sep_def] >>
     disch_then (qspecl_then [`nm`, `tv`, `iv`, `off`] mp_tac o CONJUNCT2) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!id b sz. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  Cases_on `src_loc = SOME LocMemory`
  >- suspend "staged" >>
  `compile_store_memory cenv op dst_op dty sty sa = ((),sb)` by
    gvs[compile_assign_value_def] >>
  `dty <> sty /\ ~is_bytestring_type dty ==>
     type_memory_size stv + w2n sw <= w2n w \/
     type_memory_size dtv + w2n w <= w2n sw` by
    (strip_tac >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
     irule widening_typed_copy_separation >>
     simp[] >> conj_tac >- gvs[] >>
     qexistsl_tac [`dty`, `sty`, `get_tenv cx`] >> simp[]) >>
  `?t. val_in_memory dtv v (w2n w) t.vs_memory /\
       typed_copy_effect ctx func sa sb s t (w2n w) (type_memory_size dtv)` by
    (irule tuple_place_nonword_size_effect >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> qexistsl_tac [`stv`, `get_tenv cx`] >> simp[]) >>
  qexistsl_tac [`s`, `t`] >> gvs[typed_copy_effect_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `!a len. _ ==> mem_bytes_at a len _ = _` irule >> metis_tac[])
  >- metis_tac[]
QED

Resume tuple_place_owned_memory_forward_frame[staged]:
  gvs[compile_assign_value_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_alloc_buffer (type_memory_size stv) sa = (buf,sm)` >>
  rename1 `compile_copy_memory buf.buf_operand op (type_memory_size stv) sm = ((),sn)` >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by
    (drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends sn sb` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     qspecl_then [`cenv`, `buf.buf_operand`, `dst_op`, `dty`, `sty`, `sn`]
       mp_tac ci_mono_compile_store_memory >>
     simp[ci_mono_def] >> rpt strip_tac >> gvs[]) >>
  `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by metis_tac[fn_has_code_split] >>
  `type_memory_size stv < dimword (:256)` by decide_tac >>
  `?r u tw. gas_marked_path F ctx func s 0 (OK r) /\
    stmt_state_rel ctx func cenv cx ee r /\
    eval_operand buf.buf_operand r = SOME tw /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n tw,type_memory_size stv) /\
    w2n tw+type_memory_size stv < dimword (:256) /\ r.vs_memory = s.vs_memory /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP r.vs_allocas aid = SOME e) /\
    (!name b len. local_region cenv ee.scopes r name b len ==>
       regions_disjoint (w2n tw) (type_memory_size stv) b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    ((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ w2n tw = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n tw,type_memory_size stv)) /\
    (r with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts /\
    gas_marked_path F ctx func r 0 (OK u) /\ gas_marked_path F ctx func s 0 (OK u) /\
    val_in_memory stv v (w2n tw) u.vs_memory /\
    val_in_memory stv v (w2n sw) u.vs_memory /\
    (w2n sw+type_memory_size stv <= w2n tw \/ w2n tw+type_memory_size stv <= w2n sw) /\
    u.vs_allocas = r.vs_allocas /\
    (u with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
      vs_prev_bb := r.vs_prev_bb; vs_current_bb := r.vs_current_bb;
      vs_inst_idx := r.vs_inst_idx|>) = r /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!a len. a+len <= w2n tw \/ w2n tw+type_memory_size stv <= a ==>
       mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
    (!name b len. local_region cenv ee.scopes r name b len ==>
       mem_bytes_at b len u.vs_memory = mem_bytes_at b len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    eval_operand buf.buf_operand u = SOME tw` by
    (irule tuple_place_staging_positive >>
     qpat_assum `compile_alloc_buffer _ _ = _` (irule_at Any) >>
     qpat_assum `compile_copy_memory _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `val_in_memory stv v _ _` (irule_at Any) >>
     qexistsl_tac [`len`, `b`] >> simp[] >> disj2_tac >>
     qexists_tac `aid` >> simp[]) >>
  `!name b len. local_region cenv ee.scopes s name b len ==>
     local_region cenv ee.scopes r name b len` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `local_region cenv ee.scopes r name b' len'` by metis_tac[] >>
  `w2n tw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n tw` by
    (`regions_disjoint (w2n tw) (type_memory_size stv) b' len'` by metis_tac[] >>
     qpat_x_assum `regions_disjoint _ _ b' len'` mp_tac >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  all_tac >>
  `u.vs_labels = s.vs_labels` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
       vs_current_bb := _; vs_inst_idx := _|>) = r`
       (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >>
     qpat_x_assum `(r with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|>) = s`
       (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  `eval_operand dst_op u = SOME w` by
    (Cases_on `dst_op` >> fs[eval_operand_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var` by
    (qspec_then `type_memory_size stv` (qspec_then `sa` mp_tac)
       ci_mono_compile_alloc_buffer >>
     qspecl_then [`buf.buf_operand`, `op`, `type_memory_size stv`, `sm`]
       mp_tac ci_mono_compile_copy_memory >> simp[ci_mono_def]) >>
  `(!x. dst_op = Var x ==> not_fresh_at sn x) /\
   (!x. buf.buf_operand = Var x ==> not_fresh_at sn x)` by
    (`sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
     conj_tac
     >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     rpt strip_tac >> fs[] >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `?t. val_in_memory dtv v (w2n w) t.vs_memory /\
       typed_copy_effect ctx func sn sb u t (w2n w) (type_memory_size dtv)` by
    (irule tuple_place_nonword_size_effect >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> qexistsl_tac [`stv`, `get_tenv cx`] >> gvs[]) >>
  all_tac >>
  `!aid b len a n. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= a /\ a+n <= b+len ==>
    a+n <= w2n tw \/ w2n tw+type_memory_size stv <= a` by
    (map_every qx_gen_tac [`sep_id`, `ob`, `ol`, `oa`, `on`] >> strip_tac >>
     `w2n tw + type_memory_size stv <= ob \/ ob+ol <= w2n tw` by
       (irule abi_builtin_allocate_separate >>
        qexistsl_tac [`sep_id`, `s`, `sa.cs_next_id`] >> simp[] >>
        qpat_x_assum `stmt_state_rel ctx func cenv cx ee s` mp_tac >>
        simp[stmt_state_rel_def]) >> decide_tac) >>
  pop_assum (mk_asm "old_scratch_sep") >>
  `cenv.ce_is_ctor ==> !nm tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (tv,iv) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
    mem_bytes_at off (type_memory_size tv) r.vs_memory` by
    (rpt strip_tac >>
     `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
     `off + type_memory_size tv <= w2n tw \/
      w2n tw + type_memory_size stv <= off` by
       (irule compile_alloc_buffer_immutable_disjoint >>
        goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
        goal_assum (drule_at (Pat `immutable_alloca_sep _ _ _ _ _`)) >>
        simp[] >> goal_assum (drule_at Any) >> simp[]) >>
     `mem_bytes_at off (type_memory_size tv) t.vs_memory =
      mem_bytes_at off (type_memory_size tv) u.vs_memory` by
       (irule typed_copy_effect_bytes >>
        goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
        qpat_x_assum `cenv.ce_is_ctor ==> !nm tv iv off. _ ==> _ \/ _` mp_tac >>
        simp[] >> disch_then (qspecl_then [`nm`, `tv`, `iv`, `off`] mp_tac) >> simp[]) >>
     qpat_x_assum `!a len. _ ==> mem_bytes_at a len u.vs_memory = _`
       (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >> simp[]) >>
  `sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
  drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`) staging_store_local_frame >>
  disch_then (qspecl_then [`w2n tw`, `type_memory_size stv`] mp_tac) >>
  disch_then (drule_at (Pat `(_ with <|vs_vars := _; vs_memory := _;
    vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>) = _`)) >>
  disch_then (drule_at (Pat `gas_marked_path F ctx func s 0 (OK u)`)) >>
  disch_then (qspecl_then [`ee.scopes`, `sa`, `cenv`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then strip_assume_tac >> qexistsl_tac [`r`, `t`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (qpat_assum `(t with <|vs_vars := _; vs_memory := _;
     vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>) = r` mp_tac >>
     simp[NoAsms])) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (
    qpat_assum `!name b len a k. _ ==> mem_bytes_at a k t.vs_memory = _` mp_tac >>
    simp[NoAsms, arithmeticTheory.ADD_COMM])) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (
  map_every qx_gen_tac [`oldid`, `ob`, `ol`, `oa`, `on`] >> strip_tac >>
  `mem_bytes_at oa on t.vs_memory = mem_bytes_at oa on u.vs_memory` by
    (irule typed_copy_effect_bytes >>
     goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `mem_bytes_at oa on u.vs_memory = mem_bytes_at oa on s.vs_memory` by
    (qpat_x_assum `!a len. _ ==> mem_bytes_at a len u.vs_memory = _` irule >>
     asm "old_scratch_sep" (qspecl_then [`oldid`, `ob`, `ol`, `oa`, `on`] mp_tac) >> simp[]) >> simp[])
QED

Finalise tuple_place_owned_memory_forward_frame

Theorem tuple_place_owned_memory_run_frame:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    loc = LocMemory /\
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty (type_memory_bytes cenv dty) sa = ((),sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
       evaluate_type (get_tenv cx) dty = SOME dtv ==>
       type_memory_size stv = 0 \/
       w2n sw + type_memory_size stv <= w2n w \/
       w2n w + type_memory_size dtv <= w2n sw \/ sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0. p = MemoryPlace id path /\
       lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==> !sw. eval_operand op s = SOME sw ==>
       0 < type_memory_size stv /\ type_memory_size stv + 64 < dimword (:256) /\
       w2n sw + type_memory_size stv < dimword (:256) /\
       ?aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
         aid < sa.cs_next_id /\ b <= w2n sw /\
         w2n sw + type_memory_size stv <= b+len) /\
    (loc = LocMemory ==> !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
       w2n w + type_memory_size dtv < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
       0 < type_memory_size dtv /\ type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==> 0 < type_slot_size dtv) /\
    (loc <> LocMemory /\ dty <> sty /\
     ~(is_bytestring_type dty /\ is_bytestring_type sty) ==> type_alloc_ok cenv dty) /\
    stmt_state_rel ctx func cenv cx ee s /\ write_place cx p v ee = (INL (),ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx ff t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!aid b len a n dtv. aid < sa.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= a /\ a+n <= b+len /\
        evaluate_type (get_tenv cx) dty = SOME dtv /\
        (loc = LocMemory ==> a+n <= w2n w \/ w2n w+type_memory_size dtv <= a) ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dty`
  >- suspend "word" >>
  drule_all tuple_place_owned_memory_forward_frame >> strip_tac >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (irule memory_place_write_stmt_state >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ t.vs_memory`)) >>
     qexistsl_tac [`dty`, `ee`, `env`, `p`, `r`, `s`, `sa`] >>
     gvs[] >> conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  qexists_tac `t` >> simp[] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `!aid b len a n. _ ==> mem_bytes_at _ _ _ = _` irule >>
  metis_tac[]
QED

Resume tuple_place_owned_memory_run_frame[word]:
  `sty = dty` by metis_tac[type_widens_to_word] >> gvs[] >>
  `emit_void MSTORE [dst_op; op] sa = ((),sb)` by
    gvs[compile_assign_value_def] >>
  `eval_operand op s = SOME (typed_val_to_w256 stv v)` by fs[expr_val_rel_def] >>
  qabbrev_tac `u = mstore (w2n w) (typed_val_to_w256 stv v) s` >>
  `stmt_state_rel ctx func cenv cx ff u` by
    (Cases_on `p`
     >- (gvs[place_ptr_rel_def, slot_loc_def] >> Cases_on `b` >> gvs[])
     >- (rename1 `MemoryPlace id path` >>
         unabbrev_all_tac >> irule place_store_word_memory_state >>
         qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
         qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[]) >>
     gvs[place_ptr_rel_def, slot_loc_def]) >>
  `gas_marked_path F ctx func s 0 (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
   (!x. lookup_var x u = lookup_var x s) /\
   u.vs_allocas = s.vs_allocas /\ ~u.vs_halted /\
   u.vs_current_bb = sb.cs_current_bb /\
   SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule place_store_emit_run >> simp[Abbr `u`] >>
     qexistsl_tac [`dst_op`, `LocMemory`, `op`, `sa`, `w`,
                    `typed_val_to_w256 stv v`] >> simp[]) >>
  qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  rpt strip_tac >> gvs[] >> simp[Abbr `u`] >>
  irule mstore_mem_bytes_at_disjoint >>
  drule_all abi_word_type_size >> simp[]
QED
Finalise tuple_place_owned_memory_run_frame
