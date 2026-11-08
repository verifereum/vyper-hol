Theory tuplePlaceMemoryFrame
Ancestors
  tuplePlaceStore placeMemoryStaging placeMemoryLiveRegion placeMemoryTypedForward
  placeMemoryTypeInterfaces exprSimHyps valueEncodingTyping vyperTypeArgFits
  stmtLowering loweringPosts stmtSimDefs fragGasMode exprLoweringProps
  context placeMemoryPrimitiveForward venomState compileEnv vyperTypeSystem
  memoryLocalRhsProps placeMemoryTypedPrimitive placeMemoryChildForward
  placeMemoryCopyEffect exprSimHypsDefs exprSimAlloc
  loweringHalt abiTupleProps rich_list fragExec
  placeMemoryStoreEffect placeMemoryStagingFrame freshWrites exprSimProps
  placeMemoryProtectedFrame abiBuiltinEncodeReusedInput

Theorem tuple_place_memory_forward_frame:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    loc = LocMemory /\ ~is_word_type dty /\
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty
      (case dty of
         ArrayT et (Dynamic _) =>
           SOME ((type_memory_bytes cenv et + 31) DIV 32,
                 type_memory_bytes cenv et)
       | _ => NONE)
      (type_memory_bytes cenv dty) sa = ((), sb) /\
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
              w2n w + type_memory_size dtv <= w2n sw \/
              sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==>
     !sw. eval_operand op s = SOME sw ==>
          w2n sw + type_memory_size stv <= s.vs_alloca_next /\
          !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                     sa.cs_next_id <= aid ==>
                     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    (loc = LocMemory ==>
     !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           0 < type_slot_size dtv) /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p v ee = (INL (), ff) /\
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
      (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
         FLOOKUP t.vs_allocas aid = SOME e) /\
      (!name b len. local_region cenv ee.scopes s name b len ==>
         local_region cenv ee.scopes r name b len) /\
      (!name b len a n.
         local_region cenv ee.scopes r name b len /\ b <= a /\
         a+n <= b+len /\
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
    val_in_memory stv v (w2n sw) s.vs_memory` by
    gvs[expr_val_rel_def] >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (qpat_x_assum `~is_word_type sty ==> _` mp_tac >> simp[] >>
     disch_then (qspec_then `sw` mp_tac) >> simp[]) >>
  `typed_memory_child_forward cenv (get_tenv cx) ctx func dty` by
    (irule typed_memory_rank_forward >> simp[] >>
     `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
       type_memory_bytes cenv ty = type_memory_size tv` by
       metis_tac[expr_sim_inv_memory_size] >>
     fs[expr_sim_inv_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all memory_place_live_region >> strip_tac >>
  `immutable_alloca_sep func cenv cx ee s` by
    metis_tac[stmt_state_rel_def] >>
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
     simp[regions_disjoint_def] >> decide_tac) >>
  Cases_on `src_loc = SOME LocMemory`
  >- suspend "staged" >>
  suspend "direct"
QED

Resume tuple_place_memory_forward_frame[direct]:
  `compile_store_memory cenv op dst_op dty sty sa = ((),sb)` by
    gvs[compile_assign_value_def] >>
  `dty <> sty /\ ~is_bytestring_type dty ==>
     type_memory_size stv + w2n sw <= w2n w \/
     type_memory_size dtv + w2n w <= w2n sw` by
    (strip_tac >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
     irule widening_typed_copy_separation >>
     simp[] >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`dty`, `sty`, `get_tenv cx`] >> simp[]) >>
  `?t. val_in_memory dtv v (w2n w) t.vs_memory /\
       typed_copy_effect ctx func sa sb s t (w2n w) (type_memory_size dtv)` by
    (irule compile_store_memory_nonword_effect >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> qexistsl_tac [`stv`, `get_tenv cx`] >> simp[]) >>
  qexistsl_tac [`dtv`, `s`, `t`] >> gvs[typed_copy_effect_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `!a len. _ ==> mem_bytes_at a len _ = _` irule >>
      metis_tac[])
  >- metis_tac[]
QED

Resume tuple_place_memory_forward_frame[staged]:
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
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split] >>
  `type_memory_size stv < dimword (:256)` by decide_tac >>
  drule_at (Pat `val_in_memory _ _ _ _`) compile_staging_prefix_forward >>
  disch_then drule >> disch_then drule >>
  disch_then drule >> simp[] >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `r` (qx_choose_then `u`
    (qx_choose_then `tw` assume_tac))) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  `!name b len. local_region cenv ee.scopes s name b len ==>
     local_region cenv ee.scopes r name b len` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `local_region cenv ee.scopes r name b len` by metis_tac[] >>
  `w2n tw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n tw` by
    (`regions_disjoint (w2n tw) (type_memory_size stv) b len` by metis_tac[] >>
     qpat_x_assum `regions_disjoint _ _ b len` mp_tac >>
     simp[regions_disjoint_def] >> decide_tac) >>
  suspend "staged_copy"
QED

Resume tuple_place_memory_forward_frame[staged_copy]:
  markerLib.RESUME_TAC >>
  `u.vs_labels = s.vs_labels` by
    (qpat_x_assum `(u with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
       vs_current_bb := _; vs_inst_idx := _|>) = r`
       (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >>
     qpat_x_assum `(r with <|vs_vars := _; vs_inst_idx := _;
       vs_allocas := _; vs_alloca_next := _|>) = s`
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
     >- (rpt strip_tac >> irule not_fresh_at_mono >>
         qexists_tac `sa` >> simp[]) >>
     qpat_x_assum `?p. buf.buf_operand = Var p /\ _` strip_assume_tac >>
     rpt strip_tac >> fs[] >> irule not_fresh_at_mono >>
     qexists_tac `sm` >> simp[]) >>
  `?t. val_in_memory dtv v (w2n w) t.vs_memory /\
       typed_copy_effect ctx func sn sb u t (w2n w) (type_memory_size dtv)` by
    (irule compile_store_memory_nonword_effect >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> qexistsl_tac [`stv`, `get_tenv cx`] >> simp[]) >>
  suspend "staged_post"
QED

Resume tuple_place_memory_forward_frame[staged_post]:
  markerLib.RESUME_TAC >>
  `!aid b len a n. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= a /\ a+n <= b+len ==>
    a+n <= w2n tw \/ w2n tw+type_memory_size stv <= a` by
    (map_every qx_gen_tac [`aid`, `ob`, `ol`, `oa`, `on`] >> strip_tac >>
     `w2n tw + type_memory_size stv <= ob \/ ob+ol <= w2n tw` by
       (irule abi_builtin_allocate_separate >>
        qexistsl_tac [`aid`, `s`, `sa.cs_next_id`] >>
        simp[] >>
        qpat_x_assum `stmt_state_rel ctx func cenv cx ee s` mp_tac >>
        simp[stmt_state_rel_def]) >> decide_tac) >>
  pop_assum (mk_asm "old_scratch_sep") >>
  `cenv.ce_is_ctor ==> !nm tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (tv,iv) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
    mem_bytes_at off (type_memory_size tv) r.vs_memory` by
    suspend "staged_immutables" >>
  `sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
  drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`) staging_store_local_frame >>
  simp[] >> disch_then (qspecl_then [`w2n tw`, `type_memory_size stv`] mp_tac) >>
  disch_then (drule_at (Pat `(u with <|vs_memory := _; vs_vars := _;
    vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>) = _`)) >>
  disch_then (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
  simp[] >>
  disch_then (qspecl_then [`ee.scopes`, `sa`, `cenv`] mp_tac) >>
  simp[] >> (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then strip_assume_tac >>
  qexistsl_tac [`r`, `t`] >> simp[] >>
  (conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  map_every qx_gen_tac [`aid`, `ob`, `ol`, `oa`, `on`] >> strip_tac >>
  `mem_bytes_at oa on t.vs_memory = mem_bytes_at oa on u.vs_memory` by
    (irule typed_copy_effect_bytes >>
     goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `mem_bytes_at oa on u.vs_memory = mem_bytes_at oa on s.vs_memory` by
    (qpat_x_assum `!a len. _ ==> mem_bytes_at a len u.vs_memory = _` irule >>
     asm "old_scratch_sep"
       (qspecl_then [`aid`, `ob`, `ol`, `oa`, `on`] mp_tac) >> simp[]) >> simp[])
QED

Resume tuple_place_memory_forward_frame[staged_immutables]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
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
     simp[] >> disch_then (qspecl_then [`nm`, `tv`, `iv`, `off`] mp_tac) >>
     simp[]) >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at a len u.vs_memory = _`
    (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >> simp[]
QED
Finalise tuple_place_memory_forward_frame
