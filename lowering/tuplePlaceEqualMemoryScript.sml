Theory tuplePlaceEqualMemory
Ancestors
  tuplePlaceStaging aggregateStoreSizePath placeMemoryCopyEffect
  placeMemoryStateRebuild placeMemoryLiveRegion placeMemoryStagingFrame
  tuplePlaceMemoryFrame exprSimProps exprSimHyps valueEncodingProps
  stmtLowering exprLoweringProps loweringPosts stmtSimDefs
  compileEnv loweringStateRelDefs venomState context finite_map loweringHalt rich_list fragExec
  abiBuiltinEncodeReusedInput placeMemoryProtectedFrame exprSimAlloc
  placeMemoryTypedPrimitive placeMemoryStaging arithmetic abiTupleProps freshWrites

Theorem tuple_place_same_type_size_effect:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) /\
  type_memory_size tv+64 < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory tv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size tv)
Proof
  strip_tac >> drule_all compile_store_memory_same_type_size_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[typed_copy_effect_def] >> conj_tac
  >- (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s`
        (mp_tac o Q.AP_TERM `\z. z with <|vs_prev_bb := s.vs_prev_bb;
          vs_current_bb := s.vs_current_bb|>`) >> simp[]) >>
  qpat_x_assum `(t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s`
    (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >>
  simp[] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ _ = _` irule >>
  decide_tac
QED

Theorem tuple_place_equal_memory_forward:
  ~is_word_type ty /\
  compile_assign_value cenv dst LocMemory op F src_loc ty ty
    (type_memory_bytes cenv ty) sa = ((),sb) /\
  eval_operand dst s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type ty) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  expr_val_rel cx ty v op s /\
  0 < type_memory_size tv /\ type_memory_size tv+64 < dimword (:256) /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  (!sw. eval_operand op s = SOME sw ==>
    ?b len. b <= w2n sw /\ w2n sw+type_memory_size tv <= b+len /\
      ((?name. local_region cenv ee.scopes s name b len) \/
       (?aid. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id))) /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r t. val_in_memory tv v (w2n w) t.vs_memory /\
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
    (!name b len a n. local_region cenv ee.scopes r name b len /\ b <= a /\
      a+n <= b+len /\ (a+n <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n r.vs_memory) /\
    LENGTH r.vs_memory <= LENGTH t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (cenv.ce_is_ctor ==> !nm itv iv off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (itv,iv) ==>
      mem_bytes_at off (type_memory_size itv) t.vs_memory =
      mem_bytes_at off (type_memory_size itv) r.vs_memory) /\
    r.vs_memory = s.vs_memory /\
    (!aid b len a n. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= a /\ a+n <= b+len /\
      (a+n <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  strip_tac >>
  `val_wf tv v` by metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `?sw. eval_operand op s = SOME sw /\
    val_in_memory tv v (w2n sw) s.vs_memory` by gvs[expr_val_rel_def] >>
  drule_all memory_place_live_region >> strip_tac >>
  `immutable_alloca_sep func cenv cx ee s` by metis_tac[stmt_state_rel_def] >>
  `cenv.ce_is_ctor ==> !nm itv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (itv,iv) ==>
    off+type_memory_size itv <= w2n w \/ w2n w+type_memory_size tv <= off` by
    (rpt strip_tac >> qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
     simp[immutable_alloca_sep_def] >>
     disch_then (qspecl_then [`nm`, `itv`, `iv`, `off`] mp_tac o CONJUNCT2) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!id b sz. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  Cases_on `src_loc = SOME LocMemory` >- suspend "staged" >>
  `compile_store_memory cenv op dst ty ty sa = ((),sb)` by
    gvs[compile_assign_value_def] >>
  `?t. val_in_memory tv v (w2n w) t.vs_memory /\
    typed_copy_effect ctx func sa sb s t (w2n w) (type_memory_size tv)` by
    (irule tuple_place_same_type_size_effect >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> qexists_tac `get_tenv cx` >> simp[]) >>
  qexistsl_tac [`s`, `t`] >> gvs[typed_copy_effect_def] >> rpt conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `!a len. _ ==> mem_bytes_at a len _ = _` irule >> metis_tac[]) >>
  metis_tac[]
QED

Resume tuple_place_equal_memory_forward[staged]:
  qpat_x_assum `!sw. eval_operand op s = SOME sw ==> _` (mp_tac o Q.SPEC `sw`) >>
  simp[] >> disch_then (qx_choose_then `srcb` (qx_choose_then `srclen` assume_tac)) >>
  pop_assum (mk_asm "source_region") >>
  gvs[compile_assign_value_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_alloc_buffer (type_memory_size tv) sa = (buf,sm)` >>
  rename1 `compile_copy_memory buf.buf_operand op (type_memory_size tv) sm = ((),sn)` >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by
    (drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends sn sb` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     qspecl_then [`cenv`, `buf.buf_operand`, `dst`, `ty`, `ty`, `sn`]
       mp_tac ci_mono_compile_store_memory >>
     simp[ci_mono_def] >> rpt strip_tac >> gvs[]) >>
  `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split] >>
  `type_memory_size tv < dimword (:256)` by decide_tac >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) tuple_place_staging_positive >>
  disch_then (drule_at (Pat `compile_copy_memory _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`srclen`, `srcb`] mp_tac) >>
  (impl_tac >- (asm "source_region" mp_tac >> simp[])) >>
  disch_then (qx_choose_then `r` (qx_choose_then `u`
    (qx_choose_then `tw` assume_tac))) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  `!name b len. local_region cenv ee.scopes s name b len ==>
    local_region cenv ee.scopes r name b len` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `(u with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
       vs_current_bb := _; vs_inst_idx := _|>) = r`
       (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >>
     qpat_assum `(r with <|vs_vars := _; vs_inst_idx := _;
       vs_allocas := _; vs_alloca_next := _|>) = s`
       (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  `eval_operand dst u = SOME w` by
    (Cases_on `dst` >> fs[eval_operand_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var` by
    (qspec_then `type_memory_size tv` (qspec_then `sa` mp_tac)
       ci_mono_compile_alloc_buffer >>
     qspecl_then [`buf.buf_operand`, `op`, `type_memory_size tv`, `sm`]
       mp_tac ci_mono_compile_copy_memory >> simp[ci_mono_def]) >>
  `(!x. dst = Var x ==> not_fresh_at sn x) /\
   (!x. buf.buf_operand = Var x ==> not_fresh_at sn x)` by
    (`sa.cs_next_var <= sn.cs_next_var` by decide_tac >> conj_tac
     >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     qpat_x_assum `?p. buf.buf_operand = Var p /\ _` strip_assume_tac >>
     rpt strip_tac >> fs[] >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `?t. val_in_memory tv v (w2n w) t.vs_memory /\
    typed_copy_effect ctx func sn sb u t (w2n w) (type_memory_size tv)` by
    (irule tuple_place_same_type_size_effect >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> qexists_tac `get_tenv cx` >> simp[]) >>
  suspend "post"
QED
Resume tuple_place_equal_memory_forward[post]:
  markerLib.RESUME_TAC >>
  `!aid b len a n. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= a /\ a+n <= b+len ==>
    a+n <= w2n tw \/ w2n tw+type_memory_size tv <= a` by
    (map_every qx_gen_tac [`aid`, `ob`, `ol`, `oa`, `on`] >> strip_tac >>
     `w2n tw+type_memory_size tv <= ob \/ ob+ol <= w2n tw` by
       (irule abi_builtin_allocate_separate >>
        qexistsl_tac [`aid`, `s`, `sa.cs_next_id`] >> simp[] >>
        qpat_x_assum `stmt_state_rel ctx func cenv cx ee s` mp_tac >>
        simp[stmt_state_rel_def]) >> decide_tac) >>
  pop_assum (mk_asm "old_scratch_sep") >>
  `cenv.ce_is_ctor ==> !nm itv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (itv,iv) ==>
    mem_bytes_at off (type_memory_size itv) t.vs_memory =
    mem_bytes_at off (type_memory_size itv) r.vs_memory` by
    (rpt strip_tac >>
     `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
     `off+type_memory_size itv <= w2n tw \/
      w2n tw+type_memory_size tv <= off` by
       (irule compile_alloc_buffer_immutable_disjoint >>
        goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
        goal_assum (drule_at (Pat `immutable_alloca_sep _ _ _ _ _`)) >>
        simp[] >> goal_assum (drule_at Any) >> simp[]) >>
     `mem_bytes_at off (type_memory_size itv) t.vs_memory =
      mem_bytes_at off (type_memory_size itv) u.vs_memory` by
       (irule typed_copy_effect_bytes >>
        goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
        qpat_x_assum `cenv.ce_is_ctor ==> !nm itv iv off. _ ==> _ \/ _` mp_tac >>
        simp[] >> disch_then (qspecl_then [`nm`, `itv`, `iv`, `off`] mp_tac) >> simp[]) >>
     qpat_x_assum `!a len. _ ==> mem_bytes_at a len u.vs_memory = _`
       (qspecl_then [`off`, `type_memory_size itv`] mp_tac) >> simp[]) >>
  `sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
  drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`) staging_store_local_frame >>
  simp[] >> disch_then (qspecl_then [`w2n tw`, `type_memory_size tv`] mp_tac) >>
  disch_then (drule_at (Pat `(u with <|vs_memory := _; vs_vars := _;
    vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>) = _`)) >>
  disch_then (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`ee.scopes`, `sa`, `cenv`] mp_tac) >> simp[] >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexistsl_tac [`r`, `t`] >> simp[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  map_every qx_gen_tac [`aid`, `ob`, `ol`, `oa`, `on`] >> strip_tac >>
  `mem_bytes_at oa on t.vs_memory = mem_bytes_at oa on u.vs_memory` by
    (irule typed_copy_effect_bytes >>
     goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `mem_bytes_at oa on u.vs_memory = mem_bytes_at oa on s.vs_memory` by
    (qpat_x_assum `!a len. _ ==> mem_bytes_at a len u.vs_memory = _` irule >>
     asm "old_scratch_sep" (qspecl_then [`aid`, `ob`, `ol`, `oa`, `on`] mp_tac) >> simp[]) >>
  simp[]
QED
Finalise tuple_place_equal_memory_forward

(* Correctness and byte preservation share the forward runner's endpoint. *)
Theorem tuple_place_equal_memory_run_frame:
  ~is_word_type ty /\
  compile_assign_value cenv dst LocMemory op F src_loc ty ty
    (type_memory_bytes cenv ty) sa = ((),sb) /\
  eval_operand dst s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type ty) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  expr_val_rel cx ty v op s /\
  0 < type_memory_size tv /\ type_memory_size tv+64 < dimword (:256) /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  (!sw. eval_operand op s = SOME sw ==>
    ?b len. b <= w2n sw /\ w2n sw+type_memory_size tv <= b+len /\
      ((?name. local_region cenv ee.scopes s name b len) \/
       (?aid. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id))) /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!name b len a n. local_region cenv ee.scopes s name b len /\ b <= a /\
      a+n <= b+len /\ (a+n <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
    (!aid b len a n. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= a /\ a+n <= b+len /\
      (a+n <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  strip_tac >> drule_all tuple_place_equal_memory_forward >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (irule memory_place_write_stmt_state >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `(t with <|vs_vars := _; vs_memory := _;
       vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>) = r`)) >>
     goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
     goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
     goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
     simp[ADD_COMM] >> metis_tac[ADD_COMM]) >>
  qexists_tac `t` >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len a n. _` irule >> simp[] >>
      qexists_tac `aid` >> simp[]) >>
  rpt strip_tac >>
  `local_region cenv ee.scopes r name b len` by metis_tac[] >>
  qpat_x_assum `!name b len a n. local_region _ _ _ _ _ _ /\ _ ==> _` mp_tac >>
  simp[] >> disch_then (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`a`, `n`] mp_tac) >> simp[] >> metis_tac[ADD_COMM]
QED
