(* Deterministic heads of the interleaved argument traversal. *)
Theory bodyIntCallNRStageHead
Ancestors bodyIntCallJointForce[qualified,ignore_grammar]
  bodyIntCallNRStageFragments bodyIntCallNRStageStores
  bodyIntCallFamCallIntStageInterface bodyIntCallForcingReadOnly
  exprLoweringProps loweringPosts bodyIntCallNRStageAllocCertificate
  bodyIntCallNRStageStoreDispatch bodyIntCallFamCallIntAllocationGeometry
  bodyIntCallFamCallIntForcingFrames externalNormalizePremises

Theorem intcall_stage_current_head_stack:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  unwrap_value ce vv sa = (op,sb) /\
  vv_holds ce fp.jc_cx ty r vv es s /\
  read_result fp.jc_cx r es = (INL v,es) /\ is_word_type ty /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  fn_has_code sa sb fp.jc_func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    eval_operand op u = SOME (typed_val_to_w256 tv v) /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >>
  `vv_holds ce fp.jc_cx ty (Value v) vv es s` by
    (irule vv_holds_materialise >> goal_assum (drule_at Any) >> simp[]) >>
  `sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`, `vv`, `sa`] ci_mono_unwrap_value) >>
     simp[ci_mono_def]) >>
  drule_all intcall_stage_expr_word_force >> strip_tac >>
  qexists_tac `u` >> gvs[expr_val_rel_def] >> metis_tac[]
QED

(* Full source geometry is needed only for an actual widening store. *)
Theorem intcall_stage_widening_source_disjoint[local]:
  vv_at ce cx sty a sa es r vv s /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) sty = SOME tv /\ value_has_type tv v /\
  ~is_bytestring_type sty /\ type_widens_to (get_tenv cx) sty dty /\ sty <> dty /\
  eval_operand (vv_operand vv) s = SOME w /\
  (case vv of StackValue _ _ => ~is_word_type sty
            | LocatedValue _ p => p.ptr_location = LocMemory) /\
  stmt_state_rel ctx func ce cx es u /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (dst,sz) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
    regions_disjoint dst sz lb len) ==>
  regions_disjoint (w2n w) (type_memory_size tv) dst sz
Proof
  strip_tac >>
  `val_footprint tv v = type_memory_size tv` by
    (drule_all normalize_nonbytes_footprint >> simp[]) >>
  `0 < type_memory_size tv` by
    (drule_all normalize_return_source_positive >> simp[]) >>
  `val_footprint tv v <> 0` by decide_tac >>
  drule_all intcall_vv_at_allocation_disjoint >> simp[]
QED

(* At the forcing boundary an earlier destination allocation cannot be the
   newly materialized source.  Identity sources carry their pre-allocation
   geometry instead.  Separate is false for compatible layouts. *)
Theorem intcall_stage_snapshot_force[local]:
  unwrap_value ce vv sa = (op,sb) /\
  vv_holds ce cx ty r vv es s /\ read_result cx r es = (INL v,es) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  allocas_above lo s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. P p k ==> p+k <= lo) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  FLOOKUP s.vs_allocas dstid = SOME (dst,cap) /\ dstid < sa.cs_next_id /\
  ((case vv of StackValue _ _ => T
     | LocatedValue _ p => p.ptr_location = LocMemory) /\ Separate ==>
    !w. eval_operand (vv_operand vv) s = SOME w ==>
      regions_disjoint (w2n w) (type_memory_size tv) dst cap /\
      w2n w + type_memory_size tv < dimword (:256)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand op u = SOME w /\ val_in_memory tv v (w2n w) u.vs_memory /\
    (Separate ==> regions_disjoint (w2n w) (type_memory_size tv) dst cap /\
      w2n w + type_memory_size tv < dimword (:256)) /\
    s.vs_alloca_next <= u.vs_alloca_next /\ allocas_above lo u /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!name b k. local_region ce es.scopes u name b k <=>
      local_region ce es.scopes s name b k) /\
    locals_kept ce es es s u /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all vv_holds_materialise >> strip_tac >>
  Cases_on `vv`
  >- suspend "stack" >>
  rename1 `LocatedValue ann p` >>
  Cases_on `p.ptr_location = LocMemory`
  >- suspend "memory" >>
  `ann = ty` by fs[vv_holds_def] >> gvs[] >>
  `p.ptr_location <> LocCalldata` by
    (Cases_on `p.ptr_location` >> fs[vv_holds_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sa x` by fs[contextTheory.vv_operand_def] >>
  Cases_on `p.ptr_location = LocCode`
  >- suspend "code" >>
  suspend "storage"
QED

Resume intcall_stage_snapshot_force[stack]:
  drule (SRULE [] protected_identity_value_forcing) >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
  qexists_tac `s` >>
  gvs[expr_val_rel_def, contextTheory.vv_operand_def,
      exprSimPropsTheory.locals_kept_refl] >> metis_tac[]
QED

Resume intcall_stage_snapshot_force[memory]:
  drule protected_identity_value_forcing >> disch_then drule >> simp[] >>
  disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
  qexists_tac `s` >>
  gvs[expr_val_rel_def, contextTheory.vv_operand_def,
      exprSimPropsTheory.locals_kept_refl] >> metis_tac[]
QED

Resume intcall_stage_snapshot_force[code]:
  mp_tac (Q.INST [`scopes` |-> `es.scopes`, `ty` |-> `ann`]
    (SPEC_ALL intcall_code_forcing_frames)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `FLOOKUP u.vs_allocas dstid = SOME (dst,cap)` by metis_tac[] >>
  `dstid <> sa.cs_next_id` by decide_tac >>
  `regions_disjoint (w2n w) (type_memory_size tv) dst cap` by
    (irule exprSimPrecompilesTheory.state_allocations_disjoint >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[]
QED

Resume intcall_stage_snapshot_force[storage]:
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `p.ptr_location` >> fs[]) >>
  mp_tac (Q.INST [`scopes` |-> `es.scopes`, `ty` |-> `ann`]
    (SPEC_ALL intcall_storage_forcing_frames)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `FLOOKUP u.vs_allocas dstid = SOME (dst,cap)` by metis_tac[] >>
  `dstid <> sa.cs_next_id` by decide_tac >>
  `regions_disjoint (w2n w) (type_memory_size tv) dst cap` by
    (irule exprSimPrecompilesTheory.state_allocations_disjoint >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[]
QED

Finalise intcall_stage_snapshot_force

Theorem intcall_stage_current_head_memory:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_alloc_buffer (MAX 32 (type_memory_size dtv)) sa = (buf,sc) /\
  unwrap_value ce vv sc = (src,sd) /\
  fn_has_code sa sc fp.jc_func /\ fn_has_code sc sd fp.jc_func /\
  fn_has_code sd sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  vv_holds ce fp.jc_cx sty r vv es s /\ vv_at ce fp.jc_cx sty a sa es r vv s /\
  read_result fp.jc_cx r es = (INL v,es) /\
  evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv /\
  evaluate_type (get_tenv fp.jc_cx) sty = SOME stv /\
  value_has_type dtv v /\ value_has_type stv v /\ val_wf dtv v /\ val_wf stv v /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_bytes ce sty = type_memory_size stv /\
  type_memory_size stv < 2**64 /\ type_memory_size dtv + 64 < dimword (:256) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  a.cs_next_id <= sa.cs_next_id /\
  (sty <> NoneT /\ ~is_word_type sty /\ ~is_bytestring_type sty /\
    (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
    ?w off len. eval_operand (vv_operand vv) s = SOME w /\
      off <= w2n w /\ w2n w + type_memory_size stv <= off+len /\
      off+len < dimword (:256) /\
      (fp.jc_lo <= off \/ ?b z. fp.jc_staged b z /\ b <= off /\ off+len <= b+z)) /\
  ((is_word_type sty /\ is_word_type dty /\
    compile_store_memory ce src buf.buf_operand dty sty sd = ((),sb) /\
    typed_val_to_w256 stv v = typed_val_to_w256 dtv v) \/
   (is_bytestring_type sty /\ is_bytestring_type dty /\
    compile_store_bytestring src buf.buf_operand sd = ((),sb) /\
    (!mem ptr. val_in_memory stv v ptr mem ==> val_in_memory dtv v ptr mem)) \/
   (~is_word_type sty /\ ~is_bytestring_type sty /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\
    compile_store_memory ce src buf.buf_operand dty sty sd = ((),sb) /\
    (sty <> dty ==>
      acyclic_struct_metadata ce.ce_struct_fields /\
      sfields_tenv_consistent ce.ce_struct_fields (get_tenv fp.jc_cx) /\
      (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
        ALL_DISTINCT (MAP FST fields) /\
        EVERY (\(fname,fty,sz). !tv.
          evaluate_type (get_tenv fp.jc_cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
      (!ty tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv ==>
        type_memory_bytes ce ty = type_memory_size tv) /\
      type_widens_to (get_tenv fp.jc_cx) sty dty))) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    eval_operand buf.buf_operand u = SOME w /\
    val_in_memory dtv v (w2n w) u.vs_memory /\ val_wf dtv v /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sb x) /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,MAX 32 (type_memory_size dtv)) /\
    a.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id < sb.cs_next_id /\
    fp.jc_lo <= w2n w /\
    w2n w + MAX 32 (type_memory_size dtv) <= u.vs_alloca_next /\
    w2n w + MAX 32 (type_memory_size dtv) < dimword (:256) /\
    sa.cs_next_var <= sb.cs_next_var
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MAX 32 (type_memory_size dtv) < dimword (:256)` by
    (simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  drule_all intcall_stage_alloc_readonly_landing >> strip_tac >>
  rename1 `gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t)` >>
  `intcall_expr_res fp ce env es sc t /\ ~t.vs_halted /\
   t.vs_current_bb = sc.cs_current_bb /\
   t.vs_inst_idx = LENGTH sc.cs_current_insts` by
    fs[bodyIntCallJointContractTheory.intcall_expr_cont_def] >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s` by
    metis_tac[] >>
  `vv_holds ce fp.jc_cx sty r vv es t /\
   vv_at ce fp.jc_cx sty a sc es r vv t` by
    (mp_tac (Q.INST [`u` |-> `t`, `d` |-> `sc`, `b` |-> `sa`,
       `Own` |-> `F`, `ty` |-> `sty`, `cx` |-> `fp.jc_cx`,
       `tv` |-> `stv`, `lo` |-> `fp.jc_lo`, `staged` |-> `fp.jc_staged`]
       (SPEC_ALL intcall_stage_alloc_value_certificate)) >>
     (impl_tac >- (simp[] >> metis_tac[])) >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!q x. (reserved q \/ q = buf.buf_operand) /\ q = Var x ==>
     not_fresh_at sc x` by
    (rpt gen_tac >> strip_tac >-
      (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
       simp[] >> first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
     gvs[]) >>
  Cases_on `is_word_type sty`
  >- suspend "word" >>
  suspend "nonword"
QED

Resume intcall_stage_current_head_memory[word]:
  `vv_holds ce fp.jc_cx sty (Value v) vv es t` by
    (irule vv_holds_materialise >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all intcall_stage_expr_word_force >> strip_tac >>
  `~is_bytestring_type sty` by
    (Cases_on `sty` >> fs[compileEnvTheory.is_word_type_def,
       compileEnvTheory.is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     fs[compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def] >>
     rename1 `BytesT len` >> Cases_on `len` >>
     fs[compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def]) >>
  fs[] >>
  `sc.cs_next_var <= sd.cs_next_var /\ sc.cs_next_id <= sd.cs_next_id` by
    (mp_tac (Q.SPECL [`ce`, `vv`, `sc`] ci_mono_unwrap_value) >> simp[ci_mono_def]) >>
  `sd.cs_next_var <= sb.cs_next_var /\ sd.cs_next_id <= sb.cs_next_id` by
    (mp_tac (Q.SPECL [`ce`, `src`, `buf.buf_operand`, `dty`, `sty`, `sd`]
      ci_mono_compile_store_memory) >> simp[ci_mono_def]) >>
  `intcall_expr_res fp ce env es sd u /\ ~u.vs_halted /\
   u.vs_current_bb = sd.cs_current_bb /\
   u.vs_inst_idx = LENGTH sd.cs_current_insts` by
    fs[bodyIntCallJointContractTheory.intcall_expr_cont_def] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
   local_ptrs_reserved ce sd` by fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  `eval_operand (Var p) u = SOME w` by
    (qpat_x_assum `!q. (!x. q = Var x ==> not_fresh_at sc x) ==> _` mp_tac >>
     disch_then (qspec_then `Var p` mp_tac) >> simp[]) >>
  `w2n w + MAX 32 (type_memory_size dtv) <= u.vs_alloca_next` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
        venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. FLOOKUP u.vs_allocas aid = _ ==> _`
       (qspecl_then [`sa.cs_next_id`, `w2n w`, `MAX 32 (type_memory_size dtv)`] mp_tac) >> simp[]) >>
  `!name b k. local_region ce es.scopes u name b k ==>
     regions_disjoint b k (w2n w) (type_memory_size dtv)` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) (MAX 32 (type_memory_size dtv)) b k` by metis_tac[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     gvs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  suspend "word_store"
QED

Resume intcall_stage_current_head_memory[word_store]:
  `ce.ce_is_ctor ==> !name itv iv off.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables fp.jc_cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size dtv)` by
    (rpt strip_tac >>
     qpat_x_assum `ce.ce_is_ctor ==> _` drule >>
     disch_then (qspecl_then [`name`, `off`, `itv`, `iv`] mp_tac) >>
     simp[] >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def, arithmeticTheory.MAX_DEF] >>
     decide_tac) >>
  `?sw. eval_operand src u = SOME sw /\ sw = typed_val_to_w256 dtv v` by
    (fs[loweringPostsTheory.expr_val_rel_def] >>
     qpat_x_assum `!tv. evaluate_type _ sty = SOME tv ==> _`
       (qspec_then `stv` mp_tac) >> simp[]) >>
  mp_tac (Q.INST [`s` |-> `u`, `sa` |-> `sd`, `dst` |-> `Var p`,
    `dw` |-> `w`, `sw` |-> `sw`, `src` |-> `src`,
    `tv` |-> `dtv`, `aid` |-> `sa.cs_next_id`, `start` |-> `a`,
    `tenv` |-> `get_tenv fp.jc_cx`, `ctx` |-> `fp.jc_ctx`,
    `func` |-> `fp.jc_func`, `cx` |-> `fp.jc_cx`]
    (SPEC_ALL intcall_stage_declared_snapshot)) >>
  (impl_tac >- (simp[] >> conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
    disj1_tac >> simp[] >> conj_tac >- metis_tac[] >> first_assum MATCH_ACCEPT_TAC)) >>
  strip_tac >>
  `intcall_expr_cont fp ce env es sa s es sd u` by
    (irule bodyIntCallJointAggCoreTheory.intcall_expr_cont_trans >>
     simp[] >> qexistsl_tac [`es`, `sc`, `t`] >> simp[] >> decide_tac) >>
  `alloca_inv u` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def] >>
  `sa.cs_next_var <= sd.cs_next_var` by decide_tac >>
  `intcall_expr_cont fp ce env es sa s es sb u'` by
    (irule bodyIntCallJointAggCoreTheory.intcall_owned_store_cont >>
     simp[] >> qexistsl_tac [`sa.cs_next_id`, `w2n w`, `w2n w`,
       `MAX 32 (type_memory_size dtv)`, `u`, `sd`,
       `MAX 32 (type_memory_size dtv)`] >> simp[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  suspend "word_preserved"
QED

Resume intcall_stage_current_head_memory[word_preserved]:
  `gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u')` by
    (qpat_assum `gas_marked_path F _ _ s 0 (OK t)` mp_tac >>
     qpat_assum `gas_marked_path F _ _ t 0 (OK u)` mp_tac >>
     qpat_assum `gas_marked_path F _ _ u 0 (OK u')` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD]) >>
  qexistsl_tac [`u'`, `w`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `!x. q = Var x ==> not_fresh_at sd x` by
        (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> simp[] >> metis_tac[]) >>
      `!x. q = Var x ==> not_fresh_at sc x` by
        (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> simp[] >> metis_tac[]) >> metis_tac[]) >>
  (rpt strip_tac >> rename1 `Win pp kk` >>
      `regions_disjoint pp kk (w2n w) (MAX 32 (type_memory_size dtv))` by
        (qpat_x_assum `!p k. Win p k ==> _` drule >> strip_tac >>
         qpat_x_assum `!aid b k p n. _` irule >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      drule placeMemoryCopyEffectTheory.typed_copy_effect_bytes >>
      disch_then (qspecl_then [`kk`, `pp`] mp_tac) >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  decide_tac
QED

Resume intcall_stage_current_head_memory[nonword]:
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es t /\
   local_ptrs_reserved ce sc /\ allocas_above fp.jc_lo t` by
    fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  `!p k. fp.jc_prot p k ==> p+k <= fp.jc_lo` by
    fs[bodyIntCallJointContractTheory.intcall_frame_ok_def] >>
  `((case vv of StackValue _ _ => T | LocatedValue _ vp => vp.ptr_location = LocMemory) /\
     (sty <> dty /\ ~is_bytestring_type sty)) ==>
     !sw. eval_operand (vv_operand vv) t = SOME sw ==>
       regions_disjoint (w2n sw) (type_memory_size stv) (w2n w)
         (MAX 32 (type_memory_size dtv)) /\
       w2n sw + type_memory_size stv < dimword (:256)` by
    (strip_tac >> gen_tac >> disch_tac >>
     `type_widens_to (get_tenv fp.jc_cx) sty dty` by fs[] >>
     `0 < type_memory_size stv` by
       (drule_all normalize_return_source_positive >> simp[]) >>
     `sty <> NoneT` by (strip_tac >> gvs[compileEnvTheory.type_memory_bytes_def]) >>
     conj_tac
     >- (mp_tac (Q.INST [`cx` |-> `fp.jc_cx`, `dty` |-> `dty`,
           `u` |-> `t`, `w` |-> `sw`, `tv` |-> `stv`, `ctx` |-> `fp.jc_ctx`,
           `func` |-> `fp.jc_func`, `dst` |-> `w2n w`,
           `sz` |-> `MAX 32 (type_memory_size dtv)`]
           (SPEC_ALL intcall_stage_widening_source_disjoint)) >>
         (impl_tac >- (simp[] >> metis_tac[])) >> simp[]) >>
     qpat_x_assum `sty <> NoneT /\ _ ==> _` mp_tac >> simp[] >>
     strip_tac >> gvs[] >> decide_tac) >>
  suspend "nonword_force"
QED

Resume intcall_stage_current_head_memory[nonword_force]:
  qabbrev_tac `Old = \p k. ?aid b len. aid < sc.cs_next_id /\
    FLOOKUP t.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len` >>
  mp_tac (Q.INST [`sa` |-> `sc`, `sb` |-> `sd`, `s` |-> `t`, `op` |-> `src`,
    `ty` |-> `sty`, `tv` |-> `stv`, `cx` |-> `fp.jc_cx`,
    `ctx` |-> `fp.jc_ctx`, `func` |-> `fp.jc_func`, `lo` |-> `fp.jc_lo`,
    `P` |-> `fp.jc_prot`, `Win` |-> `Old`,
    `reserved` |-> `\q. fp.jc_reserved q \/ reserved q \/ q = buf.buf_operand`,
    `dstid` |-> `sa.cs_next_id`, `dst` |-> `w2n (w:256 word)`,
    `cap` |-> `MAX 32 (type_memory_size dtv)`,
    `Separate` |-> `sty <> dty /\ ~is_bytestring_type sty`]
    (SPEC_ALL intcall_stage_snapshot_force)) >>
  (impl_tac >-
    (`!x. fp.jc_reserved (Var x) ==> not_fresh_at sc x` by
       fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
     simp[Abbr `Old`]
     >- (gen_tac >> strip_tac >> gvs[] >>
         qpat_x_assum `!q x. (reserved q \/ _) /\ _ ==> _` irule >> simp[]) >>
     rpt strip_tac >> first_x_assum irule >> simp[])) >>
  strip_tac >> suspend "nonword_endpoint"
QED

Resume intcall_stage_current_head_memory[nonword_endpoint]:
  `sc.cs_next_var <= sd.cs_next_var /\ sc.cs_next_id <= sd.cs_next_id` by
    (mp_tac (Q.SPECL [`ce`, `vv`, `sc`] ci_mono_unwrap_value) >> simp[ci_mono_def]) >>
  `intcall_expr_res fp ce env es sd u` by
    (irule bodyIntCallJointAggCoreTheory.intcall_joint_res_frame >>
     simp[] >> qexistsl_tac [`t`, `sc`] >> simp[] >> metis_tac[]) >>
  `intcall_expr_cont fp ce env es sc t es sd u` by
    (simp[bodyIntCallJointContractTheory.intcall_expr_cont_def] >>
     (rpt strip_tac >>
      qpat_x_assum `!p k. Old p k ==> _` (qspecl_then [`off`, `sz`] mp_tac) >>
      simp[Abbr `Old`] >>
      disch_then irule >> goal_assum (drule_at Any) >> simp[])) >>
  `local_ptrs_reserved ce sd` by
    fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  `eval_operand buf.buf_operand u = SOME w /\
   FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,MAX 32 (type_memory_size dtv))` by
    metis_tac[] >>
  `w2n w + MAX 32 (type_memory_size dtv) <= u.vs_alloca_next` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
        venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. FLOOKUP u.vs_allocas aid = _ ==> _`
       (qspecl_then [`sa.cs_next_id`, `w2n w`, `MAX 32 (type_memory_size dtv)`] mp_tac) >> simp[]) >>
  suspend "nonword_store"
QED

Resume intcall_stage_current_head_memory[nonword_store]:
  `!x. src = Var x ==> not_fresh_at sd x` by
    ((metis_tac[bodyIntCallJointForceTheory.unwrap_value_operand_reserved])) >>
  `!name b k. local_region ce es.scopes u name b k ==>
     regions_disjoint b k (w2n w) (MAX 32 (type_memory_size dtv))` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) (MAX 32 (type_memory_size dtv)) b k` by metis_tac[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!name b k. local_region ce es.scopes u name b k ==>
     regions_disjoint b k (w2n w) (type_memory_size dtv)` by
    (rpt strip_tac >>
     `regions_disjoint b k (w2n w) (MAX 32 (type_memory_size dtv))` by metis_tac[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     gvs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `ce.ce_is_ctor ==> !name itv iv off.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables fp.jc_cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size dtv)` by
    (rpt strip_tac >>
     qpat_x_assum `ce.ce_is_ctor ==> _` drule >>
     disch_then (qspecl_then [`name`, `off`, `itv`, `iv`] mp_tac) >>
     simp[] >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def, arithmeticTheory.MAX_DEF] >>
     decide_tac) >>
  suspend "nonword_dispatch"
QED

Resume intcall_stage_current_head_memory[nonword_dispatch]:
  `sd.cs_next_var <= sb.cs_next_var /\ sd.cs_next_id <= sb.cs_next_id` by
    (Cases_on `is_bytestring_type sty` >> fs[] >>
     mp_tac (Q.SPECL [`ce`, `src`, `buf.buf_operand`, `dty`, `sty`, `sd`]
       ci_mono_compile_store_memory) >>
     mp_tac (Q.SPECL [`src`, `buf.buf_operand`, `sd`] ci_mono_compile_store_bytestring) >>
     simp[ci_mono_def]) >>
  mp_tac (Q.INST [`s` |-> `u`, `sa` |-> `sd`, `dst` |-> `buf.buf_operand`,
    `dw` |-> `w`, `sw` |-> `w'`, `src` |-> `src`,
    `tv` |-> `dtv`, `aid` |-> `sa.cs_next_id`, `start` |-> `a`,
    `tenv` |-> `get_tenv fp.jc_cx`, `ctx` |-> `fp.jc_ctx`,
    `func` |-> `fp.jc_func`, `cx` |-> `fp.jc_cx`]
    (SPEC_ALL intcall_stage_declared_snapshot)) >>
  (impl_tac >-
    (simp[] >> conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     Cases_on `is_bytestring_type sty` >> fs[]
     >- (disj1_tac >> simp[] >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
         conj_tac >-
           (rpt strip_tac >>
            qpat_x_assum `!name b k. local_region ce es.scopes s name b k ==> _` drule >>
            metis_tac[]) >>
         rpt strip_tac >> qpat_x_assum `ce.ce_is_ctor ==> !name off tv v. _` drule >>
         (metis_tac[])) >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name b k. local_region ce es.scopes s name b k ==> _` drule >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def,
              arithmeticTheory.MAX_DEF] >> decide_tac) >>
     conj_tac >- metis_tac[] >>
     strip_tac >>
     `sty <> dty` by metis_tac[] >>
     fs[] >> conj_tac >- metis_tac[] >>
     qpat_x_assum `regions_disjoint (w2n w') _ _ _` mp_tac >>
     qpat_x_assum `w2n w + MAX 32 _ < _` mp_tac >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def,
          arithmeticTheory.MAX_DEF] >> decide_tac)) >>
  strip_tac >> suspend "nonword_join"
QED

Resume intcall_stage_current_head_memory[nonword_join]:
  `intcall_expr_cont fp ce env es sa s es sd u` by
    (irule bodyIntCallJointAggCoreTheory.intcall_expr_cont_trans >>
     simp[] >> qexistsl_tac [`es`, `sc`, `t`] >> simp[] >> decide_tac) >>
  `alloca_inv u` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def] >>
  `sa.cs_next_var <= sd.cs_next_var` by decide_tac >>
  `intcall_expr_cont fp ce env es sa s es sb u'` by
    (irule bodyIntCallJointAggCoreTheory.intcall_owned_store_cont >>
     simp[] >> qexistsl_tac [`sa.cs_next_id`, `w2n w`, `w2n w`,
       `MAX 32 (type_memory_size dtv)`, `u`, `sd`,
       `MAX 32 (type_memory_size dtv)`] >> simp[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  suspend "nonword_preserved"
QED

Resume intcall_stage_current_head_memory[nonword_preserved]:
  `gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u')` by
    (qpat_assum `gas_marked_path F _ _ s 0 (OK t)` mp_tac >>
     qpat_assum `gas_marked_path F _ _ t 0 (OK u)` mp_tac >>
     qpat_assum `gas_marked_path F _ _ u 0 (OK u')` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD]) >>
  qexistsl_tac [`u'`, `w`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `!x. q = Var x ==> not_fresh_at sd x` by
        (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> simp[] >> metis_tac[]) >> metis_tac[]) >>
  rpt strip_tac >> rename1 `Win pp kk` >>
  `Old pp kk` by
    (simp[Abbr `Old`] >>
     qpat_x_assum `!p k. Win p k ==> _` drule >> strip_tac >>
     qexistsl_tac [`aid`, `b`, `len`] >> simp[] >> metis_tac[]) >>
  `regions_disjoint pp kk (w2n w) (MAX 32 (type_memory_size dtv))` by
    (qpat_x_assum `!p k. Win p k ==> _` drule >> strip_tac >>
     qpat_x_assum `!aid b k p n. _` irule >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule placeMemoryCopyEffectTheory.typed_copy_effect_bytes >>
  disch_then (qspecl_then [`kk`, `pp`] mp_tac) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Finalise intcall_stage_current_head_memory
