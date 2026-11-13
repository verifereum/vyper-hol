Theory exprExtRequestSnapshotStoreFold
Ancestors
  exprExtRequestSnapshotStoreInterface exprExtRequestPrefixOps
  exprExtRequestTupleStore exprExtRequestHistoryCompose exprExtRequestReconstruct
  exprExtRequestHistory exprExtRequestTupleFold
  exprSafeOperand exprLoweringProps exprOperandVar loweringPosts
  compileEnv exprLowering context loweringStateRelDefs venomState venomMemDefs
  valueTypingMemoryProps valueEncodingProps freshWrites fragExec fragGasMode fragGasPath
Libs wordsLib

Theorem snapshot_store_head[local]:
  extrequest_snapshot_cell ctx func ce cx eb cb tb (vv,ty,tv,v) /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  (if is_word_type ty then emit_void MSTORE [dst;op]
   else if is_bytestring_type ty then compile_store_bytestring op dst
   else emit_void MCOPY [dst;op;Lit (n2w (type_memory_bytes ce ty))]) su = ((),sb) /\
  stmt_state_rel ctx func ce cx eb tb /\ stmt_state_rel ctx func ce cx ee s /\
  extrequest_history_frame ce cx eb cb tb ee sm s /\ cb.cs_next_id <= live /\
  fn_has_code sm sn func /\ fn_has_code sn su func /\ fn_has_code su sb func /\
  fn_inst_ids_distinct func /\ ee.gas_obs = [] /\
  eval_operand buf s = SOME w /\
  FLOOKUP s.vs_allocas live = SOME (tuple_base,sz) /\ live < sm.cs_next_id /\
  tuple_base <= w2n (w + n2w off) /\
  w2n (w + n2w off) + type_memory_size tv <= tuple_base + sz /\
  (!name b len. local_region ce ee.scopes s name b len ==>
     regions_disjoint tuple_base sz b len) /\
  (ce.ce_is_ctor ==> !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv)
       (w2n (w + n2w off)) (type_memory_size tv)) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    stmt_state_rel ctx func ce cx ee q /\
    val_in_memory tv v (w2n (w + n2w off)) q.vs_memory /\
    extrequest_history_frame ce cx eb cb tb ee sb q /\
    FLOOKUP q.vs_allocas live = SOME (tuple_base,sz) /\
    (!a k. tuple_base <= a /\ a + k <= tuple_base + sz /\
       regions_disjoint a k (w2n (w + n2w off)) (type_memory_size tv) ==>
       mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (!x z. not_fresh_at sm x /\ lookup_var x s = SOME z ==>
       lookup_var x q = SOME z) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
       FLOOKUP q.vs_allocas aid = SOME row) /\
    (!aid p k. aid < sm.cs_next_id /\ aid <> live /\
       FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!name b len. local_region ce ee.scopes s name b len ==>
       mem_bytes_at b len q.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (ce.ce_is_ctor ==> !name itv iv io.
       FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
       FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
       mem_bytes_at io (type_memory_size itv) q.vs_memory =
       mem_bytes_at io (type_memory_size itv) s.vs_memory)
Proof
  strip_tac >>
  `local_ptrs_reserved ce sm` by fs[extrequest_history_frame_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all extrequest_add_endpoint >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK t)` >>
  `extrequest_history_frame ce cx eb cb tb ee sn t` by
    (drule_all extrequest_history_frame_trans >> simp[]) >>
  qpat_x_assum `extrequest_snapshot_cell _ _ _ _ _ _ _ _` mp_tac >>
  simp[extrequest_snapshot_cell_def] >> strip_tac >>
  `local_ptrs_reserved ce sn` by fs[extrequest_history_frame_def] >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `gas_marked_path F ctx func t 0 (OK u)` >>
  `extrequest_history_frame ce cx ee sm s ee su u` by
    metis_tac[extrequest_history_frame_trans] >>
  `extrequest_history_frame ce cx eb cb tb ee su u` by
    metis_tac[extrequest_history_frame_trans] >>
  `eval_operand dst u = SOME (w + n2w off)` by
    (drule_all extrequest_history_operand >> simp[]) >>
  `safe_operand su dst` by
    (irule safe_operand_mono >> qexists_tac `sn` >>
     fs[extrequest_history_frame_def]) >>
  `!x. op = Var x \/ dst = Var x ==> not_fresh_at su x` by
    (fs[safe_operand_def] >> metis_tac[]) >>
  `!name b len. local_region ce ee.scopes u name b len ==>
    b + len <= w2n (w + n2w off) \/
    w2n (w + n2w off) + type_memory_size tv <= b` by
    (rpt strip_tac >>
     `local_region ce ee.scopes s name b len` by
       metis_tac[extrequest_history_local_regions] >>
     qpat_x_assum `!name b len. local_region ce ee.scopes s name b len ==> _`
       (drule_all_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `local_ptrs_reserved ce su` by fs[extrequest_history_frame_def] >>
  drule_all (SRULE [] extrequest_store_cell_path) >> strip_tac >>
  suspend "finish"
QED

Resume snapshot_store_head[finish]:
  `ci_mono su sb` by
    (qpat_x_assum `(if is_word_type ty then _ else _) su = _` mp_tac >>
     Cases_on `is_word_type ty` >> simp[]
     >- (strip_tac >> qspecl_then [`MSTORE`, `[dst;op]`, `su`]
           mp_tac ci_mono_emit_void >> simp[]) >>
     Cases_on `is_bytestring_type ty` >> simp[]
     >- (strip_tac >> qspecl_then [`op`, `dst`, `su`]
           mp_tac ci_mono_compile_store_bytestring >> simp[]) >>
     strip_tac >> qspecl_then
       [`MCOPY`, `[dst;op;Lit (n2w (type_memory_bytes ce ty))]`, `su`]
       mp_tac ci_mono_emit_void >> simp[]) >>
  `local_ptrs_reserved ce sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `su` >> fs[ci_mono_def]) >>
  `FLOOKUP u.vs_allocas live = SOME (tuple_base,sz)` by
    (fs[extrequest_history_frame_def] >> metis_tac[]) >>
  `allocas_non_overlapping u` by
    fs[stmt_state_rel_def, state_rel_def, alloca_inv_def] >>
  `extrequest_history_frame ce cx eb cb tb ee sb
     (q with vs_inst_idx := u.vs_inst_idx)` by
    (irule extrequest_history_store_alloca >>
     conj_tac >- simp[] >>
     conj_tac >- (qexistsl_tac [`ctx`, `func`] >> simp[]) >>
     qexistsl_tac [`w2n (w + n2w off)`, `live`, `type_memory_size tv`,
       `su`, `sz`, `u`, `tuple_base`] >>
     simp[ci_mono_def, loweringStateRelDefsTheory.regions_disjoint_def,
          lookup_var_def] >>
     fs[lookup_var_def, ci_mono_def,
        loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `extrequest_history_frame ce cx eb cb tb ee sb q` by
    (qpat_x_assum `extrequest_history_frame _ _ _ _ _ _ _ (_ with vs_inst_idx := _)`
       mp_tac >> simp[extrequest_history_frame_def, lookup_var_def] >> metis_tac[]) >>
  suspend "frames"
QED

Resume snapshot_store_head[frames]:
  `gas_marked_path F ctx func s 0 (OK u)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
       (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then (qspecl_then [`OK u`, `0`] mp_tac) >> simp[]) >>
  `gas_marked_path F ctx func s 0 (OK q)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK u)`
       (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then (qspecl_then [`OK q`, `0`] mp_tac) >> simp[]) >>
  `q.vs_allocas = u.vs_allocas` by
    (qpat_x_assum `q with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = u` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `q` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory` by
        (irule extrequest_history_alloc_window >>
         qpat_assum `extrequest_history_frame ce cx ee sm s ee su u` (irule_at Any) >>
         qpat_assum `FLOOKUP s.vs_allocas live = _` (irule_at Any) >> simp[] >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at su x` by
        (irule not_fresh_at_mono >> qexists_tac `sm` >> fs[extrequest_history_frame_def]) >>
      fs[extrequest_history_frame_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[extrequest_history_frame_def] >> metis_tac[]) >>
  conj_tac >- suspend "old_allocations" >>
  conj_tac >- suspend "local_bytes" >>
  suspend "immutable_bytes"
QED

Resume snapshot_store_head[old_allocations]:
  map_every qx_gen_tac [`aid`, `old_base`, `old_size`] >> strip_tac >>
  `FLOOKUP u.vs_allocas aid = SOME (old_base,old_size)` by
    (fs[extrequest_history_frame_def] >> metis_tac[]) >>
  `old_base + old_size <= tuple_base \/ tuple_base + sz <= old_base` by
    (qpat_x_assum `allocas_non_overlapping u` mp_tac >>
     rewrite_tac[allocas_non_overlapping_def] >>
     disch_then (qspecl_then [`aid`, `live`, `old_base`, `old_size`, `tuple_base`, `sz`] mp_tac) >>
     simp[]) >>
  `mem_bytes_at old_base old_size u.vs_memory = mem_bytes_at old_base old_size s.vs_memory` by
    (`FLOOKUP t.vs_allocas aid = SOME (old_base,old_size)` by
       (fs[extrequest_history_frame_def] >> metis_tac[]) >>
     `aid < sn.cs_next_id` by (fs[extrequest_history_frame_def] >> decide_tac) >>
     `t.vs_memory = s.vs_memory` by
       (qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
        simp[venom_state_component_equality]) >> metis_tac[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]
QED

Resume snapshot_store_head[local_bytes]:
  rpt strip_tac >>
  `mem_bytes_at b len u.vs_memory = mem_bytes_at b len s.vs_memory` by
    (fs[extrequest_history_frame_def] >> metis_tac[]) >>
  `b + len <= w2n (w + n2w off) \/
   w2n (w + n2w off) + type_memory_size tv <= b` by
    (qpat_x_assum `!name b len. local_region ce ee.scopes s name b len ==> _`
       (drule_all_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED

Resume snapshot_store_head[immutable_bytes]:
  rpt strip_tac >>
  `mem_bytes_at io (type_memory_size itv) u.vs_memory =
   mem_bytes_at io (type_memory_size itv) s.vs_memory` by
    (fs[extrequest_history_frame_def] >> metis_tac[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]
QED

Finalise snapshot_store_head[local]

Theorem extrequest_snapshot_store_fold:
  extrequest_snapshot_store_contract ctx func ce cx
Proof
  rewrite_tac[extrequest_snapshot_store_contract_def] >> Induct
  >- (simp[compile_extcall_store_values_def, comp_return_def] >>
      rpt strip_tac >> qexists_tac `s` >>
      simp[valueEncodingDefsTheory.val_in_memory_def, gas_marked_path_def] >>
      irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]) >>
  qx_gen_tac `cell` >> PairCases_on `cell` >> rpt gen_tac >>
  simp[compile_extcall_store_values_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >>
  rename1 `extrequest_snapshot_cell _ _ _ _ _ _ _ (vv,ty,tv,v)` >>
  qpat_x_assum `(\(dst,st). _) _ = _` mp_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  strip_tac >>
  rename1 `emit_op ADD _ sm = (dst,sn)` >>
  rename1 `unwrap_value ce vv sn = (op,su)` >>
  rename1 `(if is_word_type ty then _ else _) su = ((),sh)` >>
  `ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sh /\ ci_mono sh sb` by
    (rpt conj_tac
     >- (qspecl_then [`ADD`, `[buf; Lit (n2w off)]`, `sm`]
           mp_tac ci_mono_emit_op >> simp[])
     >- (qspecl_then [`ce`, `vv`, `sn`] mp_tac ci_mono_unwrap_value >> simp[])
     >- (qpat_x_assum `(if is_word_type ty then _ else _) su = _` mp_tac >>
         Cases_on `is_word_type ty` >> simp[]
         >- (strip_tac >> qspecl_then [`MSTORE`, `[dst;op]`, `su`]
               mp_tac ci_mono_emit_void >> simp[]) >>
         Cases_on `is_bytestring_type ty` >> simp[]
         >- (strip_tac >> qspecl_then [`op`, `dst`, `su`]
               mp_tac ci_mono_compile_store_bytestring >> simp[]) >>
         strip_tac >> qspecl_then
           [`MCOPY`, `[dst;op;Lit (n2w (type_memory_bytes ce ty))]`, `su`]
           mp_tac ci_mono_emit_void >> simp[]) >>
     qspecl_then [`MAP (\(vv,ty,tv,v). (vv,ty)) cells`,
       `off + type_memory_bytes ce ty`, `sh`] mp_tac
       (INST [``cenv : compile_env`` |-> ``ce : compile_env``]
         extrequest_store_values_mono) >> simp[]) >>
  `fn_has_code sm sn func /\ fn_has_code sn su func /\
   fn_has_code su sh func /\ fn_has_code sh sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `w2n (w + n2w off) = w2n w + off` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> simp[]) >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    fs[extrequest_snapshot_cell_def] >>
  `tuple_base <= w2n (w + n2w off) /\
   w2n (w + n2w off) + type_memory_size tv <= tuple_base + sz` by decide_tac >>
  `ce.ce_is_ctor ==> !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv)
       (w2n (w + n2w off)) (type_memory_size tv)` by
    (rpt strip_tac >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     first_x_assum (drule_all_then mp_tac) >> decide_tac) >>
  drule_all snapshot_store_head >> strip_tac >>
  suspend "tail"
QED

Resume extrequest_snapshot_store_fold[tail]:
  rename1 `gas_marked_path F ctx func s 0 (OK h)` >>
  `eval_operand buf h = SOME w` by
    (Cases_on `buf` >>
     gvs[eval_operand_def, safe_operand_def] >> metis_tac[]) >>
  `safe_operand sh buf` by
    (fs[safe_operand_def, ci_mono_def] >>
     metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  `!name b len. local_region ce ee.scopes h name b len ==>
       regions_disjoint tuple_base sz b len` by
    (rpt strip_tac >>
     `local_region ce eb.scopes tb name b len` by
       metis_tac[extrequest_history_local_regions] >>
     metis_tac[extrequest_history_local_regions]) >>
  `live < sh.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  first_x_assum (qspecl_then [`off + type_memory_bytes ce ty`, `sh`, `sb`, `h`,
    `eb`, `cb`, `tb`, `ee`, `buf`, `live`, `tuple_base`, `sz`, `w`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  suspend "finish"
QED

Resume extrequest_snapshot_store_fold[finish]:
  rename1 `gas_marked_path F ctx func h 0 (OK q)` >>
  `mem_bytes_at (w2n w + off) (type_memory_size tv) q.vs_memory =
   mem_bytes_at (w2n w + off) (type_memory_size tv) h.vs_memory` by
    (qpat_x_assum `!a k. tuple_base <= a /\ _ ==> mem_bytes_at a k q.vs_memory = _` irule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `val_in_memory tv v (w2n w + off) q.vs_memory` by
    (irule val_in_memory_mem_agree >>
     conj_tac >- fs[extrequest_snapshot_cell_def] >>
     qexistsl_tac [`type_memory_size tv`, `h.vs_memory`] >> gvs[]) >>
  `!x z. not_fresh_at sm x /\ lookup_var x s = SOME z ==>
      lookup_var x q = SOME z` by
    (map_every qx_gen_tac [`reg`, `word`] >> strip_tac >>
     `not_fresh_at sh reg` by
       (fs[ci_mono_def] >>
        metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  `!aid p k. aid < sm.cs_next_id /\ aid <> live /\
      FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
      mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory` by
    (map_every qx_gen_tac [`aid`, `old_base`, `old_size`] >> strip_tac >>
     `FLOOKUP h.vs_allocas aid = SOME (old_base,old_size)` by metis_tac[] >>
     `aid < sh.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
     metis_tac[]) >>
  `!name b len. local_region ce ee.scopes s name b len ==>
      mem_bytes_at b len q.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     `local_region ce ee.scopes h name b len` by
       metis_tac[extrequest_history_local_regions] >> metis_tac[]) >>
  qexists_tac `q` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  simp[valueEncodingDefsTheory.val_in_memory_def] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM] >>
  conj_tac >- suspend "windows" >>
  rpt strip_tac >> metis_tac[]
QED

Resume extrequest_snapshot_store_fold[windows]:
  rpt strip_tac >>
  `mem_bytes_at a k q.vs_memory = mem_bytes_at a k h.vs_memory` by
    (qpat_assum `!a k. tuple_base <= a /\ _ ==> mem_bytes_at a k q.vs_memory = _` irule >> simp[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at a k h.vs_memory = mem_bytes_at a k s.vs_memory` by
    (qpat_assum `!a k. tuple_base <= a /\ _ ==> mem_bytes_at a k h.vs_memory = _` irule >> simp[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED

Finalise extrequest_snapshot_store_fold
