(* The arm step of a ternary whose selected arm is a shorter bytestring
   than the ternary's: allocate a buffer of the ternary's type, unwrap the
   arm's value, copy it in, as one joint path with no GAS site, and give
   the ternary's posts at the arm's end at one horizon H.  The shared
   joint unwrap_value, alloc and bytestring-copy lemmas are premises until
   they land. *)
Theory bodyFullIfExpWiden
Ancestors
  vyperStorageFootprint bodySimFull fragGasOriginPtr exprSimIfExp exprSimDefs exprSimMemDefs
  bodyPtrDefs loweringPosts exprLowering exprLoweringProps fragExec
  emitHelper compileEnv allocaHistory stmtSimDefs vyperAST
  vyperInterpreter vyperState venomState fragGasSeqPtr fragGasEmitCtrl
  instMemFrontier memSafeRun ptrSafeRun ptrDiscipline venomInst
  ctorDeployMemoryRunPtrMono exprOperandVar exprSimVVFrame exprSimProps
  venomExecSemantics loweringStateRelDefs finite_map robustCopyTransportPtr
  exprSimUnwrap loweringHalt context exprSimAlloc
  exprSimIfExpWidenedPosts valueCopy

(* Conditional ghost boundary for the actual copy endpoint.  The window
   premises are the bytewise consequences of the copy's memory/taint equations;
   separation is required only for protected footprints and kept regions. *)
Theorem ifexp_widen_copy_ghost_finish:
  compile_ifexp_arm cenv t armty vv sm = (op,sb) /\
  ~is_word_type t /\ is_bytestring_type t /\
  evaluate_type (get_tenv cx) t = SOME rt /\
  val_wf rt v /\ val_footprint rt v <= n /\
  val_store_size rt v <= cap /\ type_memory_bytes cenv t <= cap /\
  op = Var dst /\ lookup_var dst s' = SOME dw /\
  FLOOKUP G' dst = SOME (w2n dw,cap) /\ op_taint tn' (Var dst) = {} /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory rt v src m) /\
  mem_bytes_at (w2n dw) n s'.vs_memory = mem_bytes_at src n s.vs_memory /\
  (!i. i < n ==> (w2n dw+i IN tn'.t_mem <=> src+i IN tn.t_mem)) /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x s' = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!name entry p sz w. lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
       lookup_var p s = SOME w ==>
       val_wf entry.type entry.value /\
       (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
            i NOTIN writes)) /\
  (!i. i NOTIN writes ==> mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory /\
       (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  (!i. i < lo ==> i NOTIN writes) /\
  mem_bytes_at 0 lo s'.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_accounts = s.vs_accounts /\
  s'.vs_transient = s.vs_transient /\ s'.vs_immutables = s.vs_immutables /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa0 x ==> not_fresh_at sa x) /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
       (!name b k. local_region cenv es0.scopes s0 name b k ==>
            off+sz <= b \/ b+k <= off) /\ off <= i /\ i < off+sz ==> i NOTIN writes) /\
  (!name b k i. local_region cenv es0.scopes s0 name b k /\
       b <= i /\ i < b+k ==> i NOTIN writes) ==>
  ghost_inv_at D lo d cenv cx es G' tn' s' /\
  ptr_val_ok cx t v op G' tn' s' /\
  (!e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op G' s') /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  `!p k. not_fresh_at sa p /\ ptr_covers G tn p s k ==>
          ptr_covers G' tn' p s' k` by
    (rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- suspend "inv" >>
  conj_tac >- suspend "value" >>
  conj_tac >- (rpt strip_tac >> simp[ptr_buf_ok_def, eval_operand_def] >> metis_tac[]) >>
  suspend "kept"
QED

Resume ifexp_widen_copy_ghost_finish[inv]:
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  conj_tac >- suspend "locals" >>
  conj_tac >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
    PairCases_on `x` >> gvs[return_buf_ptr_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- gvs[stor_taint_ok_at_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Resume ifexp_widen_copy_ghost_finish[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`s.vs_memory`, `s'.vs_memory`, `tn.t_mem`, `tn'.t_mem`, `writes`] >>
  metis_tac[]
QED

Resume ifexp_widen_copy_ghost_finish[value]:
  simp[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >>
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `s'.vs_memory`, `n`, `src`, `tn.t_mem`, `tn'.t_mem`] >>
  simp[]
QED

Resume ifexp_widen_copy_ghost_finish[kept]:
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_kept_at_def] >> metis_tac[]
QED

Finalise ifexp_widen_copy_ghost_finish

(* Fixed-endpoint semantic half of the copy boundary.  The ordinary copy
   execution is used only to recover state frames at the supplied endpoint. *)
Theorem ifexp_widen_copy_endpoint_posts:
  compile_ifexp_arm ce t lt vv sm = (dst,sb) /\
  compile_store_bytestring src dst sn = ((),sb) /\
  run_inst_seq (emitted_insts sn sb) s = OK sf /\
  q = sf with vs_inst_idx := idx /\
  expr_type e = t /\ post_value_type ce e = t /\
  expr_post H ctx func ce cx e es origin sn s0 ee v src s /\
  read_result cx raw ee = (INL v,ee) /\
  is_bytestring_type t /\ ~is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  mem_word_at (w2n sw) s.vs_memory = n2w len /\
  val_store_size tv v = 32 + 32 * word_size len /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sn x) /\
  type_memory_size tv < dimword (:256) /\ type_memory_size tv <= N /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,N) /\
  w2n dw + N <= s.vs_alloca_next /\
  local_ptrs_reserved ce sn /\
  (!name b sz. local_region ce ee.scopes s name b sz ==>
    b+sz <= w2n dw \/ w2n dw+N <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n dw) N) /\
  (!name b sz. local_region ce es.scopes s0 name b sz ==>
    local_region ce ee.scopes s name b sz) /\
  (!old off len. FLOOKUP s0.vs_allocas old = SOME (off,len) /\
    old < origin.cs_next_id ==> w2n dw+N <= off \/ off+len <= w2n dw) /\
  origin.cs_next_var <= sn.cs_next_var /\
  origin.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) ==>
  expr_post H ctx func ce cx (IfExp t c a b) es origin sb s0 ee v dst q /\
  vv_at ce cx t origin sb ee raw (LocatedValue t (mk_ptr dst LocMemory)) q /\
  expr_store_bound cx t v dst q /\
  (!rt w. evaluate_type (get_tenv cx) t = SOME rt /\ eval_operand dst q = SOME w ==>
    type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= q.vs_alloca_next) /\
  (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!off len. off+len <= w2n dw \/ w2n dw+N <= off ==>
    mem_bytes_at off len q.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >>
  `stmt_state_rel H ctx func ce cx ee s` by fs[expr_post_def] >>
  `val_wf tv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `32 + 32 * word_size len <= type_memory_size tv` by metis_tac[val_store_size_le] >>
  `32 + 32 * word_size len < dimword (:256)` by decide_tac >>
  drule store_bytestring_run_exact >>
  disch_then (qspecl_then [`s`, `sw`, `dw`, `len`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = OK t'` mp_tac >>
  simp[] >> disch_then SUBST_ALL_TAC >>
  rename1 `q = sf with vs_inst_idx := idx` >>
  `sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
   sf.vs_labels = s.vs_labels` by
    (qpat_x_assum `sf with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!off k. off+k <= w2n dw \/ w2n dw+N <= off ==>
     mem_bytes_at off k sf.vs_memory = mem_bytes_at off k s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  `LENGTH s.vs_memory <= LENGTH sf.vs_memory` by
    simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity,
         arithmeticTheory.MAX_DEF] >>
  `val_in_memory tv v (w2n dw) sf.vs_memory` by suspend "encoding" >>
  `stmt_state_rel H ctx func ce cx ee sf` by suspend "state" >>
  `eval_operand dst sf = SOME dw` by
    (Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `!name lb sz. local_region ce ee.scopes sf name lb sz ==>
     local_region ce ee.scopes s name lb sz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`sn`, `ee.scopes`, `sf`] >> simp[]) >>
  conj_tac >- suspend "post" >>
  conj_tac >- suspend "vv_at" >>
  conj_tac >- suspend "store" >>
  simp[] >> rpt strip_tac >> gvs[] >> decide_tac
QED

Resume ifexp_widen_copy_endpoint_posts[encoding]:
  irule exprSimMemoryTransportTheory.val_in_memory_relocate_footprint >>
  conj_tac >- simp[] >>
  qexistsl [`s.vs_memory`, `w2n sw`] >> simp[] >>
  sym_tac >>
  `val_footprint tv v <= 32 + 32 * word_size len` by
    metis_tac[val_footprint_le_store_size] >>
  irule listTheory.LIST_EQ >> simp[] >> rpt strip_tac >>
  simp[valueEncodingProofsTheory.EL_mem_bytes_at,
       GSYM allocaRemapDefsTheory.mem_byte_at_def] >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule (SRULE [LET_THM] copyFwdEquivTheory.mcopy_establishes_equiv) >> decide_tac
QED

Resume ifexp_widen_copy_endpoint_posts[state]:
  irule exprSimLiteralBufferTheory.literal_state_memory_frame >>
  qexists_tac `s` >> simp[] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _` drule >>
    strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `local_ptrs_reserved ce sn` mp_tac >>
    simp[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `local_ptrs_reserved ce sn` mp_tac >>
    simp[local_ptrs_reserved_def] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `ce.ce_is_ctor ==> _` drule >>
  disch_then drule >> strip_tac >>
  irule mem_bytes_at_mcopy_disjoint >> gvs[regions_disjoint_def] >> decide_tac
QED

Resume ifexp_widen_copy_endpoint_posts[post]:
  drule allocated_result_expr_post_frame >> disch_then irule >>
  simp[expr_type_def, expr_val_rel_def, stmt_state_rel_inst_idx] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!name lb sz. local_region _ _ sf _ _ _ ==> _` irule >>
    fs[local_region_def, lookup_var_def]) >>
  conj_tac >- (simp[lookup_var_def] >> rpt strip_tac >>
    `not_fresh_at sn x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
    qpat_x_assum `!x. not_fresh_at sn x ==> _` drule >> simp[lookup_var_def]) >>
  reverse conj_tac >- (qpat_x_assum `val_in_memory tv v (w2n dw) sf.vs_memory` mp_tac >> simp[]) >>
  qexistsl [`N`, `w2n dw`, `inst`] >> simp[] >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac >- (rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  decide_tac
QED

Resume ifexp_widen_copy_endpoint_posts[vv_at]:
  simp[vv_at_def, mk_ptr_def] >> rpt strip_tac >>
  disj1_tac >> qexistsl [`aid`, `w2n dw`, `N`] >>
  simp[] >> conj_tac >- metis_tac[val_footprint_le, arithmeticTheory.LESS_EQ_TRANS] >>
  rpt strip_tac >>
  `local_region ce ee.scopes sf n lb lsz` by fs[local_region_def, lookup_var_def] >>
  `local_region ce ee.scopes s n lb lsz` by metis_tac[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume ifexp_widen_copy_endpoint_posts[store]:
  simp[expr_store_bound_def] >> rpt strip_tac >> gvs[]
QED

Finalise ifexp_widen_copy_endpoint_posts

Theorem ifexp_widen_copy_endpoint_windows:
  compile_ifexp_arm ce t lt vv sm = (op,sb) /\
  s'.vs_memory = (mcopy dst src n s).vs_memory /\
  tf.t_mem = (tn.t_mem DIFF {i | dst <= i /\ i < dst+n}) UNION
             {dst+i | i < n /\ src+i IN tn.t_mem} /\
  lo <= dst ==>
  mem_bytes_at dst n s'.vs_memory = mem_bytes_at src n s.vs_memory /\
  (!i. i < n ==> (dst+i IN tf.t_mem <=> src+i IN tn.t_mem)) /\
  (!i. i NOTIN {j | dst <= j /\ j < dst+n} ==>
    mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  (!i. i < lo ==> i NOTIN {j | dst <= j /\ j < dst+n}) /\
  mem_bytes_at 0 lo s'.vs_memory = mem_bytes_at 0 lo s.vs_memory
Proof
  strip_tac >>
  conj_tac >- simp[valueEncodingPropsTheory.mcopy_mem_bytes_at_same] >>
  conj_tac >- (simp[] >> rpt strip_tac >> simp[pred_setTheory.IN_UNION,
    pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION] >> metis_tac[]) >>
  conj_tac >- (gen_tac >> disch_tac >> conj_tac
    >- (simp[] >> irule mem_bytes_at_mcopy_disjoint >> fs[])
    >> simp[pred_setTheory.IN_UNION, pred_setTheory.IN_DIFF,
            pred_setTheory.GSPECIFICATION] >>
       fs[] >> eq_tac >- (strip_tac >> gvs[] >> decide_tac) >> simp[]) >>
  conj_tac >- simp[] >>
  simp[] >> irule mem_bytes_at_mcopy_disjoint >> simp[]
QED

Theorem ifexp_widen_empty_dead_path:
  compile_ifexp_arm cenv t sty vv sm = (op,sb) /\
  gas_origin_ptr_path
    (<|d_stor := (\a st. {}); d_trans := (\a st. {});
       d_imm := (\im. {}); d_ret := (\ret. {})|>,
     lo,explicit,ctx,func,PG) (s,G,tn) marks (r,Gf,tf) ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) marks (r,Gf,tf)
Proof
  qabbrev_tac `E = <|d_stor := (\a st. {}); d_trans := (\a st. {});
                     d_imm := (\im. {}); d_ret := (\ret. {})|>` >>
  `!lo fuel ctx fn PG G tn inst s D.
     ptr_safe_step E lo fuel ctx fn PG G tn inst s ==>
     ptr_safe_step D lo fuel ctx fn PG G tn inst s` by
    (rpt strip_tac >> irule (cj 1 ptr_safe_dead_mono) >>
     qexists_tac `E` >> simp[Abbr `E`]) >>
  `!lo explicit ctx fn PG st marks out D.
     gas_origin_ptr_edge (E,lo,explicit,ctx,fn,PG) st marks out ==>
     gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) st marks out` by
    (rpt gen_tac >> PairCases_on `st` >> PairCases_on `out` >>
     simp[gas_origin_ptr_edge_def, fragGasPathPtrTheory.gas_path_ptr_edge_def] >>
     metis_tac[]) >>
  `!cfg st marks out.
     gas_origin_ptr_path cfg st marks out ==>
     !lo explicit ctx fn PG.
       cfg = (E,lo,explicit,ctx,fn,PG) ==>
       !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) st marks out` by
    (ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >>
     rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
     gvs[] >> metis_tac[gas_origin_ptr_path_rules]) >>
  metis_tac[]
QED

Theorem ifexp_widen_copy_parts:
  ~is_word_type dty /\ ~same_memory_layout ce sty dty /\
  compile_ifexp_arm ce dty sty vv sa = (op,sb) ==>
  ?buf sm src sn.
    compile_alloc_buffer (type_memory_bytes ce dty) sa = (buf,sm) /\
    unwrap_value ce vv sm = (src,sn) /\
    compile_store_memory ce src buf.buf_operand dty sty sn = ((),sb) /\
    op = buf.buf_operand
Proof
  strip_tac >>
  gvs[compile_ifexp_arm_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem ifexp_widen_vv_post_alloc_frame:
  compile_ifexp_arm ce dty sty vv sm = (armop,armend) /\
  vv_post H ctx func ce cx e es sa sm s0 ee tv vv s /\
  stmt_state_rel H ctx func ce cx ee u /\
  u.vs_memory = s.vs_memory /\
  contract_storage u = contract_storage s /\
  contract_transient u = contract_transient s /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!n b sz. local_region ce ee.scopes u n b sz <=>
            local_region ce ee.scopes s n b sz) /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_post H ctx func ce cx e es sa sn s0 ee tv vv u
Proof
  strip_tac >>
  `!cenv cx ty sa sm es tv vv s t sn.
    vv_at cenv cx ty sa sm es tv vv s /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
    (!n b sz. local_region cenv es.scopes t n b sz <=>
              local_region cenv es.scopes s n b sz) /\
    sm.cs_next_id <= sn.cs_next_id ==>
    vv_at cenv cx ty sa sn es tv vv t` by
    (POP_ASSUM_LIST (K all_tac) >> rpt gen_tac >> Cases_on `vv` >>
     simp[vv_at_def, contextTheory.vv_operand_def, expr_val_at_def] >>
     rpt strip_tac >> gvs[]
     >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
           disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >> metis_tac[]) >>
     metis_tac[]) >>
  `!cenv cx ty sa sm es tv vv s t sn.
    vv_own cenv cx ty sa sm es tv vv s /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
    (!n b sz. local_region cenv es.scopes t n b sz <=>
              local_region cenv es.scopes s n b sz) /\
    sm.cs_next_id <= sn.cs_next_id ==>
    vv_own cenv cx ty sa sn es tv vv t` by
    (POP_ASSUM_LIST (K all_tac) >> rpt gen_tac >> Cases_on `vv` >>
     simp[vv_own_def, contextTheory.vv_operand_def, expr_val_own_def] >>
     rpt strip_tac >> gvs[]
     >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
           disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >> metis_tac[]) >>
     metis_tac[]) >>
  qpat_x_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  `vv_holds ce cx (post_value_type ce e) tv vv ee u` by
    (irule vv_holds_vars_frame >> goal_assum (drule_at Any) >> simp[]) >>
  `vv_at ce cx (post_value_type ce e) sa sn ee tv vv u` by
    (qpat_assum `!cenv cx ty sa sm es tv vv s t sn. vv_at _ _ _ _ _ _ _ _ _ /\ _ ==> _` irule >>
     qexistsl [`s`, `sm`] >> simp[]) >>
  `post_value_type ce e <> expr_type e ==>
    vv_own ce cx (post_value_type ce e) sa sn ee tv vv u` by
    (strip_tac >>
     qpat_assum `!cenv cx ty sa sm es tv vv s t sn. vv_own _ _ _ _ _ _ _ _ _ /\ _ ==> _` irule >>
     qexistsl [`s`, `sm`] >> simp[]) >>
  `locals_kept ce es ee s0 u` by
    (irule locals_kept_mem_tail >> goal_assum (drule_at Any) >> simp[]) >>
  `vv_storage_live H cx vv ee s ==> vv_storage_live H cx vv ee u` by
    (Cases_on `vv` >> fs[contextTheory.vv_operand_def]) >>
  `~expr_has_effect e ==> pure_frame ce func es sa s0 u` by
    (strip_tac >> irule pure_frame_mem_tail >> qexists_tac `s` >> simp[]) >>
  simp[vv_post_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem ifexp_widen_alloc_resources_frame:
  compile_ifexp_arm cenv t lt vv sm = (op,sb) /\
  post_value_type cenv e = t /\ expr_type e = t /\ ~is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  ptr_vv_ok cx t tv vv ee G tn s /\
  vv_store_bound cx t lt ee tv vv s /\
  (!t' op0. vv = StackValue t' op0 /\ ~is_word_type t ==>
     ptr_buf_ok cenv e op0 G s) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
     !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
            eval_operand (vv_operand vv) s = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  op_taint tq (vv_operand vv) = op_taint tn (vv_operand vv) /\
  op_prov Gq (vv_operand vv) = op_prov G (vv_operand vv) /\
  (!x. vv_operand vv = Var x ==> FLOOKUP Gq x = FLOOKUP G x) /\
  q.vs_memory = s.vs_memory /\ q.vs_accounts = s.vs_accounts /\
  q.vs_call_ctx = s.vs_call_ctx /\ q.vs_transient = s.vs_transient /\
  tq.t_stor = tn.t_stor /\ tq.t_trans = tn.t_trans /\
  s.vs_alloca_next <= q.vs_alloca_next /\ lo <= s.vs_alloca_next /\
  (!i. i < s.vs_alloca_next ==> (i IN tq.t_mem <=> i IN tn.t_mem)) ==>
  ptr_vv_ok cx t tv vv ee Gq tq q /\
  vv_store_bound cx t lt ee tv vv q /\
  (!t' op0. vv = StackValue t' op0 /\ ~is_word_type t ==>
     ptr_buf_ok cenv e op0 Gq q) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand Gq q) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
     !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
            eval_operand (vv_operand vv) q = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tq.t_mem q.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem))
Proof
  strip_tac >>
  `!v. read_result cx tv ee = (INL v,ee) ==> val_wf rty v` by
    metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `!v p. val_wf rty v /\
      (val_store_size rty v = 0 \/ p + val_store_size rty v <= s.vs_alloca_next) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory rty v p m) ==>
      !m. mem_agree_outside tq.t_mem q.vs_memory m ==> val_in_memory rty v p m` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     rpt gen_tac >> disch_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     map_every qexists_tac [`s.vs_memory`, `q.vs_memory`, `tn.t_mem`, `tq.t_mem`,
                   `{i | s.vs_alloca_next <= i}`] >>
     simp[] >> rpt strip_tac >>
     mp_tac (Q.SPECL [`rty`, `v`] val_footprint_le_store_size) >> decide_tac) >>
  conj_tac >- suspend "pointer" >>
  conj_tac >- suspend "bound" >>
  conj_tac >- (rpt strip_tac >> Cases_on `vv` >> gvs[vv_operand_def, ptr_buf_ok_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> Cases_on `vv` >> gvs[vv_operand_def, ptr_buf_ok_def] >> metis_tac[]) >>
  suspend "ctor"
QED

Resume ifexp_widen_alloc_resources_frame[pointer]:
  Cases_on `vv` >> gvs[vv_operand_def, ptr_vv_ok_def, ptr_val_ok_def] >>
  TRY (rename1 `p.ptr_operand` >> Cases_on `p.ptr_location` >>
       gvs[] >> NO_TAC) >>
  gvs[ptr_mem_ok_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  gvs[vv_store_bound_def] >> metis_tac[]
QED
Resume ifexp_widen_alloc_resources_frame[bound]:
  qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `eval_operand _ q = _` mp_tac >>
  qpat_x_assum `s.vs_alloca_next <= q.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `vv` >> simp[vv_operand_def, vv_store_bound_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
Resume ifexp_widen_alloc_resources_frame[ctor]:
  strip_tac >>
  qpat_x_assum `cenv.ce_is_ctor /\ _ ==> _` mp_tac >>
  simp[] >> strip_tac >> qexists_tac `val` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  `val_wf rty val` by metis_tac[] >>
  `val_footprint rty val <= type_memory_size rty` by
    simp[val_footprint_le] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  map_every qexists_tac [`s.vs_memory`, `q.vs_memory`, `tn.t_mem`, `tq.t_mem`,
                        `{i | s.vs_alloca_next <= i}`] >>
  simp[] >> rpt strip_tac >> decide_tac
QED
Finalise ifexp_widen_alloc_resources_frame

(* Concrete allocation boundary; the cursor update is deliberately separate
   from execution of the instruction body. *)
Theorem ifexp_widen_alloc_boundary:
  compile_ifexp_arm cenv t src_ty vv sm = (op,sb) /\
  compile_alloc_buffer n sm = (buf,sc) /\ buf.buf_operand = Var out /\
  FLOOKUP s.vs_allocas sm.cs_next_id = NONE /\ n < dimword (:256) /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK az /\
  q = az with vs_inst_idx := SUC s.vs_inst_idx /\
  Ga = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [out]) az /\
  ta = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [out]) s az tn /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) ==>
  q.vs_memory = s.vs_memory /\ q.vs_accounts = s.vs_accounts /\
  q.vs_call_ctx = s.vs_call_ctx /\ q.vs_transient = s.vs_transient /\
  q.vs_immutables = s.vs_immutables /\ q.vs_labels = s.vs_labels /\
  q.vs_current_bb = s.vs_current_bb /\ q.vs_halted = s.vs_halted /\
  q.vs_inst_idx = SUC s.vs_inst_idx /\
  q.vs_alloca_next = s.vs_alloca_next + n /\
  s.vs_alloca_next <= q.vs_alloca_next /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!x. not_fresh_at sm x ==>
    lookup_var x q = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
    op_taint ta (Var x) = op_taint tn (Var x)) /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) /\
  Ga = G |+ (out,(s.vs_alloca_next,n)) /\
  ta = tn with <|t_mem := tn.t_mem UNION
      {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+n};
      t_var := tn.t_var |+ (out,{})|>
Proof
  strip_tac >>
  `az = update_var out (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+
      (sm.cs_next_id,(s.vs_alloca_next,n));
      vs_alloca_next := s.vs_alloca_next+n|>)` by
    (drule_all step_alloca_fresh >> disch_then (qspec_then `out` mp_tac) >> gvs[]) >>
  `new_site_bytes s az =
      {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+n}` by
    (rw[new_site_bytes_def, update_var_def, FLOOKUP_UPDATE,
        pred_setTheory.EXTENSION] >>
     gvs[AllCaseEqs(), FLOOKUP_DEF] >> eq_tac
     >- (strip_tac >> gvs[] >> decide_tac) >>
     strip_tac >> qexistsl [`sm.cs_next_id`, `s.vs_alloca_next`, `n`] >> simp[]) >>
  `Ga = G |+ (out,(s.vs_alloca_next,n)) /\
   ta = tn with <|t_mem := tn.t_mem UNION
      {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+n};
      t_var := tn.t_var |+ (out,{})|>` by
    (simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       update_var_def, FLOOKUP_UPDATE, step_taint_def, mem_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, written_taint_def, set_var_taint_def, out_taint_def,
       eval_operand_def, store_taint_def, imm_taint_def, adopt_reset_def] >>
     simp[taint_component_equality]) >>
  `!x. not_fresh_at sm x ==> x <> out` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `ta = step_taint _ _ _ _` kall_tac >>
  gvs[update_var_def] >>
  simp[lookup_var_def, FLOOKUP_UPDATE, op_taint_def] >>
  Cases_on `vv_operand vv` >> simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem ifexp_widen_alloc_boundary_general:
  compile_ifexp_arm cenv t src_ty vv sm = (op,sb) /\
  compile_alloc_buffer n sm = (buf,sc) /\ buf.buf_operand = Var out /\
  n < dimword (:256) /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK az /\
  q = az with vs_inst_idx := SUC s.vs_inst_idx /\
  Ga = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [out]) az /\
  ta = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [out]) s az tn /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) ==>
  q.vs_memory = s.vs_memory /\ q.vs_accounts = s.vs_accounts /\
  q.vs_call_ctx = s.vs_call_ctx /\ q.vs_transient = s.vs_transient /\
  q.vs_immutables = s.vs_immutables /\ q.vs_labels = s.vs_labels /\
  q.vs_current_bb = s.vs_current_bb /\ q.vs_halted = s.vs_halted /\
  q.vs_inst_idx = SUC s.vs_inst_idx /\
  s.vs_alloca_next <= q.vs_alloca_next /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv) /\
  op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv) /\
  (!x. not_fresh_at sm x ==>
    lookup_var x q = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
    op_taint ta (Var x) = op_taint tn (Var x)) /\
  (!x. vv_operand vv = Var x ==> FLOOKUP Ga x = FLOOKUP G x) /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `!x. not_fresh_at sm x ==> x <> out` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id`
  >- (drule_all ifexp_widen_alloc_boundary >> strip_tac >>
      gvs[] >> Cases_on `vv_operand vv` >>
      simp[op_prov_def, op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  PairCases_on `x` >>
  `az = update_var out (n2w x0) s` by
    (gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def]) >>
  `new_site_bytes s az = {}` by
    (simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
          pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `Ga = G |+ (out,(x0,x1)) /\ ta = tn with t_var := tn.t_var |+ (out,{})` by
    (simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       update_var_def, FLOOKUP_UPDATE, step_taint_def, mem_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, written_taint_def, set_var_taint_def, out_taint_def,
       eval_operand_def, store_taint_def, imm_taint_def, adopt_reset_def] >>
     simp[taint_component_equality]) >>
  qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `ta = step_taint _ _ _ _` kall_tac >>
  gvs[update_var_def] >>
  simp[lookup_var_def, FLOOKUP_UPDATE, op_taint_def] >>
  Cases_on `vv_operand vv` >>
  simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, op_prov_def, op_taint_def] >>
  metis_tac[]
QED

Theorem ifexp_widen_arm_step_full:
  (* The shared joint unwrap_value lemma on H (r8, family form), here a
     premise until it lands. *)
  (!ty e sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti st0.
    compile_expr cenv ty e sa = (vv,sm) /\
    (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
    sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
    unwrap_value cenv vv sb = (op,sc) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
      ~is_word_type (post_value_type cenv e) ==>
      type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
      type_memory_size rt < 2**64) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
       ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
    (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op0 G s) /\
    (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G s) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val, ee) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                  eval_operand (vv_operand vv) s = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                         val_in_memory rt val (w2n w) mem)) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    ?v z G' tn'.
      read_result cx tv ee = (INL v, ee) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
           (s, G, tn) [] (OK z, G', tn') /\
         expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
         ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
      (~is_word_type (post_value_type cenv e) ==>
       vv_at cenv cx (post_value_type cenv e) sa sc ee tv
         (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
      expr_store_bound cx (expr_type e) v op z /\
      z.vs_current_bb = sc.cs_current_bb /\
      z.vs_inst_idx = LENGTH sc.cs_current_insts /\
      alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
      s0.vs_alloca_next <= z.vs_alloca_next /\
      ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
      (~is_word_type (post_value_type cenv e) ==>
       !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
              eval_operand op z = SOME w ==>
              type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
      ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
      (!x. not_fresh_at sb x ==>
           lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
           op_taint tn' (Var x) = op_taint tn (Var x)) /\
      wb_frame cenv ee ee sb s z /\
      ghost_kept_at lo cenv ee sb G tn s G' tn') /\
  (* ifexp_alloca_origin_ptr_edge *)
  (!s ctx lo fn bb id n p u D explicit PG G tn.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
    lo <= s.vs_alloca_next /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ALLOCA [Lit n] [p]) /\
    step_inst_base (mk_inst id ALLOCA [Lit n] [p]) s = OK u ==>
    gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
       step_prov PG G (mk_inst id ALLOCA [Lit n] [p]) u,
       step_taint (mk_inst id ALLOCA [Lit n] [p]) s u tn)) /\
  (* compile_alloc_buffer_ghost_frame_at *)
  (!H D lo ctx fn cenv cx es sa sb n buf sc s out u d PG G tn.
      stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
        ctx fn cenv cx es s /\
      ghost_inv_at D lo d cenv cx es G tn s /\
      local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sb.cs_next_var /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
      buf.buf_operand = Var out /\ n < dimword (:256) /\
      step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
      ghost_inv_at D lo d cenv cx es
        (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
        (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn) u) /\
  (* compile_alloc_buffer_kept_frame_at *)
  (!H lo ctx fn cenv cx e es sa sb s0 es' tv vv s n buf sc out u PG G0 tn0 G tn.
      vv_post (H:(bool # 256 word # type_value) list # num list)
        ctx fn cenv cx e es sa sb s0 es' tv vv s /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      lo <= s.vs_alloca_next /\
      local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
      sa.cs_next_var <= sb.cs_next_var /\
      compile_alloc_buffer n sb = (buf,sc) /\ buf.buf_operand = Var out /\
      n < dimword (:256) /\
      step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
      ghost_kept_at lo cenv es sa G0 tn0 s0
        (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
        (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)) /\
  (* compile_store_bytestring_origin_ptr_path *)
  (!lo explicit ctx fn PG sa sb src dst G tn s a b len n bb.
      compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
      not_fresh_at sa src /\ not_fresh_at sa dst /\
      lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
      n = 32 + 32 * ((len+31) DIV 32) /\
      len+31 < dimword(:256) /\ n < dimword(:256) /\
      mload (w2n a) s = n2w len /\
      ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
      (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
      allocas_from lo s /\ lo <= s.vs_alloca_next /\
      run_inst_seq_mem_ok (emitted_insts sa sb) s /\
      ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
      ?Gf tnf sf.
        (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
          (OK (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tnf)) /\
        run_inst_seq (emitted_insts sa sb) s = OK sf /\
        tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
        sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
        sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
        tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
        tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+n}) UNION
          {w2n b+i | i < n /\ w2n a+i IN tn.t_mem} /\
        (!p. not_fresh_at sa p ==>
          lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
          op_taint tnf (Var p) = op_taint tn (Var p))) /\
  compile_expr cenv ty e sa = (vv,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  compile_ifexp_arm cenv t (lowered_value_type cenv e) vv sm = (op,sb) /\
  ~is_word_type t /\ ~same_memory_layout cenv (lowered_value_type cenv e) t /\
  is_bytestring_type t /\ is_bytestring_type (lowered_value_type cenv e) /\
  arg_type_fits (lowered_value_type cenv e) t /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (e = a \/ e = b) /\ expr_type e = t /\ post_value_type cenv e = t /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  (!v. read_result cx tva ee = (INL v,ee) ==> value_has_type rty v) /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es1 sa sm u ee tva vv z /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn z) /\
  vv_store_bound cx t (lowered_value_type cenv e) ee tva vv z /\
  z.vs_current_bb = sm.cs_current_bb /\
  z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
  alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
  ptr_vv_ok cx t tva vv ee G tn z /\
  (!t' op0. vv = StackValue t' op0 /\ ~is_word_type t ==>
     ptr_buf_ok cenv e op0 G z) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G z) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tva ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
                eval_operand (vv_operand vv) z = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es1 sa G1 tn1 u G tn ==>
  ?v z' Gz tf.
    read_result cx tva ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (z, G, tn) [] (OK z', Gz, tf) /\
       expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z' /\
       ghost_inv_at (DF H) lo d cenv cx ee Gz tf z') /\
    (~is_word_type t ==>
     vv_at cenv cx t sa sb ee tva (LocatedValue t (mk_ptr op LocMemory)) z') /\
    expr_store_bound cx t v op z' /\
    z'.vs_current_bb = sb.cs_current_bb /\
    z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
    ptr_val_ok cx t v op Gz tf z' /\
    (~is_word_type t ==>
     !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op Gz z') /\
    (~is_word_type t ==>
     !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
            eval_operand op z' = SOME w ==>
            type_memory_size rt = 0 \/
            w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
    ghost_kept_at lo cenv es1 sa G1 tn1 u Gz tf
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "unwrap")
    (CONJUNCTS_THEN2 (mk_asm "edge")
      (CONJUNCTS_THEN2 (mk_asm "alloc_ghost")
        (CONJUNCTS_THEN2 (mk_asm "alloc_kept")
          (CONJUNCTS_THEN2 (mk_asm "copy")
            (map_every assume_tac o CONJUNCTS)))))) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee z` by
    (first_x_assum drule >> simp[vv_post_def] >> metis_tac[]) >>
  drule_all ifexp_widen_copy_parts >> strip_tac >>
  rename1 `compile_alloc_buffer (type_memory_bytes cenv t) sm = (buf,salloc)` >>
  `compile_store_bytestring src buf.buf_operand sn = ((),sb)` by
    gvs[compile_store_memory_def] >>
  `cs_extends sn sb` by
    (qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
     simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[cs_extends_def, same_blocks_def,
       rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends sm salloc /\ cs_extends salloc sn` by
    (conj_tac >- (drule compile_alloc_buffer_extends >> simp[]) >>
     drule unwrap_value_extends >> simp[]) >>
  `fn_has_code sm salloc func /\ fn_has_code salloc sn func /\ fn_has_code sn sb func` by
    (map_every (fn s => asm_x s kall_tac)
       ["unwrap", "edge", "alloc_ghost", "alloc_kept", "copy"] >>
     metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `type_memory_bytes cenv t = type_memory_size rty` by simp[] >>
  `type_memory_size rty < 2 ** 64` by simp[] >>
  `type_memory_bytes cenv t < dimword (:256)` by
    (qpat_x_assum `type_memory_size rty < _` mp_tac >>
     qpat_x_assum `type_memory_bytes cenv t = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm salloc) z = OK az` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee az` by
    (gen_tac >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee z` by
       (first_x_assum drule >> simp[vv_post_def] >> metis_tac[]) >>
     drule_all literal_alloc_buffer_run >> strip_tac >> gvs[]) >>
  `emitted_insts sm salloc =
     [mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))] [p]] /\
   salloc.cs_current_bb = sm.cs_current_bb /\
   salloc.cs_current_insts = sm.cs_current_insts ++
     [mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))] [p]]` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  `step_inst_base (mk_inst sm.cs_next_id ALLOCA
     [Lit (n2w (type_memory_bytes cenv t))] [p]) z = OK az` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  qabbrev_tac `ai = mk_inst sm.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes cenv t))] [p]` >>
  qabbrev_tac `Ga = step_prov PG G ai az` >>
  qabbrev_tac `ta = step_taint ai z az tn` >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (qpat_assum `compile_expr _ _ _ _ = _`
       (mp_then Any mp_tac (CONJUNCT1 compiler_compile_var)) >> simp[]) >>
  `salloc.cs_next_var >= sm.cs_next_var /\
   salloc.cs_next_id >= sm.cs_next_id` by
    (qspecl_then [`type_memory_bytes cenv t`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qpat_x_assum `!H. valid_horizon _ _ _ _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` drule >>
     simp[ghost_inv_at_def] >> rpt strip_tac >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx ee Ga ta az` by
    (gen_tac >> strip_tac >>
     simp_tac bool_ss [Abbr `Ga`, Abbr `ta`, Abbr `ai`] >>
     asm "alloc_ghost" irule
     >- (simp[] >> conj_tac >- (qexists `sa` >> simp[]) >>
         qexistsl [`storage_trace_horizon ee.storage_trace`, `ctx`, `func`] >> simp[]) >>
     qpat_x_assum `!H. valid_horizon _ _ _ _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` drule >>
     simp[]) >>
  `az.vs_call_ctx = z.vs_call_ctx /\ az.vs_accounts = z.vs_accounts /\
   az.vs_transient = z.vs_transient /\ az.vs_immutables = z.vs_immutables /\
   az.vs_current_bb = z.vs_current_bb /\ az.vs_inst_idx = z.vs_inst_idx /\
   az.vs_halted = z.vs_halted /\ az.vs_labels = z.vs_labels /\
   z.vs_alloca_next <= az.vs_alloca_next` by
    (qpat_x_assum `step_inst_base _ z = OK az` mp_tac >>
     simp_tac bool_ss [Abbr `ai`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[step_inst_base_def, mk_inst_def, eval_operands_def, eval_operand_def,
       exec_alloca_def, update_var_def] >>
     Cases_on `FLOOKUP z.vs_allocas sm.cs_next_id` >> simp[] >>
     TRY (PairCases_on `x` >> simp[]) >> strip_tac >> gvs[]) >>
  `!n b k. local_region cenv ee.scopes az n b k <=>
            local_region cenv ee.scopes z n b k` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame >>
         conj_tac
         >- (qexists `func` >>
             qpat_x_assum `stmt_state_rel _ _ _ _ _ ee z` mp_tac >>
             POP_ASSUM_LIST (K all_tac) >>
             simp[stmt_state_rel_def, state_rel_def]) >>
         qexistsl [`sm`, `ee.scopes`, `az`] >> simp[]) >>
     strip_tac >> irule local_region_frame_fwd >>
     qexistsl [`z`, `sm`, `ee.scopes`] >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func cenv cx e es1 sa sm u ee tva vv az` by
    (gen_tac >> strip_tac >> irule ifexp_widen_vv_post_alloc_frame >>
     conj_tac >- (first_x_assum drule >> simp[]) >>
     qexistsl [`sb`, `op`, `t`, `z`, `sm`, `lowered_value_type cenv e`] >>
     simp[] >> rpt conj_tac
     >- (rpt strip_tac >> first_x_assum irule >>
         irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[])
     >- simp[contract_storage_def]
     >- simp[contract_transient_def] >>
     Cases_on `vv_operand vv` >> simp[eval_operand_def] >>
     first_x_assum irule >> first_x_assum irule >> simp[]) >>
  `ghost_kept_at lo cenv es1 sa G1 tn1 u Ga ta` by
    (simp_tac bool_ss [Abbr `Ga`, Abbr `ta`, Abbr `ai`] >>
     asm "alloc_kept" irule >>
     simp[] >>
     qexistsl [`storage_trace_horizon ee.storage_trace`, `ctx`, `cx`, `e`,
       `ee`, `func`, `tva`, `vv`] >> simp[] >>
     qpat_x_assum `!H. valid_horizon _ _ _ _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` drule >> simp[]) >>
  qabbrev_tac `q = az with vs_inst_idx := SUC z.vs_inst_idx` >>
  `q.vs_memory = z.vs_memory /\ q.vs_accounts = z.vs_accounts /\
   q.vs_call_ctx = z.vs_call_ctx /\ q.vs_transient = z.vs_transient /\
   z.vs_alloca_next <= q.vs_alloca_next /\
   eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) z /\
   op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv) /\
   op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv) /\
   (!x. vv_operand vv = Var x ==> FLOOKUP Ga x = FLOOKUP G x) /\
   ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\
   (!i. i < z.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem))` by
    (mp_tac (Q.INST [`s` |-> `z`, `sc` |-> `salloc`, `out` |-> `p`,
       `n` |-> `type_memory_bytes cenv t`,
       `src_ty` |-> `lowered_value_type cenv e`] ifexp_widen_alloc_boundary_general) >>
     simp[Abbr `q`, Abbr `Ga`, Abbr `ta`, Abbr `ai`]) >>
  `ptr_vv_ok cx t tva vv ee Ga ta q /\
   vv_store_bound cx t (lowered_value_type cenv e) ee tva vv q /\
   (!t' op0. vv = StackValue t' op0 /\ ~is_word_type t ==>
     ptr_buf_ok cenv e op0 Ga q) /\
   (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand Ga q) /\
   (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tva ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
       eval_operand (vv_operand vv) q = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside ta.t_mem q.vs_memory mem ==>
         val_in_memory rt val (w2n w) mem))` by
    (mp_tac (Q.INST [`s` |-> `z`, `Gq` |-> `Ga`, `tq` |-> `ta`,
       `tv` |-> `tva`, `lt` |-> `lowered_value_type cenv e`]
       ifexp_widen_alloc_resources_frame) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es1 sa sm u ee tva vv q /\
    ghost_inv_at (DF H) lo d cenv cx ee Ga ta q` by
    (gen_tac >> strip_tac >> conj_tac
     >- (simp[Abbr `q`] >>
         qpat_x_assum `!H. valid_horizon _ _ _ _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ az` drule >> simp[]) >>
     qpat_x_assum `!H. valid_horizon _ _ _ _ ==> ghost_inv_at _ _ _ _ _ _ _ _ az` drule >>
     simp[Abbr `q`, ghost_inv_at_def, ptr_covers_def, lookup_var_def,
       stor_taint_ok_at_def, allocas_from_def] >>
     strip_tac >> simp[] >>
     `!s k. return_buf_ptr d cenv Ga ta (s with vs_inst_idx := k) =
              return_buf_ptr d cenv Ga ta s` by
       (POP_ASSUM_LIST (K all_tac) >> Cases_on `d` >> simp[return_buf_ptr_def] >>
        PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]) >>
     simp[] >> conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb z.vs_inst_idx = SOME ai` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `ai`]) >>
  `alloca_inv z` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ ee z` mp_tac >>
     simp[stmt_state_rel_def, state_rel_def]) >>
  `alloca_history func q` by
    (`step_inst_base ai z = OK az` by simp[Abbr `ai`] >>
     `lookup_block z.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     drule_all alloca_history_base_step >> simp[Abbr `q`, Abbr `ai`, mk_inst_def, is_terminator_def]) >>
  `~q.vs_halted /\ q.vs_current_bb = salloc.cs_current_bb /\
   q.vs_inst_idx = LENGTH salloc.cs_current_insts /\
   u.vs_alloca_next <= q.vs_alloca_next` by
    simp[Abbr `q`] >>
  asm "unwrap" (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then drule >>
  simp[] >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  disch_then (drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_x_assum `cenv.ce_is_ctor /\ _ ==> ?val. _ /\ !rt w. _` mp_tac >>
      simp[]) >>
  strip_tac >>
  rename1 `ptr_val_ok cx t v src Gu tu su` >>
  cheat
QED
