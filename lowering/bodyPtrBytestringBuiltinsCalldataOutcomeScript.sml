Theory bodyPtrBytestringBuiltinsCalldataOutcome
Ancestors
  bodyPtrBytestringBuiltinsEval bodyPtrBytestringBuiltinsSliceEndpoint
  exprSimSource exprSimWordArgs exprSimDefs exprSimHypsDefs
  vyperTyping valueEncoding words integer compileEnv vyperValue loweringSlice
  allocationPtr bodyMemoryDefs exprSimBuffer venomExecSemantics venomInst
  ptrDiscipline venomState finite_map exprLoweringProps venomMemDefs
  bodyPtrBytestringBuiltinsCalldataFrame bodyPtrBytestringBuiltinsBounds
  bodyPtrBytestringBuiltinsExternalSlice instIdxIndep fragExec
  exprSimAlloc loweringHalt bodyPtrBytestringBuiltinsBuffer emitHelperProps
  bodyPtrBytestringBuiltinsWindowGhost bodyPtrDefs
  bodyPtrBytestringBuiltinsCalldataRuntime
  exprSimMemoryTransport valueEncodingProofs valueEncodingProps vyperState
  venomMemProofs list loweringPosts context emitHelper exprSimHash vyperContext vyperValueOperation fragGasPathPtr

Theorem covered_clean_memory_result:
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv value /\
  ptr_covers G tn p s N /\ eval_operand (Var p) s = SOME w /\
  val_in_memory tv value (w2n w) s.vs_memory /\
  val_store_size tv value <= N /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint tv value ==> i NOTIN tn.t_mem) /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= N ==>
  ptr_mem_ok cx ty value (Var p) G tn s /\
  ptr_buf_ok cenv e (Var p) G s /\
  ptr_vv_ok cx ty (Value value)
    (LocatedValue ty <|ptr_operand := Var p; ptr_location := LocMemory|>) es G tn s
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv value (w2n w) mem` by
    (rpt strip_tac >> irule val_in_memory_relocate_footprint >>
     conj_tac >- simp[] >> qexistsl_tac [`s.vs_memory`,`w2n w`] >> simp[] >>
     irule LIST_EQ >> simp[] >> rpt strip_tac >>
     rename1 `j < val_footprint tv value` >>
     `w2n w + j NOTIN tn.t_mem` by
       (qpat_x_assum `!i. _ ==> i NOTIN _` irule >> decide_tac) >>
     `mem_bytes_at (w2n w+j) 1 s.vs_memory = mem_bytes_at (w2n w+j) 1 mem` by
       metis_tac[mem_agree_outside_def] >>
     pop_assum mp_tac >> simp[listTheory.LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  `ptr_mem_ok cx ty value (Var p) G tn s` by
    (simp[ptr_mem_ok_def] >> rpt strip_tac >> gvs[] >>
     fs[ptr_covers_def, eval_operand_def] >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `ptr_buf_ok cenv e (Var p) G s` by
    (simp[ptr_buf_ok_def] >> rpt strip_tac >>
     fs[ptr_covers_def, eval_operand_def] >> gvs[] >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  fs[ptr_vv_ok_def, ptr_covers_def, read_result_def, vyperStateTheory.return_def]
QED

(* The marked operand evidence fixes both the source integer and its actual
   runtime word; no independent existential execution is introduced. *)
Theorem calldata_slice_operand_endpoint:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
  expr_post ctx func cenv cx e es sa sm s0 ee v op t /\
  (?marks ee0. ee = ee0 with gas_obs := [] /\
    !tail. vyperState$bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks readings ++ tail) =
      (INL v,ee0 with gas_obs := tail)) ==>
  ?a. v = IntV (&a) /\ a < 2 ** 256 /\
    eval_operand op t = SOME (n2w a) /\ expr_sim_inv cenv cx env ee
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all operand_eval_evidence_semantics >> strip_tac >>
  `?i. v = IntV i /\ 0 <= i /\ Num i < 2 ** 256` by
    (fs[is_word_type_def, evaluate_type_def] >> Cases_on `v` >>
     gvs[is_word_type_def, evaluate_type_def, value_has_type_def]) >>
  gvs[] >> qexists_tac `Num i` >> simp[] >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  drule expr_post_word_operand >>
  simp[is_word_type_def, evaluate_type_def, word_value_def, val_to_w256_def,
    integer_wordTheory.i2w_def]
QED

(* Reused allocation sites introduce no new bytes; a genuinely new site starts
   at the frontier.  Both cases are needed for loop/re-entry executions. *)
Theorem alloca_new_bytes_above_frontier:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w N)] [out]) (fn_insts fn) /\
  N < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w N)] [out]) s = OK u /\
  i < s.vs_alloca_next ==>
  i NOTIN new_site_bytes s u
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_new_site_bytes >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >>
  simp[new_site_bytes_def, update_var_def, pred_setTheory.EXTENSION,
    FLOOKUP_DEF, SF CONJ_ss]
QED

Theorem alloca_new_bytes_protected_regions:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w N)] [out]) (fn_insts fn) /\
  N < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w N)] [out]) s = OK u ==>
  (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
    off <= i /\ i < off + sz ==> i NOTIN new_site_bytes s u) /\
  (!name off sz i. local_region cenv es.scopes s name off sz /\
    off <= i /\ i < off + sz ==> i NOTIN new_site_bytes s u)
Proof
  strip_tac >> conj_tac
  >- (rpt gen_tac >> disch_then strip_assume_tac >>
      irule alloca_new_bytes_above_frontier >>
      reverse conj_tac >- metis_tac[] >>
      fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      qpat_x_assum `!aid base sz. _ ==> base + sz <= _` drule >> decide_tac) >>
  rpt gen_tac >> disch_then strip_assume_tac >>
  drule_all body_local_region_frontier >> strip_tac >>
  irule alloca_new_bytes_above_frontier >>
  reverse conj_tac >- metis_tac[] >> decide_tac
QED

Theorem alloca_slice_suffix_ghost_kept:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w N)] [out]) (fn_insts fn) /\
  N < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w N)] [out]) s = OK u /\
  (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  tm.t_mem SUBSET (tn.t_mem UNION new_site_bytes s u) ==>
  ghost_kept cenv es sa G tn s H tm
Proof
  strip_tac >> drule_all alloca_new_bytes_protected_regions >> strip_tac >>
  irule external_slice_allocated_ghost_kept >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `new_site_bytes s u` >> simp[] >> metis_tac[]
QED

Theorem alloca_slice_suffix_ghost_inv:
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  MEM (mk_inst id ALLOCA [Lit (n2w N)] [out]) (fn_insts fn) /\
  N < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w N)] [out]) s = OK u /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==> lookup_var x z = SOME w) /\
  (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!name b len. local_region cenv es.scopes s name b len ==>
    mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory) /\
  tm.t_mem SUBSET (tn.t_mem UNION new_site_bytes s u) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
  z.vs_call_ctx = s.vs_call_ctx ==>
  ghost_inv d cenv cx es H tm z
Proof
  strip_tac >> drule_all alloca_new_bytes_protected_regions >> strip_tac >>
  `local_ptrs_rel fn cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `stor_taint_ok cx tm z` by fs[ghost_inv_def, stor_taint_ok_def] >>
  `!name b len. local_region cenv es.scopes s name b len ==>
    mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory /\
    (!i. b <= i /\ i < b + len /\ i IN tm.t_mem ==> i IN tn.t_mem)` by
    (rpt strip_tac >> simp[] >>
     qpat_x_assum `tm.t_mem SUBSET _` mp_tac >>
     simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  drule_all ghost_inv_local_window_transport >> simp[]
QED

(* Counted replay advances the PC after each write.  The raw semantic run
   leaves it unchanged; these endpoints differ only in the final PC. *)
Theorem slice_copy_store_pc_normalization:
  r = q with vs_inst_idx := kr /\
  v = (write_memory_with_expansion dst bytes r) with vs_inst_idx := kv /\
  t = (mstore root len v) with vs_inst_idx := kt ==>
  t = (mstore root len (write_memory_with_expansion dst bytes q)) with vs_inst_idx := kt
Proof
  strip_tac >> gvs[] >>
  simp_tac (srw_ss()) [mstore_def, LET_THM]
QED

Theorem slice_bounds_run_pc:
  compile_assert_slice_bounds start len limit sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  run_inst_seq (emitted_insts sa sb) (s with vs_inst_idx := k) =
    OK (t with vs_inst_idx := k)
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (drule compile_assert_slice_bounds_layout >> strip_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  simp[fragExecTheory.run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem compile_slice_calldata_shared_success:
  compile_slice_calldata start (Lit (n2w n)) N sa = (out,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  32 + n <= N /\ N < dimword (:256) /\ n < dimword (:256) /\
  a < dimword (:256) /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  a + n < dimword (:256) /\ a + n <= LENGTH s.vs_call_ctx.cc_calldata /\
  eval_operand start s = SOME (n2w a) /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?zf w H tm root u.
    out = Var root /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [root]) s = OK u /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK zf) /\
    stmt_state_rel ctx fn cenv cx es zf /\
    val_in_memory (BaseTV (BytesT (Dynamic bound)))
      (BytesV (TAKE n (DROP a s.vs_call_ctx.cc_calldata))) (w2n w) zf.vs_memory /\
    eval_operand out zf = SOME w /\ ptr_covers H tm root zf N /\
    FLOOKUP zf.vs_allocas sa.cs_next_id = SOME (w2n w,N) /\
    (!name b len. local_region cenv es.scopes zf name b len ==>
      regions_disjoint (w2n w) N b len) /\
    zf.vs_current_bb = sb.cs_current_bb /\ zf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~zf.vs_halted /\ locals_kept cenv es s zf /\
    (!x val. not_fresh_at sa x /\ lookup_var x s = SOME val ==>
      lookup_var x zf = SOME val) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP zf.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      mem_bytes_at b len zf.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    tm.t_mem = ((tn.t_mem UNION new_site_bytes s u)
      DIFF {i | w2n w + 32 <= i /\ i < w2n w + 32 + n})
      DIFF {i | w2n w <= i /\ i < w2n w + 32} /\
    w2n w + N < dimword (:256) /\
    ghost_kept cenv es sa G tn s H tm /\
    ghost_inv d cenv cx es H tm zf /\
    zf.vs_accounts = s.vs_accounts /\ zf.vs_transient = s.vs_transient /\
    zf.vs_call_ctx = s.vs_call_ctx /\
    (!name b len. local_region cenv es.scopes s name b len ==>
      mem_bytes_at b len zf.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!i. w2n w <= i /\ i < w2n w + 32 + n ==> i NOTIN tm.t_mem)
Proof
  strip_tac >>
  drule_all compile_slice_calldata_semantic >>
  disch_then (qspecl_then [`tn`,`bound`,`PG`,`G`,`D`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts s2 s3) (v with vs_inst_idx := SUC t.vs_inst_idx) =
    OK (q with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule slice_bounds_run_pc >> metis_tac[]) >>
  `32 <= N /\ w2n (n2w n : 256 word) <= N - 32` by simp[] >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n)` by simp[eval_operand_def] >>
  `!op. MEM op [start;Lit (n2w n)] ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[] >> simp[op_prov_def, op_taint_def]) >>
  suspend "counted"
QED

Resume compile_slice_calldata_shared_success[counted]:
  qpat_x_assum `out = Var r` SUBST_ALL_TAC >>
  qpat_x_assum `data = Var p` SUBST_ALL_TAC >>
  `run_inst_seq (emitted_insts s2 s3)
    ((update_var (STRING #"%" (toString s1.cs_next_var))
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) t) with
      vs_inst_idx := SUC t.vs_inst_idx) = OK (q with vs_inst_idx := SUC t.vs_inst_idx)` by
    metis_tac[] >>
  `!op z. MEM op [start;Lit (n2w n)] /\ op = Var z ==> not_fresh_at sa z` by
    (rpt strip_tac >> gvs[MEM] >> metis_tac[]) >>
  drule_all compile_slice_calldata_counted_ok >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `w2n (w + 32w) = w2n w + 32` by
    (`w2n w + 32 < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  `TAKE n (DROP a s.vs_call_ctx.cc_calldata ++ REPLICATE n 0w) =
    TAKE n (DROP a s.vs_call_ctx.cc_calldata)` by
    (irule listTheory.TAKE_APPEND1 >> simp[]) >>
  `n MOD dimword (:256) = n /\ a MOD dimword (:256) = a` by simp[] >>
  fs[] >>
  `SUC v'.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_assum `t'.vs_inst_idx = _` mp_tac >>
     qpat_assum `t' = _` SUBST1_TAC >> simp[]) >>
  `t' = zf` by
    (qpat_assum `r'' = _` (mp_then Any mp_tac slice_copy_store_pc_normalization) >>
     disch_then drule_all >> simp[]) >>
  qpat_x_assum `t' = zf` SUBST_ALL_TAC >>
  suspend "protected"
QED

Resume compile_slice_calldata_shared_success[protected]:
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [r]) (fn_insts fn)` by
    (drule compile_slice_calldata_stages >> strip_tac >>
     drule compile_slice_out_buf_compiler_parts >> strip_tac >>
     `fn_has_code sa sm fn` by
       metis_tac[fn_has_code_split, cs_extends_trans] >>
     drule_all buffer_alloc_code >> strip_tac >>
     drule compile_alloc_buffer_parts >> strip_tac >> gvs[]) >>
  `tm.t_mem SUBSET (tn.t_mem UNION new_site_bytes s u)` by
    (qpat_assum `tm.t_mem = _` SUBST1_TAC >>
     simp[pred_setTheory.SUBSET_DEF]) >>
  `N < dimword (:256)` by decide_tac >>
  `ghost_kept cenv es sa G tn s H tm` by
    (drule_all alloca_slice_suffix_ghost_kept >> simp[]) >>
  `ghost_inv d cenv cx es H tm zf` by
    (drule_all alloca_slice_suffix_ghost_inv >> simp[]) >>
  `!i. w2n w <= i /\ i < n + (w2n w + 32) ==> i NOTIN tm.t_mem` by
    (qpat_assum `tm.t_mem = _` SUBST1_TAC >> simp[] >> rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`zf`,`w`,`H`,`tm`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise compile_slice_calldata_shared_success

Theorem calldata_bytes_result_posts:
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic bound))) /\
  val_wf (BaseTV (BytesT (Dynamic bound))) (BytesV bytes) /\
  type_memory_size (BaseTV (BytesT (Dynamic bound))) <= N /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= N /\
  ptr_covers G tn p s N /\ eval_operand (Var p) s = SOME w /\
  val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV bytes) (w2n w) s.vs_memory /\
  (!i. w2n w <= i /\ i < w2n w + 32 + LENGTH bytes ==> i NOTIN tn.t_mem) ==>
  ptr_mem_ok cx ty (BytesV bytes) (Var p) G tn s /\
  ptr_buf_ok cenv e (Var p) G s /\
  ptr_vv_ok cx ty (Value (BytesV bytes))
    (LocatedValue ty <|ptr_operand := Var p; ptr_location := LocMemory|>) es G tn s
Proof
  strip_tac >> irule covered_clean_memory_result >>
  qexistsl_tac [`N`,`BaseTV (BytesT (Dynamic bound))`,`w`] >>
  simp[val_footprint_def] >>
  drule exprSimPropsTheory.val_store_size_le >> decide_tac
QED

Theorem compile_slice_calldata_id_range:
  compile_slice_calldata start len N sa = (out,sb) ==>
  sa.cs_next_id < sb.cs_next_id
Proof
  strip_tac >> drule compile_slice_calldata_stages >> strip_tac >>
  drule compile_slice_out_buf_compiler_parts >> strip_tac >>
  drule compile_assert_slice_bounds_layout >> strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
  qpat_x_assum `emit_op CALLDATASIZE _ _ = _` mp_tac >>
  qpat_x_assum `emit_void CALLDATACOPY _ _ = _` mp_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >>
  qpat_x_assum `_ = sb` (SUBST1_TAC o SYM) >>
  qpat_x_assum `_ = s4` (SUBST1_TAC o SYM) >>
  simp_tac (srw_ss()) [] >>
  qpat_x_assum `s3.cs_next_id = _` SUBST1_TAC >>
  qpat_x_assum `_ = s2` (SUBST1_TAC o SYM) >>
  qpat_x_assum `_ = s1` (SUBST1_TAC o SYM) >>
  qpat_x_assum `_ = sm` (SUBST1_TAC o SYM) >>
  simp_tac (srw_ss()) [] >> decide_tac
QED

Theorem compile_slice_calldata_success_posts:
  compile_slice_calldata start (Lit (n2w n)) N sa = (out,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  32 + n <= N /\ N < dimword (:256) /\ n < dimword (:256) /\
  a < dimword (:256) /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  a + n < dimword (:256) /\ a + n <= LENGTH s.vs_call_ctx.cc_calldata /\
  eval_operand start s = SOME (n2w a) /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic bound))) /\
  ~is_word_type (expr_type e) /\
  val_wf (BaseTV (BytesT (Dynamic bound)))
    (BytesV (TAKE n (DROP a s.vs_call_ctx.cc_calldata))) /\
  type_memory_size (BaseTV (BytesT (Dynamic bound))) <= N /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= N ==>
  ?zf H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK zf) /\
    vv_post ctx fn cenv cx e es sa sb s es
      (Value (BytesV (TAKE n (DROP a s.vs_call_ctx.cc_calldata))))
      (LocatedValue (expr_type e) <|ptr_operand := out; ptr_location := LocMemory|>) zf /\
    ptr_vv_ok cx (expr_type e)
      (Value (BytesV (TAKE n (DROP a s.vs_call_ctx.cc_calldata))))
      (LocatedValue (expr_type e) <|ptr_operand := out; ptr_location := LocMemory|>) es H tm zf /\
    ptr_buf_ok cenv e out H zf /\ ghost_inv d cenv cx es H tm zf /\
    ghost_kept cenv es sa G tn s H tm /\
    zf.vs_current_bb = sb.cs_current_bb /\ zf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~zf.vs_halted
Proof
  strip_tac >> drule_all compile_slice_calldata_shared_success >>
  disch_then (qspecl_then [`bound`,`PG`,`D`] strip_assume_tac) >>
  `sa.cs_next_id < sb.cs_next_id` by
    (drule compile_slice_calldata_id_range >> simp[]) >>
  `wb_frame cenv es sa s zf` by
    (simp[wb_frame_def] >> metis_tac[]) >>
  `LENGTH (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) <= n` by simp[] >>
  qpat_x_assum `out = Var root` SUBST_ALL_TAC >>
  `!i. w2n w <= i /\ i < w2n w + 32 +
    LENGTH (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) ==> i NOTIN tm.t_mem` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN _` irule >> decide_tac) >>
  drule_all calldata_bytes_result_posts >> strip_tac >>
  `val_footprint (BaseTV (BytesT (Dynamic bound)))
    (BytesV (TAKE n (DROP a s.vs_call_ctx.cc_calldata))) <= N` by
    (simp[val_footprint_def] >> decide_tac) >>
  qexistsl_tac [`zf`,`H`,`tm`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (irule vv_post_allocated_memory_intro >> simp[] >>
      qexistsl_tac [`sa.cs_next_id`,`w2n w`,`N`] >>
      simp[] >> rpt gen_tac >> disch_tac >>
      qpat_x_assum `!name b len. _ ==> regions_disjoint _ _ _ _` drule >>
      simp[compileEnvTheory.regions_disjoint_def]) >>
  simp[]
QED

Theorem compile_slice_calldata_revert:
  compile_slice_calldata start (Lit (n2w n)) N sa = (out,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  32 <= N /\ N < dimword (:256) /\ n < dimword (:256) /\
  a < dimword (:256) /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  (dimword (:256) <= a + n \/ LENGTH s.vs_call_ctx.cc_calldata < a + n) /\
  eval_operand start s = SOME (n2w a) /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  op_prov G start = NONE /\ op_taint tn start = {} ==>
  ?zf H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (Abort Revert_abort zf) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all compile_slice_calldata_runtime >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  qpat_x_assum `out = Var r` SUBST_ALL_TAC >>
  qpat_x_assum `data = Var p` SUBST_ALL_TAC >>
  `run_inst_seq (emitted_insts s2 s3) v =
    Abort Revert_abort (revert_state (set_returndata [] q))` by simp[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s2 s3)` by
    (drule compile_assert_slice_bounds_layout >> strip_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  `run_inst_seq (emitted_insts s2 s3) (v with vs_inst_idx := SUC t.vs_inst_idx) =
    Abort Revert_abort ((revert_state (set_returndata [] q)) with
      vs_inst_idx := SUC t.vs_inst_idx)` by
    simp[fragExecTheory.run_inst_seq_inst_idx, exec_result_map_def] >>
  `!op. MEM op [start;Lit (n2w n)] ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt gen_tac >> simp[] >>
     strip_tac >> gvs[] >> simp[op_prov_def, op_taint_def]) >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n)` by simp[eval_operand_def] >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  `!op z. MEM op [start;Lit (n2w n)] /\ op = Var z ==> not_fresh_at sa z` by
    (rpt strip_tac >> gvs[MEM] >> metis_tac[]) >>
  drule_all compile_slice_calldata_bounds_abort >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (Abort _ _)`
    (irule_at Any) >> simp[]
QED

(* Source rejects zero length, even though the bounds-only suffix accepts it.
   The typed builtin caller rules this case out. *)
Theorem calldata_zero_length_source_probe:
  evaluate_calldata_slice [] (IntV 0) 0 =
    INR (RuntimeError "calldata slice overflow")
Proof
  EVAL_TAC
QED

Theorem calldata_slice_uint_source:
  0 < n ==>
  evaluate_calldata_slice bs (IntV &a) n =
    if dimword (:256) <= a + n then
      INR (RuntimeError "calldata slice overflow")
    else if a + n <= LENGTH bs then
      INL (BytesV (TAKE n (DROP a bs)))
    else INR (RuntimeError "evaluate_slice range")
Proof
  simp[evaluate_calldata_slice_def, dest_NumV_def, evaluate_slice_def,
    compatible_bound_def, dimword_def]
QED

Theorem memory_vv_post_end_gas_obs[local]:
  vv_post ctx fn cenv cx e es sa sb s0 (ee with gas_obs := gs) (Value v)
    (LocatedValue ty <|ptr_operand := op; ptr_location := LocMemory|>) s <=>
  vv_post ctx fn cenv cx e es sa sb s0 ee (Value v)
    (LocatedValue ty <|ptr_operand := op; ptr_location := LocMemory|>) s
Proof
  simp[vv_post_def, vv_holds_def, vv_at_def, read_result_def,
    vyperStateTheory.return_def]
QED

Theorem memory_ptr_vv_end_gas_obs[local]:
  ptr_vv_ok cx ty (Value v)
    (LocatedValue ty <|ptr_operand := op; ptr_location := LocMemory|>)
    (es with gas_obs := gs) G tn s <=>
  ptr_vv_ok cx ty (Value v)
    (LocatedValue ty <|ptr_operand := op; ptr_location := LocMemory|>) es G tn s
Proof
  simp[ptr_vv_ok_def, read_result_def, vyperStateTheory.return_def]
QED

Theorem compile_slice_calldata_source_outcome:
  compile_slice_calldata start (Lit (n2w n)) N sa = (out,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  0 < n /\ 32 + n <= N /\ N < dimword (:256) /\ n < dimword (:256) /\
  a < dimword (:256) /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  eval_operand start s = SOME (n2w a) /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic bound))) /\
  ~is_word_type (expr_type e) /\
  val_wf (BaseTV (BytesT (Dynamic bound))) (BytesV (TAKE n (DROP a bs))) /\
  type_memory_size (BaseTV (BytesT (Dynamic bound))) <= N /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= N /\
  bs = s.vs_call_ctx.cc_calldata /\
  (!tail. source (es with gas_obs := tail) =
    ((case evaluate_calldata_slice bs (IntV &a) n of
      INL v => INL (Value v) | INR err => INR (Error err)), es with gas_obs := tail)) ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s,G,tn)
    (\res ee H tm zf. ?v. res = INL (Value v) /\
      vv_post ctx fn cenv cx e es sa sb s ee (Value v)
        (LocatedValue (expr_type e) <|ptr_operand := out; ptr_location := LocMemory|>) zf /\
      ptr_vv_ok cx (expr_type e) (Value v)
        (LocatedValue (expr_type e) <|ptr_operand := out; ptr_location := LocMemory|>) ee H tm zf /\
      ptr_buf_ok cenv e out H zf /\ ghost_inv d cenv cx ee H tm zf /\
      ghost_kept cenv es sa G tn s H tm /\
      zf.vs_current_bb = sb.cs_current_bb /\ zf.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ~zf.vs_halted)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> qpat_x_assum `bs = _` SUBST_ALL_TAC >>
  Cases_on `dimword (:256) <= a+n \/ LENGTH s.vs_call_ctx.cc_calldata < a+n`
  >- suspend "bad" >>
  `a+n < dimword (:256) /\ a+n <= LENGTH s.vs_call_ctx.cc_calldata` by decide_tac >>
  drule_all compile_slice_calldata_success_posts >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >> suspend "good"
QED

Resume compile_slice_calldata_source_outcome[bad]:
  `32 <= N` by decide_tac >>
  drule_all compile_slice_calldata_revert >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`case evaluate_calldata_slice s.vs_call_ctx.cc_calldata (IntV &a) n of
    INL v => INL (Value v) | INR err => INR (Error err)`,`es`,`H`,`tm`,
    `Abort Revert_abort zf`] >>
  simp[] >> Cases_on `dimword (:256) <= a+n` >>
  fs[calldata_slice_uint_source, expr_exit_def, exit_result_def]
QED

Resume compile_slice_calldata_source_outcome[good]:
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (Value (BytesV (TAKE n (DROP a s.vs_call_ctx.cc_calldata))))`,
    `es`,`H`,`tm`,`OK zf`] >>
  simp[calldata_slice_uint_source, memory_vv_post_end_gas_obs,
    memory_ptr_vv_end_gas_obs, ghost_inv_def] >> fs[ghost_inv_def] >>
  first_assum ACCEPT_TAC
QED
Finalise compile_slice_calldata_source_outcome
