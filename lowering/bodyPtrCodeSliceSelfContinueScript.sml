(* Concrete runtime continuation for self.code: semantic runs are proved
   separately from checked pointer sequences. *)
Theory bodyPtrCodeSliceSelfContinue
Ancestors
  bodyPtrCodeSliceSelfPrefix bodyPtrCodeSliceSelfSuffix bodyPtrDefs vyperState
  exprSimSliceBounds exprSimCalldataSlice exprSimSliceSource
  fragGasSeqPtr fragGasPathPtr gasSummaryComposePtr exprSimSliceExtcode
  augAssignPtrScalarContinuation exprSimVVFrame
  emitHelperProps loweringShapeDefs venomState venomInst venomExecSemantics
  fragExec words loweringStateRelDefs exprLoweringProps
  exprLowering builtinBytes emitHelper freshWrites compileEnv
  exprSimHashBoundary stmtSimLogTopics exprSimSliceData exprSimProps
  exprSimWordArgs loweringPosts finite_map pred_set
  exprSimHash valueEncodingDefs valueEncoding vyperValue context pair
  exprSimSliceExtcodeEntry exprSimSliceExtcodeContinue
  ghostPcTransportPtr bodyPtrHashBuiltinsGhostFrame

Theorem self_code_size_bounds_run:
  emit_op CODESIZE [] sa = (limit,sb) /\
  compile_assert_slice_bounds a n limit sb = ((),sc) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  (!x. a = Var x ==> not_fresh_at sa x) /\
  (!x. n = Var x ==> not_fresh_at sa x) /\
  LENGTH s.vs_code < dimword (:256) ==>
  if LENGTH s.vs_code < w2n wa + w2n wn then
    ?t. run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s = Abort Revert_abort t
  else
    ?t. run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s = OK t /\
      t = s with vs_vars := t.vs_vars /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qabbrev_tac `v = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `u = update_var v (n2w (LENGTH s.vs_code)) s` >>
  `~not_fresh_at sa v` by simp[Abbr `v`, not_fresh_at_def] >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op u = eval_operand op s` by
    (Cases >> simp[Abbr `u`, eval_operand_def, lookup_var_update_var] >>
     rpt strip_tac >> metis_tac[]) >>
  `eval_operand a u = SOME wa /\ eval_operand n u = SOME wn` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by simp[not_fresh_at_def] >>
  `eval_operand (Var v) u = SOME (n2w (LENGTH s.vs_code)) /\ not_fresh_at sb v` by
    simp[Abbr `u`, Abbr `v`, eval_operand_def, lookup_var_update_var, not_fresh_at_def] >>
  `((wa + wn <+ wa \/ n2w (LENGTH s.vs_code) <+ wa + wn) <=>
    LENGTH s.vs_code < w2n wa + w2n wn)` by
    (mp_tac (Q.SPECL [`dimword (:256)`, `w2n (wa:bytes32)`, `w2n (wn:bytes32)`,
       `LENGTH s.vs_code`] exprSimSliceBoundsTheory.slice_bounds_mod) >>
     simp[WORD_LO, word_add_def, w2n_n2w, w2n_lt] >> decide_tac) >>
  `run_inst_seq [mk_inst sa.cs_next_id CODESIZE [] [v]] s = OK u` by
    simp[run_inst_seq_def, Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def] >>
  `(!x. a = Var x ==> not_fresh_at sb x) /\
   (!x. n = Var x ==> not_fresh_at sb x) /\
   (!x. (Var v : operand) = Var x ==> not_fresh_at sb x)` by simp[] >>
  drule_all exprSimSliceBoundsTheory.slice_bounds_run_frame >>
  qpat_x_assum `(_ \/ _) <=> _` (fn th => pure_rewrite_tac[th]) >>
  Cases_on `LENGTH s.vs_code < w2n wa + w2n wn` >> simp[] >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id CODESIZE [] [v]) s = OK u` by
    simp[Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def] >>
  simp[Once run_inst_seq_def, mk_inst_def, is_terminator_def] >>
  conj_tac
  >- (gvs[Abbr `u`, update_var_def]) >>
  rpt strip_tac >>
  `lookup_var x t = lookup_var x u` by (gvs[lookup_var_def] >> metis_tac[]) >>
  simp[Abbr `u`, lookup_var_update_var] >> metis_tac[]
QED

Theorem self_code_copy_store_run:
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand len s = SOME n /\ eval_operand out s = SOME p /\
  w2n a + w2n n <= LENGTH s.vs_code ==>
  run_inst_seq [mk_inst id CODECOPY [dst;src;len] [];
                mk_inst sid MSTORE [out;len] []] s =
    OK (mstore (w2n p) n (write_memory_with_expansion (w2n d)
      (TAKE (w2n n) (DROP (w2n a) s.vs_code)) s))
Proof
  strip_tac >>
  `TAKE (w2n n) (DROP (w2n a) s.vs_code ++ REPLICATE (w2n n) 0w) =
    TAKE (w2n n) (DROP (w2n a) s.vs_code)` by
    (irule rich_listTheory.TAKE_APPEND1 >> simp[]) >>
  drule_all step_CODECOPY >> disch_then (qspec_then `id` assume_tac) >>
  simp[Once run_inst_seq_def, mk_inst_def, is_terminator_def] >>
  `eval_operand out (write_memory_with_expansion (w2n d)
     (TAKE (w2n n) (DROP (w2n a) s.vs_code)) s) = SOME p /\
   eval_operand len (write_memory_with_expansion (w2n d)
     (TAKE (w2n n) (DROP (w2n a) s.vs_code)) s) = SOME n` by
    (Cases_on `out` >> Cases_on `len` >>
     gvs[eval_operand_def, lookup_var_def, write_memory_with_expansion_def]) >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def]
QED


Theorem self_code_tail_layout:
  emit_void CODECOPY [dst;src;len] sa = ((),sb) /\
  emit_void MSTORE [out;len] sb = ((),sc) ==>
  sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
  same_blocks sa sc /\
  emitted_insts sa sc =
    [mk_inst sa.cs_next_id CODECOPY [dst;src;len] [];
     mk_inst sb.cs_next_id MSTORE [out;len] []] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa sc)
Proof
  strip_tac >>
  drule_all (emit_void_extends |> Q.SPECL [`CODECOPY`,`[dst;src;len]`,`sa`,`sb`]) >> strip_tac >>
  drule_all (emit_void_extends |> Q.SPECL [`MSTORE`,`[out;len]`,`sb`,`sc`]) >> strip_tac >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> simp[]) >>
  drule_all (emitted_insts_emit_void |> Q.SPECL [`CODECOPY`,`[dst;src;len]`,`sa`,`sb`]) >> strip_tac >>
  drule_all (emitted_insts_emit_void |> Q.SPECL [`MSTORE`,`[out;len]`,`sb`,`sc`]) >> strip_tac >>
  rpt conj_tac
  >- simp[listTheory.APPEND_ASSOC]
  >- metis_tac[same_blocks_def]
  >- simp[] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem self_code_tail_run:
  emit_void CODECOPY [dst;src;len] sa = ((),sb) /\
  emit_void MSTORE [out;len] sb = ((),sc) /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  eval_operand dst s = SOME b /\ eval_operand out s = SOME p /\
  w2n a + w2n n <= LENGTH s.vs_code ==>
  run_inst_seq (emitted_insts sa sc) s =
    OK (mstore (w2n p) n (write_memory_with_expansion (w2n b)
      (TAKE (w2n n) (DROP (w2n a) s.vs_code)) s))
Proof
  strip_tac >> drule_all self_code_tail_layout >> strip_tac >>
  simp[] >> irule self_code_copy_store_run >> simp[]
QED

Theorem self_code_tail_frame:
  emit_void CODECOPY [dst;src;len] sa = ((),sb) /\
  emit_void MSTORE [out;len] sb = ((),sc) /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  eval_operand out s = SOME p /\ eval_operand dst s = SOME (p+32w) /\
  w2n a + w2n n <= LENGTH s.vs_code /\
  stmt_state_rel ctx fn cenv cx es s /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,cap) /\
  w2n p + cap < dimword (:256) /\ 32 + w2n n <= cap /\
  (!nm off sz. local_region cenv es.scopes s nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  (!id off sz. id < sbase.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
    regions_disjoint (w2n p) cap off sz) ==>
  ?t. run_inst_seq (emitted_insts sa sc) s = OK t /\
    stmt_state_rel ctx fn cenv cx es t /\ wb_frame cenv es es sbase s t /\
    eval_operand out t = SOME p /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n p,cap) /\
    t.vs_memory = (mstore (w2n p) n (write_memory_with_expansion (w2n p+32)
      (TAKE (w2n n) (DROP (w2n a) s.vs_code)) s)).vs_memory
Proof
  strip_tac >>
  `w2n (p+32w) = w2n p+32` by
    (simp[word_add_def, w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  drule_all self_code_tail_run >>
  qpat_assum `w2n (p+32w) = _` (fn th => rewrite_tac[th]) >> strip_tac >>
  qabbrev_tac `bs = TAKE (w2n n) (DROP (w2n a) s.vs_code)` >>
  `LENGTH bs = w2n n` by simp[Abbr `bs`] >>
  qabbrev_tac `z = mstore (w2n p) n (write_memory_with_expansion (w2n p+32) bs s)` >>
  `stmt_state_rel ctx fn cenv cx es z /\ wb_frame cenv es es sbase s z` by
    (simp[Abbr `z`] >>
     `n = n2w (LENGTH bs)` by simp[Abbr `bs`] >>
     pop_assum (fn th => once_rewrite_tac[th]) >>
     irule (SIMP_RULE std_ss [LET_THM] slice_allocated_bytes_write_frame) >>
     metis_tac[]) >>
  qexists_tac `z` >> simp[] >>
  simp[Abbr `z`] >>
  Cases_on `out` >> gvs[eval_operand_def, lookup_var_def, write_memory_with_expansion_def]
QED

Theorem self_code_tail_vv_post:
  emit_void CODECOPY [dst;src;len] sa = ((),sb) /\
  emit_void MSTORE [out;len] sb = ((),sc) /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  eval_operand out s = SOME p /\ eval_operand dst s = SOME (p+32w) /\
  w2n a + w2n n <= LENGTH s.vs_code /\
  stmt_state_rel ctx fn cenv cx es s /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,cap) /\
  w2n p + cap < dimword (:256) /\ 32 + w2n n <= cap /\
  (!nm off sz. local_region cenv es.scopes s nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  (!id off sz. id < sbase.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
    regions_disjoint (w2n p) cap off sz) /\
  expr_type e = BaseT (BytesT (Dynamic bound)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic bound))) /\
  w2n n <= bound /\
  sbase.cs_next_id <= inst.inst_id /\ inst.inst_id < sc.cs_next_id /\
  local_ptrs_reserved cenv sbase ==>
  ?t. run_inst_seq (emitted_insts sa sc) s = OK t /\
    vv_post ctx fn cenv cx e es sbase sc s es
      (Value (BytesV (TAKE (w2n n) (DROP (w2n a) s.vs_code))))
      (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t
Proof
  strip_tac >> drule_all self_code_tail_frame >> strip_tac >>
  qabbrev_tac `bs = TAKE (w2n n) (DROP (w2n a) s.vs_code)` >>
  `LENGTH bs = w2n n` by simp[Abbr `bs`] >>
  `val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV bs) (w2n p) t.vs_memory` by
    (qpat_x_assum `t.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
     metis_tac[bytes_buffer_write_encoding, n2w_w2n]) >>
  `val_wf (BaseTV (BytesT (Dynamic bound))) (BytesV bs)` by
    (simp[val_wf_def, type_memory_size_def] >>
     qspec_then `bound` mp_tac le_word_size_mul >> decide_tac) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  `!off len. off + len <= w2n p \/ w2n p + 32 + LENGTH bs <= off ==>
     mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `t.vs_memory = _` (fn th => rewrite_tac[th]) >>
     `n = n2w (LENGTH bs)` by simp[Abbr `bs`] >>
     pop_assum (fn th => once_rewrite_tac[th]) >>
     irule exprSimCalldataSliceTheory.bytes_buffer_write_frame >>
     first_assum ACCEPT_TAC) >>
  `pure_frame cenv fn es sbase s t` by
    (rewrite_tac[loweringPostsTheory.pure_frame_def] >> conj_tac >>
     rpt strip_tac >> first_x_assum irule
     >- (`regions_disjoint (w2n p) cap b sz` by metis_tac[] >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     pop_assum (qspecl_then [`inst`,`w2n p`,`cap`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qpat_x_assum `t.vs_memory = _` kall_tac >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule vv_post_allocated_memory_intro >>
  simp[mk_ptr_def, evaluate_type_def, is_word_type_def] >>
  qexistsl_tac [`inst.inst_id`,`w2n p`,`cap`] >>
  simp[val_footprint_def] >>
  rpt strip_tac >> suspend "local"
QED

Resume self_code_tail_vv_post[local]:
  `local_region cenv es.scopes s n' lb lsz` by
    (irule local_region_frame >>
     conj_tac
     >- (qexists_tac `fn` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sbase`,`es.scopes`,`t`] >>
     fs[wb_frame_def]) >>
  fs[regions_disjoint_def] >> metis_tac[]
QED

Finalise self_code_tail_vv_post

(* Compiler-facing boundary for the two writes.  The source is code, not
   memory; the only pointer operands are the allocated destination pair. *)
Theorem self_code_copy_store_emitted_ptr:
  emit_void CODECOPY [Var dst;src;len] sa = ((),sb) /\
  emit_void MSTORE [Var out;len] sb = ((),sc) /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn out s 32 /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  lookup_var out s = SOME p /\ lookup_var dst s = SOME (p+32w) /\
  w2n p+32 < dimword (:256) /\ w2n a+w2n n <= LENGTH s.vs_code /\
  op_taint tn src = {} /\ op_taint tn len = {} /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!name off sz. local_region cenv es.scopes s name off sz ==>
    off+sz <= w2n p \/ w2n p+32+w2n n <= off) ==>
  ?t tn'. run_inst_seq (emitted_insts sa sc) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc) s G tn' /\
    ghost_inv d cenv cx es G tn' t /\
    ghost_kept cenv es sa G tn s G tn' /\
    tn' = (tn with t_mem := (tn.t_mem DIFF
      {j | w2n p+32 <= j /\ j < w2n p+32+w2n n}) DIFF
      {j | w2n p <= j /\ j < w2n p+32}) /\
    t = mstore (w2n p) n (write_memory_with_expansion (w2n p+32)
      (TAKE (w2n n) (DROP (w2n a) s.vs_code)) s)
Proof
  strip_tac >>
  `w2n (p+32w) = w2n p+32` by
    (simp[word_add_def, w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> simp[]) >>
  qabbrev_tac `bs = TAKE (w2n n) (DROP (w2n a) s.vs_code)` >>
  `LENGTH bs = w2n n` by simp[Abbr `bs`] >>
  `step_inst_base (mk_inst sa.cs_next_id CODECOPY [Var dst;src;len] []) s =
    OK (write_memory_with_expansion (w2n p+32) bs s)` by
    (`eval_operand (Var dst) s = SOME (p+32w)` by simp[eval_operand_def] >>
     `TAKE (w2n n) (DROP (w2n a) s.vs_code ++ REPLICATE (w2n n) 0w) = bs` by
       (simp[Abbr `bs`] >> irule rich_listTheory.TAKE_APPEND1 >> simp[]) >>
     metis_tac[step_CODECOPY]) >>
  `w2n n = LENGTH bs` by simp[] >>
  qpat_x_assum `LENGTH bs = w2n n` kall_tac >>
  `!name off sz. local_region cenv es.scopes s name off sz ==>
    off+sz <= w2n p \/ w2n p+32+LENGTH bs <= off` by metis_tac[] >>
  drule_all self_code_copy_store_ptr >>
  disch_then (qspecl_then [`D`,`PG`,`sb.cs_next_id`] strip_assume_tac) >>
  drule_all (emitted_insts_emit_void |> Q.SPECL [`CODECOPY`,`[Var dst;src;len]`,`sa`,`sb`]) >> strip_tac >>
  drule_all (emitted_insts_emit_void |> Q.SPECL [`MSTORE`,`[Var out;len]`,`sb`,`sc`]) >> strip_tac >>
  drule_all (emit_void_extends |> Q.SPECL [`CODECOPY`,`[Var dst;src;len]`,`sa`,`sb`]) >> strip_tac >>
  drule_all (emit_void_extends |> Q.SPECL [`MSTORE`,`[Var out;len]`,`sb`,`sc`]) >> strip_tac >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> simp[]) >>
  qexistsl_tac [`mstore (w2n p) n (write_memory_with_expansion (w2n p+32) bs s)`,
    `tn with t_mem := (tn.t_mem DIFF
      {j | w2n p+32 <= j /\ j < w2n p+32+w2n n}) DIFF
      {j | w2n p <= j /\ j < w2n p+32}`] >>
  fs[Abbr `bs`] >>
  conj_tac
  >- (qpat_x_assum `w2n (p+32w) = _`
        (fn th => pure_once_rewrite_tac[GSYM th]) >>
      irule self_code_copy_store_run >> simp[eval_operand_def]) >>
  metis_tac[]
QED


Theorem self_code_prefix_shape:
  emit_op CODESIZE [] sa = (limit,sb) /\
  compile_assert_slice_bounds src len limit sb = ((),sc) /\
  compile_slice_out_buf sz sc = ((out,dst),sd) ==>
  ci_mono sa sc /\ ci_mono sc sd /\ ci_mono sa sd /\
  sd.cs_current_bb = sa.cs_current_bb /\
  sd.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sd /\
  emitted_insts sa sd =
    (emitted_insts sa sb ++ emitted_insts sb sc) ++ emitted_insts sc sd /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa sd) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sd) /\
  EVERY (\i. ~is_terminator i.inst_opcode)
    (emitted_insts sa sb ++ emitted_insts sb sc) /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode)
    (emitted_insts sa sb ++ emitted_insts sb sc)
Proof
  strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule exprSimSliceBoundsTheory.slice_bounds_shape >> strip_tac >>
  drule slice_extcode_out_control >> strip_tac >>
  `ci_mono sa sb` by metis_tac[ci_mono_emit_op, SND] >>
  `cs_extends sb sc` by
    (mp_tac (Q.SPECL [`src`,`len`,`limit`,`sb`,`\i. T`]
      externalEntryShapeTheory.compile_assert_slice_bounds_labels) >> simp[]) >>
  `ci_mono sb sc` by simp[ci_mono_def] >>
  `ci_mono sc sd` by metis_tac[ci_mono_compile_slice_out_buf, SND] >>
  `ci_mono sa sc /\ ci_mono sa sd` by metis_tac[ci_mono_trans] >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> simp[]) >>
  `sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc` by
    simp[listTheory.APPEND_ASSOC] >>
  `emitted_insts sa sd = emitted_insts sa sc ++ emitted_insts sc sd` by
    (irule emitted_insts_append >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS) (emitted_insts sa sb ++ emitted_insts sb sc)` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS) (emitted_insts sa sd)` by
    (qpat_x_assum `emitted_insts sa sd = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `emitted_insts sa sc = _` (fn th => rewrite_tac[th]) >>
     asm_rewrite_tac[listTheory.EVERY_APPEND]) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- fs[same_blocks_def]
  >- simp[listTheory.APPEND_ASSOC]
  >- simp[]
  >- first_assum ACCEPT_TAC
  >> fs[listTheory.EVERY_MEM]
QED

(* Bounds are checked before the buffer is allocated. *)
Theorem self_code_prefix_success_entry:
  emit_op CODESIZE [] sa = (limit,sb) /\
  compile_assert_slice_bounds src len limit sb = ((),sc) /\
  compile_slice_out_buf sz sc = ((out,dst),sd) /\
  fn_has_code sa sd fn /\ fn_inst_ids_distinct fn /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ 32 <= sz /\ sz < dimword (:256) /\
  ghost_inv d cenv cx es G tn s /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  op_taint tn src = {} /\ op_taint tn len = {} /\
  op_prov G src = NONE /\ op_prov G len = NONE /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  LENGTH s.vs_code < dimword (:256) /\ w2n a+w2n n <= LENGTH s.vs_code ==>
  ?u p Gf tnf.
    run_inst_seq (emitted_insts sa sd) s = OK u /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sd) s Gf tnf /\
    ghost_inv d cenv cx es Gf tnf u /\
    ghost_kept cenv es sa G tn s Gf tnf /\
    (?x y. out = Var x /\ dst = Var y /\
      ptr_covers Gf tnf x u sz /\ ptr_covers Gf tnf y u (sz-32)) /\
    eval_operand src u = SOME a /\ eval_operand len u = SOME n /\
    op_taint tnf src = {} /\ op_taint tnf len = {} /\
    eval_operand out u = SOME p /\ eval_operand dst u = SOME (p+32w) /\
    FLOOKUP u.vs_allocas sc.cs_next_id = SOME (w2n p,sz) /\
    w2n p+sz < dimword (:256) /\ sc.cs_next_id < sd.cs_next_id /\
    (!nm off cap. local_region cenv es.scopes u nm off cap ==>
      regions_disjoint (w2n p) sz off cap) /\
    stmt_state_rel ctx fn cenv cx es u /\ wb_frame cenv es es sa s u /\
    u.vs_memory = s.vs_memory /\
    (!id off cap. id < sa.cs_next_id /\ FLOOKUP u.vs_allocas id = SOME (off,cap) ==>
      regions_disjoint (w2n p) sz off cap)
Proof
  strip_tac >>
  drule_all self_code_prefix_shape >> strip_tac >>
  `?v. run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s = OK v /\
    v = s with vs_vars := v.vs_vars /\
    (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s)` by
    (drule_all self_code_size_bounds_run >> simp[]) >>
  mp_tac (Q.SPECL [`D`,`ctx`,`fn`,`PG`,`G`,`tn`,`s`,`src`,`len`,`limit`,
    `sa`,`sb`,`sc`,`a`,`n`] self_code_size_bounds_checked) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`Gb`,`tnb`] strip_assume_tac) >>
  mp_tac (Q.INST [`a`|->`src`,`n`|->`len`,`t`|->`v`,`Gf`|->`Gb`,`tnf`|->`tnb`]
    self_code_size_bounds_frame) >>
  impl_tac >- simp[] >> strip_tac >>
  `v with vs_vars := s.vs_vars = s` by
    (qpat_assum `v = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es v` by
    (irule hash_readonly_state_rel >> metis_tac[]) >>
  `wb_frame cenv es es sa s v` by (irule log_readonly_frame >> simp[]) >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> fs[ci_mono_def] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `fn_has_code sc sd fn` by
    (qspecl_then [`sa`,`sc`,`sd`,`fn`] mp_tac fn_has_code_split >> fs[ci_mono_def]) >>
  mp_tac (Q.INST [`sa`|->`sc`,`sb`|->`sd`,`s`|->`v`,`data`|->`dst`,`func`|->`fn`]
    slice_extcode_output_entry) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`u`,`p`] strip_assume_tac) >>
  drule_all slice_extcode_out_owner_inst >> strip_tac >>
  mp_tac (Q.INST [`sa`|->`sc`,`sb`|->`sd`,`G`|->`Gb`,`tn`|->`tnb`,
    `s`|->`v with vs_inst_idx :=
      s.vs_inst_idx + LENGTH (emitted_insts sa sb ++ emitted_insts sb sc)`]
    self_code_out_buffer_checked) >>
  impl_tac >- (simp[stmt_state_rel_inst_idx, hash_ghost_inv_inst_idx] >> metis_tac[]) >>
  disch_then (qx_choosel_then [`t1`,`G1`,`tn1`,`xo`,`xd`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc sd)` by
    (drule slice_extcode_out_control >> strip_tac >> fs[listTheory.EVERY_MEM]) >>
  `t1 = u with vs_inst_idx :=
      s.vs_inst_idx + LENGTH (emitted_insts sa sb ++ emitted_insts sb sc)` by
    (qpat_x_assum `run_inst_seq (emitted_insts sc sd) (v with vs_inst_idx := _) = OK t1`
       mp_tac >>
     simp[fragExecTheory.run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn
     ((emitted_insts sa sb ++ emitted_insts sb sc) ++ emitted_insts sc sd) s G1 tn1` by
    (irule exprSimPtrLiteralChunksTheory.literal_inst_seq_ptr_append >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`Gb`,`tnb`,`v`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept cenv es sc Gb tnb v G1 tn1` by
    (qpat_x_assum `ghost_kept cenv es sc Gb tnb _ G1 tn1` mp_tac >>
     simp[ghost_kept_def, local_region_def, lookup_var_def] >>
     strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept cenv es sa G tn s G1 tn1` by
    (mp_tac (Q.INST [`G0`|->`G`,`G1`|->`Gb`,`G2`|->`G1`]
       (INST_TYPE [alpha |-> ``:num # num``]
         (Q.INST [`es0`|->`es`,`es1`|->`es`,`es'`|->`es`,`sb`|->`sc`,
           `s0`|->`s`,`s1`|->`v`,`tn0`|->`tn`,`tn1`|->`tnb`,`tn2`|->`tn1`,
           `func`|->`fn`] wordArgsPtrTheory.ghost_kept_wb_trans))) >>
     impl_tac >- fs[ci_mono_def] >> simp[]) >>
  `u.vs_labels = s.vs_labels` by simp[] >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by metis_tac[] >>
  `!value. (!x. value = Var x ==> not_fresh_at sa x) ==>
    eval_operand value u = eval_operand value s /\
    op_prov G1 value = op_prov G value /\ op_taint tn1 value = op_taint tn value` by
    (gen_tac >> disch_tac >> irule self_code_prefix_operand_frame >> metis_tac[]) >>
  qexistsl_tac [`u`,`p`,`G1`,`tn1`] >>
  rpt conj_tac
  >- (qpat_x_assum `emitted_insts sa sd = _` (fn th => rewrite_tac[th]) >>
      qpat_assum `run_inst_seq (_ ++ _) s = OK v`
        (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
      first_assum ACCEPT_TAC)
  >- (qpat_x_assum `emitted_insts sa sd = _` (fn th => rewrite_tac[th]) >>
      first_assum ACCEPT_TAC)
  >- (qpat_x_assum `ghost_inv _ _ _ _ G1 tn1 t1` mp_tac >>
      simp[hash_ghost_inv_inst_idx])
  >- first_assum ACCEPT_TAC
  >- (qexistsl_tac [`xo`,`xd`] >> gvs[])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (mp_tac (Q.SPECL [`fn`,`cenv`,`cx`,`es`,`s`,`sa`,`es`,`es`,`sc`,`v`,`u`,`ctx`]
        wb_frame_trans) >>
      impl_tac >- fs[ci_mono_def] >> simp[])
  >- (qpat_x_assum `u.vs_memory = _` (fn th => rewrite_tac[th]) >>
      qpat_assum `v = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
      simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!j b len. j < sc.cs_next_id /\ _ ==> _` irule >>
  qexists_tac `id` >> fs[ci_mono_def]
QED

(* The checked suffix has a cursor-independent taint endpoint. *)
Theorem self_code_copy_store_uniform_ptr:
  emit_void CODECOPY [Var dst;src;len] sa = ((),sb) /\
  emit_void MSTORE [Var out;len] sb = ((),sc) /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn out s 32 /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  lookup_var out s = SOME p /\ lookup_var dst s = SOME (p+32w) /\
  w2n p+32 < dimword (:256) /\ w2n a+w2n n <= LENGTH s.vs_code /\
  op_taint tn src = {} /\ op_taint tn len = {} /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!name off sz. local_region cenv es.scopes s name off sz ==>
    off+sz <= w2n p \/ w2n p+32+w2n n <= off) ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc)
    (s with vs_inst_idx := k) G
    (tn with t_mem := (tn.t_mem DIFF
      {j | w2n p+32 <= j /\ j < w2n p+32+w2n n}) DIFF
      {j | w2n p <= j /\ j < w2n p+32})
Proof
  strip_tac >> gen_tac >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := k`]
    self_code_copy_store_emitted_ptr) >>
  impl_tac
  >- (fs[lookup_var_def] >>
      simp[hash_ghost_inv_inst_idx, stmt_state_rel_inst_idx, lookup_var_def] >>
      rpt strip_tac >> first_x_assum irule >>
      fs[local_region_def, eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  strip_tac >> gvs[]
QED


(* The copy/store tail runs from the allocated buffer: the semantic post and
   the checked writes meet at one raw endpoint. *)
Theorem self_code_tail_success_ptr:
  emit_void CODECOPY [Var dst;src;len] sd = ((),se) /\
  emit_void MSTORE [Var out;len] se = ((),sf) /\
  eval_operand src u = SOME a /\ eval_operand len u = SOME n /\
  eval_operand (Var out) u = SOME p /\ eval_operand (Var dst) u = SOME (p+32w) /\
  w2n a+w2n n <= LENGTH u.vs_code /\
  stmt_state_rel ctx fn cenv cx es u /\ local_ptrs_reserved cenv sd /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n p,sz) /\
  w2n p+sz < dimword (:256) /\ 32+w2n n <= sz /\
  (!nm off cap. local_region cenv es.scopes u nm off cap ==>
    regions_disjoint (w2n p) sz off cap) /\
  (!id off cap. id < sa.cs_next_id /\ FLOOKUP u.vs_allocas id = SOME (off,cap) ==>
    regions_disjoint (w2n p) sz off cap) /\
  expr_type e = BaseT (BytesT (Dynamic bound)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic bound))) /\
  w2n n <= bound /\ sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sf.cs_next_id /\
  ghost_inv d cenv cx es G tn u /\
  ptr_covers G tn dst u (sz-32) /\ ptr_covers G tn out u sz /\
  val_store_size (BaseTV (BytesT (Dynamic bound)))
    (BytesV (TAKE (w2n n) (DROP (w2n a) u.vs_code))) <= sz /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= sz /\
  op_taint tn src = {} /\ op_taint tn len = {} /\ ~ctx_has_dalloca ctx /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sd x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sd x) /\
  local_ptrs_reserved cenv sa ==>
  ?z tn'. run_inst_seq (emitted_insts sd sf) u = OK z /\
    vv_post ctx fn cenv cx e es sa sf u es
      (Value (BytesV (TAKE (w2n n) (DROP (w2n a) u.vs_code))))
      (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) z /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sd sf) u G tn' /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sd sf)
      (u with vs_inst_idx := k) G tn') /\
    ghost_inv d cenv cx es G tn' z /\
    ghost_kept cenv es sd G tn u G tn' /\
    ptr_vv_ok cx (expr_type e)
      (Value (BytesV (TAKE (w2n n) (DROP (w2n a) u.vs_code))))
      (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) es G tn' z /\
    ptr_buf_ok cenv e (Var out) G z /\
    z = mstore (w2n p) n (write_memory_with_expansion (w2n p+32)
      (TAKE (w2n n) (DROP (w2n a) u.vs_code)) u) /\
    tn' = (tn with t_mem := (tn.t_mem DIFF
      {j | w2n p+32 <= j /\ j < w2n p+32+w2n n}) DIFF
      {j | w2n p <= j /\ j < w2n p+32})
Proof
  strip_tac >>
  drule_all self_code_tail_vv_post >> disch_then (qx_choose_then `t` strip_assume_tac) >>
  `lookup_var out u = SOME p /\ lookup_var dst u = SOME (p+32w)` by
    fs[eval_operand_def] >>
  `!nm off cap. local_region cenv es.scopes u nm off cap ==>
    off+cap <= w2n p \/ w2n p+32+w2n n <= off` by
    (rpt strip_tac >>
     `regions_disjoint (w2n p) sz off cap` by metis_tac[] >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `w2n p+32 < dimword (:256)` by decide_tac >>
  `ptr_covers G tn out u 32 /\ ptr_covers G tn dst u (w2n n)` by
    (fs[ptr_covers_def] >> conj_tac >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sd sf)
    (u with vs_inst_idx := k) G
    (tn with t_mem := (tn.t_mem DIFF
      {j | w2n p+32 <= j /\ j < w2n p+32+w2n n}) DIFF
      {j | w2n p <= j /\ j < w2n p+32})` by
    (irule self_code_copy_store_uniform_ptr >>
     simp[] >> conj_tac
     >- (qexistsl_tac [`a`,`dst`,`len`,`out`,`se`,`src`] >> simp[]) >>
     qexistsl_tac [`cenv`,`cx`,`d`,`es`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  drule_all self_code_copy_store_emitted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] (qx_choosel_then [`z`,`tz`] strip_assume_tac)) >>
  `t = z` by
    (qpat_x_assum `run_inst_seq (emitted_insts sd sf) u = OK t` mp_tac >> simp[]) >>
  qpat_x_assum `t = z` SUBST_ALL_TAC >>
  `ptr_vv_ok cx (expr_type e)
     (Value (BytesV (TAKE (w2n n) (DROP (w2n a) u.vs_code))))
     (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) es G tz z /\
   ptr_buf_ok cenv e (Var out) G z` by suspend "result" >>
  qexistsl_tac [`z`,`tz`] >> gvs[]
QED

(* Finalised after the result interface below. *)


(* Consume the semantic value view and coverage without exposing its buffer
   allocation witness to the continuation consumer. *)
Theorem self_code_covered_result:
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic cap))) /\
  vv_holds cenv cx ty (Value (BytesV bs))
    (LocatedValue ty (mk_ptr (Var out) LocMemory)) es s /\
  ptr_covers G tn out s sz /\
  val_wf (BaseTV (BytesT (Dynamic cap))) (BytesV bs) /\
  val_store_size (BaseTV (BytesT (Dynamic cap))) (BytesV bs) <= sz /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= sz /\
  tn' = (tn with t_mem := (tn.t_mem DIFF
    {j | w2n p+32 <= j /\ j < w2n p+32+LENGTH bs}) DIFF
    {j | w2n p <= j /\ j < w2n p+32}) /\
  lookup_var out s = SOME p ==>
  ptr_vv_ok cx ty (Value (BytesV bs))
    (LocatedValue ty (mk_ptr (Var out) LocMemory)) es G tn' s /\
  ptr_buf_ok cenv e (Var out) G s
Proof
  strip_tac >> fs[ptr_covers_def] >>
  `val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs)
     (w2n p) s.vs_memory` by
    (fs[vv_holds_def, mk_ptr_def, eval_operand_def, read_result_def, vyperStateTheory.return_def] >> metis_tac[]) >>
  irule self_code_copy_store_located_result >>
  qexistsl_tac [`b`,`bs`,`cap`,`p`,`sz'`,`tn`] >>
  simp[read_result_def, vyperStateTheory.return_def] >> decide_tac
QED


Resume self_code_tail_success_ptr[result]:
  qabbrev_tac `bs = TAKE (w2n n) (DROP (w2n a) u.vs_code)` >>
  `LENGTH bs = w2n n` by simp[Abbr `bs`] >>
  `val_wf (BaseTV (BytesT (Dynamic bound))) (BytesV bs)` by
    (simp[val_wf_def, type_memory_size_def] >>
     qspec_then `bound` mp_tac le_word_size_mul >> decide_tac) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  `vv_holds cenv cx (expr_type e) (Value (BytesV bs))
    (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) es z` by
    (fs[vv_post_def] >> gvs[]) >>
  mp_tac (Q.INST [`ty`|->`expr_type e`,`cap`|->`bound`,`s`|->`z`,`tn'`|->`tz`]
    self_code_covered_result) >>
  impl_tac >- (
    simp[] >>
    qpat_x_assum `ptr_covers G tn out u sz` mp_tac >>
    qpat_x_assum `lookup_var out u = SOME p` mp_tac >>
    simp[NoAsms, ptr_covers_def, mstore_def,
         write_memory_with_expansion_def, lookup_var_def]) >>
  simp[]
QED

Finalise self_code_tail_success_ptr

(* Bounds, then the allocated buffer, then the copy/store tail. *)
Theorem self_code_full_success_ptr:
  emit_op CODESIZE [] sa = (limit,sb) /\
  compile_assert_slice_bounds src len limit sb = ((),sc) /\
  compile_slice_out_buf sz sc = ((Var out,Var dst),sd) /\
  emit_void CODECOPY [Var dst;src;len] sd = ((),se) /\
  emit_void MSTORE [Var out;len] se = ((),sf) /\
  fn_has_code sa sf fn /\ fn_inst_ids_distinct fn /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ 32+w2n n <= sz /\ sz < dimword (:256) /\
  ghost_inv d cenv cx es G tn s /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  op_taint tn src = {} /\ op_taint tn len = {} /\
  op_prov G src = NONE /\ op_prov G len = NONE /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  LENGTH s.vs_code < dimword (:256) /\ w2n a+w2n n <= LENGTH s.vs_code /\
  expr_type e = BaseT (BytesT (Dynamic bound)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic bound))) /\
  w2n n <= bound /\
  val_store_size (BaseTV (BytesT (Dynamic bound)))
    (BytesV (TAKE (w2n n) (DROP (w2n a) s.vs_code))) <= sz /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= sz ==>
  ?z H tm. run_inst_seq (emitted_insts sa sf) s = OK z /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sf) s H tm /\
    vv_post ctx fn cenv cx e es sa sf s es
      (Value (BytesV (TAKE (w2n n) (DROP (w2n a) s.vs_code))))
      (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) z /\
    ghost_inv d cenv cx es H tm z /\
    ghost_kept cenv es sa G tn s H tm /\
    ptr_vv_ok cx (expr_type e)
      (Value (BytesV (TAKE (w2n n) (DROP (w2n a) s.vs_code))))
      (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) es H tm z /\
    ptr_buf_ok cenv e (Var out) H z
Proof
  strip_tac >>
  drule_all self_code_prefix_shape >> strip_tac >>
  drule_all self_code_tail_layout >> strip_tac >>
  `ci_mono sd se /\ ci_mono se sf` by metis_tac[ci_mono_emit_void, SND] >>
  `ci_mono sd sf /\ ci_mono sa sf` by metis_tac[ci_mono_trans] >>
  `emitted_insts sa sf = emitted_insts sa sd ++ emitted_insts sd sf` by
    (irule emitted_insts_append >> simp[]) >>
  `fn_has_code sa sd fn` by
    (qspecl_then [`sa`,`sd`,`sf`,`fn`] mp_tac fn_has_code_split >>
     fs[ci_mono_def]) >>
  `fn_has_code sc sd fn` by
    (qspecl_then [`sa`,`sc`,`sd`,`fn`] mp_tac fn_has_code_split >>
     fs[ci_mono_def]) >>
  `32 <= sz` by decide_tac >>
  drule_all self_code_prefix_success_entry >>
  disch_then (qx_choosel_then [`u`,`p`,`Gf`,`tnf`] strip_assume_tac o SPEC_ALL) >>
  rpt (qpat_x_assum `Var _ = Var _`
    (SUBST_ALL_TAC o SYM o REWRITE_RULE [operand_11])) >>
  drule_all slice_extcode_out_owner_inst >> strip_tac >>
  `u.vs_code = s.vs_code` by
    (fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sd /\
   (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sd x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sd x)` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono]) >>
  mp_tac (Q.INST [`G`|->`Gf`,`tn`|->`tnf`,
    `inst`|->`mk_inst sc.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sc.cs_next_var)]`]
    self_code_tail_success_ptr) >>
  impl_tac >- suspend "tail_premises" >>
  disch_then (qx_choosel_then [`z`,`tz`] strip_assume_tac) >>
  qpat_assum `u.vs_code = s.vs_code` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `run_inst_seq (emitted_insts sa sf) s = OK z` by
    (qpat_x_assum `emitted_insts sa sf = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `run_inst_seq (emitted_insts sa sd) s = OK u`
       (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
     first_assum ACCEPT_TAC) >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sf) s Gf tz` by
    (qpat_x_assum `emitted_insts sa sf = _` (fn th => rewrite_tac[th]) >>
     irule exprSimPtrLiteralChunksTheory.literal_inst_seq_ptr_append >>
     metis_tac[]) >>
  qexistsl_tac [`z`,`Gf`,`tz`] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- suspend "post"
  >- first_assum ACCEPT_TAC
  >- suspend "ghost_frame"
  >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED

Resume self_code_full_success_ptr[tail_premises]:
  simp[mk_inst_def] >>
  fs[ci_mono_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  decide_tac
QED

Resume self_code_full_success_ptr[post]:
  `pure_frame cenv fn es sa s u` by
    (irule loweringPostsTheory.pure_frame_mem_eq >> first_assum ACCEPT_TAC) >>
  irule vv_post_prefix_frame >> simp[] >>
  qexistsl_tac [`es`,`sa`,`u`] >> gvs[]
QED

Resume self_code_full_success_ptr[ghost_frame]:
  irule bodyPtrHashBuiltinsAllocFrameTheory.hash_ghost_kept_clean_tail >>
  qexistsl_tac [`Gf`,`tnf`] >>
  simp[ptrDisciplineTheory.op_taint_def] >>
  pred_setLib.SET_TAC[]
QED

Finalise self_code_full_success_ptr

(* Bounds failure aborts before the buffer is allocated. *)
Theorem self_code_prefix_abort_ptr:
  emit_op CODESIZE [] sa = (limit,sb) /\
  compile_assert_slice_bounds src len limit sb = ((),sc) /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  op_taint tn src = {} /\ op_taint tn len = {} /\
  op_prov G src = NONE /\ op_prov G len = NONE /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\ ~ctx_has_dalloca ctx /\
  LENGTH s.vs_code < dimword (:256) /\ LENGTH s.vs_code < w2n a+w2n n ==>
  ?t H tm.
    run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s = Abort Revert_abort t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb ++ emitted_insts sb sc) s H tm
Proof
  strip_tac >>
  drule_all self_code_size_bounds_run >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`D`,`ctx`,`fn`,`PG`,`G`,`tn`,`s`,`src`,`len`,`limit`,
    `sa`,`sb`,`sc`,`a`,`n`] self_code_size_bounds_checked) >>
  impl_tac >- simp[] >> strip_tac >>
  metis_tac[]
QED

Theorem self_code_continue_outcome_ptr:
  emit_op CODESIZE [] sa = (limit,sb) /\
  compile_assert_slice_bounds src len limit sb = ((),sc) /\
  compile_slice_out_buf sz sc = ((Var out,Var dst),sd) /\
  emit_void CODECOPY [Var dst;src;len] sd = ((),se) /\
  emit_void MSTORE [Var out;len] se = ((),sf) /\
  fn_has_code sa sf fn /\ fn_inst_ids_distinct fn /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ es.gas_obs = [] /\
  ~ctx_has_dalloca ctx /\ 32+w2n n <= sz /\ sz < dimword (:256) /\
  ghost_inv d cenv cx es G tn s /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  op_taint tn src = {} /\ op_taint tn len = {} /\
  op_prov G src = NONE /\ op_prov G len = NONE /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  LENGTH cx.txn.code < dimword (:256) /\
  expr_type e = BaseT (BytesT (Dynamic bound)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic bound))) /\
  w2n n <= bound /\
  val_store_size (BaseTV (BytesT (Dynamic bound)))
    (BytesV (TAKE (w2n n) (DROP (w2n a) cx.txn.code))) <= sz /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= sz ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,fn) PG
    (do acc <- get_accounts;
        v <- lift_sum (evaluate_slice (BytesV cx.txn.code) (IntV (&w2n a)) (IntV (&w2n n)) bound);
        return (Value v) od) (es,s,G,tn)
    (\res ee H tm z. ?tv. res = INL tv /\
      vv_post ctx fn cenv cx e es sa sf s ee tv
        (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) z /\
      z.vs_current_bb = sf.cs_current_bb /\ z.vs_inst_idx = LENGTH sf.cs_current_insts /\
      ghost_inv d cenv cx ee H tm z /\ ghost_kept cenv es sa G tn s H tm /\
      ptr_vv_ok cx (expr_type e) tv
        (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) ee H tm z /\
      ptr_buf_ok cenv e (Var out) H z)
    (\res ee ht r. expr_exit res r)
Proof
  strip_tac >>
  `s.vs_code = cx.txn.code` by
    fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
  drule_all self_code_prefix_shape >> strip_tac >>
  drule_all self_code_tail_layout >> strip_tac >>
  `emitted_insts sa sf = emitted_insts sa sd ++ emitted_insts sd sf` by
    (irule emitted_insts_append >> simp[]) >>
  `sf.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sf` by
    (qpat_assum `emitted_insts sa sf = _` (fn th => rewrite_tac[th]) >>
     asm_rewrite_tac[listTheory.APPEND_ASSOC]) >>
  `sf.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sf)` by
    (qpat_assum `emitted_insts sa sf = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[listTheory.EVERY_APPEND] >>
     fs[listTheory.EVERY_MEM]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sf) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sa sf fn` mp_tac >>
     simp[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `bb` >>
     simp[listTheory.DROP_APPEND1, rich_listTheory.IS_PREFIX_APPEND]) >>
  Cases_on `w2n a+w2n n <= LENGTH cx.txn.code`
  >- (`LENGTH s.vs_code < dimword (:256) /\ w2n a+w2n n <= LENGTH s.vs_code /\
       val_store_size (BaseTV (BytesT (Dynamic bound)))
         (BytesV (TAKE (w2n n) (DROP (w2n a) s.vs_code))) <= sz` by simp[] >>
      drule_all self_code_full_success_ptr >> strip_tac >> suspend "success") >>
  `LENGTH s.vs_code < w2n a+w2n n /\ LENGTH s.vs_code < dimword (:256)` by
    (simp[] >> decide_tac) >>
  drule_all self_code_prefix_abort_ptr >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  suspend "abort"
QED

Resume self_code_continue_outcome_ptr[success]:
  qpat_x_assum `!a b. ?z H tm. run_inst_seq _ _ = _ /\ _`
    (strip_assume_tac o SPEC_ALL) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sf)` by fs[listTheory.EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sf) = []` by
    (simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >> fs[listTheory.EVERY_MEM]) >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  `es with gas_obs := [] = es` by
    (qpat_x_assum `es.gas_obs = []` (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (Value (BytesV (TAKE (w2n n) (DROP (w2n a) cx.txn.code))))`,
    `es`,`H`,`tm`,`OK (z with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sf))`] >>
  simp[get_accounts_def, bind_def, lift_sum_def, return_def, slice_bytes_nat] >>
  `z.vs_current_bb = s.vs_current_bb` by
    (drule_all (cj 1 fragExecTheory.exec_block_run_inst_seq) >> simp[]) >>
  gvs[hash_ghost_inv_inst_idx, ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def,
      eval_operand_def, lookup_var_def]
QED

Resume self_code_continue_outcome_ptr[abort]:
  `isPREFIX (emitted_insts sa sb ++ emitted_insts sb sc)
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (emitted_insts sa sf) _` mp_tac >>
     qpat_assum `emitted_insts sa sf = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `emitted_insts sa sd = _` (fn th => rewrite_tac[th]) >>
     strip_tac >>
     irule rich_listTheory.IS_PREFIX_APPEND1 >>
     qexists_tac `emitted_insts sc sd` >>
     irule rich_listTheory.IS_PREFIX_APPEND1 >>
     qexists_tac `emitted_insts sd sf` >>
     first_assum ACCEPT_TAC) >>
  drule_all run_inst_seq_abort_zero_path_ptr >> strip_tac >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "evaluate_slice range"))`,
    `es`,`H`,`tm`,`Abort Revert_abort (t with vs_inst_idx := j)`] >>
  simp[get_accounts_def, bind_def, lift_sum_def, return_def, raise_def,
       slice_bytes_nat, exit_result_def, exprSimDefsTheory.expr_exit_def]
QED

Finalise self_code_continue_outcome_ptr

