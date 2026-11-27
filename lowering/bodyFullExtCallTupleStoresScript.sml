Theory bodyFullExtCallTupleStores
Ancestors abiArgsLabelBoundary[qualified,ignore_grammar] calldataReconstruction[qualified,ignore_grammar] vyperLoweringCorrect[qualified,ignore_grammar] abiBoundaryChecks[qualified,ignore_grammar] valueEncodingProofs[qualified,ignore_grammar] ctorDeployDeadSectionRel[qualified,ignore_grammar] memoryValueEncoding[qualified,ignore_grammar] valueEncodingDefs[qualified,ignore_grammar] valueEncoding[qualified,ignore_grammar] vyperTyping[qualified,ignore_grammar] bool[qualified,ignore_grammar]
  bodyFullExtCallDelayedSlot bodyFullExtCallSlotWrite bodyFullExtCallPosTransport
  loweringPosts bodyPtrDefs valueEncodingProps typedMemoryCopy venomState
  assignPlaceOperandFacts exprSafeOperand targetPurePostTransport
  exprLowering context compileEnv
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyInvSplit[qualified] exprSimHypsDefs[qualified]

(* The preparation cut may allocate. Only an old, registered and
   local-disjoint window is protected by the preparation frames. *)
Theorem extcall_tuple_prepare_window[local]:
  wb_frame ce ee ee ca s z /\ ghost_kept_at lo ce ee ca G tn s Gz tz /\
  FLOOKUP s.vs_allocas aid = SOME (b,cap) /\ aid < ca.cs_next_id /\
  (!name p k. local_region ce ee.scopes s name p k ==>
      b+cap <= p \/ p+k <= b) /\ off+n <= cap ==>
  FLOOKUP z.vs_allocas aid = SOME (b,cap) /\
  mem_bytes_at (b+off) n z.vs_memory = mem_bytes_at (b+off) n s.vs_memory /\
  (!i. b+off <= i /\ i < b+off+n /\ i IN tz.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[wb_frame_def] >> strip_tac >>
  conj_tac >- (qpat_assum `!a r. FLOOKUP s.vs_allocas a = SOME r ==> _`
                (qspecl_then [`aid`,`(b,cap)`] mp_tac) >> simp[]) >>
  conj_tac
  >- (`mem_bytes_at b cap z.vs_memory = mem_bytes_at b cap s.vs_memory` by
        ((qpat_assum `!a p k. _ ==> mem_bytes_at p k _ = _`
           (qspecl_then [`aid`,`b`,`cap`] mp_tac) >> simp[] >> (metis_tac[]))) >>
      drule mem_bytes_at_translated_window >> disch_then (qspecl_then [`off`,`n`] mp_tac) >> simp[]) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_kept_at_def] >> strip_tac >> rpt strip_tac >>
  `b <= i /\ i < b+cap` by decide_tac >>
  qpat_assum `!a p k j. _ ==> j IN tn.t_mem` (qspecl_then [`aid`,`b`,`cap`,`i`] mp_tac) >> simp[] >>
  impl_tac >- (rpt strip_tac >>
    qpat_assum `!nm p k. local_region _ _ _ nm p k ==> b+cap <= p \/ p+k <= b`
      (drule_then ACCEPT_TAC)) >> simp[]
QED

(* A prefix of the tuple and the selector window are both old windows;
   the additional ordering premise excludes the current slot write. *)
Theorem extcall_tuple_slot_keeps_window[local]:
  wb_frame ce ee ee ca s z /\ ghost_kept_at lo ce ee ca G tn s Gz tz /\
  typed_copy_state_frame cw dst width z q /\
  (!i. i < dst \/ dst+width <= i ==> (i IN tq.t_mem <=> i IN tz.t_mem)) /\
  FLOOKUP s.vs_allocas aid = SOME (b,cap) /\ aid < ca.cs_next_id /\
  (!name p k. local_region ce ee.scopes s name p k ==>
      b+cap <= p \/ p+k <= b) /\ off+n <= cap /\
  (b+off+n <= dst \/ dst+width <= b+off) ==>
  FLOOKUP q.vs_allocas aid = SOME (b,cap) /\
  mem_bytes_at (b+off) n q.vs_memory = mem_bytes_at (b+off) n s.vs_memory /\
  (!i. b+off <= i /\ i < b+off+n /\ i IN tq.t_mem ==> i IN tn.t_mem)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all_then strip_assume_tac extcall_tuple_prepare_window >>
  qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[typed_copy_state_frame_def, typed_copy_frame_def] >> strip_tac >>
  `q.vs_allocas = z.vs_allocas` by
    (qpat_assum `_ with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
          vs_current_bb := _; vs_inst_idx := _|> = z` mp_tac >>
     simp[venom_state_component_equality]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (`mem_bytes_at (b+off) n q.vs_memory = mem_bytes_at (b+off) n z.vs_memory` by
        (first_x_assum irule >> decide_tac) >> simp[]) >>
  rpt strip_tac >>
  `i IN tz.t_mem` by
    (qpat_assum `!j. j < dst \/ dst+width <= j ==> _` (qspec_then `i` mp_tac) >>
     impl_tac >- decide_tac >> simp[]) >>
  qpat_assum `!j. b+off <= j /\ j < b+off+n /\ j IN tz.t_mem ==> _`
    (qspec_then `i` mp_tac) >> simp[]
QED

(* Match the compiler-only freshness of the saved operand to the later
   unwrap cut. The runtime coverage of src does not imply freshness. *)
Theorem extcall_tuple_slot_source_fresh[local]:
  compile_expr ce et e si = (vv,sm) /\ local_ptrs_reserved ce si /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
  ss.cs_next_var <= ca.cs_next_var /\
  emit_op ADD [Var root; Lit (n2w off)] ca = (dst,su) /\
  unwrap_value ce saved su = (src,cw) ==>
  !x. src = Var x ==> not_fresh_at cw x
Proof
  strip_tac >>
  `ca.cs_next_var <= su.cs_next_var` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `!x. vv_operand saved = Var x ==> not_fresh_at ss x` by
    (gen_tac >> disch_tac >>
     irule bodyFullExtCallSavedOperandTheory.extcall_saved_operand_not_fresh >>
     goal_assum (drule_at (Pat `compile_snapshot_vv _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[]) >>
  `!x. vv_operand saved = Var x ==> not_fresh_at su x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `ss` >> simp[] >> decide_tac) >>
  gen_tac >> disch_tac >>
  irule exprOperandVarTheory.compiler_unwrap_value_var >>
  goal_assum (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  Cases_on `saved` >> fs[contextTheory.vv_operand_def]
QED

Theorem extcall_tuple_slot_write_input[local]:
  lookup_var dst s = SOME b /\ allocas_from lo s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2**64 /\ value_has_type tv v /\
  expr_val_rel cx ty v src s /\ ptr_val_ok cx ty v src G tn s /\
  (~is_word_type ty ==> ptr_buf_ok ce e src G s) /\
  (~is_word_type ty ==> !a. eval_operand src s = SOME a ==>
     type_memory_size tv = 0 \/ w2n a + type_memory_size tv <= s.vs_alloca_next) /\
  ptr_covers G tn dst s (type_memory_size tv) /\
  w2n b + type_memory_size tv <= s.vs_alloca_next /\ lo <= s.vs_alloca_next /\
  not_fresh_at cw dst /\ (!x. src = Var x ==> not_fresh_at cw x) ==>
  (if is_word_type ty then
     eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {} /\
     ptr_covers G tn dst s 32 /\ w2n b + 32 <= s.vs_alloca_next
   else
     val_wf tv v /\ type_memory_size tv < dimword (:256) /\
     (?a. eval_operand src s = SOME a /\
       (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
            val_in_memory tv v (w2n a) m) /\
       (if type_memory_size tv = 0 then
          op_taint tn src = {} /\ op_taint tn (Var dst) = {}
        else
          (?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
          ptr_covers G tn dst s (type_memory_size tv) /\
          w2n a + type_memory_size tv <= s.vs_alloca_next /\
          w2n b + type_memory_size tv <= s.vs_alloca_next) /\
       (is_bytestring_type ty ==>
          type_memory_size tv + 64 < dimword (:256) /\
          type_memory_size tv <> 0 /\ lo <= s.vs_alloca_next /\
          not_fresh_at cw dst /\ (!x. src = Var x ==> not_fresh_at cw x))))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `op_taint tn src = {}` by fs[ptr_val_ok_def] >>
  Cases_on `is_word_type ty`
  >- (`type_memory_size tv = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
      fs[expr_val_rel_def] >> metis_tac[]) >>
  `type_memory_size tv + 64 < dimword (:256)` by
    (irule vyperArithTheory.lt_dimword_256 >> qexists_tac `65` >> fs[] >> decide_tac) >>
  `type_memory_size tv < dimword (:256)` by decide_tac >>
  `val_wf tv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `(is_bytestring_type ty ==> type_memory_size tv <> 0)` by
    (strip_tac >> drule_all valueCopyBytesTheory.bytestring_type_value >>
     strip_tac >> simp[valueEncodingTheory.type_memory_size_def]) >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  simp[] >>
  conj_tac >- fs[ptr_val_ok_def, ptr_mem_ok_def] >>
  Cases_on `type_memory_size tv = 0` >- fs[ptr_covers_def] >>
  `ptr_buf_ok ce e src G s` by simp[] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `ptr_buf_ok ce e src G s`
        (qspec_then `w` mp_tac o REWRITE_RULE [ptr_buf_ok_def]) >>
      simp[] >> strip_tac >>
      qexists_tac `x` >> gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  `w2n w + type_memory_size tv <= s.vs_alloca_next` by metis_tac[] >>
  simp[arithmeticTheory.ADD_COMM]
QED

(* Execute the head ADD, unwrap and write at the same physical endpoints.
   Retain the two frames separately for transport across the write window. *)
Theorem extcall_tuple_slot_run[local]:
  emit_op ADD [Var root; Lit (n2w off)] ca = (dst,su) /\
  unwrap_value ce saved su = (src,cw) /\
  fn_has_code ca su fn /\ fn_has_code su cw fn /\ fn_inst_ids_distinct fn /\
  not_fresh_at ca root /\ lookup_var root s = SOME bw /\
  ptr_covers G tn root s capacity /\ off + type_memory_size tv <= capacity /\
  w2n bw + off < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n bw,capacity) /\
  alloca_history fn s /\ ~s.vs_halted /\
  s.vs_current_bb = ca.cs_current_bb /\ s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  ty = lowered_value_type ce e /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
  ((?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
        ty = expr_type e /\ saved = vv)) /\
  (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
  sm.cs_next_var <= ca.cs_next_var /\ sm.cs_next_id <= ca.cs_next_id /\
  ss.cs_next_var <= ca.cs_next_var /\ local_ptrs_reserved ce si /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2**64 /\ value_has_type tv v /\
  storage_trace_domain cx st0 ee.storage_trace /\
  read_result cx raw ee = (INL v,ee) /\ vv_holds ce cx ty raw saved ee s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\ vv_store_bound cx ty ty ee raw saved s /\
  ((case saved of StackValue tag op0 => ~is_word_type ty
    | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) G s) /\
  (ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
    !w. eval_operand (vv_operand saved) s = SOME w ==>
      w2n w + type_memory_size tv <= lo /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv v (w2n w) mem)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx saved ee s /\ ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  (if is_word_type ty then emit_void MSTORE [dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src dst
   else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes ce ty))]) cw = ((),cb) /\
  fn_has_code cw cb fn ==>
  ?z G2 tn2 q Gf tf.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gf,tf) /\
      stmt_state_rel H ctx fn ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee G2 tn2 z) /\
    (!m. mem_agree_outside tf.t_mem q.vs_memory m ==>
         val_in_memory tv v (w2n bw + off) m) /\
    wb_frame ce ee ee ca s z /\ ghost_kept_at lo ce ee ca G tn s G2 tn2 /\
    alloca_history fn z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    (!x. not_fresh_at ca x ==>
       lookup_var x z = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
       op_taint tn2 (Var x) = op_taint tn (Var x)) /\
    typed_copy_state_frame cw (w2n bw + off) (type_memory_size tv) z q /\
    (!x. not_fresh_at cw x ==> FLOOKUP Gf x = FLOOKUP G2 x /\
      op_taint tf (Var x) = op_taint tn2 (Var x)) /\
    (!i. i < w2n bw + off \/ w2n bw + off + type_memory_size tv <= i ==>
         (i IN tf.t_mem <=> i IN tn2.t_mem)) /\
    tf.t_stor = tn2.t_stor /\ tf.t_trans = tn2.t_trans /\ tf.t_imm = tn2.t_imm /\
    z.vs_current_bb = cw.cs_current_bb /\ z.vs_inst_idx = LENGTH cw.cs_current_insts /\
    q.vs_current_bb = cb.cs_current_bb /\ q.vs_current_bb = z.vs_current_bb /\
    q.vs_inst_idx = LENGTH cb.cs_current_insts /\ ~q.vs_halted /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gf,tf))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`, vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `allocas_from lo s` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ s` mp_tac >>
     pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `stmt_state_rel H0 ctx fn ce cx ee s`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `venomMemDefs$alloca_inv s` by metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  `w2n bw + capacity <= s.vs_alloca_next` by
    (qpat_assum `venomMemDefs$alloca_inv s`
       (mp_tac o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def]) >>
     disch_then (fn th => drule (CONJUNCT2 th)) >> simp[]) >>
  drule_all (Q.INST [`n` |-> `type_memory_size tv`] extcall_saved_slot_prepare_all_dead) >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choose_then `p`
    (qx_choose_then `z` (qx_choose_then `G2` (qx_choose_then `tn2`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  suspend "write"
QED

Resume extcall_tuple_slot_run[write]:
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ z` mp_tac >>
     pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >> simp[]) >>
  `w2n (n2w (w2n bw + off) : bytes32) = w2n bw + off` by simp[wordsTheory.w2n_n2w] >>
  `w2n (n2w (w2n bw + off) : bytes32) + type_memory_size tv <= z.vs_alloca_next` by decide_tac >>
  `!x. src = Var x ==> not_fresh_at cw x` by
    (gen_tac >> disch_tac >> irule extcall_tuple_slot_source_fresh >>
     goal_assum (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `compile_snapshot_vv _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >> simp[]) >>
  `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv` by metis_tac[] >>
  drule_all extcall_tuple_slot_write_input >>
  disch_tac >>
  qpat_x_assum `dst = Var p` SUBST_ALL_TAC >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `stmt_state_rel H0 ctx fn ce cx ee z`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  drule_all extcall_tuple_slot_write >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choose_then `q`
    (qx_choose_then `Gf` (qx_choose_then `tf` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  qpat_x_assum `w2n (n2w (w2n bw + off) : bytes32) = w2n bw + off` SUBST_ALL_TAC >>
  `cw.cs_current_bb = cb.cs_current_bb` by metis_tac[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gf,tf)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` (qspec_then `D` assume_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (z,G2,tn2) _ _` (qspec_then `D` assume_tac) >>
     drule_all fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >> simp[]) >>
  qexistsl [`z`,`G2`,`tn2`,`q`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> disch_tac >>
  qpat_assum `!i. i < w2n bw + off \/ w2n bw + off + type_memory_size tv <= i ==> _`
    irule >> decide_tac
QED

Finalise extcall_tuple_slot_run[local]

(* The entire tuple row is local-disjoint even though the current write
   covers only a subwindow of that row. *)
Theorem extcall_tuple_slot_state[local]:
  stmt_state_rel H ctx fn ce cx ee z /\ local_ptrs_reserved ce ca /\
  ca.cs_next_var <= cw.cs_next_var /\
  (!x. not_fresh_at ca x ==> lookup_var x z = lookup_var x s) /\
  wb_frame ce ee ee ca s z /\
  FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
  MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [root]) (fn_insts fn) /\
  (!name p k. local_region ce ee.scopes s name p k ==>
    b+cap <= p \/ p+k <= b) /\
  typed_copy_state_frame cw (b+off) n z q /\ off+n <= cap ==>
  stmt_state_rel H ctx fn ce cx ee q
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!name p k. local_region ce ee.scopes z name p k ==>
     loweringStateRelDefs$regions_disjoint b cap p k` by
    (rpt strip_tac >>
     drule_all exprSimCopyTheory.copy_buffer_local_region_frame >> strip_tac >>
     `local_region ce ee.scopes s name p k` by metis_tac[] >>
     first_x_assum drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `FLOOKUP z.vs_allocas aid = SOME (b,cap)` by fs[wb_frame_def] >>
  gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
  `copy_static q = copy_static z` by
    gvs[exprSimStorageCopyTheory.copy_static_def, venom_state_component_equality] >>
  `!a len. a+len <= b \/ b+cap <= a ==>
     mem_bytes_at a len q.vs_memory = mem_bytes_at a len z.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!x. not_fresh_at ca x ==> not_fresh_at cw x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  irule bodyPtrMakeArrayCopyStateFrameTheory.literal_copy_window_stmt_state_rel >>
  qexistsl [`aid`,`b`,`cap`,`root`,`ca`,`cw`,`z`] >> simp[] >> metis_tac[]
QED

(* Keep the invariant across the write. The reflexive baseline records
   no old allocation rows: the tuple row itself is not an exterior window. *)
Theorem extcall_tuple_slot_ghost[local]:
  stmt_state_rel H ctx fn ce cx ee z /\
  ghost_inv_at D lo d ce cx ee Gz tz z /\
  typed_copy_state_frame cw (b+off) n z q /\
  (!x. not_fresh_at cw x ==> FLOOKUP Gq x = FLOOKUP Gz x /\
     op_taint tq (Var x) = op_taint tz (Var x)) /\
  tq.t_stor = tz.t_stor /\ tq.t_trans = tz.t_trans /\ tq.t_imm = tz.t_imm /\
  (!i. i < b+off \/ b+off+n <= i ==> (i IN tq.t_mem <=> i IN tz.t_mem)) /\
  local_ptrs_reserved ce cw /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cw x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cw x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at cw x) /\
  lo <= b /\ off+n <= cap /\
  (!name p k. local_region ce ee.scopes z name p k ==>
     b+cap <= p \/ p+k <= b) ==>
  ghost_inv_at D lo d ce cx ee Gq tq q
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_then strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >>
  `!name entry x k w. lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) k) /\ lookup_var x z = SOME w ==>
     val_wf entry.type entry.value /\
     (w2n w + val_footprint entry.type entry.value <= b+off \/ b+off+n <= w2n w)` by
    (rpt gen_tac >> strip_tac >>
     drule_all_then strip_assume_tac nameLoweringPropsTheory.local_ptrs_rel_value >>
     gvs[eval_operand_def] >>
     `local_region ce ee.scopes z name (w2n w) k` by
       (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
     qpat_assum `!name p k. local_region _ _ _ name p k ==> _` drule >>
     drule exprSimPropsTheory.val_footprint_le >> decide_tac) >>
  irule (cj 1 bodyFullStructLitFramesTheory.structlit_store_ghost_frame) >>
  qexistsl [`b+off`,`Gz`,`Gz`,`n`,`ee`,`cw`,`z`,`z`,`cw with cs_next_id := 0`,`tz`,`tz`] >>
  simp[wordArgsPtrTheory.ghost_kept_at_refl] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!name p k. local_region _ _ _ name p k ==> _` drule >>
      strip_tac >> decide_tac) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!name entry x k w. _ ==> val_wf _ _ /\ _` drule_all >>
      strip_tac >> simp[] >> decide_tac) >>
  rpt strip_tac >>
  qpat_assum `!i. _ ==> (i IN tq.t_mem <=> i IN tz.t_mem)` irule >> decide_tac
QED

(* The two head cuts preserve the old operands, the allocation table up
   to extension, and the state and ghost relations at the actual exit. *)
Theorem extcall_tuple_slot_finish[local]:
  stmt_state_rel H ctx fn ce cx ee z /\ ghost_inv_at D lo d ce cx ee Gz tz z /\
  wb_frame ce ee ee ca s z /\ s.vs_alloca_next <= z.vs_alloca_next /\
  (!x. not_fresh_at ca x ==>
     lookup_var x z = lookup_var x s /\ FLOOKUP Gz x = FLOOKUP G x /\
     op_taint tz (Var x) = op_taint tn (Var x)) /\
  typed_copy_state_frame cw (b+off) n z q /\
  (!x. not_fresh_at cw x ==> FLOOKUP Gq x = FLOOKUP Gz x /\
     op_taint tq (Var x) = op_taint tz (Var x)) /\
  tq.t_stor = tz.t_stor /\ tq.t_trans = tz.t_trans /\ tq.t_imm = tz.t_imm /\
  (!i. i < b+off \/ b+off+n <= i ==> (i IN tq.t_mem <=> i IN tz.t_mem)) /\
  local_ptrs_reserved ce ca /\ ca.cs_next_var <= cw.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at ca x) /\
  FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
  MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [root]) (fn_insts fn) /\
  (!name p k. local_region ce ee.scopes s name p k ==>
     b+cap <= p \/ p+k <= b) /\ off+n <= cap ==>
  stmt_state_rel H ctx fn ce cx ee q /\ ghost_inv_at D lo d ce cx ee Gq tq q /\
  s.vs_alloca_next <= q.vs_alloca_next /\
  (!a row. FLOOKUP s.vs_allocas a = SOME row ==> FLOOKUP q.vs_allocas a = SOME row) /\
  (!x. not_fresh_at ca x ==>
     lookup_var x q = lookup_var x s /\ FLOOKUP Gq x = FLOOKUP G x /\
     op_taint tq (Var x) = op_taint tn (Var x))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!x. not_fresh_at ca x ==> lookup_var x z = lookup_var x s` by metis_tac[] >>
  `!x. not_fresh_at ca x ==> not_fresh_at cw x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!name p k. local_region ce ee.scopes z name p k <=>
             local_region ce ee.scopes s name p k` by
    (drule_all exprSimCopyTheory.copy_buffer_local_region_frame >> simp[]) >>
  `FLOOKUP z.vs_allocas aid = SOME (b,cap)` by fs[wb_frame_def] >>
  `lo <= b` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ z`
       (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> strip_tac >>
     qpat_assum `allocas_from lo z` (drule_then ACCEPT_TAC o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def])) >>
  conj_tac >- (drule_all extcall_tuple_slot_state >> simp[]) >>
  conj_tac
  >- (irule extcall_tuple_slot_ghost >>
      goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
      simp[] >> qexistsl [`Gz`,`cap`,`tz`] >> simp[] >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!name p k. local_region _ _ _ name p k ==> _` drule >>
          decide_tac) >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!i. _ ==> (i IN tq.t_mem <=> i IN tz.t_mem)` irule >>
          decide_tac) >>
      metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]) >>
  gvs[typed_copy_state_frame_def, venom_state_component_equality] >>
  fs[wb_frame_def]
QED

(* Keep the tuple allocation above the saved-value cutoff.  The variable
   cutoff remains the current cursor; no old row below aid is overwritten. *)
Theorem extcall_tuple_slot_saved_frames[local]:
  wb_frame ce ee ee ca s z /\ ghost_kept_at lo ce ee ca G tn s Gz tz /\
  typed_copy_state_frame cw (b+off) n z q /\
  (!x. not_fresh_at cw x ==> FLOOKUP Gq x = FLOOKUP Gz x /\
     op_taint tq (Var x) = op_taint tz (Var x)) /\
  (!i. i < b+off \/ b+off+n <= i ==> (i IN tq.t_mem <=> i IN tz.t_mem)) /\
  ca.cs_next_var <= cw.cs_next_var /\
  aid < ca.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
  allocas_non_overlapping s /\ off+n <= cap /\
  (!name p k. local_region ce ee.scopes s name p k ==>
      b+cap <= p \/ p+k <= b) ==>
  wb_frame ce ee ee (ca with cs_next_id := aid) s q /\
  ghost_kept_at lo ce ee (ca with cs_next_id := aid) G tn s Gq tq
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!x. not_fresh_at ca x ==> not_fresh_at cw x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!id p k. FLOOKUP s.vs_allocas id = SOME (p,k) /\ id < aid ==>
     p+k <= b+off \/ b+off+n <= p` by
    (fs[venomMemDefsTheory.allocas_non_overlapping_def] >>
     rpt strip_tac >> `id <> aid` by decide_tac >>
     `p+k <= b \/ b+cap <= p` by metis_tac[] >> decide_tac) >>
  `!p k. p+k <= b+off \/ b+off+n <= p ==>
     mem_bytes_at p k q.vs_memory = mem_bytes_at p k z.vs_memory` by
    (fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `locals_kept ce ee ee s q` by
    (irule exprSimCopyTheory.copy_buffer_locals_kept_frame >>
     qexistsl [`b+off`,`z`,`n`] >> simp[] >>
     rpt conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!name p k. local_region _ _ _ name p k ==> _` drule >> decide_tac)
     >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     fs[wb_frame_def]) >>
  `!x. not_fresh_at (ca with cs_next_id := aid) x <=> not_fresh_at ca x` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
  `q.vs_allocas = z.vs_allocas /\
   !x. not_fresh_at cw x ==> lookup_var x q = lookup_var x z` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  qpat_x_assum `typed_copy_state_frame _ _ _ _ _` kall_tac >>
  `!i. (i < b+off \/ b+off+n <= i) /\ i IN tq.t_mem ==> i IN tz.t_mem` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!j. _ ==> (j IN tq.t_mem <=> _)` (qspec_then `i` mp_tac) >>
     fs[]) >>
  fs[wb_frame_def, ghost_kept_at_def] >>
  rpt conj_tac >> rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  >- (rename1 `mem_bytes_at p k q.vs_memory = _` >>
      rename1 `FLOOKUP s.vs_allocas id = SOME (p,k)` >>
      `id < ca.cs_next_id` by decide_tac >>
      qpat_assum `!a u v. _ ==> mem_bytes_at u v z.vs_memory = _`
        (qspecl_then [`id`,`p`,`k`] mp_tac) >>
      impl_tac >-
        (simp[] >> rpt gen_tac >> disch_tac >>
         qpat_assum `!nm u v. local_region _ _ _ nm u v ==> p+k <= u \/ u+v <= p`
           drule >> decide_tac) >>
      disch_then (SUBST1_TAC o SYM) >>
      qpat_assum `!u v. _ ==> mem_bytes_at u v q.vs_memory = _` irule >>
      qpat_assum `!a u v. _ /\ a < aid ==> _`
        (qspecl_then [`id`,`p`,`k`] mp_tac) >> simp[])
  >- (rename1 `FLOOKUP s.vs_allocas id = SOME (p,k)` >>
      rename1 `i IN tn.t_mem` >>
      `id < ca.cs_next_id` by decide_tac >>
      `i IN tz.t_mem` by
        (qpat_assum `!j. _ /\ j IN tq.t_mem ==> j IN tz.t_mem` irule >>
         qpat_assum `!a u v. _ /\ a < aid ==> _`
           (qspecl_then [`id`,`p`,`k`] mp_tac) >> simp[] >> decide_tac) >>
      qpat_assum `!a u v j. FLOOKUP _ a = SOME (u,v) /\ _ ==> j IN tn.t_mem`
        (qspecl_then [`id`,`p`,`k`,`i`] mp_tac) >> simp[] >>
      impl_tac >-
        (rpt gen_tac >> disch_tac >>
         qpat_assum `!nm u v. local_region _ _ _ nm u v ==> p+k <= u \/ u+v <= p`
           drule >> decide_tac) >> simp[]) >>
  rename1 `local_region ce ee.scopes s name p k` >>
  rename1 `i IN tn.t_mem` >>
  `i IN tz.t_mem` by
    (qpat_assum `!j. _ /\ j IN tq.t_mem ==> j IN tz.t_mem` irule >>
     qpat_assum `!name p k. local_region _ _ _ name p k ==> _` drule >>
     simp[] >> decide_tac) >>
  qpat_assum `!nm u v j. local_region _ _ _ nm u v /\ _ ==> j IN tn.t_mem`
    (qspecl_then [`name`,`p`,`k`,`i`] mp_tac) >> simp[]
QED

(* A saved value's footprint sits in an old disjoint row, a local region,
   or the empty window. The narrowed write-back frame covers all three. *)
Theorem extcall_tuple_saved_footprint[local]:
  expr_val_at ce cx ty origin cut ee v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\ wb_frame ce ee ee cut s q ==>
  mem_bytes_at (w2n w) (val_footprint tv v) q.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (qspec_then `tv` mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  simp[] >> strip_tac >> gvs[]
  >- (`mem_bytes_at b sz q.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
         pure_rewrite_tac[wb_frame_def] >> strip_tac >>
         qpat_assum `!a p k. _ ==> mem_bytes_at p k _ = _`
           (qspecl_then [`aid`,`b`,`sz`] mp_tac) >> simp[] >> metis_tac[]) >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >> simp[] >> metis_tac[])
  >- (`mem_bytes_at b sz q.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
         pure_rewrite_tac[wb_frame_def, locals_kept_def] >> strip_tac >>
         (metis_tac[])) >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >> simp[] >> metis_tac[]) >>
  simp[valueEncodingDefsTheory.mem_bytes_at_def]
QED

Theorem extcall_tuple_saved_footprint_frame[local]:
  expr_val_at ce cx ty origin cut ee v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\ wb_frame ce ee ee cut s q /\
  ghost_kept_at lo ce ee cut G tn s Gq tq ==>
  val_wf tv v /\
  mem_bytes_at (w2n w) (val_footprint tv v) q.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tq.t_mem ==>
       i IN tn.t_mem)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  conj_tac >- fs[expr_val_at_def] >>
  conj_tac >- (drule_all extcall_tuple_saved_footprint >> simp[]) >>
  rpt strip_tac >> drule_all bodyFullLogArgsTheory.pure_argument_taint_kept >> simp[]
QED

Theorem extcall_tuple_saved_mem_ptr[local]:
  ~is_word_type ty /\ p.ptr_location = LocMemory /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  vv_at ce cx ty origin cut ee raw (LocatedValue tag p) s /\
  ptr_vv_ok cx ty raw (LocatedValue tag p) ee G tn s /\
  eval_operand p.ptr_operand q = eval_operand p.ptr_operand s /\
  (!x. p.ptr_operand = Var x ==> FLOOKUP Gq x = FLOOKUP G x) /\
  op_taint tq p.ptr_operand = op_taint tn p.ptr_operand /\
  wb_frame ce ee ee cut s q /\ ghost_kept_at lo ce ee cut G tn s Gq tq ==>
  ptr_vv_ok cx ty raw (LocatedValue tag p) ee Gq tq q
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all_then assume_tac exprSimPropsTheory.vv_at_memory_val_at >>
  gvs[ptr_vv_ok_def] >>
  irule bodyPtrBopRepresentationFrameTheory.bop_ptr_mem_ok_frame >>
  goal_assum (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >> simp[] >>
  reverse conj_tac >- (fs[expr_val_at_def] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >> drule_all extcall_tuple_saved_footprint_frame >> simp[]
QED

(* The write-back frame preserves successful lookups, which is enough
   for equality on a saved operand known to denote a value. *)
Theorem extcall_tuple_saved_operand_frame[local]:
  wb_frame ce ee ee cut s q /\ ghost_kept_at lo ce ee cut G tn s Gq tq /\
  (!x. op = Var x ==> not_fresh_at cut x) /\
  (?w. eval_operand op s = SOME w) /\
  ((!l. op <> Label l) \/ q.vs_labels = s.vs_labels) ==>
  eval_operand op q = eval_operand op s /\
  op_taint tq op = op_taint tn op /\ op_prov Gq op = op_prov G op /\
  (!x. op = Var x ==> FLOOKUP Gq x = FLOOKUP G x)
Proof
  Cases_on `op` >>
  gvs[wb_frame_def, ghost_kept_at_def, eval_operand_def,
      ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >>
  metis_tac[]
QED

Theorem extcall_tuple_saved_stack_ptr[local]:
  read_result cx raw ee = (INL v,ee) /\
  vv_at ce cx ty origin cut ee raw (StackValue tag op) s /\
  ptr_vv_ok cx ty raw (StackValue tag op) ee G tn s /\
  eval_operand op q = eval_operand op s /\
  (!x. op = Var x ==> FLOOKUP Gq x = FLOOKUP G x) /\
  op_taint tq op = op_taint tn op /\
  wb_frame ce ee ee cut s q /\ ghost_kept_at lo ce ee cut G tn s Gq tq ==>
  ptr_vv_ok cx ty raw (StackValue tag op) ee Gq tq q
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  gvs[ptr_vv_ok_def, vv_at_def] >>
  irule logValueFramePtrTheory.ptr_val_ok_footprint_frame >>
  goal_assum (drule_at (Pat `ptr_val_ok _ _ _ _ _ _ _`)) >> simp[] >>
  rpt gen_tac >> disch_tac >> (metis_tac[extcall_tuple_saved_footprint_frame])
QED

(* The old value's region bounds and the frame's byte cutoff are separate:
   the allocation map keeps all existing rows, not only protected ones. *)
Theorem extcall_tuple_saved_region[local]:
  vv_at ce cx ty origin end_st ee raw saved s /\
  eval_operand (vv_operand saved) q = eval_operand (vv_operand saved) s /\
  wb_frame ce ee ee cut s q /\ local_ptrs_reserved ce cut /\
  local_ptrs_rel fn ce ee.scopes s /\ end_st.cs_next_id <= end_st'.cs_next_id ==>
  vv_at ce cx ty origin end_st' ee raw saved q
Proof
  strip_tac >>
  irule bodyPtrIfExpAllocSourceTheory.vv_at_alloc_map_frame >>
  goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >> simp[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[exprSimSubscriptArrayFrameTheory.local_region_wb_frame]) >>
  fs[wb_frame_def]
QED

(* For footprint transport we can lower the protected row cutoff further
   to the saved value's own end ID, without lowering the variable cutoff. *)
Theorem extcall_tuple_saved_cut[local]:
  wb_frame ce ee ee cut s q /\ ghost_kept_at lo ce ee cut G tn s Gq tq /\
  end_st.cs_next_id <= cut.cs_next_id /\ end_st.cs_next_var <= cut.cs_next_var ==>
  wb_frame ce ee ee end_st s q /\ ghost_kept_at lo ce ee end_st G tn s Gq tq
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!x. not_fresh_at end_st x ==> not_fresh_at cut x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!aid. aid < end_st.cs_next_id ==> aid < cut.cs_next_id` by decide_tac >>
  fs[wb_frame_def, ghost_kept_at_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem extcall_tuple_slot_storage_rels[local]:
  stmt_state_rel H ctx fn ce cx ee q ==>
  storage_rel H cx.txn.target ee q /\ transient_rel H cx.txn.target ee q
Proof
  strip_tac >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ _`
    (mp_then Any (qspec_then `F` assume_tac) stmtSimAssignStorageCopyTheory.storage_copy_initial_agree) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ _`
    (mp_then Any (qspec_then `T` assume_tac) stmtSimAssignStorageCopyTheory.storage_copy_initial_agree) >>
  fs[loweringStateRelDefsTheory.storage_rel_def, loweringStateRelDefsTheory.transient_rel_def,
     vyperStorageBackendTheory.get_storage_def, vfmStateTheory.lookup_account_def]
QED

(* The new ghost classifies taint using the new storage backend. Liveness
   and slot agreement put that classification inside the saved type. *)
Theorem extcall_tuple_saved_storage_ptr[local]:
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  vv_holds ce cx ty raw (LocatedValue ty p) ee q /\
  vv_storage_live H cx (LocatedValue ty p) ee q /\
  stmt_state_rel H ctx fn ce cx ee q /\ ghost_inv_at D lo d ce cx ee Gq tq q /\
  dead_lo_ok H D lo ce cx /\ op_taint tq p.ptr_operand = {} ==>
  ptr_vv_ok cx ty raw (LocatedValue ty p) ee Gq tq q
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!k b. (k,b) IN (if tr then tq.t_trans else tq.t_stor) ==>
    storage_dead H tr (if tr then contract_transient q else contract_storage q) (w2n k) b` by
    (Cases_on `tr` >>
     gvs[ghost_inv_at_def, stor_taint_ok_at_def, dead_lo_ok_def, sourceUnitExecutionTheory.cx_dead_def,
         pred_setTheory.SUBSET_DEF, contract_storage_def, contract_transient_def,
         vfmStateTheory.lookup_account_def] >>
     rpt strip_tac >> first_x_assum drule >>
     Cases_on `q.vs_call_ctx.cc_address = cx.txn.target` >> simp[]) >>
  drule_then (qspec_then `tr` assume_tac) stmtSimAssignStorageCopyTheory.storage_copy_initial_agree >>
  `!w tv k b. eval_operand p.ptr_operand q = SOME w /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    w2n w <= w2n k /\ w2n k < w2n w + type_slot_size tv /\
    (k,b) IN (if tr then tq.t_trans else tq.t_stor) ==>
    dead_bytes (if tr then contract_transient q else contract_storage q) (w2n w) tv (w2n k) b` by
    (rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
     `storage_range_agree (get_storage cx ee tr)
       (if tr then contract_transient q else contract_storage q) w tv /\
      storage_read_live H tr (get_storage cx ee tr) w tv` by
       (Cases_on `tr` >> gvs[vv_holds_def, storage_holds_def] >> metis_tac[]) >>
     drule accountsRelPropsTheory.storage_agree_storage_dead >> strip_tac >>
     drule exprPtrUnwrapStorageFactsTheory.storage_range_agree_dead_bytes >> strip_tac >>
     gvs[loweringStateRelDefsTheory.storage_read_live_def] >> metis_tac[]) >>
  Cases_on `tr` >> gvs[ptr_vv_ok_def, contract_storage_def, contract_transient_def,
                       vfmStateTheory.lookup_account_def] >> metis_tac[]
QED

Theorem extcall_tuple_saved_entry:
  vv_holds ce cx ty raw saved ee s /\ vv_at ce cx ty origin end_st ee raw saved s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\
  vv_store_bound cx ty ty ee raw saved s /\
  read_result cx raw ee = (INL v,ee) /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  (vv_location saved = SOME LocMemory ==> ~is_word_type ty) /\
  ((case saved of StackValue tag op0 => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==>
       ptr_buf_ok ce e (vv_operand saved) G s) /\
  (!x. vv_operand saved = Var x ==> not_fresh_at cut x) /\
  (!l. vv_operand saved <> Label l) /\
  wb_frame ce ee ee cut s q /\ ghost_kept_at lo ce ee cut G tn s Gq tq /\
  end_st.cs_next_var <= cut.cs_next_var /\ end_st.cs_next_id <= cut.cs_next_id /\
  local_ptrs_reserved ce cut /\ local_ptrs_rel fn ce ee.scopes s /\
  s.vs_alloca_next <= q.vs_alloca_next /\
  vv_storage_live H cx saved ee s /\ stmt_state_rel H ctx fn ce cx ee q /\
  ghost_inv_at D lo d ce cx ee Gq tq q /\ dead_lo_ok H D lo ce cx /\
  (!tag p. saved = LocatedValue tag p ==> tag = ty) ==>
  vv_holds ce cx ty raw saved ee q /\ vv_at ce cx ty origin end_st ee raw saved q /\
  ptr_vv_ok cx ty raw saved ee Gq tq q /\
  vv_store_bound cx ty ty ee raw saved q /\
  ((case saved of StackValue tag op0 => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==>
       ptr_buf_ok ce e (vv_operand saved) Gq q)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?w. eval_operand (vv_operand saved) s = SOME w` by metis_tac[target_saved_operand_exists] >>
  `eval_operand (vv_operand saved) q = eval_operand (vv_operand saved) s /\
   op_taint tq (vv_operand saved) = op_taint tn (vv_operand saved) /\
   op_prov Gq (vv_operand saved) = op_prov G (vv_operand saved) /\
   (!x. vv_operand saved = Var x ==> FLOOKUP Gq x = FLOOKUP G x)` by
    (irule extcall_tuple_saved_operand_frame >> metis_tac[]) >>
  `wb_frame ce ee ee end_st s q /\ ghost_kept_at lo ce ee end_st G tn s Gq tq` by
    (irule extcall_tuple_saved_cut >> qexists `cut` >> simp[]) >>
  `vv_holds ce cx ty raw saved ee q` by
    (irule target_saved_holds_frame >>
     goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `vv_storage_live _ _ _ _ _`)) >> simp[] >>
     drule extcall_tuple_slot_storage_rels >> simp[]) >>
  `vv_at ce cx ty origin end_st ee raw saved q` by
    (irule extcall_tuple_saved_region >>
     goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >> simp[] >> metis_tac[]) >>
  `vv_storage_live H cx saved ee q` by
    metis_tac[target_saved_storage_live_frame] >>
  simp[] >> reverse conj_tac
  >- (conj_tac
      >- (irule exprSimMemDefsTheory.vv_store_bound_frame_mem_src >> metis_tac[]) >>
      disch_tac >> irule logValueFramePtrTheory.ptr_buf_ok_frame >>
      qexistsl [`G`,`s`] >> simp[]) >>
  Cases_on `saved` >> fs[vv_operand_def, vv_location_def]
  >- (drule_all extcall_tuple_saved_stack_ptr >> simp[]) >>
  Cases_on `p.ptr_location` >> gvs[]
  >- metis_tac[extcall_tuple_saved_mem_ptr]
  >- (irule (Q.INST [`tr` |-> `F`] extcall_tuple_saved_storage_ptr) >>
      fs[ptr_vv_ok_def, vv_storage_live_def] >>
      qexistsl [`D`,`H`,`ce`,`ctx`,`d`,`fn`,`lo`] >> simp[ptr_vv_ok_def])
  >- (irule (Q.INST [`tr` |-> `T`] extcall_tuple_saved_storage_ptr) >>
      fs[ptr_vv_ok_def, vv_storage_live_def] >>
      qexistsl [`D`,`H`,`ce`,`ctx`,`d`,`fn`,`lo`] >> simp[ptr_vv_ok_def]) >>
  gvs[ptr_vv_ok_def]
QED

(* A slot write advances across straight code with no allocation. *)
Theorem extcall_tuple_slot_history[local]:
  (if is_word_type ty then emit_void MSTORE [dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src dst
   else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes ce ty))]) cw = ((),cb) /\
  fn_has_code cw cb fn /\ alloca_history fn z /\
  typed_copy_state_frame cw pos n z q /\
  z.vs_current_bb = cw.cs_current_bb /\ q.vs_current_bb = cb.cs_current_bb /\
  q.vs_current_bb = z.vs_current_bb /\
  z.vs_inst_idx = LENGTH cw.cs_current_insts /\ q.vs_inst_idx = LENGTH cb.cs_current_insts ==>
  alloca_history fn q
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `cb.cs_current_insts = cw.cs_current_insts ++ emitted_insts cw cb /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts cw cb)` by
    (Cases_on `is_word_type ty` >> fs[]
     >- (drule emitHelperPropsTheory.emitted_insts_emit_void >> simp[venomInstTheory.mk_inst_def]) >>
     Cases_on `is_bytestring_type ty` >> fs[]
     >- (drule exprSimBufferStoreTheory.buffer_store_bytestring_shape >> strip_tac >>
         drule logBytesCodePtrTheory.compile_store_bytestring_opcodes >>
         simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
         qpat_assum `!i. MEM i _ ==> _` drule >> simp[]) >>
     drule emitHelperPropsTheory.emitted_insts_emit_void >> simp[venomInstTheory.mk_inst_def]) >>
  `cb.cs_current_bb = cw.cs_current_bb` by metis_tac[] >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >>
  simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  `q.vs_allocas = z.vs_allocas` by fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `q.vs_inst_idx = z.vs_inst_idx + LENGTH (emitted_insts cw cb)` by
    gvs[listTheory.LENGTH_APPEND] >>
  `lookup_block z.vs_current_bb fn.fn_blocks = SOME bb /\
   DROP z.vs_inst_idx bb.bb_instructions = emitted_insts cw cb ++ l` by simp[] >>
  drule_all bodyBinopFragMemoryTheory.alloca_history_no_alloca_slice >>
  qpat_assum `q.vs_inst_idx = z.vs_inst_idx + _`
    (fn th => pure_rewrite_tac [GSYM th]) >> simp[]
QED

(* Expose the intermediate PCs, including the cut for the recursive tail. *)
Theorem extcall_tuple_cons_cuts[local]:
  compile_extcall_store_values ce ((saved,ty)::rest) (Var root) off ca = ((),cb) /\
  fn_has_code ca cb fn ==>
  ?dst su src cw cm.
    emit_op ADD [Var root; Lit (n2w off)] ca = (dst,su) /\
    unwrap_value ce saved su = (src,cw) /\
    (if is_word_type ty then emit_void MSTORE [dst;src]
     else if is_bytestring_type ty then compile_store_bytestring src dst
     else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes ce ty))]) cw = ((),cm) /\
    compile_extcall_store_values ce rest (Var root) (off + type_memory_bytes ce ty) cm = ((),cb) /\
    fn_has_code ca su fn /\ fn_has_code su cw fn /\ fn_has_code cw cm fn /\
    fn_has_code cm cb fn /\ ca.cs_next_var <= cw.cs_next_var /\
    ca.cs_next_var <= cm.cs_next_var /\ ca.cs_next_id <= cm.cs_next_id
Proof
  simp[Once compile_extcall_store_values_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `emit_op ADD [Var root; Lit (n2w off)] ca = (dst,su)` >>
  rename1 `unwrap_value ce saved su = (src,cw)` >>
  rename1 `(if _ then _ else _) cw = (r,cm)` >> Cases_on `r` >>
  `ci_mono ca su /\ ci_mono su cw /\ ci_mono cw cm` by
    (conj_tac >- metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND] >>
     conj_tac >- metis_tac[exprLoweringPropsTheory.ci_mono_unwrap_value, pairTheory.SND] >>
     Cases_on `is_word_type ty` >> gvs[]
     >- metis_tac[exprLoweringPropsTheory.ci_mono_emit_void, pairTheory.SND] >>
     Cases_on `is_bytestring_type ty` >> gvs[] >>
     metis_tac[exprLoweringPropsTheory.ci_mono_emit_void,
       exprLoweringPropsTheory.ci_mono_compile_store_bytestring, pairTheory.SND]) >>
  `cs_extends cm cb` by
    metis_tac[externalEntryShapeTheory.compile_extcall_store_values_labels, pairTheory.SND] >>
  fs[exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code ca cm fn /\ fn_has_code cm cb fn` by
    (irule fragExecTheory.fn_has_code_split >> simp[] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code ca cw fn /\ fn_has_code cw cm fn` by
    (irule fragExecTheory.fn_has_code_split >> simp[] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code ca su fn /\ fn_has_code su cw fn` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  simp[] >> fs[cs_extends_def]
QED

(* The continuation starts at the end of the write, not at the unwrap
   cut. Retain the prefix separately from the fixed-cut saved-value frame. *)
Theorem extcall_tuple_head_middle_post[local]:
  valid_horizon cx st0 H0 ee.storage_trace /\
  stmt_state_rel H0 ctx fn ce cx ee s /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK m,Gm,tm) /\
     stmt_state_rel H ctx fn ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at (DF H) lo d ce cx ee Gz tz z) /\
  wb_frame ce ee ee ca s z /\ ghost_kept_at lo ce ee ca G tn s Gz tz /\
  s.vs_alloca_next <= z.vs_alloca_next /\
  (!x. not_fresh_at ca x ==> lookup_var x z = lookup_var x s /\
     FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) /\
  typed_copy_state_frame cw (w2n bw+off) n z m /\
  (!x. not_fresh_at cw x ==> FLOOKUP Gm x = FLOOKUP Gz x /\
     op_taint tm (Var x) = op_taint tz (Var x)) /\
  (!i. i < w2n bw+off \/ w2n bw+off+n <= i ==> (i IN tm.t_mem <=> i IN tz.t_mem)) /\
  tm.t_stor = tz.t_stor /\ tm.t_trans = tz.t_trans /\ tm.t_imm = tz.t_imm /\
  local_ptrs_reserved ce ca /\ ca.cs_next_var <= cw.cs_next_var /\ ca.cs_next_var <= cm.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at ca x) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n bw,cap) /\ aid < ca.cs_next_id /\
  MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [root]) (fn_insts fn) /\
  (!name p k. local_region ce ee.scopes s name p k ==> w2n bw+cap <= p \/ p+k <= w2n bw) /\
  off+n <= cap /\ not_fresh_at ca root /\ lookup_var root s = SOME bw /\
  ptr_covers G tn root s cap /\ return_buf_frame d ce ca s ==>
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK m,Gm,tm) /\
     stmt_state_rel H ctx fn ce cx ee m /\ storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at (DF H) lo d ce cx ee Gm tm m) /\
  s.vs_alloca_next <= m.vs_alloca_next /\ lookup_var root m = SOME bw /\
  ptr_covers Gm tm root m cap /\ FLOOKUP m.vs_allocas aid = SOME (w2n bw,cap) /\
  (!a row. FLOOKUP s.vs_allocas a = SOME row ==> FLOOKUP m.vs_allocas a = SOME row) /\
  (!name p k. local_region ce ee.scopes m name p k <=> local_region ce ee.scopes s name p k) /\
  return_buf_frame d ce cm m /\
  wb_frame ce ee ee (ca with cs_next_id := aid) s m /\
  ghost_kept_at lo ce ee (ca with cs_next_id := aid) G tn s Gm tm /\
  mem_bytes_at (w2n bw) off m.vs_memory = mem_bytes_at (w2n bw) off s.vs_memory /\
  (!i. w2n bw <= i /\ i < w2n bw+off /\ i IN tm.t_mem ==> i IN tn.t_mem)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK m,Gm,tm) /\
     stmt_state_rel H ctx fn ce cx ee m /\ storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at (DF H) lo d ce cx ee Gm tm m /\
     s.vs_alloca_next <= m.vs_alloca_next /\
     (!a row. FLOOKUP s.vs_allocas a = SOME row ==> FLOOKUP m.vs_allocas a = SOME row) /\
     (!x. not_fresh_at ca x ==> lookup_var x m = lookup_var x s /\
        FLOOKUP Gm x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- simp[] >>
     disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
     drule_all extcall_tuple_slot_finish >> simp[]) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ stmt_state_rel _ _ _ _ _ _ m /\ _`
    (qspec_then `H0` mp_tac) >> simp[] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_then strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >>
  `allocas_non_overlapping s` by fs[venomMemDefsTheory.alloca_inv_def] >>
  `!x. not_fresh_at ca x ==> lookup_var x m = lookup_var x s` by simp[] >>
  `ptr_covers Gm tm root m cap` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl [`G`,`s`,`tn`] >> simp[]) >>
  `!name p k. local_region ce ee.scopes m name p k <=> local_region ce ee.scopes s name p k` by
    (drule_all exprSimCopyTheory.copy_buffer_local_region_frame >> simp[]) >>
  `return_buf_frame d ce cm m` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl [`ce`,`s`,`ca`] >> simp[]) >>
  drule_all_then strip_assume_tac extcall_tuple_slot_saved_frames >>
  `FLOOKUP m.vs_allocas aid = SOME (w2n bw,cap) /\
   mem_bytes_at (w2n bw) off m.vs_memory = mem_bytes_at (w2n bw) off s.vs_memory /\
   (!i. w2n bw <= i /\ i < w2n bw + off /\ i IN tm.t_mem ==> i IN tn.t_mem)` by
    (irule (REWRITE_RULE [arithmeticTheory.ADD_CLAUSES]
       (Q.INST [`off` |-> `0`]
          (INST_TYPE [alpha |-> ``:num # num``] extcall_tuple_slot_keeps_window))) >>
     simp[] >> goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `wb_frame _ _ _ _ _ _`)) >>
     qexistsl [`G`,`Gz`,`lo`,`tz`] >>
     asm_rewrite_tac[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.LESS_EQ_REFL] >>
     conj_tac
     >- (rpt gen_tac >> disch_tac >>
         qpat_assum `!name p k. local_region _ _ _ name p k ==> _` drule >> decide_tac) >>
     decide_tac) >>
  simp[]
QED

(* The recursive suffix preserves every byte the head representation
   can observe, and introduces no taint there. *)
Theorem extcall_tuple_robust_cons[local]:
  value_has_type tv v /\
  mem_bytes_at b (off + type_memory_size tv) new =
    mem_bytes_at b (off + type_memory_size tv) old /\
  (!i. b <= i /\ i < b + (off + type_memory_size tv) /\ i IN dirty' ==> i IN dirty) /\
  (!mem. mem_agree_outside dirty old mem ==> val_in_memory tv v (b + off) mem) /\
  (!mem. mem_agree_outside dirty' new mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (b + (off + type_memory_size tv)) mem) ==>
  !mem. mem_agree_outside dirty' new mem ==>
    val_in_memory (TupleTV (tv::tvs)) (ArrayV (TupleV (v::vs))) (b + off) mem
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `val_wf tv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `val_footprint tv v <= type_memory_size tv` by simp[exprSimPropsTheory.val_footprint_le] >>
  `!mem. mem_agree_outside dirty' new mem ==> val_in_memory tv v (b + off) mem` by
    (gen_tac >> disch_tac >>
     irule logValueFramePtrTheory.robust_val_in_memory_footprint_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`old`,`new`,`dirty`,`dirty'`] >> simp[] >>
     drule valueEncodingProofsTheory.mem_bytes_at_agree_window >> strip_tac >>
     sym_tac >> first_x_assum irule >> decide_tac) >>
  gen_tac >> disch_tac >>
  pure_rewrite_tac [val_in_memory_tuple,
    List.last (CONJUNCTS valueEncodingDefsTheory.val_in_memory_def),
    boolTheory.LET_THM, pairTheory.pair_case_thm, listTheory.list_case_def,
    arithmeticTheory.ADD_ASSOC] >>
  gvs[val_in_memory_tuple]
QED

(* The write cursor moves, but the allocation-ID cutoff for saved operands
   is fixed at the tuple row.  Old resource bytes and the tuple prefix
   are protected separately. *)
Theorem extcall_store_values_joint_all_dead:
  !mods exps.
  compile_extcall_store_values ce (ZIP (svs,tys)) (Var root) off ca = ((),cb) /\
  LENGTH svs = LENGTH tys /\ LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tys /\
  fn_has_code ca cb fn /\ fn_inst_ids_distinct fn /\
  storage_trace_domain cx st0 ee.storage_trace /\ (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (ce.ce_is_ctor ==> (contract_inv mods exps ctx ce cx /\
     module_body_inv mods ce.ce_module tops ce cx) /\ expr_sim_inv_mods mods ce cx env entry /\
                     ee.immutables = entry.immutables) /\
  local_ptrs_reserved ce ca /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at ca x) /\
  not_fresh_at ca root /\ lookup_var root s = SOME bw /\ ptr_covers G tn root s cap /\
  FLOOKUP s.vs_allocas aid = SOME (w2n bw,cap) /\ aid < ca.cs_next_id /\
  MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [root]) (fn_insts fn) /\
  w2n bw + cap < dimword (:256) /\ off + SUM (MAP (type_memory_bytes ce) tys) <= cap /\
  (!name p k. local_region ce ee.scopes s name p k ==> w2n bw+cap <= p \/ p+k <= w2n bw) /\
  alloca_history fn s /\ ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\ return_buf_frame d ce ca s /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  (!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    type_memory_bytes ce (EL i tys) = type_memory_size (EL i tvs) /\
      type_memory_size (EL i tvs) < 2**64 /\ value_has_type (EL i tvs) (EL i vs) /\
      (!l. vv_operand (EL i svs) <> Label l) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==> vv_storage_live H cx (EL i svs) ee s) /\
      ?e si vv sm ss raw copy.
        (EL i tys) = lowered_value_type ce e /\ compile_expr ce (expr_type e) e si = (vv,sm) /\
        compile_snapshot_vv ce copy (ext_call_arg_value (EL i tys) vv) sm = ((EL i svs),ss) /\
        ((?tag op0. (EL i svs) = StackValue tag op0) \/
         (?p. (EL i svs) = LocatedValue (EL i tys) p /\
         ~is_word_type (EL i tys) /\
         p.ptr_location = LocMemory) \/
         (?p. (EL i svs) = LocatedValue (EL i tys) p /\
         ~is_word_type (EL i tys) /\
         p.ptr_location <> LocMemory /\
              (EL i tys) = expr_type e /\ (EL i svs) = vv)) /\
        (~is_word_type (EL i tys) ==> ~is_word_type (expr_type e)) /\
        local_ptrs_reserved ce si /\
        (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
        (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
        sm.cs_next_var <= ca.cs_next_var /\ sm.cs_next_id <= ca.cs_next_id /\
        ss.cs_next_var <= ca.cs_next_var /\ ss.cs_next_id <= aid /\
        read_result cx raw ee = (INL (EL i vs),ee) /\ vv_holds ce cx (EL i tys) raw (EL i svs) ee s /\
        vv_at ce cx (EL i tys) si ss ee raw (EL i svs) s /\
        ptr_vv_ok cx (EL i tys) raw (EL i svs) ee G tn s /\
        vv_store_bound cx (EL i tys) (EL i tys) ee raw (EL i svs) s /\
        ((case (EL i svs) of StackValue tag op0 => ~is_word_type (EL i tys)
          | LocatedValue tag p => p.ptr_location = LocMemory) ==>
         ptr_buf_ok ce e (vv_operand (EL i svs)) G s)) ==>
  ?q Gq tq.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gq,tq) /\
      stmt_state_rel H ctx fn ce cx ee q /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee Gq tq q) /\
    (!mem. mem_agree_outside tq.t_mem q.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n bw+off) mem) /\
    lookup_var root q = SOME bw /\ ptr_covers Gq tq root q cap /\
    FLOOKUP q.vs_allocas aid = SOME (w2n bw,cap) /\ s.vs_alloca_next <= q.vs_alloca_next /\
    alloca_history fn q /\ ~q.vs_halted /\ q.vs_current_bb = cb.cs_current_bb /\
    q.vs_inst_idx = LENGTH cb.cs_current_insts /\ return_buf_frame d ce cb q /\
    wb_frame ce ee ee (ca with cs_next_id := aid) s q /\
    ghost_kept_at lo ce ee (ca with cs_next_id := aid) G tn s Gq tq /\
    mem_bytes_at (w2n bw) off q.vs_memory = mem_bytes_at (w2n bw) off s.vs_memory /\
    (!i. w2n bw <= i /\ i < w2n bw+off /\ i IN tq.t_mem ==> i IN tn.t_mem) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gq,tq))
Proof
  map_every qid_spec_tac [`cb`,`ca`,`off`,`s`,`G`,`tn`,`tys`,`tvs`,`vs`] >>
  Induct_on `svs`
  >- (rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      gvs[compile_extcall_store_values_def, comp_return_def] >>
      qexistsl [`s`,`G`,`tn`] >>
      simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules, val_in_memory_tuple,
           valueEncodingDefsTheory.val_in_memory_def, exprSimWordArgsTheory.wb_frame_refl,
           wordArgsPtrTheory.ghost_kept_at_refl]) >>
  rpt gen_tac >>
  namedCases_on `tys` ["", "ty tys"] >> namedCases_on `tvs` ["", "tv tvs"] >>
  namedCases_on `vs` ["", "v vs"] >>
  simp[] >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  suspend "head"
QED

Resume extcall_store_values_joint_all_dead[head]:
  rename1 `compile_extcall_store_values ce ((h,ty)::ZIP (svs,rest)) (Var root) off ca = _` >>
  rename1 `val_in_memory (TupleTV (tv::rts)) (ArrayV (TupleV (v::rvs))) _ _` >>
  qpat_assum `!i. i < SUC (LENGTH rest) ==> _`
    (qspec_then `0` (mp_tac o SIMP_RULE (srw_ss()) [])) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN (fn th =>
    let val choose = qx_choose_then `e` (qx_choose_then `si` (qx_choose_then `vv`
          (qx_choose_then `sm` (qx_choose_then `ss` (qx_choose_then `raw`
          (qx_choose_then `copy` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))))
    in choose th ORELSE assume_tac th end)) >>
  drule_all extcall_tuple_cons_cuts >>
  disch_then (qx_choose_then `dst` (qx_choose_then `su` (qx_choose_then `src`
    (qx_choose_then `cw` (qx_choose_then `cm`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`, vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx fn ce cx ee s /\ ghost_inv_at (DF H0) lo d ce cx ee G tn s` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `H0` mp_tac) >> simp[]) >>
  `(ce.ce_is_ctor /\ vv_location h = SOME LocCode ==>
    !w. eval_operand (vv_operand h) s = SOME w ==>
      w2n w + type_memory_size tv <= lo /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv v (w2n w) mem))` by
    (disch_then (CONJUNCTS_THEN assume_tac) >>
     `body_inv tops ctx ce cx /\ expr_sim_inv ce cx env entry /\
       ee.immutables = entry.immutables /\ dead_lo_ok H0 (DF H0) lo ce cx` by
       (qpat_assum `ce.ce_is_ctor ==> _` (drule_then strip_assume_tac) >> simp[]) >>
     Cases_on `h` >> gvs[vv_location_def, vv_operand_def] >>
     `stmt_state_rel H0 ctx fn ce cx ee s /\ ghost_inv_at (DF H0) lo d ce cx ee G tn s` by simp[] >>
     `dead_lo_ok H0 (DF H0) lo ce cx` by simp[] >>
     rename1 `vv_holds ce cx tag raw (LocatedValue tag p) ee s` >>
     `(?raw. read_result cx raw ee = (INL v,ee) /\ vv_holds ce cx tag raw (LocatedValue tag p) ee s)`
       suffices_by (disch_tac >> gen_tac >> disch_tac >>
         drule_all bodyFullExtCallPosTransportTheory.extcall_request_saved_ctor_read >>
         simp[arithmeticTheory.ADD_COMM]) >>
     qexists `raw` >> simp[]) >>
  `off + type_memory_size tv <= cap /\ w2n bw + off < dimword (:256)` by
    decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx h ee s /\ ghost_inv_at (DF H) lo d ce cx ee G tn s` by simp[] >>
  drule_all (REWRITE_RULE [EVAL ``2 ** 64:num``] extcall_tuple_slot_run) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `z` (qx_choose_then `Gz` (qx_choose_then `tz`
       (qx_choose_then `m` (qx_choose_then `Gm` (qx_choose_then `tm`
         (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))))) >>
  `!name p k. local_region ce ee.scopes s name p k ==>
    w2n bw + cap <= p \/ p + k <= w2n bw` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name p k. local_region _ _ _ name p k ==> _` drule >> decide_tac) >>
  drule_all_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) extcall_tuple_head_middle_post >>
  `alloca_history fn m` by (drule_all extcall_tuple_slot_history >> simp[]) >>
  qpat_x_assum `!vs tvs tys tn G s off ca cb. _`
    (qspecl_then [`rvs`,`rts`,`rest`,`tm`,`Gm`,`m`,
                  `off + type_memory_bytes ce ty`,`cm`,`cb`] mp_tac) >>
  impl_tac >- suspend "tail_input" >>
  suspend "join"
QED

Resume extcall_store_values_joint_all_dead[tail_input]:
  `local_ptrs_reserved ce cm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at ca x ==> not_fresh_at cm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `cw.cs_current_bb = cm.cs_current_bb` by metis_tac[] >>
  simp[] >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE (rpt strip_tac >> decide_tac))) >>
  qx_gen_tac `i` >> disch_tac >>
  `SUC i < SUC (LENGTH rest)` by decide_tac >>
  qpat_assum `!j. j < SUC (LENGTH rest) ==> _`
    (qspec_then `SUC i` (mp_tac o SIMP_RULE (srw_ss()) [])) >>
  simp[] >>
  qabbrev_tac `saved = EL i svs` >>
  qabbrev_tac `tyi = EL i rest` >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN (fn th =>
    let val choose = qx_choose_then `ei` (qx_choose_then `sii` (qx_choose_then `vvi`
          (qx_choose_then `smi` (qx_choose_then `ssi` (qx_choose_then `ri`
          (qx_choose_then `copy'` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))))
    in choose th ORELSE assume_tac th end)) >>
  `!x. vv_operand saved = Var x ==> not_fresh_at ssi x` by
    (gen_tac >> disch_tac >>
     irule bodyFullExtCallSavedOperandTheory.extcall_saved_operand_not_fresh >>
     goal_assum (drule_at (Pat `compile_snapshot_vv _ _ _ _ = (saved,ssi)`)) >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ sii = _`)) >> simp[]) >>
  qabbrev_tac `cut = ca with cs_next_id := aid` >>
  `ssi.cs_next_id <= cut.cs_next_id /\ ssi.cs_next_var <= cut.cs_next_var /\
   local_ptrs_reserved ce cut` by
    (simp[Abbr `cut`] >> irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists `ca` >> simp[]) >>
  `!x. vv_operand saved = Var x ==> not_fresh_at cut x` by
    (gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `ssi` >> simp[]) >>
  `?w. eval_operand (vv_operand saved) s = SOME w` by
    (irule target_saved_operand_exists >> goal_assum (drule_at Any)) >>
  `eval_operand (vv_operand saved) m = eval_operand (vv_operand saved) s` by
    (irule (cj 1 extcall_tuple_saved_operand_frame) >> simp[] >>
     qexistsl [`G`,`Gm`,`ce`,`cut`,`ee`,`lo`,`tn`,`tm`] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule target_saved_storage_live_frame >>
      qexists `s` >> simp[]) >>
  `local_ptrs_rel fn ce ee.scopes s` by
    (drule_then (ACCEPT_TAC o CONJUNCT1) stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
  `stmt_state_rel H0 ctx fn ce cx ee m /\ ghost_inv_at (DF H0) lo d ce cx ee Gm tm m /\
   vv_storage_live H0 cx saved ee s /\ dead_lo_ok H0 (DF H0) lo ce cx` by simp[] >>
  `(vv_location saved = SOME LocMemory ==> ~is_word_type tyi) /\
   (!tag p. saved = LocatedValue tag p ==> tag = tyi)` by
    (qpat_assum `(?tag op0. saved = StackValue tag op0) \/ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[vv_location_def]) >>
  `vv_holds ce cx tyi ri saved ee m /\ vv_at ce cx tyi sii ssi ee ri saved m /\
   ptr_vv_ok cx tyi ri saved ee Gm tm m /\
   vv_store_bound cx tyi tyi ee ri saved m /\
   ((case saved of StackValue tag op0 => ~is_word_type tyi
       | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok ce ei (vv_operand saved) Gm m)` by
    (irule (INST_TYPE [alpha |-> ``:256``] extcall_tuple_saved_entry) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists `EL i rts` >> first_assum ACCEPT_TAC) >>
     conj_tac >- (qexists `EL i rvs` >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`DF H0`,`G`,`H0`,`ctx`,`cut`,`d`,`fn`,`lo`,`s`,`tn`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`ei`,`sii`,`vvi`,`smi`,`ssi`,`ri`,`copy'`] >>
  simp[] >> decide_tac
QED

Resume extcall_store_values_joint_all_dead[join]:
  disch_then (qx_choose_then `q` (qx_choose_then `Gq` (qx_choose_then `tq`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  qexistsl [`q`,`Gq`,`tq`] >>
  conj_tac
  >- (qx_gen_tac `H` >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (m,Gm,tm) _ _ /\ _`
        (qspec_then `H` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (s,G,tn) _ (OK m,Gm,tm) /\ stmt_state_rel _ _ _ _ _ _ m /\ _`
        (qspec_then `H` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      conj_tac >- (drule_all fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
                    disch_then ACCEPT_TAC) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      once_rewrite_tac [arithmeticTheory.ADD_COMM] >>
      irule extcall_tuple_robust_cons >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`tm.t_mem`,`tq.t_mem`,`q.vs_memory`,`m.vs_memory`] >>
      qpat_assum `type_memory_bytes ce ty = type_memory_size tv`
        (once_rewrite_tac o single o GSYM) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE decide_tac)) >>
  qabbrev_tac `cutA = ca with cs_next_id := aid` >>
  qabbrev_tac `cutM = cm with cs_next_id := aid` >>
  `cutA.cs_next_var <= cutM.cs_next_var /\ cutA.cs_next_id <= cutM.cs_next_id` by
    simp[Abbr `cutA`, Abbr `cutM`] >>
  `local_ptrs_reserved ce cutA` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists `ca` >> simp[Abbr `cutA`]) >>
  conj_tac
  >- (irule (INST_TYPE [alpha |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qexistsl [`ee`,`cutM`,`m`] >> simp[]) >>
      qexistsl [`H0`,`ctx`,`cx`,`fn`] >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule wordArgsPtrTheory.ghost_kept_at_trans >>
      qexistsl [`Gm`,`ee`,`m`,`cutM`,`tm`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (`mem_bytes_at (w2n bw) off m.vs_memory = mem_bytes_at (w2n bw) off q.vs_memory` by
        (qpat_assum `mem_bytes_at _ (off + _) q.vs_memory = _`
           (mp_tac o MATCH_MP valueEncodingProofsTheory.mem_bytes_at_agree_window) >>
         disch_then (irule o CONJUNCT1) >> decide_tac) >>
      metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      qpat_assum `!i. _ /\ _ /\ i IN tm.t_mem ==> _` irule >>
      conj_tac >- decide_tac >>
      conj_tac >- decide_tac >>
      qpat_assum `!i. _ /\ _ /\ i IN tq.t_mem ==> _` irule >>
      rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac)) >>
  gen_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` (qspec_then `D` assume_tac) >>
  qpat_assum `!D. gas_origin_ptr_path _ (m,Gm,tm) _ _` (qspec_then `D` assume_tac) >>
  drule_all fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >> simp[]
QED

Finalise extcall_store_values_joint_all_dead

Theorem extcall_store_values_joint:
  !mods exps.
  compile_extcall_store_values ce (ZIP (svs,tys)) (Var root) off ca = ((),cb) /\
  LENGTH svs = LENGTH tys /\ LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tys /\
  fn_has_code ca cb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  storage_trace_domain cx st0 ee.storage_trace /\ (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (ce.ce_is_ctor ==> (contract_inv mods exps ctx ce cx /\
     module_body_inv mods ce.ce_module tops ce cx) /\ expr_sim_inv_mods mods ce cx env entry /\
                     ee.immutables = entry.immutables) /\
  local_ptrs_reserved ce ca /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at ca x) /\
  not_fresh_at ca root /\ lookup_var root s = SOME bw /\ ptr_covers G tn root s cap /\
  FLOOKUP s.vs_allocas aid = SOME (w2n bw,cap) /\ aid < ca.cs_next_id /\
  MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [root]) (fn_insts fn) /\
  w2n bw + cap < dimword (:256) /\ off + SUM (MAP (type_memory_bytes ce) tys) <= cap /\
  (!name p k. local_region ce ee.scopes s name p k ==> w2n bw+cap <= p \/ p+k <= w2n bw) /\
  alloca_history fn s /\ ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\ return_buf_frame d ce ca s /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  (!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    type_memory_bytes ce (EL i tys) = type_memory_size (EL i tvs) /\
      type_memory_size (EL i tvs) < 2**64 /\ value_has_type (EL i tvs) (EL i vs) /\
      (!l. vv_operand (EL i svs) <> Label l) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==> vv_storage_live H cx (EL i svs) ee s) /\
      ?e si vv sm ss raw copy.
        (EL i tys) = lowered_value_type ce e /\ compile_expr ce (expr_type e) e si = (vv,sm) /\
        compile_snapshot_vv ce copy (ext_call_arg_value (EL i tys) vv) sm = ((EL i svs),ss) /\
        ((?tag op0. (EL i svs) = StackValue tag op0) \/
         (?p. (EL i svs) = LocatedValue (EL i tys) p /\
         ~is_word_type (EL i tys) /\
         p.ptr_location = LocMemory) \/
         (?p. (EL i svs) = LocatedValue (EL i tys) p /\
         ~is_word_type (EL i tys) /\
         p.ptr_location <> LocMemory /\
              (EL i tys) = expr_type e /\ (EL i svs) = vv)) /\
        (~is_word_type (EL i tys) ==> ~is_word_type (expr_type e)) /\
        local_ptrs_reserved ce si /\
        (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
        (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
        sm.cs_next_var <= ca.cs_next_var /\ sm.cs_next_id <= ca.cs_next_id /\
        ss.cs_next_var <= ca.cs_next_var /\ ss.cs_next_id <= aid /\
        read_result cx raw ee = (INL (EL i vs),ee) /\ vv_holds ce cx (EL i tys) raw (EL i svs) ee s /\
        vv_at ce cx (EL i tys) si ss ee raw (EL i svs) s /\
        ptr_vv_ok cx (EL i tys) raw (EL i svs) ee G tn s /\
        vv_store_bound cx (EL i tys) (EL i tys) ee raw (EL i svs) s /\
        ((case (EL i svs) of StackValue tag op0 => ~is_word_type (EL i tys)
          | LocatedValue tag p => p.ptr_location = LocMemory) ==>
         ptr_buf_ok ce e (vv_operand (EL i svs)) G s)) ==>
  ?q Gq tq.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gq,tq) /\
      stmt_state_rel H ctx fn ce cx ee q /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee Gq tq q) /\
    (!mem. mem_agree_outside tq.t_mem q.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n bw+off) mem) /\
    lookup_var root q = SOME bw /\ ptr_covers Gq tq root q cap /\
    FLOOKUP q.vs_allocas aid = SOME (w2n bw,cap) /\ s.vs_alloca_next <= q.vs_alloca_next /\
    alloca_history fn q /\ ~q.vs_halted /\ q.vs_current_bb = cb.cs_current_bb /\
    q.vs_inst_idx = LENGTH cb.cs_current_insts /\ return_buf_frame d ce cb q /\
    wb_frame ce ee ee (ca with cs_next_id := aid) s q /\
    ghost_kept_at lo ce ee (ca with cs_next_id := aid) G tn s Gq tq /\
    mem_bytes_at (w2n bw) off q.vs_memory = mem_bytes_at (w2n bw) off s.vs_memory /\
    (!i. w2n bw <= i /\ i < w2n bw+off /\ i IN tq.t_mem ==> i IN tn.t_mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL extcall_store_values_joint_all_dead) >>
  impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  qexistsl [`q`,`Gq`,`tq`] >> simp[]
QED
