(* Fixed RawLog buffer retention and the checked store/log suffix. *)
Theory rawLogPtrFixed
Ancestors
  wordLoadStorePtr rawLogPtrInst rawLogPtrTopics bodyPtrHashBuiltinsAllocFrame wordArgsPtr
  bodyPtrHashBuiltinsKeccakFixed assignTuplePtrCopyLen exprSimRawLog
  instSeqComposePtr ghostPcTransportPtr instIdxIndep fragExecPtr bodyPtrDefs loweringPosts
  fragGasSeqPtr exprLoweringProps emitHelper context compileEnv loweringStateRelDefs rich_list typedCopyPtr ptrDiscipline venomState venomInst
  venomExecSemantics words finite_map pred_set list

(* Applies to any older covered pointer, including a just-allocated buffer. *)
Theorem ptr_covers_evaluation_frame:
  ptr_covers G tn p s n /\ not_fresh_at sa p /\
  wb_frame cenv es es' sa s t /\ ghost_kept cenv es sa G tn s G' tn' ==>
  ptr_covers G' tn' p t n
Proof
  strip_tac >> irule ptr_covers_lookup_frame >>
  fs[ghost_kept_def, wb_frame_def] >>
  `?w. lookup_var p s = SOME w` by fs[ptr_covers_def] >>
  metis_tac[]
QED

Theorem raw_log_fixed_inst_seq_ptr:
  !D ctx fn PG G tn s p value a w sid lid ops vals.
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME a /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  eval_operands ops s = SOME vals /\ EVERY (\op. op_taint tn op = {}) ops /\
  LENGTH ops < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_call_ctx.cc_static ==>
  ?tn' t.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst sid MSTORE [Var p;value] [];
       mk_inst lid LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var p]) []]
      s G tn' /\
    run_inst_seq
      [mk_inst sid MSTORE [Var p;value] [];
       mk_inst lid LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var p]) []]
      s = OK t /\
    tn' = step_taint (mk_inst sid MSTORE [Var p;value] []) s (mstore (w2n a) w s) tn /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32} /\
    t = (mstore (w2n a) w s) with vs_logs := s.vs_logs ++
      [<|logger := w2w s.vs_call_ctx.cc_address; topics := vals;
         data := TAKE 32 (DROP (w2n a) (mstore (w2n a) w s).vs_memory ++ REPLICATE 32 0w)|>] /\
    t.vs_memory = (mstore (w2n a) w s).vs_memory /\
    t.vs_logs = s.vs_logs ++
      [<|logger := w2w s.vs_call_ctx.cc_address; topics := vals;
         data := TAKE 32 (DROP (w2n a) (mstore (w2n a) w s).vs_memory ++ REPLICATE 32 0w)|>]
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `st = mstore (w2n a) w s` >>
  qabbrev_tac `si = mk_inst sid MSTORE [Var p;value] []` >>
  qabbrev_tac `tn1 = step_taint si s st tn` >>
  `step_inst_base si s = OK st` by
    (simp[Abbr `si`, Abbr `st`, step_inst_base_opcode_eqs,
      mk_inst_def, exec_write2_def, eval_operand_def]) >>
  `step_prov PG G si st = G /\ tn1.t_var = tn.t_var /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\
   tn1.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}` by
    (simp[Abbr `si`, Abbr `st`, Abbr `tn1`] >>
     drule_all mstore_ghost_frame >> simp[]) >>
  `ptr_covers G tn1 p st 32` by
    fs[ptr_covers_def, Abbr `st`, mstore_def, lookup_var_def, op_taint_def] >>
  suspend "tail"
QED

Resume raw_log_fixed_inst_seq_ptr[tail]:
  `eval_operands ops st = SOME vals` by
    (`eval_operands ops st = eval_operands ops s` by
       (qunabbrev_tac `st` >> rpt (pop_assum kall_tac) >>
        Induct_on `ops` >> simp[eval_operands_def] >>
        Cases_on `h` >> simp[eval_operand_def, mstore_def, lookup_var_def]) >>
     simp[]) >>
  `eval_operand (Var p) st = SOME a /\
   st.vs_call_ctx = s.vs_call_ctx /\ st.vs_logs = s.vs_logs` by
    simp[Abbr `st`, mstore_def, eval_operand_def, lookup_var_def] >>
  qabbrev_tac `li = mk_inst lid LOG
    (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var p]) []` >>
  qabbrev_tac `logs = s.vs_logs ++
    [<|logger := w2w s.vs_call_ctx.cc_address; topics := vals;
       data := TAKE 32 (DROP (w2n a) st.vs_memory ++ REPLICATE 32 0w)|>]` >>
  `step_inst_base li st = OK (st with vs_logs := logs)` by
    (mp_tac (Q.GENL [`off`, `len`, `topics`] (Q.INST
      [`inst` |-> `li`, `sz` |-> `Lit 32w`, `pop` |-> `Var p`, `s` |-> `st`]
      raw_log_core_step)) >>
     simp[Abbr `li`, Abbr `logs`, mk_inst_def, eval_operand_def, dimword_def]) >>
  qexistsl_tac [`tn1`, `st with vs_logs := logs`] >> simp[] >>
  conj_tac >- suspend "checked" >>
  simp[run_inst_seq_def, Abbr `logs`]

QED

Resume raw_log_fixed_inst_seq_ptr[checked]:
  pure_rewrite_tac[Once inst_seq_ptr_def] >>
  conj_tac
  >- (simp[Abbr `si`] >> irule ptr_inst_ok_mstore >> simp[]) >>
  simp[] >>
  `!k. step_inst_base li (st with vs_inst_idx := k) =
    OK ((st with vs_logs := logs) with vs_inst_idx := k)` by
    (`~is_terminator li.inst_opcode` by
       simp[Abbr `li`, mk_inst_def, is_terminator_def] >>
     gen_tac >> drule step_inst_inst_idx_indep >>
     disch_then (qspecl_then [`st`, `k`] mp_tac) >>
     simp[exec_result_map_def]) >>
  simp[Once inst_seq_ptr_def] >> conj_tac >- suspend "logcheck" >>
  simp[inst_seq_ptr_def, Abbr `li`, log_ghost]
QED

Resume raw_log_fixed_inst_seq_ptr[logcheck]:
  `EVERY (\op. op_taint tn1 op = {}) ops` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     `op_taint tn1 op = op_taint tn op` by
       (Cases_on `op` >> pure_rewrite_tac[op_taint_def] >>
        qpat_assum `tn1.t_var = _` (fn th => pure_rewrite_tac[th]) >>
        simp[NoAsms]) >> metis_tac[]) >>
  qunabbrev_tac `li` >> irule log_inst_ok >>
  simp[op_taint_def] >>
  fs[ptr_covers_def, eval_operand_def, op_taint_def] >>
  simp[dimword_def]
QED

Finalise raw_log_fixed_inst_seq_ptr

Theorem raw_log_fixed_emitted_ptr:
  !D ctx fn PG G tn s p value a w sa sm sb u v ops vals.
  emit_void MSTORE [Var p;value] sa = (u,sm) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var p]) [] sm = (v,sb) /\
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME a /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  eval_operands ops s = SOME vals /\ EVERY (\op. op_taint tn op = {}) ops /\
  LENGTH ops < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_call_ctx.cc_static ==>
  ?tn' t.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tn' /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    tn' = step_taint (mk_inst sa.cs_next_id MSTORE [Var p;value] []) s (mstore (w2n a) w s) tn /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32} /\
    t = (mstore (w2n a) w s) with vs_logs := s.vs_logs ++
      [<|logger := w2w s.vs_call_ctx.cc_address; topics := vals;
         data := TAKE 32 (DROP (w2n a) (mstore (w2n a) w s).vs_memory ++ REPLICATE 32 0w)|>] /\
    t.vs_memory = (mstore (w2n a) w s).vs_memory /\
    t.vs_logs = s.vs_logs ++
      [<|logger := w2w s.vs_call_ctx.cc_address; topics := vals;
         data := TAKE 32 (DROP (w2n a) (mstore (w2n a) w s).vs_memory ++ REPLICATE 32 0w)|>]
Proof
  rpt gen_tac >> strip_tac >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id MSTORE [Var p;value] [];
     mk_inst sm.cs_next_id LOG
       (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var p]) []]` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_void_def, emit_inst_def, comp_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       GSYM APPEND_ASSOC]) >>
  drule_all raw_log_fixed_inst_seq_ptr >>
  simp[] >> metis_tac[]
QED

(* The source log emission and target LOG preserve the clean-store ghost. *)
Theorem raw_log_fixed_ghost_frame:
  !PG G tn s id p value a w d cenv cx es ctx fn sa logs vlogs k.
    lookup_var p s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\ ghost_inv d cenv cx es G tn s /\
    stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
    (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
    (!n b z i. local_region cenv es.scopes s n b z /\ b <= i /\ i < b+z ==>
      ~(w2n a <= i /\ i < w2n a+32)) ==>
    ghost_inv d cenv cx (es with logs := logs) G
      (step_taint (mk_inst id MSTORE [Var p;value] []) s (mstore (w2n a) w s) tn)
      (((mstore (w2n a) w s) with vs_logs := vlogs) with vs_inst_idx := k) /\
    ghost_kept cenv es sa G tn s G
      (step_taint (mk_inst id MSTORE [Var p;value] []) s (mstore (w2n a) w s) tn)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all hash_clean_mstore_frame >>
  drule_all mstore_ghost_frame >> strip_tac >>
  simp[log_ghost_frame]
QED

(* The buffer is allocated before the data expression, not after it.
   Allocation supplies the initial coverage and exterior placement; the data
   expression's ordinary and ghost frames retain precisely those facts. *)
Theorem raw_log_fixed_data_frame:
  !ctx fn cenv cx es es' sa s t G tn G' tn' p a d id value w logs vlogs k.
    stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    wb_frame cenv es es' sa s t /\ ghost_kept cenv es sa G tn s G' tn' /\
    ptr_covers G tn p s 32 /\ lookup_var p s = SOME a /\ not_fresh_at sa p /\
    (!n b z. local_region cenv es.scopes s n b z ==>
      regions_disjoint (w2n a) 32 b z) /\
    stmt_state_rel ctx fn cenv cx es' t /\ ghost_inv d cenv cx es' G' tn' t /\
    eval_operand value t = SOME w /\ op_taint tn' value = {} /\
    (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
    (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) ==>
    ptr_covers G' tn' p t 32 /\ lookup_var p t = SOME a /\
    ghost_inv d cenv cx (es' with logs := logs) G'
      (step_taint (mk_inst id MSTORE [Var p;value] []) t (mstore (w2n a) w t) tn')
      (((mstore (w2n a) w t) with vs_logs := vlogs) with vs_inst_idx := k) /\
    ghost_kept cenv es' sa G' tn' t G'
      (step_taint (mk_inst id MSTORE [Var p;value] []) t (mstore (w2n a) w t) tn')
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_covers G' tn' p t 32` by
    (irule ptr_covers_evaluation_frame >> metis_tac[]) >>
  `lookup_var p t = SOME a` by metis_tac[wb_frame_def] >>
  drule_all wb_frame_local_regions >> strip_tac >>
  `!n b z i. local_region cenv es'.scopes t n b z /\ b <= i /\ i < b+z ==>
      ~(w2n a <= i /\ i < w2n a+32)` by
    (rpt gen_tac >> strip_tac >>
     `local_region cenv es.scopes s n b z` by metis_tac[] >>
     `regions_disjoint (w2n a) 32 b z` by metis_tac[] >>
     fs[regions_disjoint_def] >> decide_tac) >>
  simp[] >> irule raw_log_fixed_ghost_frame >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`ctx`, `fn`] >> simp[]
QED

(* Counted suffix and ghost endpoint, after the allocated-buffer/data boundary. *)
Theorem raw_log_fixed_tail:
  !D ctx fn PG G tn s p value a w sid lid ops vals bb d cenv cx es sa logs.
    ptr_covers G tn p s 32 /\ lookup_var p s = SOME a /\
    eval_operand value s = SOME w /\ op_taint tn value = {} /\
    eval_operands ops s = SOME vals /\ EVERY (\op. op_taint tn op = {}) ops /\
    LENGTH ops < dimword (:256) /\ ~ctx_has_dalloca ctx /\
    ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX
      [mk_inst sid MSTORE [Var p;value] [];
       mk_inst lid LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var p]) []]
      (DROP s.vs_inst_idx bb.bb_instructions) /\
    ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx fn cenv cx es s /\
    local_ptrs_reserved cenv sa /\
    (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
    (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
    (!n b z i. local_region cenv es.scopes s n b z /\ b <= i /\ i < b+z ==>
      ~(w2n a <= i /\ i < w2n a+32)) ==>
    ?tn' t.
      run_inst_seq
        [mk_inst sid MSTORE [Var p;value] [];
         mk_inst lid LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var p]) []]
        s = OK t /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G tn'
        (OK (t with vs_inst_idx := s.vs_inst_idx+2)) /\
      ghost_inv d cenv cx (es with logs := logs) G tn'
        (t with vs_inst_idx := s.vs_inst_idx+2) /\
      ghost_kept cenv es sa G tn s G tn'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all raw_log_fixed_inst_seq_ptr >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `sid`, `lid`] strip_assume_tac) >>
  qexistsl_tac [`tn'`, `t`] >> simp[] >>
  conj_tac >- suspend "path" >>
  drule_all raw_log_fixed_ghost_frame >> simp[]
QED

Resume raw_log_fixed_tail[path]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst sid MSTORE [Var p;value] [];
     mk_inst lid LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var p]) []]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def, is_terminator_def]
QED

Finalise raw_log_fixed_tail
