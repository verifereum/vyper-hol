(*
 * The field-agnostic joint pieces of a Log statement's suffix, at any dead
 * mask D and low-memory bound lo: the read-only topic hashes and the LOG
 * instruction.  Both run no GAS, so each is a zero-mark joint path, and
 * both leave memory, allocations and taints alone, so ghost_inv_at carries
 * over unchanged.  The data stage between them (the two buffers, the
 * stores and the ABI encoder) has its own joint producers.
 *
 * TOP-LEVEL:
 *   compile_log_topic_ops_origin_ptr_path -- the indexed topics
 *   compile_log_emit_origin_ptr_path -- the LOG instruction
 *   ghost_inv_at_logs_idx -- ghost_inv_at ignores the logs and the index
 *)
Theory bodyFullLogSuffix
Ancestors
  logTopicsRunPtr logEmitPtr logEventCodePtr stmtSimLogTopics stmtLogEmitMemory
  fragGasOriginPtrLoop fragGasOriginPtr instSeqPtrLo fragGasSeqPtr
  bodyFullGhostFrame bodyPtrDefs logInstSeqPtr ptrDiscipline ptrSafeRun
  stmtLowering compileEnv emitHelper emitHelperProps exprLoweringProps
  loweringStateRelDefs exprSimHashBoundary venomInst venomState list

Theorem ghost_inv_at_logs_idx:
  ghost_inv_at D lo d cenv cx es G tn
    (s with <| vs_logs := l; vs_inst_idx := k |>) <=>
  ghost_inv_at D lo d cenv cx es G tn s
Proof
  simp[ghost_inv_at_def, ptr_covers_def, stor_taint_ok_at_def,
       lookup_var_def, allocas_from_def] >>
  Cases_on `d` >> TRY (PairCases_on `x`) >>
  simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

(* ===== Topics ===== *)

Theorem compile_log_topic_ops_origin_ptr_path:
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  compile_log_topic_ops (MAP (\p. (FST p,is_bytestring_type (SND p))) xs) sm =
    (ops,sb) /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
              (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel cenv cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v)
    xs vs /\
  encode_indexed_event_topics (REPLICATE (LENGTH xs) T) (MAP SND xs) vs =
    SOME topics /\
  LIST_REL (\arg v. ptr_val_ok cx (SND arg) v (FST arg) G tn s) xs vs /\
  ~ctx_has_dalloca ctx /\
  run_inst_seq_mem_ok (emitted_insts sm sb) s /\
  fn_has_code sm sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
           (OK t,Gf,tnf)) /\
    (t with <| vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx |>) = s /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted /\
    LIST_REL (\op w. eval_operand op t = SOME w) ops topics /\
    EVERY (\op. op_taint tnf op = {}) ops /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    stmt_state_rel H ctx func cenv cx es t /\
    ((!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
             not_fresh_at sm x) /\
     (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
             not_fresh_at sm x) ==>
     !D d. ghost_inv_at D lo d cenv cx es G tn s ==>
           ghost_inv_at D lo d cenv cx es Gf tnf t)
Proof
  strip_tac >>
  drule_all compile_log_topic_ops_seq_ptr >>
  disch_then (fn th =>
    qspecl_then [`PG`, `ARB`] strip_assume_tac th >>
    `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sm sb) s Gf tnf` by
      (gen_tac >> qspecl_then [`PG`, `D`] strip_assume_tac th >>
       metis_tac[inst_seq_ptr_ghost_unique])) >>
  `stmt_state_rel H ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum (drule_at Any) >>
     qexists_tac `sm` >> simp[]) >>
  qpat_x_assum `t with vs_vars := s.vs_vars = s`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `inst_extends sm sb /\ same_blocks sm sb` by
    metis_tac[log_topics_compiler_interval] >>
  `sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (gen_tac >>
     `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) s Gf tnf` by
       (irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> simp[]) >>
     irule fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >> simp[] >>
     qexists_tac `sm` >> simp[] >>
     drule log_topics_opcode_shape >> simp[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,
                `Gf`, `tnf`] >>
  simp[venom_state_component_equality, stmt_state_rel_inst_idx] >>
  rpt strip_tac
  >~ [`lookup_var p (t with vs_inst_idx := _) = lookup_var p s`]
  >- fs[lookup_var_def] >>
  mp_tac (Q.SPECL [`D`, `lo`, `d`, `cenv`, `cx`, `es`, `es`,
    `G`, `Gf`, `tn`, `tnf`, `s`,
    `t with vs_inst_idx := LENGTH sb.cs_current_insts`, `sm`]
    ghost_inv_at_exterior_frame) >>
  (impl_tac >- fs[lookup_var_def]) >> disch_then ACCEPT_TAC
QED

(* ===== LOG ===== *)

Theorem compile_log_emit_origin_ptr_path:
  emit_inst LOG (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++
    [len_op;ptr_op]) [] sa = ((),sb) /\
  LENGTH topic_ops < dimword (:256) /\
  eval_operands topic_ops s = SOME topics /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME len /\
  EVERY (\op. op_taint tn op = {}) (ptr_op::len_op::topic_ops) /\
  (w2n len <> 0 ==> ?v. ptr_op = Var v /\ ptr_covers G tn v s (w2n len)) /\
  (!i. w2n off <= i /\ i < w2n off + w2n len ==> i NOTIN tn.t_mem) /\
  (w2n len = 0 \/ w2n off + w2n len <= s.vs_alloca_next) /\
  ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (s with <| vs_logs := s.vs_logs ++
            [<|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
               data := mem_bytes_at (w2n off) (w2n len) s.vs_memory|>];
            vs_inst_idx := LENGTH sb.cs_current_insts |>), G, tn)
Proof
  strip_tac >> gen_tac >>
  drule emitted_insts_emit_inst >> strip_tac >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) []` >>
  `inst.inst_opcode = LOG /\ inst.inst_outputs = [] /\
   inst.inst_operands = Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++
     [len_op;ptr_op]` by simp[Abbr `inst`, mk_inst_def] >>
  drule_all log_emit_singleton_seq_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  `inst_seq_ptr D lo ctx func PG G tn [inst] s G tn` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule compile_log_emit_mem_ok >> metis_tac[]) >>
  qpat_x_assum `t with vs_logs := s.vs_logs = s`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `t = s with vs_logs := s.vs_logs ++
     [<|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
        data := mem_bytes_at (w2n off) (w2n len) s.vs_memory|>]` by
    simp[venom_state_component_equality] >>
  `t with vs_inst_idx := LENGTH sb.cs_current_insts =
   s with <| vs_logs := t.vs_logs;
             vs_inst_idx := LENGTH sb.cs_current_insts |>` by simp[] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G,tn)` suffices_by
    gvs[] >>
  irule fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >> simp[] >>
  qexists_tac `sa` >> simp[] >>
  drule inst_extends_emit_inst >> simp[is_terminator_def]
QED
