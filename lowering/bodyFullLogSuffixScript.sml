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
  logTopicsRunPtr logTopicsNonDalloca rawLogPtrInst stmtSimLogEmit stmtSimLogSuffixCode
  stmtSimLogTopics stmtLogEmitMemory stmtLogTopicsMemory
  fragGasOriginPtrLoop fragGasOriginPtr instSeqPtrLo fragGasSeqPtr
  bodyFullGhostFrame bodyPtrDefs logInstSeqPtr ptrDiscipline ptrSafeRun
  stmtLowering compileEnv emitHelper emitHelperProps exprLoweringProps
  loweringStateRelDefs exprSimHashBoundary valueCopyBytes exprSimMemDefs exprSimProps
  eventLoweringStructure exprSafeOperand exprBopSimProps freshWrites fragExec loweringPosts
  vyperEvent vyperTyping vfmConstants venomInst venomState list

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
    supported_event_leaf_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v)
    xs vs /\
  encode_indexed_event_topics (REPLICATE (LENGTH xs) T) (MAP SND xs) vs =
    SOME topics /\
  LIST_REL (\arg v. ptr_val_ok cx (SND arg) v (FST arg) G tn s) xs vs /\
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
    metis_tac[log_topics_straight] >>
  `sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (gen_tac >>
     `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) s Gf tnf` by
       (irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> simp[]) >>
     irule fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >> simp[] >>
     qexists_tac `sm` >> simp[] >>
     drule log_topics_opcode_shape >> simp[] >>
     drule log_topics_emitted_non_dalloca >> strip_tac >>
     rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     qpat_x_assum `emitted_insts _ _ = _ ++ _` (fn code =>
       qpat_assum `EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts _ _)`
         (mp_tac o PURE_REWRITE_RULE [code])) >>
     simp[EVERY_APPEND]) >>
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

Theorem compile_log_hash_origin_ptr_path:
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  log_arg_rel cenv cx sa sm es s (src,ty) v /\ supported_event_leaf_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  encode_event_topic ty v = SOME topic /\
  (!z. src = Var z ==> not_fresh_at sm z) /\ (!l. src <> Label l) /\
  compile_encode_log_topic src (is_bytestring_type ty) sm = (op,sb) /\
  ptr_val_ok cx ty v src G tn s /\ expr_store_bound cx ty v src s /\
  fn_has_code sm sb func /\ ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ allocas_from lo s /\
  lo <= s.vs_alloca_next ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    (t with <| vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx |>) = s /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted /\
    eval_operand op t = SOME topic /\ op_taint tnf op = {} /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    wb_frame cenv es es sm s t /\ ghost_kept_at lo cenv es sm G tn s Gf tnf /\
    ((!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
     (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) ==>
     !D d. ghost_inv_at D lo d cenv cx es G tn s ==>
           ghost_inv_at D lo d cenv cx es Gf tnf t)
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) s` by
    (mp_tac (Q.INST [`x` |-> `src`,`ce` |-> `cenv`]
       compile_encode_log_topic_event_mem_ok) >>
     impl_tac >- (asm_rewrite_tac[] >>
     rpt strip_tac >>
     `is_bytestring_type ty` by metis_tac[log_event_topic_shape] >>
     drule_all bytestring_type_value >> strip_tac >>
     gvs[value_has_type_def, expr_store_bound_def, val_store_size_def, word_size_def] >>
     decide_tac) >> disch_then ACCEPT_TAC) >>
  `compile_log_topic_ops [(src,is_bytestring_type ty)] sm = ([op],sb)` by
    simp[compile_log_topic_ops_def, comp_bind_def, comp_return_def] >>
  mp_tac (Q.INST [`xs` |-> `[(src,ty)]`, `ops` |-> `[op]`, `vs` |-> `[v]`,
                   `topics` |-> `[topic]`] (SPEC_ALL compile_log_topic_ops_origin_ptr_path)) >>
  impl_tac >- (`REPLICATE 1 T = [T]` by EVAL_TAC >>
               simp[encode_indexed_event_topics_def]) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tnf`] strip_assume_tac) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory` by
    (qpat_assum `t with <| vs_vars := _; vs_inst_idx := _ |> = s`
       (mp_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >> simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  fs[wb_frame_def, ghost_kept_at_def, locals_kept_regions] >> metis_tac[]
QED

Theorem compile_log_saved_topics_run:
  (!row w a b u Gu tu op.
    R row w /\ P a u Gu tu /\ ~u.vs_halted /\
    compile_log_saved_topics ce [row] a = ([op],b) /\ fn_has_code a b func ==>
    ?v Gv tv.
      P b v Gv tv /\ ~v.vs_halted /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (u,Gu,tu) [] (OK v,Gv,tv)) /\
      safe_operand b op /\ eval_operand op v = SOME w /\ op_taint tv op = {} /\
      (!x. not_fresh_at a x ==>
        lookup_var x v = lookup_var x u /\ FLOOKUP Gv x = FLOOKUP Gu x /\
        op_taint tv (Var x) = op_taint tu (Var x))) ==>
  !rows ws sa sb ops s G tn.
    LIST_REL R rows ws /\ compile_log_saved_topics ce rows sa = (ops,sb) /\
    fn_has_code sa sb func /\ P sa s G tn /\ ~s.vs_halted ==>
    ?t Gf tf.
      P sb t Gf tf /\ ~t.vs_halted /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tf)) /\
      LIST_REL (\op w. safe_operand sb op /\
        eval_operand op t = SOME w /\ op_taint tf op = {}) ops ws /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  Induct >> rpt gen_tac
  >- (simp[compile_log_saved_topics_def, comp_return_def] >>
      strip_tac >> gvs[] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[gas_origin_ptr_path_rules]) >>
  Cases_on `ws` >- simp[LIST_REL_def] >>
  rename1 `LIST_REL R (row::rows) (topic::remaining)` >>
  simp[LIST_REL_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_log_saved_topics ce (row::rows) sa = (ops,sb)`
    (qx_choosel_then [`topic_op`,`sm`,`rest`] strip_assume_tac o
     PURE_ONCE_REWRITE_RULE [compile_log_saved_topics_cons]) >>
  qpat_x_assum `ops = topic_op::rest` SUBST_ALL_TAC >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    (conj_tac
     >- (qpat_assum `compile_log_saved_topics ce [row] sa = _` (fn code =>
           ACCEPT_TAC (SIMP_RULE bool_ss [code, pairTheory.SND]
             (Q.SPECL [`[row]`,`ce`,`sa`] compile_log_saved_topics_ci_mono)))) >>
     qpat_assum `compile_log_saved_topics ce rows sm = _` (fn code =>
       ACCEPT_TAC (SIMP_RULE bool_ss [code, pairTheory.SND]
         (Q.SPECL [`rows`,`ce`,`sm`] compile_log_saved_topics_ci_mono)))) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  qpat_assum `!r w a b z Gz tz op.
      R r w /\ P a z Gz tz /\ ~z.vs_halted /\
      compile_log_saved_topics ce [r] a = ([op],b) /\ fn_has_code a b func ==> _`
    (qspecl_then [`row`,`topic`,`sa`,`sm`,`s`,`G`,`tn`,`topic_op`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tu`] strip_assume_tac) >>
  qpat_assum `!ws a b os z Gz tz.
      LIST_REL R rows ws /\ compile_log_saved_topics ce rows a = (os,b) /\
      fn_has_code a b func /\ P a z Gz tz /\ ~z.vs_halted ==> _`
    (qspecl_then [`remaining`,`sm`,`sb`,`rest`,`u`,`Gu`,`tu`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac) >>
  `safe_operand sb topic_op` by metis_tac[safe_operand_mono, ci_mono_def] >>
  `eval_operand topic_op t = SOME topic` by
    (irule eval_operand_frame >>
     conj_tac >- fs[safe_operand_def] >>
     qexistsl_tac [`sm`,`u`] >>
     fs[safe_operand_def] >> metis_tac[]) >>
  `op_taint tf topic_op = op_taint tu topic_op` by
    (qpat_assum `safe_operand sm topic_op` mp_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `topic_op` >> simp[safe_operand_def, op_taint_def] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]) >>
  `!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at sm x` by metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     asm_rewrite_tac[]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[LIST_REL_def]
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
  ~s.vs_call_ctx.cc_static /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
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
  qabbrev_tac `t = s with vs_logs := s.vs_logs ++
    [<|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
       data := mem_bytes_at (w2n off) (w2n len) s.vs_memory|>]` >>
  `step_inst_base inst s = OK t` by
    (mp_tac (Q.INST [`sz` |-> `len`] (SPEC_ALL log_emit_step)) >>
     (impl_tac >- simp[Abbr `inst`, mk_inst_def]) >> simp[Abbr `t`]) >>
  `ptr_inst_ok D 0 0 ctx func G tn inst s` by
    (mp_tac (Q.INST [`fn` |-> `func`, `id` |-> `sa.cs_next_id`,
       `fuel` |-> `0:num`, `n` |-> `len`, `off` |-> `off`,
       `vals` |-> `topics`, `t` |-> `t`]
       (Q.INST [`topics` |-> `topic_ops`, `len` |-> `len_op`,
                `pop` |-> `ptr_op`] (SPEC_ALL rawLogPtrInstTheory.log_inst_ok))) >>
     (impl_tac >-
       (fs[Abbr `inst`, Abbr `t`] >> rpt strip_tac >>
        gvs[ptr_covers_def, eval_operand_def] >> metis_tac[wordsTheory.w2n_eq_0])) >>
     simp[Abbr `inst`]) >>
  `run_inst_seq [inst] s = OK t` by
    (qpat_assum `step_inst_base inst s = OK t`
       (fn th => simp[Once run_inst_seq_def, th, Abbr `inst`, mk_inst_def,
                      is_terminator_def, run_inst_seq_def])) >>
  `step_prov PG G inst t = G /\ step_taint inst s t tn = tn` by
    simp[Abbr `inst`, Abbr `t`, log_ghost] >>
  `inst_seq_ptr D 0 ctx func PG G tn [inst] s G tn` by
    (drule_all inst_seq_ptr_singleton >>
     disch_then (qspec_then `PG` mp_tac) >> asm_simp_tac bool_ss []) >>
  `inst_seq_ptr D lo ctx func PG G tn [inst] s G tn` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule compile_log_emit_mem_ok >> metis_tac[]) >>
  `t = s with vs_logs := s.vs_logs ++
     [<|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
        data := mem_bytes_at (w2n off) (w2n len) s.vs_memory|>]` by
    simp[Abbr `t`] >>
  `inst_extends sa sb` by
    (qpat_assum `emit_inst LOG _ _ sa = _`
       (ACCEPT_TAC o MATCH_MP inst_extends_emit_inst)) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t` by
    (qpat_assum `emitted_insts sa sb = [inst]` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G tn` by
    (qpat_assum `emitted_insts sa sb = [inst]` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
                i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (qpat_assum `emitted_insts sa sb = [inst]` (fn code =>
       qpat_assum `inst.inst_opcode = LOG` (fn opcode =>
         simp_tac (srw_ss()) [code, opcode, is_terminator_def]))) >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sb = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (`EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sa sb)` by simp[] >>
     rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     qpat_x_assum `emitted_insts _ _ = _ ++ _` (fn code =>
       qpat_assum `EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts _ _)`
         (mp_tac o PURE_REWRITE_RULE [code])) >>
     simp[EVERY_APPEND]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G,tn)` suffices_by
    (qpat_assum `t = s with vs_logs := _`
       (fn th => simp_tac (srw_ss()) [th])) >>
  irule fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
  (conj_tac >- first_assum ACCEPT_TAC >>
   qexists_tac `sa` >> rpt conj_tac >> first_assum ACCEPT_TAC)

QED
