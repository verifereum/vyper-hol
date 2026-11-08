(* RawLog body simulation boundaries. *)
Theory bodySimRawLog
Ancestors
  bodySim exprSimSend exprSimHyps vyperTypeSystem vyperAST list
  exprSimAggregateSource vyperInterpreter vyperValue vyperState vyperContext
  exprSimWordArgs exprLowering compileEnv loweringStateRelDefs emitHelper venomExecSemantics
  exprLoweringProps venomState venomMemDefs exprSimDefs exprSimStack loweringPosts exprSimHypsDefs exprSimSource vyperEvent fragExec venomInst
  exprSimHash exprSimBuffer exprSimPrecompiles emitHelperProps ASCIInumbers exprSimRawLog
  bodySimRawLogSource bodySimRawLogBodySource bodySimRawLogTails bodySimRawLogTopics
Libs
  pairLib


Theorem raw_log_step_frame:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [sz; pop]) /\ LENGTH ops <= 4 /\
  eval_operand pop s = SOME off /\ eval_operand sz s = SOME len /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  TAKE (w2n len) (DROP (w2n off) s.vs_memory ++
    REPLICATE (w2n len) 0w) = bytes /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sa s0 s ==>
  ?t. step_inst_base inst s = OK t /\
    stmt_state_rel ctx func cenv cx
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bytes]) t /\
    wb_frame cenv es0 sa s0 t
Proof
  strip_tac >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all raw_log_step >>
  disch_then SUBST1_TAC >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  simp[encode_raw_event_values_def, encode_raw_event_def] >>
  conj_tac >- (irule raw_log_state_rel >> simp[]) >>
  irule raw_log_wb_frame >> simp[]
QED


Theorem raw_log_dynamic_tail_frag:
  emit_op MLOAD [data_op] sm = (len_op, s1) /\
  emit_op ADD [data_op; Lit 32w] s1 = (ptr_op, s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [len_op; ptr_op])) [] s2 = (u, sb) /\
  (!x. data_op = Var x ==> not_fresh_at sm x) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) ops /\
  LENGTH ops <= 4 /\
  eval_operand data_op s = SOME (n2w b) /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  mload b s = n2w (LENGTH bs) /\
  TAKE (LENGTH bs) (DROP (b + 32) s.vs_memory ++
    REPLICATE (LENGTH bs) 0w) = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  wb_frame cenv es0 sa s0 s /\ sa.cs_next_var <= sm.cs_next_var /\
  expr_type e = NoneT ==>
  frag_exec ctx sm sb ($= s)
    (expr_post ctx func cenv cx e es0 sa sb s0
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w))
    (expr_exit (INL NoneV))
Proof
  strip_tac >>
  `LENGTH ops < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  irule raw_log_dynamic_tail_core >>
  qpat_assum `emit_inst LOG _ _ _ = _` (irule_at Any) >>
  simp[] >> qexistsl_tac [`s1`, `data_op`, `b`] >> simp[]
QED


Theorem raw_log_fixed_tail_frag:
  emit_void MSTORE [ptr_op; data_op] sm = (u, s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [Lit 32w; ptr_op])) [] s1 = (u', sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand data_op s = SOME w /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\ LENGTH ops <= 4 /\
  LENGTH bs = 32 /\ TAKE 32 (word_to_bytes_be w) = bs /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sa s0 s /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,32) /\
  (!aid b sz. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n p) 32 b sz) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
     regions_disjoint (w2n p) 32 b sz) /\ expr_type e = NoneT ==>
  frag_exec ctx sm sb ($= s)
    (expr_post ctx func cenv cx e es0 sa sb s0
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w))
    (expr_exit (INL NoneV))
Proof
  strip_tac >>
  `LENGTH ops < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  Cases_on `u` >> Cases_on `u'` >> fs[] >>
  irule raw_log_fixed_tail_core >> simp[] >>
  qpat_assum `emit_inst LOG _ _ _ = _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED




