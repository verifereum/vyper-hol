(* Structural compiler certificate, shared by all nonliteral reason encoders. *)
Theory reasonEncoderLayoutPtr
Ancestors
  reasonFinishCode reasonMemoryEncoderPtr compilerChainCode exprLoweringProps
  loweringHalt emitHelperProps fragExec context compileEnv venomInst
  exprLowering stmtLowering
Libs wordsLib intLib

Theorem reason_encoder_layout_ptr:
  compile_revert_with_reason cenv vv mt m cc = ((),se) /\
  fn_has_code cc se func ==>
  ?buf payload tuple msg slot v1 v2 v3 v4 slotname
    c1 c2 c3 c4 cb d1 d2 d3 d4 sm sc sb.
    compile_alloc_buffer (64+m) cc = (buf,c1) /\
    emit_void MSTORE [buf.buf_operand;Lit 0x08c379a0w] c1 = ((),c2) /\
    emit_op ADD [buf.buf_operand;Lit 32w] c2 = (payload,c3) /\
    compile_alloc_buffer m c3 = (tuple,c4) /\
    unwrap_value cenv vv c4 = (msg,cb) /\
    emit_op MLOAD [msg] cb = (Var v1,d1) /\
    emit_op ADD [Var v1;Lit 31w] d1 = (Var v2,d2) /\
    emit_op AND [Var v2;Lit (i2w (-32))] d2 = (Var v3,d3) /\
    emit_op ADD [Lit 32w;Var v3] d3 = (Var v4,d4) /\
    emit_void MCOPY [tuple.buf_operand;msg;Var v4] d4 = ((),sm) /\
    compile_alloc_buffer 32 sm = (slot,sc) /\ slot.buf_operand = Var slotname /\
    emit_void MSTORE [Var slotname;Lit 32w] sc = ((),sb) /\
    reason_encode_finish buf.buf_operand payload tuple.buf_operand (Var slotname) sb = ((),se) /\
    fn_has_code cc c1 func /\ fn_has_code c1 c2 func /\
    fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\
    fn_has_code c4 cb func /\ fn_has_code cb d1 func /\
    fn_has_code d1 d2 func /\ fn_has_code d2 d3 func /\
    fn_has_code d3 d4 func /\ fn_has_code d4 sm func /\
    fn_has_code sm sc func /\ fn_has_code sc sb func /\ fn_has_code sb se func /\
    cb.cs_next_id <= sm.cs_next_id
Proof
  strip_tac >> drule compile_revert_reason_finish_split >> strip_tac >>
  `?v1 v2 v3 v4 slotname.
    len = Var v1 /\ rounded0 = Var v2 /\ rounded = Var v3 /\
    cnt = Var v4 /\ slot.buf_operand = Var slotname` by suspend "vars" >>
  `fn_has_code cc c1 func /\ fn_has_code c1 c2 func /\
    fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\
    fn_has_code c4 c5 func /\ fn_has_code c5 c6 func /\
    fn_has_code c6 c7 func /\ fn_has_code c7 c8 func /\
    fn_has_code c8 c9 func /\ fn_has_code c9 c10 func /\
    fn_has_code c10 c11 func /\ fn_has_code c11 c12 func /\
    fn_has_code c12 se func` by suspend "code" >>
  `c5.cs_next_id <= c10.cs_next_id` by suspend "ids" >>
  `(i2w (-32):bytes32) = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w`
    by EVAL_TAC >>
  qexistsl_tac [`buf`, `payload`, `tuple`, `msg`, `slot`,
    `v1`, `v2`, `v3`, `v4`, `slotname`, `c1`, `c2`, `c3`, `c4`,
    `c5`, `c6`, `c7`, `c8`, `c9`, `c10`, `c11`, `c12`] >>
  gvs[]
QED

Resume reason_encoder_layout_ptr[vars]:
  rpt (qpat_x_assum `emit_op _ _ _ = _` mp_tac) >>
  qpat_x_assum `compile_alloc_buffer 32 _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  drule compile_alloc_buffer_parts >> strip_tac >> metis_tac[]
QED

Resume reason_encoder_layout_ptr[code]:
  qpat_x_assum `fn_has_code cc se func` mp_tac >>
  qpat_x_assum `reason_encode_finish _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `emit_void _ _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  imp_res_tac compile_alloc_buffer_extends >>
  imp_res_tac reason_emit_op_cs_extends >> imp_res_tac reason_emit_void_cs_extends >>
  imp_res_tac reason_encode_finish_extends >>
  `cs_extends c4 c5` by
    (qspecl_then [`cenv`, `vv`, `c4`] mp_tac ci_mono_unwrap_value >>
     simp[ci_mono_def]) >>
  qspecl_then [`[c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;se]`, `cc`, `func`]
    mp_tac compiler_chain_has_code >> simp[]
QED

Resume reason_encoder_layout_ptr[ids]:
  rpt (qpat_x_assum `emit_op _ _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `emit_void _ _ _ = _` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  decide_tac
QED

Finalise reason_encoder_layout_ptr
