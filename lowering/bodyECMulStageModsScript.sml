(* Linked ECMul staging at the reached operand cursor. *)
Theory bodyECMulStageMods
Ancestors
  bodyECMulLaunchCodeMods bodyECMulPayloadCutMods bodyECMulPayloadFrameMods
  bodyFullAllocaFresh bodyFullBuiltinECMulStagingCore
  compileEnv loweringStateRelDefs venomState venomInst

Theorem ecmul_stage_mods:
  compile_ecmul_point p scalar sf = (res,sb) /\
  gas_shadow_state sf shadow_sf /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sf sb func /\
  fn_has_code shadow_sf shadow_sb shadow_func /\
  compile_ecmul_point p scalar shadow_sf = (res,shadow_sb) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) ==>
  ?ib ca c1 c2 cpost ob sm src dst gv cv.
    compile_alloc_buffer 96 sf = (ib,ca) /\
    (do x <- emit_op ADD [p; Lit 0w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [y;v] od)
      ca = ((),c1) /\
    (do x <- emit_op ADD [p; Lit 32w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [y;v] od)
      c1 = ((),c2) /\
    (do y <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [y;scalar] od)
      c2 = ((),cpost) /\
    (do x <- emit_op ADD [p; Lit 0w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [y;v];
        x <- emit_op ADD [p; Lit 32w]; v <- emit_op MLOAD [x];
        y <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [y;v];
        y <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [y;scalar] od)
      ca = ((),cpost) /\
    compile_alloc_buffer 64 cpost = (ob,sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 7w; ib.buf_operand; Lit 96w; ob.buf_operand; Lit 64w];
        emit_void ASSERT [success]; return ob.buf_operand od) sm = (res,sb) /\
    gas_shadow_state sb shadow_sb /\
    ib.buf_operand = Var src /\ ob.buf_operand = Var dst /\ res = Var dst /\
    emitted_insts sf sm = emitted_insts sf ca ++ emitted_insts ca cpost ++
      emitted_insts cpost sm /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    cpost.cs_current_insts = ca.cs_current_insts ++ emitted_insts ca cpost /\
    sm.cs_current_insts = sf.cs_current_insts ++ emitted_insts sf sm /\
    sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
    same_blocks ca cpost /\ same_blocks sf sm /\ same_blocks sm sb /\
    ci_mono sf ca /\ ci_mono ca cpost /\ ci_mono cpost sm /\ ci_mono sm sb /\
    sf.cs_next_id < ca.cs_next_id /\
    cpost.cs_next_id = ca.cs_next_id + 10 /\
    cpost.cs_next_var = ca.cs_next_var + 7 /\
    cpost.cs_next_id < sm.cs_next_id /\
    sb.cs_next_id = sm.cs_next_id + 3 /\
    sb.cs_next_var = sm.cs_next_var + 2 /\
    fn_has_code sf ca func /\ fn_has_code ca cpost func /\
    fn_has_code cpost sm func /\ fn_has_code sm sb func /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 96w] [src]) (fn_insts func) /\
    MEM (mk_inst cpost.cs_next_id ALLOCA [Lit 64w] [dst]) (fn_insts func) /\
    local_ptrs_reserved cenv ca /\
    local_ptrs_reserved cenv cpost /\
    local_ptrs_reserved cenv sm /\
    not_fresh_at ca src /\ not_fresh_at sm src /\ not_fresh_at sm dst /\
    ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
    src <> gv /\ dst <> gv /\ dst <> cv /\ gv <> cv /\
    emitted_insts sm sb =
      [mk_inst sm.cs_next_id GAS [] [gv];
       mk_inst (sm.cs_next_id + 1) STATICCALL
         [Var gv; Lit 7w; Var src; Lit 96w; Var dst; Lit 64w] [cv];
       mk_inst (sm.cs_next_id + 2) ASSERT [Var cv] []] /\
    (!u. ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
         u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
      (func.fn_name,sm.cs_next_id) NOTIN gas_explicit_sites ctx shadow_ctx /\
      ?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
           isPREFIX (emitted_insts sm sb) (DROP u.vs_inst_idx bb.bb_instructions))
Proof
  strip_tac >>
  drule_all ecmul_launch_code_mods >>
  disch_then (qx_choosel_then
    [`ib`,`ca`,`c1`,`c2`,`cpost`,`ob`,`sm`,`src`,`dst`,`gv`,`cv`]
    strip_assume_tac) >>
  qexistsl_tac [`ib`,`ca`,`c1`,`c2`,`cpost`,`ob`,`sm`,`src`,`dst`,`gv`,`cv`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
