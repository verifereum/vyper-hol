(* Restatements of the local compile_ecrecover_run and
   compile_ecrecover_oracle_failure in exprSimPrecompilesScript.sml.
   Compiler splitting is shared below; semantic boundaries are reused. *)
Theory bodyMemBiECRecoverRun
Ancestors
  bodyMemBiECRecoverBuffers bodyMemBiECRecoverEncoding
  bodyMemBiECRecoverSuffix exprSimPrecompiles exprSimDefs exprSimProps
  exprSimWordArgs exprLoweringProps builtinMisc compileEnv context emitHelper
  venomExecSemantics venomState venomMemDefs venomCallOracleDefs
  extCallOracle valueEncoding words byte list rich_list
Libs
  monadsyntax

Theorem compile_ecrecover_split[local]:
  compile_ecrecover h v r sig sf = (res,sb) ==>
  ?ip op sm.
    (do ib <- context$compile_alloc_buffer 128;
        emit_void MSTORE [ib.buf_operand; h];
        p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [p1; v];
        p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [p2; r];
        p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
        emit_void MSTORE [p3; sig];
        ob <- context$compile_alloc_buffer 32;
        emit_void MSTORE [ob.buf_operand; Lit 0w];
        return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
        emit_void ASSERT [success]; emit_op MLOAD [op] od) sm = (res,sb) /\
    LENGTH sf.cs_current_insts <= LENGTH sm.cs_current_insts
Proof
  rewrite_tac[compile_ecrecover_prefix] >>
  pure_once_rewrite_tac[comp_bind_def] >>
  pure_rewrite_tac[LET_THM] >> pairarg_tac >> strip_tac >>
  rename1 `_ sf = (ipop,sm)` >> PairCases_on `ipop` >> fs[] >>
  rename1 `_ sf = ((ip,op),sm)` >>
  qpat_x_assum `(\(x,y). _) _ = _` mp_tac >>
  asm_rewrite_tac[] >> simp[pairTheory.UNCURRY_DEF] >> strip_tac >>
  qexistsl_tac [`ip`, `op`, `sm`] >>
  conj_tac >- gvs[comp_bind_def] >>
  conj_tac >- gvs[comp_bind_def] >>
  qpat_x_assum `_ sf = ((ip,op),sm)` mp_tac >>
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[]
QED

Theorem compile_ecrecover_run:
  compile_ecrecover h v r sig sf = (res,sb) /\
  s.vs_outcomes = co::rest /\ co.co_success /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sf x) ==>
  ?t. run_inst_seq (emitted_insts sf sb) s = OK t /\
    stmt_state_rel ctx func cenv cx (es with outcomes := SOME rest) t /\
    wb_frame cenv es sf s t /\
    eval_operand res t = SOME
      (typed_val_to_w256 (BaseTV AddressT)
        (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws) of
          NONE => 0w | SOME addr => addr)))
Proof
  strip_tac >> drule compile_ecrecover_split >> strip_tac >>
  drule ecrecover_suffix_shape >> strip_tac >>
  `!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[emitted_insts_def, rich_listTheory.DROP_APPEND] >> simp[]) >>
  drule_all ecrecover_buffers_run >> strip_tac >>
  rename1 `eval_operand ip t = SOME wi` >>
  `local_ptrs_reserved cenv sm /\
   sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id` by
    (drule_all ecrecover_buffers_prefix_shape >> strip_tac >> simp[] >> decide_tac) >>
  `(!y. ip = Var y ==> not_fresh_at sm y) /\
   (!y. op = Var y ==> not_fresh_at sm y)` by simp[] >>
  drule ecrecover_request_result >> strip_tac >>
  `?data. precompile_result (venom_call_request t 1w 0w wi 128w T).cr_target
      (venom_call_request t 1w 0w wi 128w T).cr_data = SOME (SOME data) /\
    mem_word_at (w2n po)
      (write_memory_with_expansion (w2n po) (TAKE 32 data) t).vs_memory =
      typed_val_to_w256 (BaseTV AddressT)
        (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws) of
          NONE => 0w | SOME addr => addr))` by
    (Cases_on `vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws)`
     >- (gvs[] >> drule ecrecover_output_write >>
         disch_then (qspecl_then [`[]`, `0w:address`] mp_tac) >> simp[]) >>
     rename1 `_ = SOME addr` >> gvs[] >> drule ecrecover_output_write >>
     disch_then (qspecl_then [`PAD_LEFT 0w 32 (word_to_bytes addr T)`, `addr`] mp_tac) >>
     simp[]) >>
  `t.vs_outcomes = co::rest` by
    (gvs[stmt_state_rel_def, state_rel_def]) >>
  drule_all ecrecover_suffix_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sb) t = OK tf` >>
  drule_all ecrecover_suffix_preserves >> strip_tac >>
  `LENGTH sf.cs_current_insts - LENGTH sm.cs_current_insts = 0` by decide_tac >>
  qexists_tac `tf` >> simp[] >>
  conj_tac
  >- (`emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb` by
        simp[emitted_insts_def, rich_listTheory.DROP_APPEND,
             arithmeticTheory.SUB_EQ_0] >>
      metis_tac[run_inst_seq_append]) >>
  conj_tac
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ (_ with outcomes := _) tf` mp_tac >> simp[]) >>
  irule wb_frame_trans >>
  conj_tac >- simp[] >>
  conj_tac >- (qexistsl_tac [`es`, `sf`, `t`] >> simp[]) >>
  qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]
QED

Theorem compile_ecrecover_oracle_failure:
  compile_ecrecover h v r sig sf = (res,sb) /\
  ~(?co rest. s.vs_outcomes = co::rest /\ co.co_success) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sf x) ==>
  ?u. run_inst_seq (emitted_insts sf sb) s = Abort Revert_abort u
Proof
  strip_tac >> drule compile_ecrecover_split >> strip_tac >>
  drule ecrecover_suffix_shape >> strip_tac >>
  `!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[emitted_insts_def, rich_listTheory.DROP_APPEND] >> simp[]) >>
  drule_all ecrecover_buffers_run >> strip_tac >>
  rename1 `eval_operand ip t = SOME wi` >>
  `~(?co rest. t.vs_outcomes = co::rest /\ co.co_success)` by
    (gvs[stmt_state_rel_def, state_rel_def]) >>
  `(!y. ip = Var y ==> not_fresh_at sm y) /\
   (!y. op = Var y ==> not_fresh_at sm y)` by simp[] >>
  drule_all ecrecover_suffix_oracle_failure >> strip_tac >>
  `LENGTH sf.cs_current_insts - LENGTH sm.cs_current_insts = 0` by decide_tac >>
  `emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb` by
    simp[emitted_insts_def, rich_listTheory.DROP_APPEND, arithmeticTheory.SUB_EQ_0] >>
  drule run_inst_seq_append >>
  disch_then (qspec_then `emitted_insts sm sb` mp_tac) >>
  simp[] >> metis_tac[]
QED
