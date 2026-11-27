Theory bodyIntCallBufferHeadSpecMods
Ancestors
  bodyIntCallStagePacketMods bodyFullPredsMods bodyFullPostsMods
  exprSimFullBundleProps exprSimDefs gasOutcomeFullMods gasExplicitSites
  fragGasOriginPtr fragGasPath fragExec exprLowering context emitHelper
  gasShadow vyperInterpreter vyperState vyperTyping vyperStorageFootprint
  venomInst words

(* The compiler interval stops at cs, where the remaining arguments start. *)
Definition intcall_buffer_head_input_mods_def:
  intcall_buffer_head_input_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    mods exps src tops cenv cx env st0 (sa,es0,s0,G0,tn0) (si,esi,s,G,tn)
    pin (ops,ws,vals,ptys,pflags) e dty (shi,vv,ci,shci,buf,ca,opn,cu,cs) <=>
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env esi /\
  expr_body_pre_mods mods cenv cx env e esi /\ body_expr_full_ok_mods mods exps cx e /\
  type_memory_bytes cenv dty < 2 ** 64 /\
  type_widens_to (get_tenv cx) (expr_type e) dty /\
  (~is_word_type dty /\ ~is_bytestring_type dty ==>
    vv_type vv = lowered_value_type cenv e) /\
  compile_expr cenv (expr_type e) e si = (vv,ci) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shi = (vv,shci) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,ci,shi,shci) /\
  compile_alloc_buffer (MAX 32 (type_memory_bytes cenv dty)) ci = (buf,ca) /\
  unwrap_value cenv vv ca = (opn,cu) /\
  (if is_word_type dty then emit_void MSTORE [buf.buf_operand;opn]
   else if (case dty of BaseT (BytesT (Dynamic _)) => T
                       | BaseT (StringT _) => T | _ => F) then
     (do compile_store_bytestring opn buf.buf_operand; return () od)
   else compile_store_memory cenv opn buf.buf_operand dty (vv_type vv)) cu = ((),cs) /\
  fn_has_code ci ca func /\ fn_has_code ca cu func /\ fn_has_code cu cs func /\
  local_ptrs_reserved cenv si /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin /\
  intcall_stage_ops_mods (lo,func) cenv cx sa (si,esi,s,G,tn) pin
    (ops,ws,vals,ptys,pflags)
End

(* The successful callback carries the same marks through the physical suffix. *)
Definition intcall_buffer_head_success_mods_def:
  intcall_buffer_head_success_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    mods cenv cx env st0 (sa,es0,s0,G0,tn0) (si,esi,s,G,tn)
    pin (ops,ws,vals,ptys,pflags) e dty buf cs marks base v mid t Gf tf <=>
  (?raw. (!tail. eval_expr cx e
    (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL raw,mid with gas_obs := tail)) /\
    read_result cx raw mid = (INL v,mid)) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK t,Gf,tf)) /\
  gas_path ctx func s (LENGTH marks) (OK t) /\
  intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (cs,mid,t,Gf,tf) pin /\
  intcall_stage_ops_mods (lo,func) cenv cx sa (cs,mid,t,Gf,tf) pin
    (ops ++ [buf.buf_operand], ws ++ [n2w base], vals ++ [v],
     ptys ++ [dty], pflags ++ [F]) /\
  body_const_cells_agree_mods mods cx env mid /\ expr_sim_inv_mods mods cenv cx env mid /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)
End

(* The witness indexes the continuation result type, not the head value. *)
Definition intcall_buffer_head_rule_mods_def:
  intcall_buffer_head_rule_mods (ty : 'a itself) <=>
  !DF lo d ctx shadow_ctx PG func shadow_func mods exps src tops cenv cx env st0
   sa es0 s0 G0 tn0 si esi s G tn pin ops ws vals ptys pflags e dty
   shi vv ci shci buf ca opn cu cs
   (next : value -> evaluation_state -> ('a + vyperState$exception) # evaluation_state) P Q R.
    intcall_buffer_head_input_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      mods exps src tops cenv cx env st0 (sa,es0,s0,G0,tn0) (si,esi,s,G,tn)
      pin (ops,ws,vals,ptys,pflags) e dty (shi,vv,ci,shci,buf,ca,opn,cu,cs) /\
    gas_admissible (bind (bind (eval_expr cx e) (read_result cx)) next) P esi /\
    (!exc. P (INR exc) ==> expr_res_ok (INR exc)) /\
    (!v. storage_trace_frame (next v)) /\
    (!H exc ee gt r.
      expr_exit (INR exc : value + vyperState$exception) r /\
      halt_exit H cx ee (INR exc : value + vyperState$exception) r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==>
      R H (INR exc) ee gt r) /\
    (!marks base v mid t Gf tf.
      intcall_buffer_head_success_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        mods cenv cx env st0 (sa,es0,s0,G0,tn0) (si,esi,s,G,tn)
        pin (ops,ws,vals,ptys,pflags) e dty buf cs marks base v mid t Gf tf /\
      gas_admissible (next v) P mid ==>
      gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cenv.ce_modules cx st0 (next v) (mid,t,Gf,tf) Q R) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (bind (bind (eval_expr cx e) (read_result cx)) next)
      (esi,s,G,tn) Q R
End
