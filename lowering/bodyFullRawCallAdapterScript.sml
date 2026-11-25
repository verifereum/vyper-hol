(* Answer-independent contracts for assembling the memory raw-call VV proof.
   The endpoint sb is fixed: the two suppliers conclude at sa and s7. *)
Theory bodyFullRawCallAdapter
Ancestors
  bodyFullRawCallPrefix bodyFullRawCallFinishPost

Definition raw_call_vv_answer_post_def:
  raw_call_vv_answer_post (DF,lo,dframe,ctx,func) cenv cx e
    (es,sa,sb,s0,vv,G0,tn0) H (res : eval_result + vyperState$exception) ee G tn t <=>
    ?tv. res = INL tv /\
      vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo dframe cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
           ~is_bytestring_type (post_value_type cenv e) ==>
           vv_own cenv cx (post_value_type cenv e) sa sb ee (Value v) vv t /\
           (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                 eval_operand (vv_operand vv) t = SOME w ==>
                 w2n w + type_memory_size rt <= lo /\
                 (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                        val_in_memory rt val (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
               ptr_buf_ok cenv e op G t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
               ptr_buf_ok cenv e p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
End

Definition raw_call_vv_answer_exit_def:
  raw_call_vv_answer_exit ctx cx (H : (bool # bytes32 # type_value) list # num list)
    (res : eval_result + vyperState$exception) ee (gt : (string |-> (num # num)) # taint) r <=>
    expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !h. r = Halt h ==> allocas_below_fmp h)
End

Definition raw_call_vv_answer_rules_def:
  raw_call_vv_answer_rules A ctx <=>
    (!i source x Q R Q' R'.
       A i source x Q R /\
       (!H res ee G tn t. Q H res ee G tn t ==> Q' H res ee G tn t) /\
       (!H res ee gt r. R H res ee gt r ==> R' H res ee gt r) ==>
       A i source x Q' R') /\
    (!i source x Q R. A i source x Q R ==>
      A i source x Q (\H res ee gt r.
        R H res ee gt r /\
        (ctx_has_dalloca ctx ==> !h. r = Halt h ==> allocas_below_fmp h)))
End

(* The occurrence antecedent of expr_vv_sim_full, with a named interface
   upstream of the scoped consumers. *)
Definition raw_call_vv_pre_def:
  raw_call_vv_pre (DF,lo,dframe,ctx,shadow_ctx,(PG:(num # num) option list),func,shadow_func)
    cenv cx ty e es (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) <=>
    compile_expr cenv ty e sa = (vv,sb) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa = (vv,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
    return_buf_frame dframe cenv sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo dframe cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts
End

Definition raw_call_vv_prefix_rule_def:
  raw_call_vv_prefix_rule A
    (DF,lo,dframe,ctx,shadow_ctx,(PG:(num # num) option list),func,shadow_func)
    (tops,cenv,env,cx,ty,ann,flags,es)
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) <=>
  !a d kws addr data len ptr vo go ignored gas ov op result s1 s2 s3 s4 s5 s6 s7 xs k Q R.
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_exprs_full_ok cx (a::d::kws) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) NONE) es /\
    raw_call_vv_pre (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann (RawCallTarget flags) (a::d::kws) NONE) es
      (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
    lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
    lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
    emit_op MLOAD [data] s2 = (len,s3) /\
    emit_op ADD [data;Lit 32w] s3 = (ptr,s4) /\
    compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws s4 =
      ((vo,go,ignored),s5) /\
    lower_word_args cenv (K (BaseT (UintT 256))) kws s4 = (xs,s5) /\
    (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) /\
    compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
    compile_raw_call_finish addr ptr len gas (case vo of NONE=>Lit 0w | SOME v=>v)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
    (!av dv kvs. storage_trace_frame (k av dv kvs)) /\
    (!H exc ee gt r. expr_exit (INR exc : eval_result + vyperState$exception) r /\
      halt_exit H cx ee (INR exc : eval_result + vyperState$exception) r ==>
      R H (INR exc) ee gt r) /\
    (!gsA av esA gsD bs esD gsK kvs esK b ob gw tA tD t4 tk t7 G7 tn7.
      bind (eval_expr cx a) (read_result cx) (es with gas_obs:=gsA) = (INL av,esA) /\
      esA.gas_obs = [] /\
      bind (eval_expr cx d) (read_result cx) (esA with gas_obs:=gsD) =
        (INL (BytesV bs),esD) /\ esD.gas_obs = [] /\
      eval_exprs cx kws (esD with gas_obs:=gsK) = (INL kvs,esK) /\ esK.gas_obs = [] /\
      expr_sim_inv cenv cx env esK /\ storage_trace_domain cx st0 esK.storage_trace /\
      vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
      go = ext_call_kwarg EKGas flags.rcf_kws xs /\ ignored = NONE /\
      (!H. valid_horizon cx st0 H esK.storage_trace ==>
        expr_post H ctx func cenv cx a es sa s1 s0 esA av addr tA /\
        expr_post H ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
        expr_store_bound cx (post_value_type cenv d) (BytesV bs) data tD /\
        typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
        stmt_state_rel H ctx func cenv cx esK t7 /\
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx esK (FST H) /\
        expr_val_rel cx (BaseT AddressT) av addr t7 /\
        (!x w. MEM x xs /\ eval_operand x tk = SOME w ==> eval_operand x t7 = SOME w) /\
        eval_operand len t7 = SOME (n2w (LENGTH bs)) /\
        eval_operand ptr t7 = SOME (n2w (b+32)) /\ eval_operand gas t7 = SOME gw /\
        b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
        b+32+LENGTH bs <= t7.vs_alloca_next /\
        mem_bytes_at (b+32) (LENGTH bs) t7.vs_memory = bs /\
        (!mem. mem_agree_outside tn7.t_mem t7.vs_memory mem ==>
          mem_bytes_at (b+32) (LENGTH bs) mem = bs) /\
        EVERY (\x. op_taint tn7 x={})
          [addr;len;ptr;gas;(case vo of NONE=>Lit 0w | SOME v=>v)] /\
        EVERY (\x. op_prov G7 x=NONE) [addr;len] /\
        (LENGTH bs<>0 ==> ?base sz. op_prov G7 ptr=SOME(base,sz) /\
          base<=b+32 /\ b+32+LENGTH bs<=base+sz) /\
        eval_operand ov t7=SOME(n2w ob) /\
        eval_operand op t7=SOME(n2w(if flags.rcf_max_outsize=0 then ob else ob+32)) /\
        (flags.rcf_max_outsize=0 ==> ov=op) /\
        ob+(if flags.rcf_max_outsize=0 then 0
            else ((flags.rcf_max_outsize+31) DIV 32)*32+32)<dimword(:256) /\
        FLOOKUP t7.vs_allocas s6.cs_next_id=
          SOME(ob,if flags.rcf_max_outsize=0 then 0
                  else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
        op_prov G7 ov=SOME(ob,if flags.rcf_max_outsize=0 then 0
                              else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
        op_prov G7 op=SOME(ob,if flags.rcf_max_outsize=0 then 0
                              else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
        op_taint tn7 ov={} /\ op_taint tn7 op={} /\
        (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
          regions_disjoint ob (if flags.rcf_max_outsize=0 then 0
                               else ((flags.rcf_max_outsize+31) DIV 32)*32+32) lb sz) /\
        (cenv.ce_is_ctor ==> !name tv v off.
          FLOOKUP cenv.ce_module_vars (cenv.ce_module,name)=SOME(ImmutableLoc off) /\
          FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE=>FEMPTY
            | SOME imms=>get_source_immutables cenv.ce_module imms) name=SOME(tv,v) ==>
          regions_disjoint off (type_memory_size tv) ob
            (if flags.rcf_max_outsize=0 then 0
             else ((flags.rcf_max_outsize+31) DIV 32)*32+32)) /\
        wb_frame cenv es esK sa s0 t7 /\ return_buf_frame dframe cenv sa t7 /\
        ~t7.vs_halted /\ t7.vs_current_bb=s7.cs_current_bb /\
        t7.vs_inst_idx=LENGTH s7.cs_current_insts /\ alloca_history func t7 /\
        s0.vs_alloca_next<=t7.vs_alloca_next /\ lo<=t7.vs_alloca_next /\ allocas_from lo t7 /\
        ghost_inv_at (DF H) lo dframe cenv cx esK G7 tn7 t7 /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G7 tn7 /\
        EVERY (safe_operand s7)
          [addr;len;ptr;gas;(case vo of NONE=>Lit 0w | SOME v=>v);ov;op] /\
        (!x. MEM (Var x)
          [addr;len;ptr;gas;(case vo of NONE=>Lit 0w | SOME v=>v);ov;op] ==>
          not_fresh_at s7 x)) ==>
      A s7 (k av (BytesV bs) kvs) (esK,t7,G7,tn7) Q R) ==>
    A sa (bind (bind (eval_expr cx a) (read_result cx)) (\av.
      bind (bind (eval_expr cx d) (read_result cx)) (\dv.
        bind (eval_exprs cx kws) (k av dv)))) (es,s0,G0,tn0) Q R
End

Definition raw_call_vv_request_rule_def:
  raw_call_vv_request_rule A (DF,lo,dframe,ctx,func)
    (cenv,env,cx,flags,st0) (es,sa,sb,s0,G0,tn0) <=>
  !e vv amount esK s6 sout s7 ov op addr dp len gas xs result t7 G7 tn7
     target gw kvs ib bs ob.
    expr_has_effect e /\ post_value_type cenv e = expr_type e /\
    lowered_value_type cenv e = expr_type e /\
    expr_type e = raw_call_return_type flags /\ type_alloc_ok cenv (expr_type e) /\
    ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
    (flags.rcf_is_delegate ==> amount = 0) /\
    (flags.rcf_is_static ==> amount = 0) /\
    amount < dimword (:256) /\ flags.rcf_max_outsize < dimword (:256) /\
    expr_sim_inv cenv cx env esK /\ esK.gas_obs = [] /\
    storage_trace_domain cx st0 esK.storage_trace /\
    fn_has_code sa sb func /\ fn_has_code s6 sout func /\ fn_inst_ids_distinct func /\
    ci_mono sa s6 /\ ci_mono s6 s7 /\ ci_mono sout s7 /\ ci_mono sa s7 /\
    compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),sout) /\
    compile_raw_call_finish addr dp len gas
      (case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME p => p)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
    vv = (if flags.rcf_max_outsize = 0
          then StackValue (raw_call_return_type flags) result
          else LocatedValue (raw_call_return_type flags) (mk_ptr result LocMemory)) /\
    local_ptrs_reserved cenv sa /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!H. valid_horizon cx st0 H esK.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
    (!H. valid_horizon cx st0 H esK.storage_trace ==>
      stmt_state_rel H ctx func cenv cx esK t7 /\
      storage_well_formed_on cx esK (FST H) /\
      ghost_inv_at (DF H) lo dframe cenv cx esK G7 tn7 t7) /\
    return_buf_frame dframe cenv sa t7 /\
    wb_frame cenv es esK sa s0 t7 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G7 tn7 /\
    ~t7.vs_halted /\ t7.vs_current_bb = s7.cs_current_bb /\
    t7.vs_inst_idx = LENGTH s7.cs_current_insts /\ alloca_history func t7 /\
    s0.vs_alloca_next <= t7.vs_alloca_next /\ lo <= t7.vs_alloca_next /\ allocas_from lo t7 /\
    eval_operand addr t7 = SOME (w2w target) /\
    eval_operand (case ext_call_kwarg EKValue flags.rcf_kws xs of
        NONE => Lit 0w | SOME p => p) t7 = SOME (n2w amount) /\
    eval_operand gas t7 = SOME gw /\
    (!g. OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV = SOME g ==>
         g = w2n gw) /\
    eval_operand dp t7 = SOME (n2w ib) /\ eval_operand len t7 = SOME (n2w (LENGTH bs)) /\
    ib < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    (LENGTH bs = 0 \/ ib + LENGTH bs <= t7.vs_alloca_next \/
     ctx_has_dalloca ctx /\
     w2n t7.vs_initial_fmp <= ib /\ ib + LENGTH bs <= w2n t7.vs_fmp) /\
    read_memory ib (LENGTH bs) t7 = bs /\
    (!j. ib <= j /\ j < ib + LENGTH bs ==> j NOTIN tn7.t_mem) /\
    (bs <> [] ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs)) /\
    eval_operand ov t7 = SOME (n2w ob) /\
    eval_operand op t7 = SOME (n2w (if flags.rcf_max_outsize = 0 then ob else ob + 32)) /\
    (flags.rcf_max_outsize = 0 ==> ov = op) /\
    ob + (if flags.rcf_max_outsize = 0 then 0
        else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32) < dimword (:256) /\
    FLOOKUP t7.vs_allocas s6.cs_next_id = SOME (ob,(if flags.rcf_max_outsize = 0 then 0
        else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
    op_prov G7 ov = SOME (ob,(if flags.rcf_max_outsize = 0 then 0
        else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
    op_prov G7 op = SOME (ob,(if flags.rcf_max_outsize = 0 then 0
        else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
    op_taint tn7 ov = {} /\ op_taint tn7 op = {} /\
    (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
      regions_disjoint ob (if flags.rcf_max_outsize = 0 then 0
                           else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32) lb sz) /\
    (cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) ob (if flags.rcf_max_outsize = 0 then 0
        else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
    EVERY (\x. op_taint tn7 x = {})
      [addr;len;dp;gas;(case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME p => p)] /\
    EVERY (safe_operand s7)
      [addr;len;dp;gas;(case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME p => p);ov;op] /\
    (!x. MEM (Var x)
      [addr;len;dp;gas;(case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME p => p);ov;op] ==>
      not_fresh_at s7 x) ==>
    A s7 (eval_raw_call cx flags target bs amount (ext_call_kwarg EKGas flags.rcf_kws kvs))
      (esK,t7,G7,tn7)
      (raw_call_vv_answer_post (DF,lo,dframe,ctx,func) cenv cx e (es,sa,sb,s0,vv,G0,tn0))
      (raw_call_vv_answer_exit ctx cx)
End

Theorem raw_call_vv_answer_exit_fun:
  raw_call_vv_answer_exit ctx cx = (\H res ee gt r.
    (expr_exit res r /\ halt_exit H cx ee res r) /\
    (ctx_has_dalloca ctx ==> !h. r = Halt h ==> allocas_below_fmp h))
Proof
  simp[FUN_EQ_THM, raw_call_vv_answer_exit_def, CONJ_ASSOC]
QED

Theorem raw_call_vv_answer_basic_exit:
  raw_call_vv_answer_rules A ctx /\
  A i source x Q (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r) ==>
  A i source x Q (raw_call_vv_answer_exit ctx cx)
Proof
  rw[raw_call_vv_answer_rules_def] >>
  first_x_assum (drule_then mp_tac) >>
  simp[raw_call_vv_answer_exit_fun]
QED
