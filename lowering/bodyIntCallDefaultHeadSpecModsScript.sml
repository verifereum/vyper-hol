(* Selected internal defaults use selected source typing but keep the caller's
   compiler environment on every machine cut. *)
Theory bodyIntCallDefaultHeadSpecMods
Ancestors
  bodyIntCallDefaultReadCutMods bodyIntCallStagePacketMods
  bodyFullPostsMods bodyFullPredsMods exprSimFullBundleProps exprSimDefs
  exprSimHypsDefs gasOutcomeFullMods fragGasOriginPtr fragGasPath fragExec
  exprLowering context compileEnv emitHelper gasShadow
  vyperTypeContract supportedExprTraverse constSubstMods vyperInterpreter
  vyperState vyperTyping vyperStorageFootprint venomInst list

(* Keep the full selected slice fixed, even when executing a strict child of
   a default expression or staging only the remaining suffix of the list. *)
Definition intcall_default_slice_mods_def[nocompute]:
  intcall_default_slice_mods mods ce p ed src tops ds <=>
    get_module_code p src = SOME tops /\
    (?name mut nr args dflts ret ss nargs.
      lookup_callable_function p.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
      EVERY (runtime_constant_expr mods) (DROP (LENGTH dflts - (LENGTH args - nargs)) dflts) /\
      ds = DROP (LENGTH dflts - (LENGTH args - nargs))
             (subst_consts_exprs_mods (consts_env_mods mods) dflts)) /\
    EVERY (runtime_constant_expr mods) ds /\
    ~supported_exprs_exists (const_name_root_mods mods) ds /\
    ~supported_exprs_exists (unallocated_bare_global_root ce ed) ds
End

Definition intcall_default_cut_ready_mods_def[nocompute]:
  intcall_default_cut_ready_mods (DF,lo,d,ctx,func) ce p st0 origin
    (si,esi,s,G,tn) pin <=>
    intcall_stage_frame_mods (DF,lo,d,ctx,func) ce p st0 origin (si,esi,s,G,tn) pin /\
    local_ptrs_reserved ce si /\
    (!H. dead_lo_ok_mods H (DF H) lo ce p) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
    (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0)
End

(* The raw success post is the linked value post, at the expression cut ci
   before forcing or allocating. It has no selected-pin physical hypothesis. *)
Definition intcall_default_raw_post_mods_def[nocompute]:
  intcall_default_raw_post_mods (DF,lo,d,ctx,func) ce p e vv
    (si,esi,s,G,tn) ci H res mid Gu tu u <=>
    ?raw. res = INL raw /\
      vv_post_mods H ctx func ce p e esi si ci s mid raw vv u /\
      vv_store_bound p (post_value_type ce e) (lowered_value_type ce e) mid raw vv u /\
      expr_sim_full_endpoint func ci s u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      ghost_inv_at_mods (DF H) lo d ce p mid Gu tu u /\
      ptr_vv_ok p (post_value_type ce e) raw vv mid Gu tu u /\
      (!v. raw = Value v /\ ~is_word_type (post_value_type ce e) /\
           ~is_bytestring_type (post_value_type ce e) ==>
           vv_own ce p (post_value_type ce e) si ci mid raw vv u /\
           (!ann ptr. vv = LocatedValue ann ptr ==> ptr.ptr_location = LocMemory)) /\
      (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        ?v. read_result p raw mid = (INL v,mid) /\
          !rt w. evaluate_type (get_tenv p) (post_value_type ce e) = SOME rt /\
            eval_operand (vv_operand vv) u = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
              val_in_memory rt v (w2n w) mem)) /\
      (!ann opn. vv = StackValue ann opn /\ ~is_word_type (post_value_type ce e) ==>
        ptr_buf_ok ce e opn Gu u) /\
      (!ann ptr. vv = LocatedValue ann ptr /\ ptr.ptr_location = LocMemory ==>
        ptr_buf_ok ce e ptr.ptr_operand Gu u) /\
      ghost_kept_at lo ce esi si G tn s Gu tu
End

(* Immutable occurrences use intcall_default_qualified_immutable_read_cut_mods
   at their reached cut, not a read certificate assumed for an arbitrary state. *)
Definition intcall_default_raw_rule_for_mods_def[nocompute]:
  intcall_default_raw_rule_for_mods mods e <=>
    !DF lo d ctx shadow_ctx PG func shadow_func exps ce p ed src tops ds
     st0 origin pin si shi ci shci esi s G tn ty vv.
      let cd = ce with ce_module := src in
      intcall_default_slice_mods mods ce p ed src tops ds /\
      runtime_constant_expr mods e /\ supported_exprs_exists ($= e) ds /\
      contract_inv mods exps ctx cd p /\ module_body_inv mods src tops cd p /\
      shadow_body_inv_mods mods exps ctx shadow_ctx /\
      expr_body_pre_mods mods cd p ed e esi /\ body_const_cells_agree mods p ed esi /\
      compile_expr ce ty e si = (vv,ci) /\
      compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) shi = (vv,shci) /\
      expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,ci,shi,shci) /\
      intcall_default_cut_ready_mods (DF,lo,d,ctx,func) ce p st0 origin (si,esi,s,G,tn) pin /\
      gas_admissible (eval_expr p e) expr_vv_res_ok esi ==>
      gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        ce.ce_modules p st0 (eval_expr p e) (esi,s,G,tn)
        (intcall_default_raw_post_mods (DF,lo,d,ctx,func) ce p e vv (si,esi,s,G,tn) ci)
        (\H res ee gt r. expr_exit res r /\ halt_exit H p ee res r /\
          (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
End

(* Stack and buffer heads share the same callback. The head's physical
   suffix does not consume additional source observations. *)
Definition intcall_default_head_success_mods_def[nocompute]:
  intcall_default_head_success_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    mods ce p ed src st0 (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin
    (ops,ws,vals,ptys,pflags) (e,dty,flag,opn,cs) marks w v mid t Gf tf <=>
    (?raw. (!tail. eval_expr p e
      (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL raw,mid with gas_obs := tail)) /\
      read_result p raw mid = (INL v,mid)) /\
    (!tail. bind (eval_expr p e) (read_result p)
      (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain p st0 mid.storage_trace /\
    (!H. valid_horizon p st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,Gf,tf)) /\
    gas_path ctx func s (LENGTH marks) (OK t) /\
    intcall_stage_frame_mods (DF,lo,d,ctx,func) ce p st0
      (sa,es0,s0,G0,tn0) (cs,mid,t,Gf,tf) pin /\
    intcall_stage_ops_mods (lo,func) ce p sa (cs,mid,t,Gf,tf) pin
      (ops ++ [opn],ws ++ [w],vals ++ [v],ptys ++ [dty],pflags ++ [flag]) /\
    expr_sim_inv_mods mods (ce with ce_module := src) p ed mid /\
    body_const_cells_agree mods p ed mid /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)
End

(* The type witness indexes the continuation, not the staged value. Both
   compiler equations stop at the first cursor of the remaining arguments. *)
Definition intcall_default_head_rule_mods_def[nocompute]:
  intcall_default_head_rule_mods (ty : 'a itself) flag <=>
    !DF lo d ctx shadow_ctx PG func shadow_func mods exps ce p ed src tops ds
     st0 sa es0 s0 G0 tn0 si shi cs shcs esi s G tn pin ops ws vals ptys pflags e dty opn
     (next : value -> evaluation_state -> ('a + vyperState$exception) # evaluation_state) P Q R.
      let cd = ce with ce_module := src in
      intcall_default_slice_mods mods ce p ed src tops ds /\ MEM e ds /\
      contract_inv mods exps ctx cd p /\ module_body_inv mods src tops cd p /\
      shadow_body_inv_mods mods exps ctx shadow_ctx /\
      expr_body_pre_mods mods cd p ed e esi /\ body_const_cells_agree mods p ed esi /\
      type_widens_to (get_tenv p) (expr_type e) dty /\
      (flag ==> is_word_type dty) /\
      (~flag ==> type_memory_bytes ce dty < 2 ** 64 /\
        (!vv ci. compile_expr ce (expr_type e) e si = (vv,ci) /\
          ~is_word_type dty /\ ~is_bytestring_type dty ==>
          vv_type vv = lowered_value_type ce e)) /\
      compile_stage_intcall_args compile_expr ce [e] [flag] [dty] si = ([opn],cs) /\
      compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
        [gas_shadow_expr e] [flag] [dty] shi = ([opn],shcs) /\
      expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,cs,shi,shcs) /\
      intcall_default_cut_ready_mods (DF,lo,d,ctx,func) ce p st0
        (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin /\
      intcall_stage_ops_mods (lo,func) ce p sa (si,esi,s,G,tn) pin (ops,ws,vals,ptys,pflags) /\
      gas_admissible (bind (bind (eval_expr p e) (read_result p)) next) P esi /\
      (!exc. P (INR exc) ==> expr_res_ok (INR exc)) /\
      (!v. storage_trace_frame (next v)) /\
      (!H exc ee gt r. expr_exit (INR exc : value + vyperState$exception) r /\
        halt_exit H p ee (INR exc : value + vyperState$exception) r /\
        (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==>
        R H (INR exc) ee gt r) /\
      (!marks w v mid t Gf tf.
        intcall_default_head_success_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
          mods ce p ed src st0 (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin
          (ops,ws,vals,ptys,pflags) (e,dty,flag,opn,cs) marks w v mid t Gf tf /\
        gas_admissible (next v) P mid ==>
        gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          ce.ce_modules p st0 (next v) (mid,t,Gf,tf) Q R) ==>
      gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        ce.ce_modules p st0 (bind (bind (eval_expr p e) (read_result p)) next)
        (esi,s,G,tn) Q R
End

Theorem default_raw_caller_cut[local]:
  intcall_default_raw_post_mods (DF,lo,d,ctx,func) ce p e vv
    (si,esi,s,G,tn) ci H res mid Gu tu u ==>
  (?raw. res = INL raw /\ vv_post_mods H ctx func ce p e esi si ci s mid raw vv u) /\
  u.vs_current_bb = ci.cs_current_bb /\ u.vs_inst_idx = LENGTH ci.cs_current_insts /\
  ghost_inv_at_mods (DF H) lo d ce p mid Gu tu u /\ ghost_kept_at lo ce esi si G tn s Gu tu
Proof
  simp[intcall_default_raw_post_mods_def, expr_sim_full_endpoint_def] >>
  strip_tac >> simp[]
QED

Theorem default_head_tail_packet[local]:
  intcall_default_head_success_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    mods ce p ed src st0 (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin
    (ops,ws,vals,ptys,pflags) (e,dty,flag,opn,cs) marks w v mid t Gf tf ==>
  intcall_stage_frame_mods (DF,lo,d,ctx,func) ce p st0
    (sa,es0,s0,G0,tn0) (cs,mid,t,Gf,tf) pin /\
  intcall_stage_ops_mods (lo,func) ce p sa (cs,mid,t,Gf,tf) pin
    (ops ++ [opn],ws ++ [w],vals ++ [v],ptys ++ [dty],pflags ++ [flag]) /\
  LENGTH (ops ++ [opn]) = SUC (LENGTH ops)
Proof
  simp[intcall_default_head_success_mods_def]
QED
