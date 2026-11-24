(* The array suffix starts only after the two linked prefix runs land. *)
Theory bodyWriteArrayPacketMods
Ancestors
  bodyWriteTargetStageMods bodyInvSplit exprSimHypsDefs vyperTypeExprSoundness
  targetSubscriptContinuation exprSimArrayIndex allocLimits loweringPosts
  gasOutcomeFullMods gasOutcomeFull fragGasOriginPtr gasShadow
  vyperStorageFootprint vyperInterpreter vyperState compileEnv venomState
  venomInst finite_map alist

(* Packet fields: run configuration; static types; original entry; code cuts;
   successful base endpoint; successful index/read endpoint. *)
Definition write_array_reached_mods_def[nocompute]:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,pv,t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) <=>
    contract_inv mods exps ctx cenv cx /\
    type_place_target env bt = SOME (Type (ArrayT et bd)) /\
    type_place_target env (SubscriptTarget bt e) = SOME vt /\
    alloc_limits_target cenv (SubscriptTarget bt e) /\
    write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (SubscriptTarget bt e) es st0 sa sb shadow_sa shadow_sb r s0 G0 tn0 /\
    compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
    lower_value compile_expr cenv (expr_type e) e sm = (iop,sn) /\
    target_subscript_suffix cenv e rb iop sn = (r,sb) /\
    ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
    fn_has_code sn sb func /\
    expr_sim_inv_mods mods cenv cx env es /\
    expr_sim_inv_mods mods cenv cx env mid1 /\
    expr_body_pre_mods mods cenv cx env e (mid1 with gas_obs := index_gas) /\
    expr_sim_inv_mods mods cenv cx env mid2 /\
    value_runtime_typed env (expr_type e) v /\
    eval_base_place cx bt (es with gas_obs := base_gas) = (INL pv,mid1) /\
    bind (eval_expr cx e) (read_result cx) (mid1 with gas_obs := index_gas) =
      (INL v,mid2) /\
    mid1.gas_obs = [] /\ mid2.gas_obs = [] /\
    storage_trace_domain cx st0 mid2.storage_trace /\
    gas_admissible (extend_place cx pv (ValueSubscript v)) target_res_ok mid2 /\
    ~t2.vs_halted /\
    (!H. valid_horizon cx st0 H mid2.storage_trace ==>
      write_target_post_mods H (DF H) lo d ctx func cenv cx bt
        es sa sm s0 mid1 pv (Type (ArrayT et bd)) rb G0 tn0 G1 tn1 t1 /\
      expr_post_mods H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\
      expr_store_bound cx (post_value_type cenv e) v iop t2 /\
      t2.vs_current_bb = sn.cs_current_bb /\
      t2.vs_inst_idx = LENGTH sn.cs_current_insts /\
      alloca_history func t2 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t2) /\
      t1.vs_alloca_next <= t2.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid2 G2 tn2 t2 /\
      ptr_val_ok cx (post_value_type cenv e) v iop G2 tn2 t2 /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e iop G2 t2) /\
      ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2)
End

Definition write_array_suffix_mods_def[nocompute]:
  write_array_suffix_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,pv,t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) <=>
    gas_outcome_full_mods
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (extend_place cx pv (ValueSubscript v)) (mid2,t2,G2,tn2)
      (\H res ee G tn t. ?child. res = INL child /\
        write_target_post_mods H (DF H) lo d ctx func cenv cx (SubscriptTarget bt e)
          es sa sb s0 ee child vt r G0 tn0 G tn t)
      (\H res ee gt q. expr_exit res q /\ halt_exit H cx ee res q /\
        (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s))
End

(* The tested length is supplied by the location-specific view. This frame
   does not say what source value was stored there, or that extension succeeds. *)
Definition write_array_select_frame_def[nocompute]:
  write_array_select_frame
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,pv,t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2))
    (loc,b,iw,nw) (t3,G3,tn3) <=>
    FST (SND rb) = SOME loc /\
    eval_operand (FST rb) t2 = SOME b /\ eval_operand iop t2 = SOME iw /\
    (!H. valid_horizon cx st0 H mid2.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t2,G2,tn2) []
        ((if idx_in_range (is_signed_type (expr_type e)) iw nw
          then OK t3 else Abort Revert_abort t3),G3,tn3)) /\
    tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\
    tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm /\
    (!x. not_fresh_at sn x ==>
      FLOOKUP G3 x = FLOOKUP G2 x /\ FLOOKUP tn3.t_var x = FLOOKUP tn2.t_var x /\
      FLOOKUP t3.vs_vars x = FLOOKUP t2.vs_vars x) /\
    (t3 with <|vs_vars := t2.vs_vars; vs_inst_idx := t2.vs_inst_idx|>) =
      (if idx_in_range (is_signed_type (expr_type e)) iw nw
       then t2 else revert_state (set_returndata [] t2)) /\
    (idx_in_range (is_signed_type (expr_type e)) iw nw ==>
      ~t3.vs_halted /\ t3.vs_current_bb = sb.cs_current_bb /\
      t3.vs_inst_idx = LENGTH sb.cs_current_insts /\
      sb.cs_current_bb = sn.cs_current_bb /\
      (?code. sb.cs_current_insts = sn.cs_current_insts ++ code /\
              EVERY (\i. i.inst_opcode <> ALLOCA) code) /\
      eval_operand (FST r) t3 = SOME
        ((if (case bd of Dynamic _ => T | _ => F) then b + n2w (word_scale loc) else b) +
         iw * n2w (elem_size_in_location cenv loc et)) /\
      op_prov G3 (FST r) = op_prov G2 (FST rb) /\ op_taint tn3 (FST r) = {})
End

Theorem write_array_reached_posts_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,pv,t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) /\
  valid_horizon cx st0 H mid2.storage_trace ==>
  write_target_post_mods H (DF H) lo d ctx func cenv cx bt
    es sa sm s0 mid1 pv (Type (ArrayT et bd)) rb G0 tn0 G1 tn1 t1 /\
  expr_post_mods H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid2 G2 tn2 t2 /\
  ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2
Proof
  simp[write_array_reached_mods_def] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem write_array_reached_immutable_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (ImmutablePlace owner id path),t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) /\
  valid_horizon cx st0 H mid2.storage_trace ==>
  target_root bt = TopLevelNameTarget (owner,id) /\
  cenv.ce_is_ctor /\ FST (SND rb) = SOME LocCode /\
  op_prov G1 (FST rb) = NONE /\
  ?off imms itv iv k ptv a.
    FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
    ALOOKUP mid1.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables owner imms) id = SOME (itv,iv) /\
    mem_path_offset itv path = SOME (k,ptv) /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME ptv /\
    evaluate_subscripts itv iv path = INL a /\
    eval_operand (FST rb) t1 = SOME (n2w (off+k)) /\
    (~target_through_dynarray cenv bt ==> fixed_shape_path itv path)
Proof
  strip_tac >> drule_all write_array_reached_posts_mods >> strip_tac >>
  drule write_target_immutable_view_mods >> simp[]
QED
