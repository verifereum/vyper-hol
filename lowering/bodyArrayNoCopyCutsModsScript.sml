(* The reached selection after the non-reading array base and forced index.
   Entry, compiler intervals, base run and index run are separate tuples:
   the selector preserves these witnesses rather than selecting new ones. *)
Theory bodyArrayNoCopyCutsMods
Ancestors
  bodyFullPostsMods exprSimSubscriptArrayFramed gasOutcomeFullMods
  gasShadow gasShadowState exprLowering compileEnv context
  vyperInterpreter vyperState vyperAST vyperTypeSystem vyperStorageFootprint

Definition array_nocopy_cut_mods_def[nocompute]:
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty obj idx et bd st0
      (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
      (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
      (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) <=>
    compile_expr cenv ty obj sa = (bvv,sm) /\
    lower_value compile_expr cenv ty idx sm = (iop,st2) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa =
      (bvv,shadow_sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr idx)
      shadow_sm = (iop,shadow_st2) /\
    loc = (case vv_location bvv of SOME l => l | NONE => LocMemory) /\
    compile_array_subscript (vv_operand bvv) iop
      (case bd of vyperAST$Fixed _ => F | vyperAST$Dynamic _ => T)
      (case bd of vyperAST$Fixed n => n | vyperAST$Dynamic _ => 0)
      (word_scale loc) (elem_size_in_location cenv loc et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) st2 = (dst,sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
    gas_shadow_state st2 shadow_st2 /\ gas_shadow_state sb shadow_sb /\
    fn_has_code sa sb func /\ fn_has_code sa sm func /\
    fn_has_code sm st2 func /\ fn_has_code st2 sb func /\
    fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\
    fn_has_code shadow_sm shadow_st2 shadow_func /\
    fn_has_code shadow_st2 shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
    local_ptrs_reserved cenv st2 /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    sm.cs_next_var <= st2.cs_next_var /\ sm.cs_next_id <= st2.cs_next_id /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    eval_expr cx obj (es with gas_obs := gs1) = (INL raw,mid) /\
    bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin) /\
    (!tail. eval_expr cx obj (es with gas_obs := gs1 ++ tail) =
              (INL raw,mid with gas_obs := tail)) /\
    (!tail. bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs2 ++ tail) =
              (INL key,fin with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    storage_trace_domain cx st0 fin.storage_trace /\
    mid.gas_obs = [] /\ fin.gas_obs = [] /\
    gas_admissible (select_result cx (ArrayT et bd) raw (ValueSubscript key)) expr_vv_res_ok fin /\
    ~s.vs_halted /\ ~it.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    it.vs_current_bb = st2.cs_current_bb /\ it.vs_inst_idx = LENGTH st2.cs_current_insts /\
    alloca_history func s /\ alloca_history func it /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s /\ allocas_below_fmp it) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= it.vs_alloca_next /\
    vv_store_bound cx (post_value_type cenv obj) (lowered_value_type cenv obj) mid raw bvv s /\
    ptr_vv_ok cx (post_value_type cenv obj) raw bvv mid G1 tn1 s /\
    (!v. raw = Value v /\ ~is_word_type (post_value_type cenv obj) /\
         ~is_bytestring_type (post_value_type cenv obj) ==>
         vv_own cenv cx (post_value_type cenv obj) sa sm mid raw bvv s /\
         (!t p. bvv = LocatedValue t p ==> p.ptr_location = LocMemory)) /\
    (cenv.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
     ?v. read_result cx raw mid = (INL v,mid) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv obj) = SOME rt /\
                eval_operand (vv_operand bvv) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn1.t_mem s.vs_memory mem ==>
                       val_in_memory rt v (w2n w) mem)) /\
    (!t op. bvv = StackValue t op /\ ~is_word_type (post_value_type cenv obj) ==>
            ptr_buf_ok cenv obj op G1 s) /\
    (!t p. bvv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
           ptr_buf_ok cenv obj p.ptr_operand G1 s) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
    expr_store_bound cx (post_value_type cenv idx) key iop it /\
    ptr_val_ok cx (post_value_type cenv idx) key iop Gi tni it /\
    (~is_word_type (post_value_type cenv idx) ==> ptr_buf_ok cenv idx iop Gi it) /\
    ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni /\
    (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace /\ valid_horizon cx st0 H es.storage_trace) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       vv_post_mods H ctx func cenv cx obj es sa sm s0 mid raw bvv s /\
       ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 s) /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
       expr_post_mods H ctx func cenv cx idx mid sm st2 s fin key iop it /\
       ghost_inv_at_mods (DF H) lo d cenv cx fin Gi tni it)
End

(* Only the selection remains to run, but its success post is relative to
   entry, not to the end of the key. *)
Definition array_select_outcome_mods_def[nocompute]:
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
      cenv cx ann obj idx et bd st0
      (es,s0,G0,tn0) (sa,sb,dst,loc) (raw,key) (fin,it,Gi,tni) <=>
    let e = Subscript ann obj idx;
        vv = LocatedValue ann (mk_ptr dst loc)
    in
      gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cenv.ce_modules cx st0
        (select_result cx (ArrayT et bd) raw (ValueSubscript key)) (fin,it,Gi,tni)
        (\H res ee G tn t. ?tv. res = INL tv /\
          vv_post_mods H ctx func cenv cx e es sa sb s0 ee tv vv t /\
          vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
          ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
          (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
               ~is_bytestring_type (post_value_type cenv e) ==>
               vv_own cenv cx (post_value_type cenv e) sa sb ee tv vv t /\
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
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
           (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
End

Theorem array_nocopy_cut_posts_mods:
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty obj idx et bd st0
      (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
      (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
      (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  valid_horizon cx st0 H fin.storage_trace ==>
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid raw bvv s /\
  expr_post_mods H ctx func cenv cx idx mid sm st2 s fin key iop it
Proof
  rewrite_tac[array_nocopy_cut_mods_def] >> strip_tac >>
  qpat_assum `!H. _ ==> valid_horizon _ _ H mid.storage_trace /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. _ ==> vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  asm_rewrite_tac[]
QED
