(* Certificates for the loop between Concat's allocation and final length store. *)
Theory bodyConcatCutsMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  exprSimFullBundleProps exprLowering exprSimMemDefs loweringPosts
  loweringStateRelDefs bodyPtrDefs ptrDiscipline compileEnv context
  gasOutcomeFullMods fragGasOriginPtr gasExplicitSites gasSummary
  exprSimDefs vyperStorageFootprint vyperInterpreter vyperState vyperAST
  vyperContext vyperValue vyperTyping venomState venomInst finite_map pred_set words list pair
Libs monadsyntax

Definition concat_payload_mods_def:
  concat_payload_mods v =
    case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []
End

(* The state tuple is (source, compile cursor, machine, provenance, taint).
   The counter is a separate allocation; it holds the logical byte count. *)
Definition concat_live_mods_def[nocompute]:
  concat_live_mods (func,cenv,lo) ((dv,ov,ow,binst,oinst,B,bsz) :
       string # string # bytes32 # instruction # instruction # num # num)
      (es,sa,s,G,tn) bs <=>
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
    lookup_var dv s = SOME (n2w (B+32)) /\ lookup_var ov s = SOME ow /\
    not_fresh_at sa dv /\ not_fresh_at sa ov /\
    MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
    binst.inst_id < sa.cs_next_id /\ FLOOKUP s.vs_allocas binst.inst_id = SOME (B,bsz) /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    oinst.inst_id < sa.cs_next_id /\ FLOOKUP s.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
    (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
       (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
    (B+bsz <= w2n ow \/ w2n ow+64 <= B) /\
    B+bsz < dimword (:256) /\ w2n ow+64 < dimword (:256) /\
    B+bsz <= s.vs_alloca_next /\ w2n ow+64 <= s.vs_alloca_next /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ lo <= B /\ lo <= w2n ow /\
    ptr_covers G tn dv s (bsz-32) /\ ptr_covers G tn ov s 32 /\
    (!i. B+32 <= i /\ i < B+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem) /\
    mload (w2n ow) s = n2w (LENGTH bs) /\
    mem_bytes_at (B+32) (LENGTH bs) s.vs_memory = bs /\ 32+LENGTH bs <= bsz
End

(* Until the final length write, the two loop-owned allocations are
   excluded from the byte frame, not from the old allocation map. *)
Definition concat_old_frame_mods_def[nocompute]:
  concat_old_frame_mods (func,cenv,lo,pure) ((dv,ov,ow,binst,oinst,B,bsz) :
       string # string # bytes32 # instruction # instruction # num # num)
      (es,sa,s,G,tn) (ee,sb,t,G',tn') <=>
    sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ghost_kept_at lo cenv es sa G tn s G' tn' /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    (!name lb lsz. local_region cenv ee.scopes t name lb lsz <=>
                   local_region cenv es.scopes s name lb lsz) /\
    (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==> lookup_var z t = SOME w) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
    (!aid p n. FLOOKUP s.vs_allocas aid = SOME (p,n) /\ aid < sa.cs_next_id /\
       (p+n <= B \/ B+bsz <= p) /\ (p+n <= w2n ow \/ w2n ow+64 <= p) /\
       (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
                     p+n <= lb \/ lb+lsz <= p) ==>
       mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory) /\
    locals_kept cenv es ee s t /\
    (pure ==>
      (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
         mem_bytes_at lb lsz t.vs_memory = mem_bytes_at lb lsz s.vs_memory) /\
      (!p n. (p+n <= B \/ B+bsz <= p) /\ (p+n <= w2n ow \/ w2n ow+64 <= p) /\
         (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
            sa.cs_next_id <= inst.inst_id /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
            regions_disjoint p n b sz) ==>
         mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory))
End

(* The fixed arm can write beyond the new logical prefix (a padded
   MSTORE). Neither arm changes memory outside the two scratch windows. *)
Definition concat_copy_effect_mods_def[nocompute]:
  concat_copy_effect_mods (ctx,func,cenv,cx,lo,d) ((dv,ov,ow,binst,oinst,B,bsz) :
       string # string # bytes32 # instruction # instruction # num # num)
      (es,sa,s,G,tn) (sb,u,G',tn') bs added <=>
    ~u.vs_halted /\ expr_sim_full_endpoint func sb s u /\
    (!z. not_fresh_at sa z ==>
       lookup_var z u = lookup_var z s /\ FLOOKUP G' z = FLOOKUP G z /\
       op_taint tn' (Var z) = op_taint tn (Var z)) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
    u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables /\
    u.vs_data_section = s.vs_data_section /\
    tn'.t_mem SUBSET tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!i. B+32+LENGTH bs <= i /\ i < B+32+LENGTH bs+LENGTH added ==>
         i NOTIN tn'.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn'.t_mem) /\
    mem_bytes_at (B+32) (LENGTH bs+LENGTH added) u.vs_memory =
      mem_bytes_at (B+32) (LENGTH bs) s.vs_memory ++ added /\
    mload (w2n ow) u = n2w (LENGTH bs+LENGTH added) /\
    (!p n. (p+n <= B \/ B+bsz <= p) /\ (p+n <= w2n ow \/ w2n ow+64 <= p) ==>
       mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory) /\
    (!(H : (bool # bytes32 # type_value) list # num list).
       stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es u) /\
    (!D. ghost_inv_at D lo d cenv cx es G tn s ==> ghost_inv_at D lo d cenv cx es G' tn' u) /\
    (!sa0 G0 tn0 s0. ghost_kept_at lo cenv es sa0 G0 tn0 s0 G tn /\
       (!z. not_fresh_at sa0 z ==> not_fresh_at sa z) ==>
       ghost_kept_at lo cenv es sa0 G0 tn0 s0 G' tn')
End

Definition concat_infos_mods_def:
  concat_infos_mods args =
    MAP (\e. if is_bytestring_type (expr_type e) then (T,0:num)
             else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m)
                      | _ => (F,32:num)) args
End

Definition concat_loop_code_mods_def[nocompute]:
  concat_loop_code_mods (ctx,shadow_ctx,func,shadow_func) cenv
      ((dv,ov,ow,binst,oinst,B,bsz) :
       string # string # bytes32 # instruction # instruction # num # num) args (sa,sb,shadow_sa,shadow_sb) <=>
    compile_concat compile_expr cenv args (Var dv) (concat_infos_mods args)
      (Var ov) sa = ((),sb) /\
    compile_concat compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr args)
      (Var dv) (concat_infos_mods args) (Var ov) shadow_sa = ((),shadow_sb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb)
End

Definition concat_horizon_mods_def[nocompute]:
  concat_horizon_mods (ctx,func,cenv,cx,lo,d)
      (H : (bool # bytes32 # type_value) list # num list,D)
      (es,sa : compile_state,s,G,tn) <=>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods D lo d cenv cx es G tn s
End

(* Only the last conjunct is horizon-indexed. The machine cursor, the
   scratch resources and the protection relative to the anchor are fixed. *)
Definition concat_loop_entry_mods_def[nocompute]:
  concat_loop_entry_mods (mods,exps,cx,env,src,tops,st0,cenv,pure)
      (DF,lo,d,ctx,shadow_ctx,PG : (num # num) option list,func,shadow_func) scratch anchor
      args (sb,shadow_sa,shadow_sb) (es,sa,s,G,tn) bs P <=>
    concat_loop_code_mods (ctx,shadow_ctx,func,shadow_func) cenv scratch
      args (sa,sb,shadow_sa,shadow_sb) /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\ expr_sim_inv_mods mods cenv cx env es /\
    (!e ee. MEM e args /\ expr_sim_inv_mods mods cenv cx env ee ==>
       expr_body_pre_mods mods cenv cx env e ee) /\
    body_exprs_full_ok_mods mods exps cx args /\
    EVERY (\e. is_bytestring_type (expr_type e) \/
                ?m. expr_type e = BaseT (BytesT (Fixed m))) args /\
    (pure ==> ~EXISTS expr_has_effect args) /\
    concat_live_mods (func,cenv,lo) scratch (es,sa,s,G,tn) bs /\
    concat_old_frame_mods (func,cenv,lo,pure) scratch anchor (es,sa,s,G,tn) /\
    (let (_,_,_,_,_,_,bsz) = scratch in
       LENGTH bs <= P /\
       32+P+SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
       32+concat_data_bound P (MAP expr_type args) <= bsz) /\
    local_ptrs_reserved cenv sa /\ return_buf_frame d cenv sa s /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,DF H) (es,sa,s,G,tn))
End

Definition concat_head_post_mods_def[nocompute]:
  concat_head_post_mods (DF,lo,d,ctx,func,cenv,cx) e (es,sa,s,G,tn)
      (op,sc) H (res : value + vyperState$exception) ee g ts t <=>
    ?v. res = INL v /\ expr_post_mods H ctx func cenv cx e es sa sc s ee v op t /\
      expr_store_bound cx (post_value_type cenv e) v op t /\
      expr_sim_full_endpoint func sc s t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee g ts t /\
      ptr_val_ok cx (post_value_type cenv e) v op g ts t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op g t) /\
      ghost_kept_at lo cenv es sa G tn s g ts
End

(* A cut includes the head execution and a success-only bridge to the
   next operand's input. Neither the tail outcome nor a per-horizon
   choice of the post-copy witnesses appears here. *)
Definition concat_head_cut_mods_def[nocompute]:
  concat_head_cut_mods (mods,exps,cx,env,src,tops,st0,cenv,pure)
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) scratch anchor
      e args (sb,shadow_sa,shadow_sb) (es,sa,s,G,tn) bs P <=>
    ?op sc shadow_sc s2 shadow_s2.
      lower_value compile_expr cenv (expr_type e) e sa = (op,sc) /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
        (gas_shadow_expr e) shadow_sa = (op,shadow_sc) /\
      expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sc,shadow_sa,shadow_sc) /\
      gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
        (concat_head_post_mods (DF,lo,d,ctx,func,cenv,cx) e (es,sa,s,G,tn) (op,sc))
        (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
           (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) /\
      (!marks v mid G1 tn1 t.
         (!tail. bind (eval_expr cx e) (read_result cx)
            (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
            (INL v,mid with gas_obs := tail)) /\
         mid.gas_obs = [] /\ ~t.vs_halted /\ storage_trace_domain cx st0 mid.storage_trace /\
         (!H. valid_horizon cx st0 H mid.storage_trace ==>
            gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
              (s,G,tn) marks (OK t,G1,tn1) /\
            concat_head_post_mods (DF,lo,d,ctx,func,cenv,cx) e (es,sa,s,G,tn)
              (op,sc) H (INL v) mid G1 tn1 t) ==>
         ?tv u G2 tn2.
           evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
           (!H. valid_horizon cx st0 H mid.storage_trace ==>
              gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
                (t,G1,tn1) [] (OK u,G2,tn2)) /\
           concat_loop_entry_mods (mods,exps,cx,env,src,tops,st0,cenv,pure)
             (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) scratch anchor
             args (sb,shadow_s2,shadow_sb) (mid,s2,u,G2,tn2)
             (bs ++ concat_payload_mods v) (P+concat_payload_capacity (expr_type e)))
End
