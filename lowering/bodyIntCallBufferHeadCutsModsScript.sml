(* Cut interfaces for the physical suffix of one memory-passed argument. *)
Theory bodyIntCallBufferHeadCutsMods
Ancestors
  bodyIntCallBufferHeadSpecMods bodyIntCallBufferHeadVVMods
  bodyIntCallBufferAllocVVMods bodyIntCallBufferWordInputMods
  bodyIntCallBufferNonwordInputMods bodyIntCallBufferStoreCutMods
  bodyIntCallBufferStoreFrameMods bodyIntCallStagePacketTransportMods
  bodyIntCallStageSnocMods bodyFullPostsMods exprSimMemorySource
  gasExplicitSites gasOutcomeFullMods fragGasOriginPtr
  vyperStorageFootprint vyperInterpreter vyperState venomState
  compileEnv loweringPosts bodyPtrDefs

Definition intcall_buffer_head_raw_post_mods_def[nocompute]:
  intcall_buffer_head_raw_post_mods
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    mods cenv cx env st0 (si,esi,s,G,tn) e dty marks raw vv ci mid u Gu tu <=>
    (!tail. eval_expr cx e
      (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL raw,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      vv_post_mods H ctx func cenv cx e esi si ci s mid raw vv u /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid Gu tu u /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK u,Gu,tu)) /\
    ghost_kept_at lo cenv esi si G tn s Gu tu /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    u.vs_current_bb = ci.cs_current_bb /\
    u.vs_inst_idx = LENGTH ci.cs_current_insts /\
    alloca_history func u
End

Definition intcall_buffer_head_edge_mods_def[nocompute]:
  intcall_buffer_head_edge_mods cenv cx sa pin
    (si,esi,s,G,tn) (sj,esj,t,Gj,tj) <=>
    si.cs_next_var <= sj.cs_next_var /\ si.cs_next_id <= sj.cs_next_id /\
    s.vs_alloca_next <= t.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    (!x w. not_fresh_at si x /\ lookup_var x s = SOME w ==>
       lookup_var x t = SOME w) /\
    (!x. not_fresh_at si x ==>
       FLOOKUP Gj x = FLOOKUP G x /\ op_taint tj (Var x) = op_taint tn (Var x)) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
       FLOOKUP t.vs_allocas aid = SOME row) /\
    (!n lb sz. local_region cenv esj.scopes t n lb sz ==>
       local_region cenv esi.scopes s n lb sz) /\
    intcall_stage_ops_mods (0,ARB) cenv cx sa
      (si,esi,s,G,tn) pin ([],[],[],[],[]) /\
    wb_frame cenv esi esj si s t
End

Definition intcall_buffer_head_alloc_post_mods_def[nocompute]:
  intcall_buffer_head_alloc_post_mods
    (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin
    (ci,mid,u,Gu,tu) (ca,mida,a,Ga,ta) dst base cap <=>
    mid = mida /\ ci.cs_next_id < ca.cs_next_id /\ ci.cs_next_var <= ca.cs_next_var /\
    FLOOKUP a.vs_allocas ci.cs_next_id = SOME (base,cap) /\
    lookup_var dst a = SOME (n2w base) /\ lo <= base /\
    base + cap <= a.vs_alloca_next /\
    (!aid row. FLOOKUP u.vs_allocas aid = SOME row ==>
       FLOOKUP a.vs_allocas aid = SOME row) /\
    a.vs_memory = u.vs_memory /\ a.vs_labels = u.vs_labels /\
    intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
      (sa,es0,s0,G0,tn0) (ca,mid,a,Ga,ta) pin
End

Definition intcall_buffer_head_unwrap_post_mods_def[nocompute]:
  intcall_buffer_head_unwrap_post_mods cenv cx st0 d lo func
    (ca,mid,a,Ga,ta) (cu,midz,z,Gz,tz) dst base cap v dty <=>
    mid = midz /\ ca.cs_next_id <= cu.cs_next_id /\ ca.cs_next_var <= cu.cs_next_var /\
    lookup_var dst z = SOME (n2w base) /\
    FLOOKUP z.vs_allocas ca.cs_next_id = SOME (base,cap) /\
    lo <= base /\ base + cap <= z.vs_alloca_next /\
    ~z.vs_halted /\ alloca_history func z /\
    z.vs_labels = a.vs_labels /\
    (!aid row. FLOOKUP a.vs_allocas aid = SOME row ==>
       FLOOKUP z.vs_allocas aid = SOME row)
End

Definition intcall_buffer_head_store_post_mods_def[nocompute]:
  intcall_buffer_head_store_post_mods cenv cx st0 d lo func
    (cu,mid,z,Gz,tz) (cs,midt,t,Gf,tf) dst base cap v dty nw <=>
    mid = midt /\ nw <= cap /\ cu.cs_next_id <= cs.cs_next_id /\
    ~t.vs_halted /\ alloca_history func t /\
    lookup_var dst t = SOME (n2w base) /\
    FLOOKUP t.vs_allocas cu.cs_next_id = SOME (base,cap) /\
    t.vs_current_bb = cs.cs_current_bb /\
    t.vs_inst_idx = LENGTH cs.cs_current_insts /\
    tf.t_stor = tz.t_stor /\ tf.t_trans = tz.t_trans /\ tf.t_imm = tz.t_imm
End

Theorem intcall_buffer_head_raw_post_intro_mods:
  intcall_buffer_head_raw_post_mods
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    mods cenv cx env st0 (si,esi,s,G,tn) e dty marks raw vv ci mid u Gu tu ==>
  intcall_buffer_head_raw_post_mods
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    mods cenv cx env st0 (si,esi,s,G,tn) e dty marks raw vv ci mid u Gu tu
Proof
  strip_tac >> first_assum ACCEPT_TAC
QED
