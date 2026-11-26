(* Between expression evaluation and the item allocation, the length slice
   fixes the list, base, backing descriptor and machine endpoint. *)
Theory bodyForArrayLengthPacketMods
Ancestors
  bodyForArrayEntryMods bodyForArrayHeaderInstallMods
  fragGasOriginPtr bodyFullShadowBodyInv vyperInterpreter vyperStorageTrace
  vyperStorageFootprint vyperValue vyperAST loweringPosts

Definition for_array_length_packet_mods_def[nocompute]:
  for_array_length_packet_mods mods (DF,lo,d,ctx,func,shadow_func)
      (explicit,PG) cx env st0 (es0,sa0,s0,G0,tn0)
      ((c,id,fty,e,sty,bd,ret_ty,loop_body),
       (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
       item,blocks,addr_cut,body_cut)
      raw n (r,Gr,traw) (em,u,Gu,tu,bw,capture,vs) <=>
    compatible_bound (Dynamic n) (LENGTH vs) /\
    (!tail. array_iterator_results cx (expr_type e) raw (em with gas_obs := tail) =
       (INL vs,em with gas_obs := tail)) /\
    LENGTH vs <= bound_length bd /\
    ~u.vs_halted /\ u.vs_current_bb = saL.cs_current_bb /\
    u.vs_inst_idx = LENGTH saL.cs_current_insts /\
    eval_operand (vv_operand vv) u = SOME bw /\ op_taint tu (vv_operand vv) = {} /\
    eval_operand len_op u = SOME (n2w (LENGTH vs)) /\
    op_prov Gu len_op = NONE /\ op_taint tu len_op = {} /\
    ret_pc_ok c sa0 u /\ return_buf_frame d c sa0 u /\ return_buf_sep d c em u /\
    (!fn inst q. frag_reachable ctx func u fn inst q ==> dalloca_fmp_headroom inst q) /\
    for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 em Gu tu u /\
    (!K. valid_horizon cx st0 K em.storage_trace ==>
       gas_origin_ptr_path (DF K,lo,explicit,ctx,func,PG) (r,Gr,traw) [] (OK u,Gu,tu) /\
       stmt_state_rel K ctx func c cx em u /\ immutable_frame_mods func c cx em u /\
       storage_well_formed_on cx em (FST K) /\ ghost_inv_at_mods (DF K) lo d c cx em Gu tu u) /\
    (!K t G tn. valid_horizon cx st0 K em.storage_trace /\
       for_array_install_frame_mods saL u Gu tu G tn t ==>
       for_array_entry_route_mods c cx lo (sty,bd,loc) (em,sbExpr,u,Gu,tu)
         (vv_operand vv,bw) vs capture K vs em G tn t)
End

(* Both uses are at the very same length endpoint. No new choice of the
   list or capture is needed when applying the install frame at K. *)
Theorem length_packet_install_interface[local]:
  for_array_length_packet_mods mods (DF,lo,d,ctx,func,shadow_func)
    (explicit,PG) cx env st0 outer
    ((c,id,fty,e,sty,bd,ret_ty,loop_body),
     (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),item,blocks,addr_cut,body_cut)
    raw n (r,Gr,traw) (em,u,Gu,tu,bw,capture,vs) /\
  valid_horizon cx st0 H em.storage_trace /\
  for_array_install_frame_mods saL u Gu tu G tn t ==>
  gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (r,Gr,traw) [] (OK u,Gu,tu) /\
  for_array_entry_route_mods c cx lo (sty,bd,loc) (em,sbExpr,u,Gu,tu)
    (vv_operand vv,bw) vs capture H vs em G tn t
Proof
  PairCases_on `outer` >> simp[for_array_length_packet_mods_def]
QED
