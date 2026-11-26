(* Keep the concrete packet descriptor visible while adding an observation
   that is available at every installed endpoint. *)
Theory bodyForArrayNamedPacketInstallMods
Ancestors
  bodyForArrayPacketInstallMods bodyForArrayLengthPacketMods
  bodyForArrayHeaderInstallMods bodyForArrayHeaderMods bodyForArrayEntryMods
  fragGasOriginPtrLoop vyperState

Theorem for_array_named_packet_install_mods:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    addr_cut body_cut /\
  fn_inst_ids_distinct func /\ capacity < dimword (:256) /\
  bound_length bd < dimword (:256) /\
  storage_trace_domain cx st0 em.storage_trace /\ em.gas_obs = [] /\
  body_const_cells_agree_mods mods cx env em /\
  expr_sim_inv_mods mods c cx env em /\ lookup_scopes id em.scopes = NONE /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  copy_old_operand saL (vv_operand vv) /\ (!lbl. vv_operand vv <> Label lbl) /\
  for_array_length_packet_mods mods (DF,lo,d,ctx,func,shadow_func)
    (explicit,PG) cx env st0 (es0,sa0,s0,G0,tn0)
    ((c,id,fty,e,sty,bd,ret_ty,loop_body),
     (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
     (bc,saD,saA,xd,capacity,aidItem),
     (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
     addr_cut,body_cut)
    raw n (r,Gr,traw) (em,u,Gu,tu,bw,capture,vs) /\
  (!K G' tn' t'. valid_horizon cx st0 K em.storage_trace /\
       for_array_install_frame_mods saL u Gu tu G' tn' t' ==>
       Extra K em G' tn' t') ==>
  ?dw t G tn. !H. valid_horizon cx st0 H em.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (r,Gr,traw) [] (OK t,G,tn) /\
    for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
      (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
      (bc,saD,saA,xd,capacity,aidItem)
      (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
      addr_cut body_cut /\
    copy_old_operand saL (vv_operand vv) /\ (!lbl. vv_operand vv <> Label lbl) /\
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,capacity,aidItem)
      vs (vv_operand vv,bw,len_op,idx) cond
      (\K rs ee G' tn' t'.
         for_array_entry_route_mods c cx lo (sty,bd,loc)
           (em,sbExpr,u,Gu,tu) (vv_operand vv,bw) vs capture
           K rs ee G' tn' t' /\ Extra K em G tn t)
      H vs em G tn t
Proof
  PairCases_on `addr_cut` >> PairCases_on `body_cut` >> strip_tac >>
  qhdtm_x_assum `for_array_length_packet_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_length_packet_mods_def]) >>
  `!H. valid_horizon cx st0 H em.storage_trace ==>
       stmt_state_rel H ctx func c cx em u /\ immutable_frame_mods func c cx em u /\
       storage_well_formed_on cx em (FST H) /\ ghost_inv_at_mods (DF H) lo d c cx em Gu tu u` by
    (gen_tac >> strip_tac >>
     qpat_assum `!K. valid_horizon _ _ K _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `RouteX = for_array_entry_route_mods c cx lo (sty,bd,loc)
      (em,sbExpr,u,Gu,tu) (vv_operand vv,bw) vs capture` >>
  drule_all_then (qspecl_then [`explicit`,`RouteX`,`PG`]
    (qx_choosel_then [`dw`,`G`,`tn`,`t`] strip_assume_tac))
    for_array_header_install_mods >>
  `em with gas_obs := [] = em` by simp[evaluation_state_component_equality] >>
  qexistsl_tac [`dw`,`t`,`G`,`tn`] >> pure_asm_rewrite_tac [] >>
  gen_tac >> strip_tac >> conj_tac
  >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`tu`] >>
      conj_tac >-
        (qpat_assum `!K. valid_horizon _ _ K _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
      qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
        (qspec_then `DF H` ACCEPT_TAC))
  >- (qpat_assum `!K. valid_horizon _ _ K _ /\ RouteX K _ _ _ _ _ ==> _`
        (qspec_then `H` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (strip_assume_tac o REWRITE_RULE [for_array_header_mods_def]) >>
      qpat_assum `!K G' tn' t'. valid_horizon _ _ K _ /\ for_array_install_frame_mods _ _ _ _ G' tn' t' ==> Extra K _ G' tn' t'`
        (qspecl_then [`H`,`G`,`tn`,`t`] mp_tac) >>
      impl_tac >- simp[] >>
      disch_then assume_tac >>
      simp[for_array_header_mods_def,Abbr `RouteX`] >> first_assum ACCEPT_TAC)
QED
