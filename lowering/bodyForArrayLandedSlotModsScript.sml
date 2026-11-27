(* The storage branch, from the concrete body landing through slot copy. *)
Theory bodyForArrayLandedSlotMods
Ancestors
  bodyForArrayEntryMods bodyForArrayHeaderMods bodyForArraySlotCompilerCutsMods
  bodyForArraySlotAddressFrameMods bodyForArraySlotLandedPostMods
  bodyForArraySlotItemMods bodyFullForArrayRound exprSimCopy exprBodyPreProps
  exprLoweringProps loweringShapeDefs loweringPosts vyperStorageFootprint vyperStorageTrace
  vyperTypeContract[qualified,ignore_grammar] words arithmetic

val _ = Parse.hide "body";

Theorem for_array_landed_slot_item_mods:
  for_nonslot_layout (c,id,typ,e,sty,bd,ret_ty,body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,cap,inst.inst_id)
    (entry,cond,bod,incr,exit,idx,invalid,valid,dv,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  vyperTypeContract$loop_iterator_place e = SOME tgt /\
  target_root tgt = TopLevelNameTarget nid /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ fn_inst_ids_distinct func /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!H. dead_lo_ok_mods H (DF H) lo c cx) /\
  storage_trace_domain cx st0 es.storage_trace /\
  a::rs = DROP k vs /\
  sh.vs_current_bb = sa.cs_current_bb /\ sh.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~sh.vs_halted /\ lookup_var idx sh = SOME (n2w k) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u0,tu0) (xd,dw,cap,inst.inst_id)
      vs (vv_operand vv,bw,len_op,idx) bod (\_ _ _ _ _ _. T) H (a::rs) es Gh th sh /\
    for_array_entry_route_mods c cx lo (sty,bd,loc) (em,sbExpr,u0,Gu0,tu0)
      (vv_operand vv,bw) vs (ForArraySlot tr off root path delta) H (a::rs) es G tn s) ==>
  ?v z Gf tf.
    read_result cx a es = (INL v,es) /\ value_has_type tyv v /\ val_wf tyv v /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory tyv v (w2n dw) mem) /\
    z.vs_current_bb = sbCopy.cs_current_bb /\ z.vs_inst_idx = LENGTH sbCopy.cs_current_insts /\
    ~z.vs_halted /\ lookup_var idx z = SOME (n2w k) /\
    FLOOKUP Gf idx = FLOOKUP Gh idx /\ op_taint tf (Var idx) = op_taint th (Var idx) /\
    eval_operand (vv_operand vv) z = eval_operand (vv_operand vv) sh /\
    eval_operand len_op z = eval_operand len_op sh /\
    (!q. not_fresh_at saL q ==>
      FLOOKUP Gf q = FLOOKUP Gh q /\ op_taint tf (Var q) = op_taint th (Var q)) /\
    for_array_item_mods c sa0 sbExpr (xd,dw,cap,inst.inst_id) es Gf tf z /\
    for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 es Gf tf z /\
    for_array_capture_frame_mods c (em,sbExpr,saL,u0,tu0) es tf z /\
    immutable_frame_mods func c cx es z /\
    ret_pc_ok c sa0 z /\ return_buf_frame d c sa0 z /\ return_buf_sep d c es z /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (sh,Gh,th) [] (OK z,Gf,tf) /\
      stmt_state_rel H ctx func c cx es z /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at_mods (DF H) lo d c cx es Gf tf z)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ for_array_entry_route_mods _ _ _ _ _ _ _ _ H _ _ _ _ _`
    (drule_then strip_assume_tac) >>
  qhdtm_x_assum `for_array_header_mods`
    (strip_assume_tac o REWRITE_RULE[for_array_header_mods_def, AND_CLAUSES]) >>
  qhdtm_x_assum `for_array_entry_route_mods`
    (strip_assume_tac o SIMP_RULE bool_ss
       [for_array_entry_route_mods_def, for_array_capture_case_def]) >>
  qhdtm_assum `for_nonslot_layout`
    (mp_then (Pat `for_nonslot_layout _ _ _ _ _ _ _`) (drule_all_then strip_assume_tac)
       for_array_slot_compiler_cuts_mods) >>
  suspend "address"
QED

Resume for_array_landed_slot_item_mods[address]:
  `tv = tyv` by (qpat_assum `sty = typ` (fn th => fs[th])) >>
  qpat_x_assum `tv = tyv` SUBST_ALL_TAC >>
  `sa0.cs_next_var <= sa.cs_next_var /\ saL.cs_next_var <= sa.cs_next_var /\
   not_fresh_at sa xd` by
    (qhdtm_assum `for_nonslot_layout`
       (strip_assume_tac o REWRITE_RULE[for_nonslot_layout_def]) >>
     fs[ci_mono_def] >> decide_tac) >>
  `copy_old_operand sa (vv_operand vv) /\ copy_old_operand sa len_op` by
    (simp[copy_old_operand_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func c cx es sh /\ storage_well_formed_on cx es (FST H) /\
    dead_lo_ok_mods H (DF H) lo c cx /\ ghost_inv_at_mods (DF H) lo d c cx es Gh th sh` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!K. valid_horizon _ _ K _ ==> _ /\ for_array_entry_route_mods _ _ _ _ _ _ _ _ K _ _ _ _ _`
       (qspec_then `H` (drule_then
         (strip_assume_tac o REWRITE_RULE[for_array_header_mods_def, AND_CLAUSES] o CONJUNCT1))) >>
     simp[]) >>
  qpat_assum `emit_op MUL _ _ = (Var _,_)`
    (mp_then (Pat `emit_op MUL _ _ = _`) (fn address =>
       qpat_assum `for_array_outer_frame_mods _ _ _ _ _ _ _ _ _ Gh th sh`
         (mp_then (Pat `for_array_outer_frame_mods _ _ _ _ _ _ _ _ _ _ _ _`) drule_all address))
      for_array_slot_address_frame_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`u1`,`Gu1`,`tu1`] strip_assume_tac)) >>
  suspend "copy"
QED

Resume for_array_landed_slot_item_mods[copy]:
  `32 * type_slot_size tyv <= cap` by simp[] >>
  `!x. not_fresh_at saL x ==> not_fresh_at saCopy x` by simp[] >>
  Q.SUBGOAL_THEN
    `?v z Gf tf.
      read_result cx a es = (INL v,es) /\ value_has_type tyv v /\ val_wf tyv v /\
      (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory tyv v (w2n dw) mem) /\
      z.vs_current_bb = sbCopy.cs_current_bb /\ z.vs_inst_idx = LENGTH sbCopy.cs_current_insts /\
      ~z.vs_halted /\
      (!op. slot_copy_external saCopy op ==>
        eval_operand op z = eval_operand op u1 /\ op_prov Gf op = op_prov Gu1 op /\
        op_taint tf op = op_taint tu1 op) /\
      for_array_item_mods c sa0 sbExpr (xd,dw,cap,inst.inst_id) es Gf tf z /\
      for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 es Gf tf z /\
      for_array_capture_frame_mods c (em,sbExpr,saL,u0,tu0) es tf z /\
      immutable_frame_mods func c cx es z /\
      ret_pc_ok c sa0 z /\ return_buf_frame d c sa0 z /\ return_buf_sep d c es z /\ allocas_from lo z /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u1,Gu1,tu1) [] (OK z,Gf,tf) /\
        stmt_state_rel H ctx func c cx es z /\ storage_well_formed_on cx es (FST H) /\
        ghost_inv_at_mods (DF H) lo d c cx es Gf tf z)`
    (qx_choosel_then [`v`,`z`,`Gf`,`tf`] strip_assume_tac)
  >- suspend "copy_input" >>
  suspend "post"
QED

Resume for_array_landed_slot_item_mods[copy_input]:
  qpat_assum `vs = GENLIST _ _`
    (mp_then (Pat `vs = GENLIST _ _`) (fn copy =>
       qpat_assum `eval_operand (Var ep) u1 = SOME _`
         (mp_then (Pat `eval_operand _ _ = SOME _`) match_mp_tac copy))
      for_array_slot_item_mods) >>
  qexistsl_tac [`typ`,`rs`,`root`,`path`,`off`,`k`,`extra`,`delta`] >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
  first_assum ACCEPT_TAC
QED

Resume for_array_landed_slot_item_mods[post]:
  `lookup_var idx u1 = lookup_var idx sh` by simp[] >>
  `!q. not_fresh_at saL q ==>
    FLOOKUP Gu1 q = FLOOKUP Gh q /\ op_taint tu1 (Var q) = op_taint th (Var q)` by simp[] >>
  `!q. not_fresh_at saL q ==> slot_copy_external saCopy (Var q)` by simp[] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (sh,Gh,th) [] (OK u1,Gu1,tu1)` by simp[] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u1,Gu1,tu1) [] (OK z,Gf,tf)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (u1,Gu1,tu1) _ _ /\ _`
       (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  `lookup_var idx z = SOME (n2w k) /\ FLOOKUP Gf idx = FLOOKUP Gh idx /\
   op_taint tf (Var idx) = op_taint th (Var idx) /\
   eval_operand (vv_operand vv) z = eval_operand (vv_operand vv) sh /\
   eval_operand len_op z = eval_operand len_op sh /\
   (!q. not_fresh_at saL q ==>
     FLOOKUP Gf q = FLOOKUP Gh q /\ op_taint tf (Var q) = op_taint th (Var q)) /\
   (!H. valid_horizon cx st0 H es.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (sh,Gh,th) [] (OK z,Gf,tf))` by
    (match_mp_tac (Q.INST [`u` |-> `u1`, `Gu` |-> `Gu1`, `tu` |-> `tu1`,
                          `saCopy` |-> `saCopy`] for_array_slot_landed_post_mods) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`v`,`z`,`Gf`,`tf`] >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >> rpt gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (u1,Gu1,tu1) _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  simp[]
QED

Finalise for_array_landed_slot_item_mods
