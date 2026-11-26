(* Adapt the saved nonslot capture to the concrete item-address cursor.
   The pointer certificate stays at the length endpoint; only the current
   backing observations are transported across the loop test. *)
Theory bodyForArrayLandedSnapshotMods
Ancestors
  bodyForArrayEntryMods bodyForArraySnapshotItemMods bodyFullForArrayRound
  exprSimCopy loweringShapeDefs vyperTypeSystem vyperStorageFootprint
  bodyForArrayHeaderMods exprBodyPreProps logArgumentTypeEval
  vyperTypeEvalCaseProofs vyperValue words arithmetic

val _ = Parse.hide "body";

Theorem for_array_landed_snapshot_item_mods:
  for_nonslot_layout (c,id,typ,e,sty,bd,ret_ty,body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,cap,inst.inst_id)
    (entry,cond,bod,incr,exit,idx,invalid,valid,dv,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  contract_inv mods exps ctx c cx /\ well_typed_iterator env typ (Array e) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ fn_inst_ids_distinct func /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!lbl. vv_operand vv <> Label lbl) /\
  storage_trace_domain cx st0 es.storage_trace /\
  a::rs = DROP k vs /\
  sh.vs_inst_idx = LENGTH sa.cs_current_insts /\ lookup_var idx sh = SOME (n2w k) /\
  (!q. q <> dv ==> lookup_var q sh = lookup_var q s) /\
  op_prov Gh (vv_operand vv) = op_prov G (vv_operand vv) /\
  sh.vs_memory = s.vs_memory /\ sh.vs_data_section = s.vs_data_section /\
  sh.vs_allocas = s.vs_allocas /\ th.t_mem = tn.t_mem /\
  (!tr off root path delta. capture <> ForArraySlot tr off root path delta) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,cap,inst.inst_id)
      vs (vv_operand vv,bw,len_op,idx) bod (\_ _ _ _ _ _. T) H (a::rs) es Gh th sh /\
    for_array_entry_route_mods c cx lo (sty,bd,loc) (em,sbExpr,u,Gu,tu)
      (vv_operand vv,bw) vs capture H (a::rs) es G tn s) ==>
  ?v z Gf tf.
    read_result cx a es = (INL v,es) /\ value_has_type tv v /\ val_wf tv v /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory tv v (w2n dw) mem) /\
    z.vs_current_bb = sbCopy.cs_current_bb /\ z.vs_inst_idx = LENGTH sbCopy.cs_current_insts /\
    ~z.vs_halted /\ lookup_var idx z = SOME (n2w k) /\
    FLOOKUP Gf idx = FLOOKUP Gh idx /\ op_taint tf (Var idx) = op_taint th (Var idx) /\
    eval_operand (vv_operand vv) z = eval_operand (vv_operand vv) sh /\
    eval_operand len_op z = eval_operand len_op sh /\
    (!q. not_fresh_at saL q ==>
      FLOOKUP Gf q = FLOOKUP Gh q /\ op_taint tf (Var q) = op_taint th (Var q)) /\
    for_array_item_mods c sa0 sbExpr (xd,dw,cap,inst.inst_id) es Gf tf z /\
    for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 es Gf tf z /\
    for_array_capture_frame_mods c (em,sbExpr,saL,u,tu) es tf z /\
    immutable_frame_mods func c cx es z /\
    ret_pc_ok c sa0 z /\ return_buf_frame d c sa0 z /\ return_buf_sep d c es z /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (sh,Gh,th) [] (OK z,Gf,tf) /\
      stmt_state_rel H ctx func c cx es z /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at_mods (DF H) lo d c cx es Gf tf z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type e = ArrayT sty bd /\ local_ptrs_reserved c saL /\ ~not_fresh_at saL dv` by
    (qhdtm_assum `for_nonslot_layout`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [for_nonslot_layout_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `sty = typ` by fs[well_typed_iterator_def] >>
  qpat_x_assum `sty = typ` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,cap,inst.inst_id)
      vs (vv_operand vv,bw,len_op,idx) bod (\_ _ _ _ _ _. T) H (a::rs) es Gh th sh` by
    (gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
  qpat_assum `!H. _ ==> _ /\ for_array_entry_route_mods c cx lo _ _ _ vs capture H _ es G tn s`
    (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac)) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV tv bd)` by
    (qhdtm_assum `for_array_header_mods`
       (strip_assume_tac o REWRITE_RULE [for_array_header_mods_def, AND_CLAUSES]) >>
     drule expr_sim_inv_mods_env >> strip_tac >>
     `well_typed_expr env e` by fs[well_typed_iterator_def] >>
     drule_then assume_tac env_consistent_type_defs_get_tenv >>
     drule_all checked_expr_type_well_formed >>
     simp[well_formed_type_def, evaluate_type_def, LET_THM]) >>
  Q.SUBGOAL_THEN
    `?av. vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
      value_has_type (ArrayTV tv bd) (ArrayV av) /\
      ((loc = LocMemory /\
        (!m. mem_agree_outside th.t_mem sh.vs_memory m ==>
          val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) m) /\
        ptr_mem_ok cx (ArrayT typ bd) (ArrayV av) (vv_operand vv) Gu tu u /\
        eval_operand (vv_operand vv) u = SOME bw /\
        op_prov Gh (vv_operand vv) = op_prov Gu (vv_operand vv) /\
        (0 < type_memory_size (ArrayTV tv bd) ==>
          (?aid b sz. FLOOKUP sh.vs_allocas aid = SOME (b,sz) /\
            aid < sbExpr.cs_next_id /\ b <= w2n bw /\
            w2n bw + type_memory_size (ArrayTV tv bd) <= b + sz) \/
          (?name b sz. local_region c es.scopes sh name b sz /\ b <= w2n bw /\
            w2n bw + type_memory_size (ArrayTV tv bd) <= b + sz))) \/
       (loc = LocCode /\ op_prov Gh (vv_operand vv) = NONE /\
        w2n bw + type_memory_size (ArrayTV tv bd) < dimword (:256) /\
        (c.ce_is_ctor ==> w2n bw + type_memory_size (ArrayTV tv bd) <= lo /\
          !m. mem_agree_outside th.t_mem sh.vs_memory m ==>
            val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) m) /\
        (~c.ce_is_ctor ==> w2n bw + type_memory_size (ArrayTV tv bd) <= LENGTH sh.vs_data_section /\
          val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) sh.vs_data_section)))`
    (qx_choose_then `av` (map_every assume_tac o CONJUNCTS))
  >- suspend "backing" >>
  suspend "copy"
QED

Resume for_array_landed_snapshot_item_mods[backing]:
  `!q. not_fresh_at saL q ==> lookup_var q sh = lookup_var q s` by
    (gen_tac >> disch_tac >> first_x_assum irule >> CCONTR_TAC >> gvs[]) >>
  `!name b sz. local_region c es.scopes sh name b sz <=> local_region c es.scopes s name b sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists `saL` >> simp[]) >>
  Cases_on `capture` >>
  gvs[for_array_entry_route_mods_def, for_array_memory_backing_mods_def] >>
  rename1 `value_has_type (ArrayTV tv bd) (ArrayV av)` >>
  qexists_tac `av` >> simp[]
  >- (disch_tac >> disj1_tac >>
      qpat_assum `0 < _ ==> ?aid b sz. _` (drule_then strip_assume_tac) >>
      qexistsl [`aid`,`b`,`sz`] >> simp[])
  >- (disch_tac >> disj2_tac >>
      qpat_assum `0 < _ ==> ?b sz. _` (drule_then strip_assume_tac) >>
      rename1 `local_region c es.scopes s saved_name b sz` >>
      qexistsl_tac [`saved_name`,`b`,`sz`] >> simp[])
QED

Resume for_array_landed_snapshot_item_mods[copy]:
  qpat_assum `!H. _ ==> for_array_header_mods mods DF lo d ctx func c cx env id st0 _ _ _ vs _ bod _ H _ es Gh th sh`
    (mp_then Any
      (fn th => qhdtm_assum `for_nonslot_layout`
        (mp_then (Pat `for_nonslot_layout _ _ _ _ _ _ _`) (mp_tac o SPEC_ALL) th))
      (Q.INST [`Gq` |-> `Gu`, `av` |-> `av`] for_array_snapshot_item_mods)) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`v`,`z`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`v`,`z`,`Gf`,`tf`] >> asm_rewrite_tac[]
QED

Finalise for_array_landed_snapshot_item_mods
