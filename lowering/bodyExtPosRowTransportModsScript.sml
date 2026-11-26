(* Transport a saved positional operand without widening its compile interval. *)
Theory bodyExtPosRowTransportMods
Ancestors
  bodyExtPosSavedRowMods bodyExtSavedRowCutMods bodyExtSavedCodeEndpointMods
  bodyExtSavedSlotEndpointMods bodyExtBorrowedFootprintMods
  bodyExtSavedValueEndpointMods bodyExtOwnedRowEndpointMods
  bodyFullExtCallSavedOperand exprLoweringProps exprSimUnwrap stateRelProj
  wordArgsPtr loweringPosts loweringStateRelDefs bodyPtrDefs context finite_map
  bodyFullPostsMods

Theorem ext_pos_row_transport_mods:
  compile_expr cenv (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv cenv copy
    (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
  (~copy ==> ~exprs_can_mutate cenv kw_es) /\
  (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
    ?x w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var x /\
      eval_operand (vv_operand sv) u = SOME w /\
      evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
      val_wf tv v /\ FLOOKUP u.vs_allocas sm.cs_next_id =
        SOME (w2n w,type_memory_size tv) /\ sm.cs_next_id < ss.cs_next_id /\
      (!n b sz. local_region cenv pos.scopes u n b sz ==>
        regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
  sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
  ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= se.cs_next_var /\ sb.cs_next_id <= se.cs_next_id /\
  local_ptrs_reserved cenv si /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  ((?tag op. sv = StackValue tag op) \/
   (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
        ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
   (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
        ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
        lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
  (?raw. read_result cx raw pos = (INL v,pos) /\
    vv_holds_mods cenv cx (lowered_value_type cenv e) raw sv pos u /\
    vv_at cenv cx (lowered_value_type cenv e) si ss pos raw sv u /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw sv pos Gp tp u /\
    vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) pos raw sv u) /\
  vv_storage_live (H:(bool # bytes32 # type_value) list # num list) cx sv pos u /\
  (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
    ptr_buf_ok cenv e op Gp u) /\
  (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand Gp u) /\
  wb_frame cenv pos ee sb u t /\ ghost_kept_at lo cenv pos sb Gp tp u G tn /\
  (!x w. not_fresh_at sb x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
  (!aid row. FLOOKUP u.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
  u.vs_alloca_next <= t.vs_alloca_next /\ t.vs_labels = u.vs_labels /\
  MAP FDOM ee.scopes = MAP FDOM pos.scopes /\
  (~copy ==> ee.scopes = pos.scopes /\ ee.immutables = pos.immutables /\
    (!tr. get_storage cx ee tr = get_storage cx pos tr)) /\
  stmt_state_rel H ctx func cenv cx pos u /\ stmt_state_rel H ctx func cenv cx ee t /\
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env pos /\
  immutable_frame_mods func cenv cx ee t /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\ dead_lo_ok_mods H (DF H) lo cenv cx /\
  (!p ty.
     contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env pos /\
     cenv.ce_is_ctor /\ p.ptr_location = LocCode /\ dead_lo_ok_mods H (DF H) lo cenv cx /\
     ee.immutables = pos.immutables /\ immutable_frame_mods func cenv cx ee t /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
     (?raw. read_result cx raw ee = (INL v,ee) /\
       vv_holds_mods cenv cx ty raw (LocatedValue ty p) ee t) ==>
     !tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
       eval_operand p.ptr_operand t = SOME w ==>
       w2n w + type_memory_size tv <= lo /\
       (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
         val_in_memory tv v (w2n w) mem)) ==>
  ext_pos_saved_row_mods lo cenv cx kw_es sa se H e sv v ee G tn t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac ext_saved_row_restrict_frame >>
  `!x. vv_operand sv = Var x ==> not_fresh_at ss x` by
    metis_tac[extcall_saved_operand_not_fresh] >>
  `ci_mono sm ss` by
    (qspecl_then [`cenv`, `copy`, `ext_call_arg_value (lowered_value_type cenv e) vv`, `sm`]
       mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id` by
    (drule compile_expr_extends >> simp[]) >>
  `local_ptrs_reserved cenv ss` by
    (irule local_ptrs_reserved_next_var >> qexists `si` >> fs[ci_mono_def] >> decide_tac) >>
  `alloca_inv u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx pos u`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `!n b sz. local_region cenv pos.scopes u n b sz <=> local_region cenv ee.scopes t n b sz` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_local_regions) >> conj_tac >- simp[] >>
     conj_tac >- (qexistsl [`ee`, `ss`] >> simp[]) >>
     qexistsl [`H`, `ctx`, `cx`, `func`] >> simp[]) >>
  qabbrev_tac `ty = lowered_value_type cenv e` >>
  `((?tag op. sv = StackValue tag op) \/
     (?p. sv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory)) /\
   (~is_word_type ty ==> ~copy) ==>
   (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds_mods cenv cx ty raw sv ee t /\ vv_at cenv cx ty si ss ee raw sv t /\
    ptr_vv_ok cx ty raw sv ee G tn t /\ vv_store_bound cx ty ty ee raw sv t) /\
   (!tag op. sv = StackValue tag op /\ ~is_word_type ty ==> ptr_buf_ok cenv e op G t) /\
   (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G t)` by
    (disch_then (CONJUNCTS_THEN assume_tac) >>
     `!tv w. ~is_word_type ty /\ expr_val_at cenv cx ty si ss pos v (vv_operand sv) u /\
       evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand (vv_operand sv) u = SOME w ==>
       val_wf tv v /\ mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
         mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory /\
       (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn.t_mem ==> i IN tp.t_mem)` by
       (qx_genl_tac [`tv`,`w`] >> strip_tac >>
        `ee.scopes = pos.scopes` by metis_tac[] >>
        irule (INST_TYPE [alpha |-> ``:num # num``, beta |-> ``:num # num``]
          ext_borrowed_footprint_frame) >>
        qexistsl [`Gp`, `G`, `cenv`, `cx`, `ee`, `pos`, `lo`, `vv_operand sv`,
                  `si`, `ss`, `ss`, `ty`] >> simp[]) >>
     irule ext_saved_value_endpoint_mods >> simp[Abbr `ty`] >>
     qexistsl [`Gp`, `H`, `ctx`, `func`, `lo`, `pos`, `tp`, `u`] >> simp[]) >>
  `(?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds_mods cenv cx ty raw sv ee t /\ vv_at cenv cx ty si ss ee raw sv t /\
    ptr_vv_ok cx ty raw sv ee G tn t /\ vv_store_bound cx ty ty ee raw sv t) /\
   vv_storage_live H cx sv ee t /\
   (!tag op. sv = StackValue tag op /\ ~is_word_type ty ==> ptr_buf_ok cenv e op G t) /\
   (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G t) /\
   (copy /\ ~is_word_type ty ==>
     ?x w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var x /\
       eval_operand (vv_operand sv) t = SOME w /\ evaluate_type (get_tenv cx) ty = SOME tv /\
       val_wf tv v /\ FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
       sm.cs_next_id < ss.cs_next_id /\
       (!n b sz. local_region cenv ee.scopes t n b sz ==>
         regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
   (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
     !tv w. evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand (vv_operand sv) t = SOME w ==>
       w2n w + type_memory_size tv <= lo /\
       (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory tv v (w2n w) mem))`
  by
    (namedCases_on `sv` ["tag op", "tag p"]
     >- (`~is_word_type ty ==> ~copy` by
           (disch_tac >> strip_tac >>
            qpat_x_assum `_ ==> ?x w tv. vv_location _ = SOME LocMemory /\ _` mp_tac >>
            simp[vv_location_def]) >>
         qpat_assum `_ ==> (?raw. read_result cx raw ee = _ /\ _) /\ _` mp_tac >>
         simp[vv_location_def, vv_storage_live_def] >>
         Cases_on `is_word_type ty` >> fs[]) >>
     `tag = ty /\ ~is_word_type ty` by
       (qpat_x_assum `(?tag' op. LocatedValue tag p = StackValue tag' op) \/ _` mp_tac >>
        simp[NoAsms] >> strip_tac >> simp[]) >>
     qpat_x_assum `tag = ty` SUBST_ALL_TAC >>
     `!x. p.ptr_operand = Var x ==> not_fresh_at ss x` by
       (qpat_assum `!x. vv_operand _ = Var x ==> not_fresh_at ss x` mp_tac >> simp[vv_operand_def]) >>
     Cases_on `p.ptr_location = LocMemory`
     >- (Cases_on `copy`
         >- (qunabbrev_tac `ty` >>
             qpat_x_assum `_ ==> ?x w tv. vv_location _ = SOME LocMemory /\ _` mp_tac >>
             simp[vv_location_def, vv_operand_def, vv_storage_live_def] >>
             disch_then (qx_choosel_then [`x`,`w`,`tv`] strip_assume_tac) >>
             mp_tac ext_owned_row_endpoint_mods >>
             simp[vv_location_def, vv_operand_def] >>
             impl_tac >- (conj_tac >- metis_tac[] >>
               qpat_assum `?raw. read_result cx raw pos = _ /\ _`
                 (qx_choose_then `old` strip_assume_tac) >> qexists `old` >> simp[]) >>
             simp[]) >>
         qpat_assum `_ ==> (?raw. read_result cx raw ee = _ /\ _) /\ _`
           mp_tac >> simp[vv_location_def, vv_storage_live_def]) >>
     `~copy` by
       (strip_tac >> qpat_assum `_ ==> ?x w tv. vv_location _ = SOME LocMemory /\ _` mp_tac >>
        simp[vv_location_def]) >>
     `?raw. read_result cx raw pos = (INL v,pos) /\
        vv_holds_mods cenv cx ty raw (LocatedValue ty p) pos u /\
        ptr_vv_ok cx ty raw (LocatedValue ty p) pos Gp tp u` by
       (qpat_assum `?raw. read_result cx raw pos = _ /\ _` (qx_choose_then `old` strip_assume_tac) >>
        qexists `old` >> simp[]) >>
     qpat_x_assum `~copy ==> ee.scopes = pos.scopes /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     Cases_on `?tr. p.ptr_location = slot_loc tr`
     >- (qpat_x_assum `?tr. p.ptr_location = slot_loc tr` (qx_choose_then `tr` assume_tac) >>
         `slot_loc tr <> LocCode` by (Cases_on `tr` >> simp[slot_loc_def]) >>
         simp[vv_location_def, Excl "vv_storage_live_def"] >>
         irule ext_saved_slot_endpoint_mods >> conj_tac
         >- (qexistsl [`ctx`,`func`] >> simp[]) >>
         qexistsl [`DF H`,`Gp`,`d`,`lo`,`pos`,`ss`,`u`,`tp`,`tr`] >>
         simp[Excl "vv_storage_live_def"] >> qexists `raw` >> simp[]) >>
     Cases_on `p.ptr_location = LocCode`
     >- (simp[vv_location_def, vv_operand_def, vv_storage_live_def] >>
         conj_asm1_tac
         >- (irule (cj 1 ext_saved_code_endpoint_mods) >> simp[] >>
             qexistsl [`Gp`,`lo`,`pos`,`ss`,`u`,`tp`] >> simp[] >>
             qexists `raw` >> simp[]) >>
         disch_tac >>
         qpat_x_assum `!p ty. contract_inv _ _ _ _ _ /\ _ ==> _`
           (qspecl_then [`p`,`ty`] mp_tac) >>
         impl_tac
         >- (simp[] >> qpat_assum `?raw. read_result cx raw ee = _ /\ _`
               (qx_choose_then `out` strip_assume_tac) >> qexists `out` >> simp[]) >>
         simp[]) >>
     `p.ptr_location <> LocStorage /\ p.ptr_location <> LocTransient` by
       (qpat_x_assum `~(?tr. p.ptr_location = slot_loc tr)` (mp_tac o CONV_RULE NOT_EXISTS_CONV) >>
        simp[boolTheory.FORALL_BOOL, slot_loc_def]) >>
     `p.ptr_location = LocCalldata` by (Cases_on `p.ptr_location` >> gvs[]) >>
     qpat_x_assum `?raw. read_result cx raw pos = _ /\ _` strip_assume_tac >>
     fs[vv_holds_mods_def, vv_holds_def]) >>
  `sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
   ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  qunabbrev_tac `ty` >>
  simp[ext_pos_saved_row_mods_def, Excl "vv_storage_live_def"] >>
  qexistsl [`si`, `sm`, `ss`, `vv`, `raw`, `copy`] >> simp[]
QED
