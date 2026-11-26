(* Transport a single saved argument through the actual positional suffix. *)
Theory bodyAbiEncodeSuffixRowMods
Ancestors
  bodyAbiEncodePackedPostMods bodyFullExtCallSavedOperand
  bodyExtSavedValueEndpointMods bodyExtSavedCodeEndpointMods bodyExtSavedCtorReadMods
  bodyExtOwnedRowEndpointMods bodyExtBorrowedFootprintMods
  abiEncodeArgsScopes exprLoweringProps wordArgsPtr stateRelProj
  stmtSimAssignStorageCopy exprPtrUnwrapStorageFacts accountsRelProps
  vyperStorageBackend bodyPtrDefs ptrDiscipline venomState vfmState
  loweringStateRelDefs loweringPosts arithmetic context bodyFullPostsMods
  sourceUnitExecution bodyFullShadowBodyInv vyperState exprSimMemDefs

Triviality suffix_eval_operand:
  (!x. op = Var x ==> not_fresh_at ss x) /\
  (!x w. not_fresh_at ss x /\ lookup_var x m = SOME w ==> lookup_var x t = SOME w) /\
  t.vs_labels = m.vs_labels /\ eval_operand op m = SOME w ==>
  eval_operand op t = SOME w
Proof
  Cases_on `op` >> simp[eval_operand_def]
QED

(* The reached slot proof needs agreement on the live bytes at the final
   endpoint, not agreement between the source backends at the two cuts. *)
Triviality suffix_slot_target:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx ee t /\
  ghost_inv_at_mods D lo d cenv cx ee G tn t /\ dead_lo_ok_mods H D lo cenv cx /\
  w2n w + type_slot_size tv <= dimword (:256) /\
  storage_read_live H tr (get_storage cx ee tr) w tv ==>
  storage_range_agree (get_storage cx ee tr)
    (if tr then contract_transient t else contract_storage t) w tv /\
  (!k b. w2n w <= w2n k /\ w2n k < w2n w + type_slot_size tv /\
      (k,b) IN (if tr then tn.t_trans else tn.t_stor) ==>
    dead_bytes (if tr then contract_transient t else contract_storage t) (w2n w) tv (w2n k) b)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (qspec_then `tr` assume_tac) storage_copy_initial_agree >>
  drule_all_then assume_tac storage_range_agree_of_live >>
  conj_tac >- first_assum ACCEPT_TAC >>
  drule_then assume_tac storage_agree_storage_dead >>
  drule_then assume_tac storage_range_agree_dead_bytes >>
  qpat_assum `storage_read_live _ _ _ _ _`
    (assume_tac o REWRITE_RULE [storage_read_live_def]) >>
  rpt strip_tac >>
  `storage_dead H tr (if tr then contract_transient t else contract_storage t) (w2n k) b` by
    (Cases_on `tr` >>
     fs[ghost_inv_at_mods_def,stor_taint_ok_at_def,dead_lo_ok_mods_def,cx_dead_def,
        pred_setTheory.SUBSET_DEF,contract_storage_def,contract_transient_def,
        vfmStateTheory.lookup_account_def] >>
     first_x_assum drule >> Cases_on `t.vs_call_ctx.cc_address = cx.txn.target` >> simp[]) >>
  `storage_dead H tr (get_storage cx ee tr) (w2n k) b` by
    (qpat_assum `storage_dead _ _ _ = storage_dead _ _ _`
       (fn eq => qpat_assum `storage_dead _ _ _ (w2n k) b` (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  qpat_assum `!j b. storage_dead _ _ _ j b ==> _`
    (qspecl_then [`w2n k`,`b`] mp_tac) >> simp[]
QED

Theorem abi_encode_suffix_row_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env mid /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx mid m /\
  dead_lo_ok_mods H (DF H) lo cenv cx /\
  abi_encode_saved_row_mods lo cenv cx sa ss e sv v si sm ss vv copy H mid Gm tm m /\
  (copy = exprs_can_mutate cenv xs) /\
  compile_abi_encode_args compile_expr cenv xs ss = (svs,sb) /\
  eval_exprs cx xs (mid with gas_obs := obs) = (INL vs,ee with gas_obs := []) /\
  abi_encode_packed_post_mods mods DF lo d ctx func cenv cx env
    xs svs ss sb mid m Gm tm H (INL vs) ee G tn t /\
  (~copy /\ vv_location sv = SOME LocCode ==> ee.immutables = mid.immutables) /\
  t.vs_labels = m.vs_labels /\
  (!p tr w tv. ~copy /\ ~is_word_type (lowered_value_type cenv e) /\
       sv = LocatedValue (lowered_value_type cenv e) p /\
       p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand m = SOME w /\
       evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
       read_storage_slot cx tr w tv mid = (INL v,mid) ==>
       read_storage_slot cx tr w tv ee = (INL v,ee) /\
       storage_read_live H tr (get_storage cx ee tr) w tv /\
       slots_in_range (get_storage cx ee tr) (w2n w) tv) ==>
  abi_encode_saved_row_mods lo cenv cx sa sb e sv v si sm ss vv copy H ee G tn t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `abi_encode_saved_row_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  qhdtm_x_assum `abi_encode_packed_post_mods`
    (qx_choose_then `vs'` (map_every assume_tac o CONJUNCTS) o
     REWRITE_RULE [abi_encode_packed_post_mods_def]) >>
  qpat_x_assum `LIST_REL _ _ _` kall_tac >>
  `ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id` by
    (mp_tac (Q.INST [`f` |-> `compile_expr`, `st` |-> `ss`,
                      `args` |-> `xs`, `cenv` |-> `cenv`]
               ci_mono_compile_abi_encode_args) >>
     simp[cj 1 compile_expr_ci_mono,ci_mono_def]) >>
  drule_then (map_every assume_tac o CONJUNCTS) (cj 1 compile_expr_grows) >>
  `sm.cs_next_var <= ss.cs_next_var` by
    (qspecl_then [`cenv`,`copy`,
        `ext_call_arg_value (lowered_value_type cenv e) vv`,`sm`] mp_tac
       ci_mono_compile_snapshot_vv >> simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv ss` by
    (irule local_ptrs_reserved_next_var >> qexists `si` >> simp[] >> decide_tac) >>
  `!x. vv_operand sv = Var x ==> not_fresh_at ss x` by
    (rpt strip_tac >> drule_all extcall_saved_operand_not_fresh >> simp[]) >>
  `~copy ==> ee.scopes = mid.scopes` by
    (strip_tac >>
     `~exprs_can_mutate cenv xs` by fs[] >>
     drule_all eval_exprs_no_mutation_scopes >> simp[]) >>
  `alloca_inv m` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx mid m`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `!n b sz. local_region cenv mid.scopes m n b sz <=> local_region cenv ee.scopes t n b sz` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_local_regions) >>
     conj_tac >- simp[] >> conj_tac >- (qexistsl [`ee`,`ss`] >> simp[]) >>
     qexistsl [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
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
     `!tv w. ~is_word_type ty /\ expr_val_at cenv cx ty si ss mid v (vv_operand sv) m /\
       evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand (vv_operand sv) m = SOME w ==>
       val_wf tv v /\ mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
         mem_bytes_at (w2n w) (val_footprint tv v) m.vs_memory /\
       (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn.t_mem ==> i IN tm.t_mem)` by
       (qx_genl_tac [`tv`,`w`] >> strip_tac >>
        `ee.scopes = mid.scopes` by metis_tac[] >>
        irule (INST_TYPE [alpha |-> ``:num # num``, beta |-> ``:num # num``]
          ext_borrowed_footprint_frame) >>
        qexistsl [`Gm`,`G`,`cenv`,`cx`,`ee`,`mid`,`lo`,`vv_operand sv`,`si`,`ss`,`ss`,`ty`] >>
        simp[]) >>
     irule ext_saved_value_endpoint_mods >> simp[Abbr `ty`] >>
     qexistsl [`Gm`,`H`,`ctx`,`func`,`lo`,`mid`,`tm`,`m`] >> simp[]) >>
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
       (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory tv v (w2n w) mem))` by
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
             mp_tac (Q.INST [`u` |-> `m`,`pos` |-> `mid`,`Gp` |-> `Gm`,`tp` |-> `tm`]
                       ext_owned_row_endpoint_mods) >>
             simp[vv_location_def, vv_operand_def] >>
             impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
               qpat_assum `?raw. read_result cx raw mid = _ /\ _`
                 (qx_choose_then `old` strip_assume_tac) >> qexists `old` >> simp[]) >>
             simp[]) >>
         qpat_assum `_ ==> (?raw. read_result cx raw ee = _ /\ _) /\ _`
           mp_tac >> simp[vv_location_def, vv_storage_live_def]) >>
     `~copy` by
       (strip_tac >> qpat_assum `_ ==> ?x w tv. vv_location _ = SOME LocMemory /\ _` mp_tac >>
        simp[vv_location_def]) >>
     Cases_on `?tr. p.ptr_location = slot_loc tr` >- suspend "slot" >>
     Cases_on `p.ptr_location = LocCode` >- suspend "code" >>
     suspend "calldata") >>
  qunabbrev_tac `ty` >>
  asm_rewrite_tac[abi_encode_saved_row_mods_def] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >> qexists `raw` >> simp[]
QED

Resume abi_encode_suffix_row_mods[slot]:
  qpat_x_assum `?tr. p.ptr_location = slot_loc tr` (qx_choose_then `tr` assume_tac) >>
  `slot_loc tr <> LocCode` by (Cases_on `tr` >> simp[slot_loc_def]) >>
  simp[vv_location_def, Excl "vv_storage_live_def"] >>
  qpat_x_assum `?raw. read_result cx raw mid = _ /\ _` (qx_choose_then `old` strip_assume_tac) >>
  `?w. eval_operand p.ptr_operand m = SOME w /\ storage_holds cx tr ty old w mid m` by
    (Cases_on `tr` >> gvs[vv_holds_mods_def,vv_holds_def,slot_loc_def]) >>
  `eval_operand p.ptr_operand t = SOME w` by (drule_all suffix_eval_operand >> simp[]) >>
  `op_taint tn p.ptr_operand = {}` by
    (Cases_on `p.ptr_operand` >>
     gvs[ptr_vv_ok_def,ghost_kept_at_def,op_taint_def] >> metis_tac[]) >>
  qhdtm_x_assum `storage_holds` (strip_assume_tac o REWRITE_RULE [storage_holds_def]) >>
  `v' = v` by gvs[] >> qpat_x_assum `v' = v` SUBST_ALL_TAC >>
  rename1 `evaluate_type (get_tenv cx) ty = SOME tv` >>
  qpat_assum `!q tr w tv. _ ==> read_storage_slot cx tr w tv ee = _ /\ _`
    (qspecl_then [`p`,`tr`,`w`,`tv`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n w + type_slot_size tv <= dimword (:256)` by fs[storage_range_agree_def] >>
  drule_all_then strip_assume_tac suffix_slot_target >>
  `storage_holds cx tr ty (Value v) w ee t` by
    (simp[storage_holds_def,read_result_def,return_def] >> qexists `tv` >> simp[]) >>
  reverse conj_tac >- (Cases_on `tr` >> gvs[slot_loc_def,vv_storage_live_def]) >>
  qexists `Value v` >> Cases_on `tr` >>
  gvs[slot_loc_def,vv_holds_mods_def,vv_holds_def,vv_at_def,vv_store_bound_def,
      ptr_vv_ok_def,read_result_def,return_def,contract_storage_def,contract_transient_def,
      vfmStateTheory.lookup_account_def]
QED

Resume abi_encode_suffix_row_mods[code]:
  `ee.immutables = mid.immutables` by
    (qpat_assum `~copy /\ vv_location _ = SOME LocCode ==> _` mp_tac >> simp[vv_location_def]) >>
  simp[vv_location_def,vv_operand_def,vv_storage_live_def] >> conj_asm1_tac
  >- (irule (cj 1 ext_saved_code_endpoint_mods) >> simp[] >>
      qexistsl [`Gm`,`lo`,`mid`,`ss`,`m`,`tm`] >> simp[] >>
      qpat_assum `?raw. read_result cx raw mid = _ /\ _`
        (qx_choose_then `old` strip_assume_tac) >> qexists `old` >> simp[]) >>
  disch_tac >> pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  match_mp_tac (Q.INST [`D` |-> `DF H`, `entry` |-> `mid`]
    (Q.INST_TYPE [`:'a` |-> `:256`] ext_saved_ctor_read_linked)) >>
  simp[] >>
  qpat_assum `?raw. read_result cx raw ee = _ /\ _`
    (qx_choose_then `out` strip_assume_tac) >> qexists `out` >> simp[]
QED

Resume abi_encode_suffix_row_mods[calldata]:
  `p.ptr_location <> LocStorage /\ p.ptr_location <> LocTransient` by
    (qpat_x_assum `~(?tr. p.ptr_location = slot_loc tr)` (mp_tac o CONV_RULE NOT_EXISTS_CONV) >>
     simp[boolTheory.FORALL_BOOL, slot_loc_def]) >>
  `p.ptr_location = LocCalldata` by (Cases_on `p.ptr_location` >> gvs[]) >>
  qpat_x_assum `?raw. read_result cx raw mid = _ /\ _` strip_assume_tac >>
  qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_mods_def, vv_holds_def]
QED

Finalise abi_encode_suffix_row_mods
