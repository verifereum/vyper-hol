(* Array storage headers are read at the index endpoint, in the selected bank. *)
Theory bodyWriteArrayStorageMods
Ancestors
  bodyWriteArrayPacketMods bodyWriteArraySelectMods bodyWriteTargetStageMods
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullTargetArrayLoad bodyFullTargetDefs
  targetSubscriptStorage targetSubscriptSplit exprSimSubscriptArraySuffix
  appendStorageGhostPtr accountsRelProps sourceUnitExecution bodyPtrDefs
  exprSimHypsDefs exprSimFieldLayout typedMemoryCopy vyperTypeValues
  vyperStorageTrace vyperStorageFootprint vyperStorageBackend
  loweringStateRelDefs exprLoweringProps loweringPosts vyperTypeEnv
  context compileEnv emitHelper freshWrites ptrDiscipline venomState integer_word
  exprLowering venomExecSemantics unitTransformDefs contextCodegenRel codegenRel
  memLocDefs venomInst finite_map vyperValue vyperAST vyperTypeSystem

Theorem write_array_storage_source[local]:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (StoragePlace tr slot tv),t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) /\
  valid_horizon cx st0 H mid2.storage_trace ==>
  eval_operand (FST rb) t1 = SOME slot /\ FST (SND rb) = SOME (slot_loc tr) /\
  SND (SND rb) = SOME (ValPT (ArrayT et bd)) /\ op_prov G1 (FST rb) = NONE /\
  stmt_state_rel H ctx func cenv cx mid2 t2 /\
  storage_read_live H tr (get_storage cx mid2 tr) slot tv /\
  w2n slot + type_slot_size tv <= dimword (:256) /\
  (!etv cap. tv = ArrayTV etv (Dynamic cap) ==>
     w2n (lookup_storage slot (get_storage cx mid2 tr)) <= cap) /\
  ?etv. tv = ArrayTV etv bd /\ evaluate_type (get_tenv cx) et = SOME etv /\
        bound_length bd < dimword (:256)
Proof
  strip_tac >> drule_all_then strip_assume_tac write_array_reached_posts_mods >>
  drule_then strip_assume_tac write_target_storage_view_mods >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  drule_then strip_assume_tac evaluate_type_ArrayT_cases >>
  gvs[value_type_place_def] >>
  drule_then strip_assume_tac target_storage_array_type_bound >>
  qpat_x_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
  qpat_x_assum `write_array_reached_mods _`
    (strip_assume_tac o REWRITE_RULE [write_array_reached_mods_def]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H mid1.storage_trace` by
    (drule_all valid_horizon_frame >> simp[]) >>
  drule_all_then strip_assume_tac eval_base_place_storage_ready >>
  simp[value_type_place_def] >> metis_tac[]
QED

Theorem write_array_storage_header_clean[local]:
  stmt_state_rel H ctx func cenv cx es s /\ dead_lo_ok_mods H D lo cenv cx /\
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  storage_read_live H tr (get_storage cx es tr) slot tv /\ 0 < type_slot_size tv ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}
Proof
  strip_tac >>
  `storage_agree (storage_dead H tr (get_storage cx es tr))
     (get_storage cx es tr) (if tr then contract_transient s else contract_storage s)` by
    (Cases_on `tr` >> fs[stmt_state_rel_def, state_rel_def, storage_rel_def,
       transient_rel_def, vyperStorageBackendTheory.get_storage_def,
       vfmStateTheory.lookup_account_def]) >>
  drule_then assume_tac storage_agree_storage_dead >>
  irule storage_dead_key_taint_empty >>
  qexistsl [`H`, `get_storage cx es tr`, `tr`, `tv`] >> simp[] >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  fs[ghost_inv_at_mods_def, stor_taint_ok_at_def, dead_lo_ok_mods_def] >>
  Cases_on `tr` >>
  gvs[cx_dead_def, contract_storage_def, contract_transient_def,
      vfmStateTheory.lookup_account_def] >>
  rw[pred_setTheory.SUBSET_DEF] >> first_x_assum drule >> simp[]
QED

Theorem write_array_storage_loader[local]:
  compile_ptr_load ctor imm (slot_loc tr) bop sn = (len,sl) /\
  eval_operand bop s = SOME slot /\ op_taint tn bop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  w = (if tr then tload slot s else sload slot s) ==>
  ?ul Gl tl.
    array_length_loader_ok ctor imm (slot_loc tr) bop w
      sn len sl lo ctx func PG s G tn ul Gl tl /\
    op_prov Gl len = NONE /\ op_taint tl len = {}
Proof
  strip_tac >>
  `?out. len = Var out` by
    (Cases_on `tr` >>
     gvs[slot_loc_def, compile_ptr_load_def, emit_op_def,
         comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, comp_return_def, emit_def]) >>
  qabbrev_tac `opc = if tr then TLOAD else SLOAD` >>
  qabbrev_tac `inst = mk_inst sn.cs_next_id opc [bop] [out]` >>
  qabbrev_tac `u = update_var out w s` >>
  `compile_ptr_load ctor imm (slot_loc tr) bop = emit_op opc [bop]` by
    (Cases_on `tr` >> simp[Abbr `opc`, slot_loc_def, compile_ptr_load_def]) >>
  `slot_loc tr <> LocCode` by (Cases_on `tr` >> simp[slot_loc_def]) >>
  gvs[array_length_loader_ok_def] >>
  qexistsl [`u with vs_inst_idx := LENGTH sl.cs_current_insts`, `step_prov PG G inst u`,
            `step_taint inst s u tn`] >>
  conj_tac
  >- (qexists `opc` >> simp[Abbr `inst`, Abbr `u`] >>
      Cases_on `tr` >> gvs[Abbr `opc`] >>
      simp[array_length_step_ok_def, step_inst_base_def, mk_inst_def,
           exec_read1_def, access_ok_def, taint_ok_def,
           inst_mem_below_frontier_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, mem_read_ops_def, mem_write_ops_def]) >>
  Cases_on `tr` >> gvs[Abbr `inst`, Abbr `u`, Abbr `opc`] >>
  simp[op_taint_def, op_prov_def, step_taint_def, step_prov_def, mk_inst_def,
       set_prov_def, set_var_taint_def, mem_taint_def, out_taint_def, out_prov_def,
       mem_read_ops_def, mem_write_ops_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  fs[op_taint_def]
QED

Theorem write_array_storage_length_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (StoragePlace tr slot tv),t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) /\
  valid_horizon cx st0 H mid2.storage_trace /\
  eval_operand (FST rb) t2 = SOME slot /\ op_taint tn2 (FST rb) = {} ==>
  FST (SND rb) = SOME (slot_loc tr) /\ SND (SND rb) = SOME (ValPT (ArrayT et bd)) /\
  allocas_from lo t2 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t2) /\
  (!n. bd = Fixed n ==>
    (case bd of Fixed k => n2w k | Dynamic k => lookup_storage slot (get_storage cx mid2 tr)) = n2w n) /\
  (!cap len sl. bd = Dynamic cap /\
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca (slot_loc tr) (FST rb) sn = (len,sl) ==>
    ?ul Gl tl.
      array_length_loader_ok cenv.ce_is_ctor cenv.ce_imm_alloca (slot_loc tr) (FST rb)
        (lookup_storage slot (get_storage cx mid2 tr))
        sn len sl lo ctx func PG t2 G2 tn2 ul Gl tl /\
      op_prov Gl len = NONE /\ op_taint tl len = {})
Proof
  strip_tac >> drule_all_then strip_assume_tac write_array_storage_source >>
  drule_all_then strip_assume_tac write_array_reached_posts_mods >>
  `allocas_from lo t2` by fs[ghost_inv_at_mods_def] >>
  qpat_x_assum `write_array_reached_mods _`
    (strip_assume_tac o REWRITE_RULE [write_array_reached_mods_def]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  `w2n slot + type_slot_size (ArrayTV etv (Dynamic cap)) <= dimword (:256)` by
    (once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
  drule_all_then assume_tac (cj 2 target_storage_array_len_ok) >>
  `dead_lo_ok_mods H (DF H) lo cenv cx` by fs[write_target_entry_mods_def] >>
  `0 < type_slot_size (ArrayTV etv (Dynamic cap))` by simp[type_slot_size_def] >>
  `key_taint (if tr then tn2.t_trans else tn2.t_stor) slot = {}` by
    (drule_all write_array_storage_header_clean >> simp[]) >>
  irule write_array_storage_loader >> simp[] >> qexists `slot` >> simp[]
QED

Theorem write_array_storage_range[local]:
  i = (if sgn then w2i iw else &(w2n iw)) /\
  bound_length bd < dimword (:256) /\
  (!cap. bd = Dynamic cap ==> w2n lw <= cap) /\
  nw = (case bd of Fixed n => n2w n | Dynamic n => lw) ==>
  (idx_in_range sgn iw nw <=>
    0 <= i /\ Num i < bound_length bd /\
      (case bd of Fixed _ => T | Dynamic _ => Num i < w2n lw)) /\
  (idx_in_range sgn iw nw ==> iw = i2w i)
Proof
  strip_tac >> reverse conj_tac
  >- (strip_tac >> Cases_on `sgn` >> gvs[integer_wordTheory.i2w_def]) >>
  `!n. n < dimword (:256) ==>
     (idx_in_range sgn iw (n2w n) <=> 0 <= i /\ Num i < n)` by
    (rpt strip_tac >> drule idx_in_range_integer >> disch_then (qspecl_then [`iw`,`sgn`] mp_tac) >>
     simp[] >> metis_tac[integerTheory.INT_OF_NUM, integerTheory.INT_LT]) >>
  Cases_on `bd` >> gvs[] >>
  qpat_x_assum `!n. n < dimword (:256) ==> _` (qspec_then `w2n lw` mp_tac) >>
  simp[wordsTheory.w2n_lt] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem write_array_storage_address[local]:
  expr_sim_inv_mods mods cenv cx env ee /\
  evaluate_type (get_tenv cx) et = SOME etv /\ 0 <= i ==>
  (if (case bd of Dynamic _ => T | _ => F) then
     slot + n2w (word_scale (slot_loc tr)) else slot) +
      i2w i * n2w (elem_size_in_location cenv (slot_loc tr) et) =
  (slot : bytes32) + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + Num i * type_slot_size etv)
Proof
  strip_tac >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule typed_copy_memory_size >> qexists `get_tenv cx` >>
     fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  `word_scale (slot_loc tr) = 1 /\
   elem_size_in_location cenv (slot_loc tr) et = type_slot_size etv` by
    (Cases_on `tr` >> simp[slot_loc_def, word_scale_def, elem_size_in_location_def,
         is_slot_addressed_def, slot_count_of_memory_size]) >>
  drule target_storage_array_offset >>
  disch_then (qspecl_then [`slot`,`etv`,`case bd of Fixed _ => F | Dynamic _ => T`] mp_tac) >>
  Cases_on `bd` >> simp[]
QED

(* The source result and the child pointer use the same bounds test. Changing
   the gas-observation tail does not change the selected source storage bank. *)
Theorem write_array_storage_extend_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (StoragePlace tr slot tv),t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) /\
  valid_horizon cx st0 H mid2.storage_trace /\
  v = IntV i /\ i = (if is_signed_type (expr_type e) then w2i iw else &(w2n iw)) /\
  op_prov G2 (FST rb) = op_prov G1 (FST rb) /\
  nw = (case bd of Fixed n => n2w n | Dynamic n => lookup_storage slot (get_storage cx mid2 tr)) /\
  write_array_select_frame
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (StoragePlace tr slot tv),t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) (slot_loc tr,slot,iw,nw) (t3,G3,tn3) ==>
  ?child msg.
    (!gs. extend_place cx (PlaceR (StoragePlace tr slot tv)) (ValueSubscript v)
              (mid2 with gas_obs := gs) =
          (if idx_in_range (is_signed_type (expr_type e)) iw nw then INL child
           else INR (Error (RuntimeError msg)),mid2 with gas_obs := gs)) /\
    (idx_in_range (is_signed_type (expr_type e)) iw nw ==>
      write_target_location_mods cenv cx (SubscriptTarget bt e) mid2 child vt r G3 t3 /\
      target_ptr_ok cenv child r G3 tn3 t3 /\
      SND (SND r) = SOME (value_type_place vt) /\
      (!x. FST r = Var x ==> not_fresh_at sb x))
Proof
  strip_tac >> drule_all_then strip_assume_tac write_array_storage_source >>
  `!cap. bd = Dynamic cap ==> w2n (lookup_storage slot (get_storage cx mid2 tr)) <= cap` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> qexists `etv` >> simp[]) >>
  drule_all_then strip_assume_tac write_array_storage_range >>
  qpat_x_assum `write_array_reached_mods _`
    (strip_assume_tac o REWRITE_RULE [write_array_reached_mods_def]) >>
  `vt = Type et` by gvs[type_place_target_SubscriptTarget, subscript_vtype_def, AllCaseEqs()] >>
  drule_all_then strip_assume_tac write_array_select_cut_mods >>
  `FST (SND r) = SOME (slot_loc tr) /\ SND (SND r) = SOME (ValPT et)` by
    (qpat_x_assum `r = (_,_,_)` (mp_tac o Q.AP_TERM `SND`) >> simp[NoAsms]) >>
  qpat_x_assum `r = (_,_,_)` kall_tac >>
  drule_then assume_tac target_subscript_suffix_var >>
  qabbrev_tac `offset = (case bd of Fixed _ => 0 | Dynamic _ => 1) + Num i * type_slot_size etv` >>
  qexistsl [`PlaceR (StoragePlace tr (slot + n2w offset) etv)`,
           `case bd of Fixed _ => "array fixed oob" | Dynamic cap =>
              if 0 <= i /\ Num i < cap then "array dynamic length oob"
              else "array dynamic capacity oob"`] >>
  conj_tac
  >- (`!gs. get_storage cx (mid2 with gas_obs := gs) tr = get_storage cx mid2 tr` by
        (Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
      simp[extend_place_storage_array_index, Abbr `offset`] >>
      Cases_on `bd` >> gvs[] >> rpt IF_CASES_TAC >> gvs[]) >>
  strip_tac >>
  qpat_x_assum `write_array_select_frame _ _ _`
    (strip_assume_tac o REWRITE_RULE [write_array_select_frame_def]) >>
  qpat_x_assum `idx_in_range _ _ _ ==> ~t3.vs_halted /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  `0 <= i /\ iw = i2w i` by fs[] >>
  `eval_operand (FST r) t3 = SOME (slot + n2w offset)` by
    (drule_all write_array_storage_address >>
     disch_then (qspecl_then [`tr`,`slot`,`bd`] (fn size =>
       qpat_assum `iw = i2w i` (fn idx =>
         qpat_assum `eval_operand (FST r) t3 = SOME _`
           (mp_tac o PURE_REWRITE_RULE [idx, size])))) >>
     simp[NoAsms, Abbr `offset`]) >>
  simp[write_target_location_mods_def, place_ptr_rel_def, place_readable_def,
       target_ptr_ok_def, value_type_place_def]
QED
