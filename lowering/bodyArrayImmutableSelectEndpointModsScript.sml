(* Qualified immutable coordinates and read-only selection at the key cut. *)
Theory bodyArrayImmutableSelectEndpointMods
Ancestors
  bodyArrayNoCopyCutsMods bodyFullSubscriptLiveImmSelect
  exprSimSubscriptArrayLiveImmutableSuffix exprSimSubscriptArraySuffix
  exprSimSubscriptArrayFramed immutableRegionFrameProps targetSubscriptMemory
  bodyForRangeScalarFrameMods bodyFullUnwrapRun gasOutcomeFullPostMods
  exprSimSubscriptArrayEndpoint wordArgsPtr stateRelProj exprSimProps
  loweringPosts context bodyFullPostsMods bodyPtrDefs immutableCopyExecution
  valueEncoding valueEncodingDefs ptrDiscipline exprSimCopy exprSimWordArgs
  vyperAST exprSimDefs exprLoweringProps bodyInvSplit exprSimHypsDefs loweringStateRelDefs
  memSafeRun fragGasPath fragExec venomExecProofs venomState
  exprOperandVar compileEnv exprLowering vyperStorageFootprint
  gasExplicitSites exprSimMemDefs bodyFullShadowBodyInv
  vyperTypeValues vyperAssignPreservesType vyperArray vyperTyping
  vyperValueOperation vyperPlaceTyping vyperState valueEncodingProps finite_map words

Theorem immutable_selected_source[local]:
  FLOOKUP (case ALOOKUP fin.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME v ==>
  let child = PlaceR (ImmutablePlace src id (path ++ [ValueSubscript (IntV i)])) in
  (!tail. select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path))
    (ValueSubscript (IntV i)) (fin with gas_obs := tail) = (INL child,fin with gas_obs := tail)) /\
  read_result cx child fin = (INL v,fin)
Proof
  simp[LET_THM] >> strip_tac >>
  `evaluate_subscripts (ArrayTV etv bd) (ArrayV av) [ValueSubscript (IntV i)] = INL v` by
    simp[evaluate_subscripts_def] >>
  drule_all live_immutable_select >>
  disch_then (qspec_then `ArrayT et bd` strip_assume_tac) >> simp[] >>
  qpat_assum `select_result _ _ _ _ _ = _` (assume_tac o AP_TERM ``SND : ((eval_result + exception) # evaluation_state) -> evaluation_state``) >>
  fs[] >>
  `!tr slot vt. PlaceR (ImmutablePlace src id path) <> PlaceR (StoragePlace tr slot vt)` by simp[] >>
  drule_all_then (fn th => simp[th]) select_result_nonstorage_gas_obs
QED

Theorem immutable_selected_pointer[local]:
  ALOOKUP cenv.ce_modules src = SOME tops /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP fin.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  eval_operand dst q = SOME (n2w (off+k) + n2w
    ((case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv)) ==>
  vv_place_ptr_mods cenv cx fin q
    (PlaceR (ImmutablePlace src id (path ++ [ValueSubscript (IntV i)])))
    (LocatedValue et (mk_ptr dst LocCode))
Proof
  strip_tac >> drule_all_then assume_tac array_element_step_offset >>
  drule_all_then strip_assume_tac mem_path_offset_snoc >>
  simp[vv_place_ptr_mods_def, vv_place_ptr_def, mk_ptr_def] >>
  pure_rewrite_tac[GSYM word_add_n2w, arithmeticTheory.ADD_ASSOC, WORD_ADD_ASSOC] >>
  REFL_TAC
QED

(* The linked constructor frame gives robust root bytes. A selected path
   consumes only its own slice of those bytes. *)
Theorem immutable_path_robust_bytes[local]:
  mem_path_offset itv path = SOME (k,tv) /\
  evaluate_subscripts itv iv path = INL v /\
  off + type_memory_size itv < dimword (:256) /\
  off + type_memory_size itv <= lo /\
  value_has_type itv iv /\ well_formed_type_value itv /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory itv iv off mem) ==>
  w2n (n2w (off+k):bytes32) + type_memory_size tv <= lo /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n (n2w (off+k):bytes32)) mem)
Proof
  strip_tac >> drule_then strip_assume_tac mem_path_offset_sound >>
  `off+k < dimword (:256)` by decide_tac >> simp[w2n_n2w] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all_then mp_tac mem_path_offset_current_value >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem immutable_array_header[local]:
  value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV av) /\
  (ctor ==> w2n a + type_memory_size (ArrayTV etv (Dynamic cap)) <= lo /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV av) (w2n a) mem)) /\
  (~ctor ==> w2n a <= LENGTH s.vs_data_section /\
    val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV av) (w2n a) s.vs_data_section) ==>
  immutable_copy_read ctor a s = n2w (array_length (ArrayTV etv (Dynamic cap)) av) /\
  (ctor ==> w2n a + 32 <= lo /\ mem_word_taint tn.t_mem (w2n a) = {}) /\
  (~ctor ==> w2n a <= LENGTH s.vs_data_section)
Proof
  strip_tac >> Cases_on `av` >> gvs[value_has_type_def] >>
  Cases_on `ctor` >> gvs[immutable_copy_read_def,array_length_def]
  >- (`val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV l)) (w2n a) s.vs_memory` by
        simp[mem_agree_outside_def] >>
      conj_tac >- fs[val_in_memory_dynarray, mem_word_at_eq_mload] >>
      conj_tac >- fs[type_memory_size_def] >>
      drule_then ACCEPT_TAC bodyPtrBopInMemoryContentsTheory.dynarray_memory_header_clean) >>
  fs[val_in_memory_dynarray, mem_word_at_def]
QED

(* Read-only selection adds fresh variables but no source writeback. *)
Theorem immutable_selected_linked_post[local]:
  stmt_state_rel H ctx func cenv cx es s0 /\
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid raw bvv s /\
  expr_post_mods H ctx func cenv cx idx mid sm st2 s fin key iop it /\
  is_word_type (expr_type idx) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= st2.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  copy_old_operand st2 iop /\ (!l. iop <> Label l) /\
  (!x. not_fresh_at st2 x ==> lookup_var x q = lookup_var x it) /\
  q.vs_allocas = it.vs_allocas /\ q.vs_memory = it.vs_memory /\
  stmt_state_rel H ctx func cenv cx fin q /\ immutable_frame_mods func cenv cx fin q /\
  vv_holds_mods cenv cx et (PlaceR (ImmutablePlace src id path))
    (LocatedValue et (mk_ptr dst LocCode)) fin q /\
  vv_place_ptr_mods cenv cx fin q (PlaceR (ImmutablePlace src id path))
    (LocatedValue et (mk_ptr dst LocCode)) ==>
  vv_post_mods H ctx func cenv cx (Subscript et obj idx) es sa sb s0 fin
    (PlaceR (ImmutablePlace src id path)) (LocatedValue et (mk_ptr dst LocCode)) q
Proof
  strip_tac >>
  `expr_post H ctx func cenv cx idx mid sm st2 s fin key iop q` by
    (fs[expr_post_mods_def] >> irule word_expr_post_readonly_tail >>
     simp[] >> qexistsl [`it`,`st2`] >> fs[copy_old_operand_def]) >>
  `wb_frame cenv es mid sa s0 s` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ s`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ q`
    (mp_then Any assume_tac expr_post_frame) >>
  `wb_frame cenv es fin sa s0 q` by (drule_all wb_frame_trans >> simp[]) >>
  `~expr_has_effect obj /\ ~expr_has_effect idx ==> pure_frame cenv func es sa s0 q` by
    (strip_tac >>
     `pure_frame cenv func es sa s0 s` by fs[vv_post_mods_def] >>
     `pure_frame cenv func mid sm s q` by (drule_then irule expr_post_pure_frame >> simp[]) >>
     irule pure_frame_trans >> asm_rewrite_tac[] >> qexistsl [`mid`,`sm`,`s`] >>
     qpat_assum `wb_frame _ es mid _ _ s` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
     qpat_assum `expr_post_mods _ _ _ _ _ idx _ _ _ _ _ _ _ it`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     qpat_assum `expr_post _ _ _ _ _ idx _ _ _ _ _ _ _ it`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def] o MATCH_MP expr_post_frame) >>
     asm_rewrite_tac[]) >>
  `storage_well_formed_on cx fin (FST H)` by fs[expr_post_def] >>
  fs[vv_post_mods_def,expr_type_def,vv_at_def,vv_storage_live_def,mk_ptr_def,
     expr_has_effect_thm,wb_frame_def] >>
  qpat_assum `q.vs_memory = it.vs_memory` (PURE_ONCE_REWRITE_TAC o single o SYM) >>
  first_assum ACCEPT_TAC
QED

Theorem immutable_selection_edge_data[local]:
  gas_path_edge ctx func s n (OK t) ==> t.vs_data_section = s.vs_data_section
Proof
  simp[gas_path_edge_def, exit_result_def] >> rpt strip_tac >> gvs[]
  >- (drule_then strip_assume_tac step_inst_ok_code_data >> simp[])
  >- (drule_then strip_assume_tac step_inst_ok_code_data >>
      drule_then (fn th => PURE_ONCE_REWRITE_TAC [th]) eval_phis_only_updates_vs_vars >>
      simp[]) >>
  simp[jump_to_def] >>
  qpat_assum `OK _ = step_inst _ _ _ _` (assume_tac o SYM) >> fs[exit_result_def]
QED

Theorem immutable_selection_path_data[local]:
  !ctx func s n r. gas_path ctx func s n r ==>
    !q. r = OK q ==> q.vs_data_section = s.vs_data_section
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac >> simp[exit_result_def]
  >- (rpt strip_tac >> drule_then assume_tac immutable_selection_edge_data >> simp[]) >>
  rpt strip_tac >> gvs[exit_result_def]
QED

Theorem immutable_live_array_buffer[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env fin /\
  dead_lo_ok_mods H D lo cenv cx /\ ghost_inv_at_mods D lo d cenv cx fin G tn s /\
  immutable_frame_mods func cenv cx fin s /\ ALOOKUP cenv.ce_modules src = SOME tops /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP fin.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,tv) /\ evaluate_subscripts itv iv path = INL v /\
  off + type_memory_size itv < dimword (:256) /\
  value_has_type itv iv /\ well_formed_type_value itv ==>
  (cenv.ce_is_ctor ==> w2n (n2w (off+k):bytes32) + type_memory_size tv <= lo /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory tv v (w2n (n2w (off+k):bytes32)) mem)) /\
  (~cenv.ce_is_ctor ==> w2n (n2w (off+k):bytes32) <= LENGTH s.vs_data_section /\
    val_in_memory tv v (w2n (n2w (off+k):bytes32)) s.vs_data_section)
Proof
  strip_tac >> Cases_on `cenv.ce_is_ctor`
  >- (`immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor fin s` by
        fs[immutable_frame_mods_def] >>
      `off + type_memory_size itv <= lo /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory itv iv off mem)` by
        (irule qualified_immutable_ctor_frame_mods >>
         qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
         qpat_assum `expr_sim_inv_mods _ _ _ _ _` (irule_at Any) >>
         qpat_assum `FLOOKUP cenv.ce_module_vars _ = _` (irule_at Any) >>
         qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` (irule_at Any) >>
         goal_assum (drule_at (Pat `ALOOKUP fin.immutables _ = SOME _`)) >>
         simp[] >> qexists_tac `H` >> simp[]) >>
      drule_all_then strip_assume_tac immutable_path_robust_bytes >> simp[]) >>
  `immutables_rel cenv cx.txn.target src F fin s` by
    fs[immutable_frame_mods_def,immutables_rel_mods_def] >>
  pop_assum (mp_tac o REWRITE_RULE [immutables_rel_def,LET_THM]) >>
  simp[] >> disch_then (qspecl_then [`id`,`itv`,`iv`,`off`] mp_tac) >>
  simp[] >> strip_tac >> drule_all_then assume_tac mem_path_offset_current_value >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `off+k < dimword (:256) /\ off+k <= LENGTH s.vs_data_section` by decide_tac >>
  simp[w2n_n2w,AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
  >> (gvs[])
QED

Theorem immutable_selected_error[local]:
  FLOOKUP (case ALOOKUP fin.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  ~valid_index (ArrayTV etv bd) av i ==>
  !tail. select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path))
      (ValueSubscript (IntV i)) (fin with gas_obs := tail) =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")), fin with gas_obs := tail)
Proof
  strip_tac >>
  `!al. av = SArrayV al ==> ?n. bd = Fixed n` by
    (rpt strip_tac >> Cases_on `bd` >> gvs[value_has_type_def]) >>
  drule_all live_immutable_select_error >>
  disch_then (qspec_then `ArrayT et bd` assume_tac) >>
  `SND (select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path))
      (ValueSubscript (IntV i)) fin) = fin` by simp[] >>
  `!tr slot vt. PlaceR (ImmutablePlace src id path) <> PlaceR (StoragePlace tr slot vt)` by simp[] >>
  drule_all_then (fn th => simp[th]) select_result_nonstorage_gas_obs
QED

Theorem immutable_code_compile_normalize[local]:
  compile_array_subscript bop iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic _ => 0)
      (word_scale LocCode) (elem_size_in_location cenv LocCode et) sgn
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) st2 = (dst,sb) /\
  type_memory_bytes cenv et = type_memory_size etv /\
  value_has_type (ArrayTV etv bd) (ArrayV av) ==>
  let dyn = (case bd of Fixed _ => F | Dynamic _ => T);
      cnt = array_length (ArrayTV etv bd) av in
  compile_array_subscript bop iop dyn (if dyn then 0 else cnt) 32
    (type_memory_size etv) sgn (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode)
    st2 = (dst,sb)
Proof
  Cases_on `bd` >> Cases_on `av` >>
  simp[LET_THM,value_has_type_def,array_length_def,word_scale_def,
       elem_size_in_location_def,is_slot_addressed_def] >> strip_tac >> simp[]
  >> (gvs[])
QED

Theorem immutable_region_clean[local]:
  stmt_state_rel H ctx func cenv cx fin it /\ local_ptrs_reserved cenv st2 /\
  ghost_inv_at_mods D lo d cenv cx fin Gi tni it /\ lo <> 0 /\
  cenv.ce_imm_alloca = SOME region ==>
  eval_operand region it = SOME 0w /\ copy_old_operand st2 region /\
  op_taint tni region = {} /\ op_prov Gi region = NONE
Proof
  strip_tac >> conj_tac
  >- (drule_all_then ACCEPT_TAC bodyPtrBopInRepresentationTheory.membership_immutable_base_value) >>
  Cases_on `region` >> simp[copy_old_operand_def,op_taint_def,op_prov_def] >>
  conj_tac >- (drule_all local_ptrs_reserved_imm_base >> simp[]) >>
  fs[ghost_inv_at_mods_def,op_taint_def]
QED

Theorem immutable_path_layout[local]:
  mem_path_offset itv path = SOME (k,tv) /\ evaluate_subscripts itv iv path = INL v /\
  value_has_type itv iv /\ well_formed_type_value itv ==> sub_layout itv iv k tv v
Proof
  strip_tac >> rewrite_tac[sub_layout_def] >> conj_tac
  >- (drule_then strip_assume_tac mem_path_offset_sound >> simp[]) >>
  rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC mem_path_offset_current_value
QED

(* Read the immutable at the reached key state, not at the saved base state.
   The caller certifies that the captured path is still live at this cut. *)
Theorem immutable_select_endpoint_mods:
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0 (es,s0,G0,tn0)
    (sa,sm,st2,sb,LocatedValue (ArrayT et bd) p,iop,dst,LocCode)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,PlaceR (ImmutablePlace src id path),s,G1,tn1) (gs2,fin,IntV i,it,Gi,tni) /\
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env fin /\
  p.ptr_location = LocCode /\ expr_type obj = ArrayT et bd /\
  post_value_type cenv obj = ArrayT et bd /\ post_value_type cenv idx = expr_type idx /\
  is_word_type (expr_type idx) /\ (!l. p.ptr_operand <> Label l /\ iop <> Label l) /\
  ALOOKUP cenv.ce_modules src = SOME tops /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP fin.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  off + type_memory_size itv < dimword (:256) /\
  value_has_type itv iv /\ well_formed_type_value itv /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  type_memory_bytes cenv et = type_memory_size etv /\
  eval_operand p.ptr_operand it = SOME (n2w (off+k)) /\
  eval_operand iop it = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx et obj idx et bd st0 (es,s0,G0,tn0) (sa,sb,dst,LocCode)
    (PlaceR (ImmutablePlace src id path),IntV i) (fin,it,Gi,tni)
Proof
  strip_tac >>
  qhdtm_assum `array_nocopy_cut_mods` (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon fin.storage_trace` >>
  `valid_horizon cx st0 H0 fin.storage_trace` by simp[Abbr `H0`,GSYM storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ it /\ _`
    (drule_then strip_assume_tac) >>
  `stmt_state_rel H0 ctx func cenv cx fin it /\ immutable_frame_mods func cenv cx fin it` by
    (fs[expr_post_mods_def] >> drule_then assume_tac expr_post_state >> simp[]) >>
  `dead_lo_ok_mods H0 (DF H0) lo cenv cx` by simp[] >>
  drule_all_then strip_assume_tac immutable_live_array_buffer >>
  `copy_old_operand sm p.ptr_operand` by
    (qpat_assum `compile_expr cenv ty obj sa = _`
       (mp_then Any mp_tac (cj 1 compiler_compile_var)) >> simp[vv_operand_def,copy_old_operand_def]) >>
  `copy_old_operand st2 iop` by
    (qpat_assum `lower_value compile_expr cenv ty idx sm = _`
       (mp_then Any mp_tac compile_lower_value_var) >> simp[copy_old_operand_def]) >>
  `copy_old_operand st2 p.ptr_operand` by (drule_all copy_old_operand_mono >> simp[]) >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by fs[ptr_val_ok_def] >>
  `op_taint tn1 p.ptr_operand = {} /\ op_prov G1 p.ptr_operand = NONE` by fs[ptr_vv_ok_def] >>
  `op_taint tni p.ptr_operand = {} /\ op_prov Gi p.ptr_operand = NONE` by
    (Cases_on `p.ptr_operand` >> fs[copy_old_operand_def,ghost_kept_at_def,op_taint_def,op_prov_def] >>
     metis_tac[]) >>
  `allocas_from lo it /\ lo <= it.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  suspend "machine"
QED

Resume immutable_select_endpoint_mods[machine]:
  qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [vv_operand_def]) >>
  drule_all_then (assume_tac o CONV_RULE (DEPTH_CONV BETA_CONV) o REWRITE_RULE [LET_THM])
    immutable_code_compile_normalize >>
  qabbrev_tac `dyn = (case bd of Fixed _ => F | Dynamic _ => T)` >>
  qabbrev_tac `cnt = array_length (ArrayTV etv bd) av` >>
  `!region. lo <> 0 /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region it = SOME 0w /\ copy_old_operand st2 region /\
    op_taint tni region = {} /\ op_prov Gi region = NONE` by
    (gen_tac >> strip_tac >> drule_all (REWRITE_RULE [GSYM AND_IMP_INTRO] immutable_region_clean) >> simp[]) >>
  `dyn ==> immutable_copy_read cenv.ce_is_ctor (n2w (off+k)) it = n2w cnt /\
    (cenv.ce_is_ctor ==> w2n (n2w (off+k):bytes32) + 32 <= lo /\
      mem_word_taint tni.t_mem (w2n (n2w (off+k):bytes32)) = {} /\
      (!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region it = SOME 0w /\
        copy_old_operand st2 region /\ op_taint tni region = {} /\ op_prov Gi region = NONE)) /\
    (~cenv.ce_is_ctor ==> w2n (n2w (off+k):bytes32) <= LENGTH it.vs_data_section)` by
    (qabbrev_tac `a = (n2w (off+k):bytes32)` >>
     Cases_on `bd` >> simp[Abbr `dyn`, Abbr `cnt`] >>
     drule_all_then strip_assume_tac immutable_array_header >> simp[] >>
     strip_tac >>
     `lo <> 0` by (qpat_assum `cenv.ce_is_ctor ==> w2n a + 32 <= lo /\ _` (drule_then strip_assume_tac) >> decide_tac) >>
     simp[]) >>
  `eval_operand iop it = SOME (n2w (w2n iw))` by simp[] >>
  qpat_x_assum `eval_operand iop it = SOME iw` kall_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp it` by simp[] >>
  drule_all live_code_select_joint >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`Gf`,`tnf`,`q`] (strip_assume_tac o SIMP_RULE (srw_ss()) []))) >>
  `cnt < dimword (:256)` by (simp[Abbr `cnt`] >> drule_all target_memory_array_length_bound >> simp[]) >>
  `valid_index (ArrayTV etv bd) av i <=> idx_in_range (is_signed_type (expr_type idx)) iw (n2w cnt)` by
    (qpat_assum `Abbrev (cnt = _)` (PURE_ONCE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     irule array_index_word_bounds >> fs[Abbr `cnt`]) >>
  Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w cnt)`
  >- suspend "selected" >> suspend "bounds_exit"
QED

Resume immutable_select_endpoint_mods[bounds_exit]:
  `~valid_index (ArrayTV etv bd) av i` by simp[] >>
  `FLOOKUP (case ALOOKUP fin.immutables cx.txn.target of NONE => FEMPTY
     | SOME imms => get_source_immutables src imms) id = SOME (itv,iv)` by simp[] >>
  drule_all_then assume_tac immutable_selected_error >>
  pure_rewrite_tac[array_select_outcome_mods_def,LET_THM] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  irule gas_outcome_full_mods_exit >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gf`,`fin`,`Abort Revert_abort q`,
    `INR (Error (RuntimeError "evaluate_subscripts array_index"))`,`tnf`] >>
  simp[exit_result_def,expr_exit_def,halt_exit_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `~idx_in_range _ _ _` (fn bad =>
    qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
      (qspec_then `DF H` (ACCEPT_TAC o REWRITE_RULE [bad])))
QED

Resume immutable_select_endpoint_mods[selected]:
  `valid_index (ArrayTV etv bd) av i` by simp[] >>
  `Num i = w2n iw` by
    (`0 <= i` by fs[valid_index_def, IgnAsm `i = _`] >>
     Cases_on `is_signed_type (expr_type idx)` >>
     gvs[overflowElimHelpersTheory.nonneg_w2i_eq_w2n]) >>
  drule_then (qx_choose_then `v` assume_tac)
    (REWRITE_RULE [optionTheory.IS_SOME_EXISTS] array_index_valid) >>
  qpat_assum `idx_in_range _ _ _ ==> _` (drule_then strip_assume_tac) >>
  `eval_operand dst q = SOME (n2w (off+k) + n2w
    ((case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv))` by
    (Cases_on `bd` >> fs[Abbr `dyn`, IgnAsm `i = _`]) >>
  qpat_assum `idx_in_range _ _ _` (fn ok =>
    qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _` (assume_tac o REWRITE_RULE [ok])) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  `FLOOKUP (case ALOOKUP fin.immutables cx.txn.target of NONE => FEMPTY
     | SOME imms => get_source_immutables src imms) id = SOME (itv,iv)` by simp[] >>
  drule_all immutable_selected_source >>
  disch_then (qspec_then `et` (strip_assume_tac o CONV_RULE (DEPTH_CONV BETA_CONV) o REWRITE_RULE [LET_THM])) >>
  `val_wf (ArrayTV etv bd) (ArrayV av)` by simp[valueEncodingTypingTheory.value_has_type_val_wf] >>
  drule_all_then assume_tac immutable_selected_pointer >>
  qabbrev_tac `child = PlaceR (ImmutablePlace src id (path ++ [ValueSubscript (IntV i)]))` >>
  `q.vs_data_section = it.vs_data_section` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
       (qspec_then `DF H0` (mp_then Any mp_tac bodyFullIfExpReachTheory.gas_origin_ptr_path_erase)) >>
     strip_tac >> drule_then irule immutable_selection_path_data >> simp[]) >>
  `immutable_frame_mods func cenv cx fin q` by
    (irule immutable_frame_mods_exterior_frame >> simp[] >>
     qexistsl [`fin`,`it`,`st2`] >> simp[]) >>
  qabbrev_tac `j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv` >>
  drule_all_then assume_tac array_element_step_offset >>
  `mem_step_offset (ArrayTV etv bd) (ValueSubscript (IntV i)) = SOME (j,etv)` by
    simp[Abbr `j`] >>
  drule_all_then assume_tac mem_path_offset_snoc >>
  `evaluate_subscripts itv iv (path ++ [ValueSubscript (IntV i)]) = INL v` by
    (qpat_assum `mem_path_offset itv path = SOME (k,_)`
       (mp_then Any strip_assume_tac mem_path_offset_sound) >>
     drule_all_then (fn th => simp[th,evaluate_subscripts_def])
       vyperPlaceResultTypingTheory.evaluate_subscripts_append) >>
  `value_has_type etv v` by
    (irule array_index_has_type >> conj_tac
     >- (qpat_assum `evaluate_type _ et = SOME etv`
           (mp_then Any ACCEPT_TAC evaluate_type_well_formed_type_value)) >>
     qexistsl [`av`,`bd`,`i`,`ArrayTV etv bd`] >> simp[]) >>
  `vv_holds_mods cenv cx et child (LocatedValue et (mk_ptr dst LocCode)) fin q` by
    (`sub_layout itv iv (k+j) etv v` by
       (irule immutable_path_layout >> simp[] >> qexists `path ++ [ValueSubscript (IntV i)]` >> simp[]) >>
     simp[vv_holds_mods_def,mk_ptr_def,immutable_holds_mods_def] >>
     qexistsl [`src`,`tops`] >> simp[immutable_holds_def] >>
     qexistsl [`id`,`off`,`itv`,`iv`,`k+j`] >>
     simp[] >> pure_rewrite_tac[GSYM word_add_n2w] >>
     simp[AC WORD_ADD_ASSOC WORD_ADD_COMM]) >>
  `cenv.ce_is_ctor ==> w2n (n2w (off+(k+j)):bytes32) + type_memory_size etv <= lo /\
    (!mem. mem_agree_outside tnf.t_mem q.vs_memory mem ==>
       val_in_memory etv v (w2n (n2w (off+(k+j)):bytes32)) mem)` by
    (drule_all_then strip_assume_tac immutable_live_array_buffer >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `eval_expr cx obj _ = _`
      (mp_then Any mp_tac vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >> simp[]) >>
  `fin with gas_obs := [] = (fin:evaluation_state)` by
    (qpat_x_assum `fin.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  rewrite_tac[array_select_outcome_mods_def,LET_THM] >> BETA_TAC >>
  irule gas_outcome_full_mods_pure >> (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`Gf`,`fin`,`INL child`,`q`,`tnf`] >>
  conj_tac >- first_assum ACCEPT_TAC >> asm_rewrite_tac[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF H` assume_tac) >>
  BETA_TAC >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  qpat_assum `!H. _ ==> valid_horizon _ _ H mid.storage_trace /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ es _ /\ _` (drule_then strip_assume_tac) >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ it /\ _`
    (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func cenv cx fin it` by
    (qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ it`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_then ACCEPT_TAC expr_post_state) >>
  `stmt_state_rel H ctx func cenv cx fin q` by
    (qpat_assum `!H cenv cx es. stmt_state_rel H _ _ cenv cx es it /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `alloca_inv it` by
    (qpat_assum `stmt_state_rel H _ _ _ _ _ it`
      (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >> first_assum ACCEPT_TAC) >>
  `alloca_history func q` by (drule_all_then ACCEPT_TAC bodyFullPathHistoryTheory.body_full_path_alloca_history) >>
  qpat_assum `stmt_state_rel H _ _ _ _ _ q`
    (mp_then Any assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  `sa.cs_next_var <= st2.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at st2 x` by
    (gen_tac >> strip_tac >> drule_all freshWritesTheory.not_fresh_at_mono >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x` by simp[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x` by simp[] >>
  `ghost_inv_at_mods (DF H) lo d cenv cx fin Gf tnf q` by
    (irule ghost_inv_at_mods_exterior_frame >>
     goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
     qexists `st2` >> asm_rewrite_tac[]) >>
  qpat_x_assum `LocCode = case _ of _ => _ | _ => _` (SUBST_ALL_TAC o SYM) >>
  `vv_post_mods H ctx func cenv cx (Subscript et obj idx) es sa sb s0 fin child
       (LocatedValue et (mk_ptr dst LocCode)) q` by
    (simp[Abbr `child`] >> irule immutable_selected_linked_post >> simp[] >>
     goal_assum (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[] >>
     goal_assum (drule_at (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `wb_frame cenv es mid sa s0 s` by
    (qpat_assum `vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ s`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni` by
    (drule_all_then ACCEPT_TAC ghost_kept_at_wb_trans) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf` by
    (irule ghost_kept_at_clean_suffix >> qexistsl [`Gi`,`tni`] >> simp[] >>
     gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at st2 x ==> _` irule >> simp[]) >>
  `eval_operand dst q = SOME (n2w (off+(k+j)))` by
    (simp[] >> pure_rewrite_tac[GSYM word_add_n2w] >> simp[AC WORD_ADD_ASSOC WORD_ADD_COMM]) >>
  qexists `child` >>
  simp[mk_ptr_def, vv_location_def,vv_operand_def,expr_type_def,vv_store_bound_nonmem,ptr_vv_ok_def,
       Abbr `child`] >>
  qpat_x_assum `cenv.ce_is_ctor ==> w2n (n2w (off+(k+j)):bytes32) + type_memory_size etv <= lo /\ _` mp_tac >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Finalise immutable_select_endpoint_mods
