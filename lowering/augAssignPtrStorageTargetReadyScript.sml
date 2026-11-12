Theory augAssignPtrStorageTargetReady
Ancestors
  stmtSimAugAssignPlaceStorage bodyPtrPopTargetDefs bodyAugPlaceTarget
  bodySimAugPlaceScopes bodySimAugPlaceMemory targetPlaceSimCasesBase
  exprSimSource exprSimHypsDefs bodyExprPreFacts targetPlaceSim targetPlaceSimDefs loweringPosts
  supportedTargets targetPlaceLive exprSimDefs vyperInterpreter vyperState vyperAST vyperTyping
  vyperLookupStorage vyperStorageBackend
  augAssignPtrStorageFieldLoad augAssignPtrLoad bodyPtrPopTargetSimStorageHeader
  bodyPtrDefs emitHelper compileEnv exprLoweringProps venomState freshWrites
  stmtSimProps stmtFragPtr finite_map loweringStateRelDefs

Theorem aug_place_storage_target_ready_ptr:
  body_inv tops ctx cenv cx /\
  supported_target_info tops bindings bt = SOME pt /\
  supported_target_pure tops bt /\
  (!id. target_root bt <> NameTarget id) /\
  target_pre cenv cx env bt es /\ expr_body_pre cenv cx env e es /\
  eval_base_place cx bt es = (INL pv,mid) /\
  target_post ctx func cenv cx es sa sp s0 mid pv (Type ty) ptrout t /\
  target_ptr_ok cenv pv ptrout G tn t ==>
  ?tr slot tv cur.
    pv = PlaceR (StoragePlace tr slot tv) /\
    eval_target_place cx bt es = (INL (StoragePlace tr slot tv),mid) /\
    eval_operand (FST ptrout) t = SOME slot /\
    FST (SND ptrout) = SOME (slot_loc tr) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    stmt_state_rel ctx func cenv cx mid t /\
    (!x. FST ptrout = Var x ==> not_fresh_at sp x) /\
    read_place cx (StoragePlace tr slot tv) mid = (INL cur,mid) /\
    place_type_value cx (StoragePlace tr slot tv) mid = (INL tv,mid) /\
    value_has_type tv cur /\ expr_body_pre cenv cx env e mid /\
    op_prov G (FST ptrout) = NONE /\ op_taint tn (FST ptrout) = {} /\
    slots_in_range (get_storage cx mid tr) (w2n slot) tv /\
    storage_read_live cx tr (get_storage cx mid tr) slot tv
Proof
  strip_tac >>
  `?p. pv = PlaceR p` by
    (gvs[target_post_def] >> Cases_on `pv` >>
     gvs[place_ptr_rel_def] >> Cases_on `p` >> gvs[place_ptr_rel_def]) >>
  gvs[] >>
  `eval_target_place cx bt es = (INL p,mid)` by
    simp[Once evaluate_def, bind_def, get_place_def, return_def] >>
  drule_all aug_place_supported_success_kind >> strip_tac
  >- (`!bt cx st id path fin.
        eval_base_place cx bt st = (INL (PlaceR (MemoryPlace id path)),fin) ==>
        target_root bt = NameTarget id` by
        (`(!e:expr. T) /\ (!bt. !cx st id path fin.
          eval_base_place cx bt st = (INL (PlaceR (MemoryPlace id path)),fin) ==>
          target_root bt = NameTarget id)` suffices_by simp[] >>
         ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
         simp[] >> rpt conj_tac >> rpt gen_tac
         >- simp[Once evaluate_def, bind_def, get_scopes_def, ignore_bind_def,
                 type_check_def, assert_def, return_def, raise_def, AllCaseEqs(),
                 target_root_def]
         >- (rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
             simp[Once evaluate_def] >>
             metis_tac[aug_place_lookup_global_not_memory]) >>
         rpt strip_tac >>
         qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
         simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
         strip_tac >> gvs[] >>
         drule aug_place_extend_memory_inversion >> strip_tac >> gvs[] >>
         simp[target_root_def] >> metis_tac[]) >> metis_tac[]) >>
  gvs[target_post_def, place_ptr_rel_def, target_ptr_ok_def] >>
  `EVERY (supported_pure_expr tops) (target_indices bt)` by
    (qpat_x_assum `supported_target_pure tops bt` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
     fs[supported_target_pure_def, target_indices_def] >>
     first_x_assum irule >> simp[]) >>
  `contract_storage_well_formed cx es` by
    gvs[target_pre_def, expr_sim_inv_def] >>
  drule_all aug_place_pure_target_storage_range >> strip_tac >>
  drule_all aug_place_pure_target_storage_live >> strip_tac >>
  `expr_body_pre cenv cx env e mid` by
    (drule_all eval_base_place_sim_inv >> gvs[expr_body_pre_def]) >>
  `well_formed_type_value tv` by
    metis_tac[cj 1 evaluate_type_well_formed] >>
  drule_all decode_value_from_slots_in_range >> strip_tac >>
  qexists_tac `v` >>
  simp[read_place_def, read_storage_slot_eq, place_type_value_def, return_def]
QED

Theorem aug_place_storage_ready_load_ptr:
  emit_op (if tr then TLOAD else SLOAD) [addr] sp = (Var out,sb) /\
  fn_has_code sp sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sp.cs_current_bb /\
  s.vs_inst_idx = LENGTH sp.cs_current_insts /\
  eval_operand addr s = SOME slot /\ op_prov G addr = NONE /\
  op_taint tn addr = {} /\ local_ptrs_reserved cenv sp /\
  target_post ctx fn cenv cx es sa sp s0 mid
    (PlaceR (StoragePlace tr slot tv)) (Type ty) ptrout s /\
  read_place cx (StoragePlace tr slot tv) mid = (INL cur,mid) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  slots_in_range (get_storage cx mid tr) (w2n slot) tv /\
  storage_read_live cx tr (get_storage cx mid tr) slot tv /\
  0 < type_slot_size tv /\ ghost_inv d cenv cx mid G tn s /\
  ret_pc_ok cenv sp s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) ==>
  ?H tm u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK u) /\
    eval_operand (Var out) u = SOME (typed_val_to_w256 tv cur) /\
    stmt_state_rel ctx fn cenv cx mid u /\ ghost_inv d cenv cx mid H tm u /\
    ghost_kept cenv mid sp G tn s H tm /\ tm.t_mem = tn.t_mem /\
    op_taint tm (Var out) = {} /\ op_prov H (Var out) = NONE /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ not_fresh_at sb out /\
    (!rp. not_fresh_at sp rp ==> lookup_var rp u = lookup_var rp s)
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx mid s` by gvs[target_post_def] >>
  `stor_taint_ok cx tn s` by gvs[ghost_inv_def] >>
  drule_all target_storage_header_clean_ptr >> strip_tac >>
  drule_all aug_place_storage_load_ready >> strip_tac >>
  drule_all emit_storage_address_load_clean_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `sb.cs_next_var = sp.cs_next_var + 1 /\
   out = STRCAT "%" (toString sp.cs_next_var)` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]) >>
  qexistsl [`H`, `tm`, `t`] >> simp[IgnAsm `t = _`] >>
  conj_tac
  >- (qpat_x_assum `t = _` kall_tac >> gvs[eval_operand_def]) >>
  conj_tac
  >- (gvs[] >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> simp[stmt_state_rel_inst_idx] >>
      irule local_ptrs_reserved_fresh >> qexists_tac `sp` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `t = _` kall_tac >> irule ghost_inv_load_frame >>
      qexistsl [`G`, `s`, `sp`, `tn`] >> simp[] >> gvs[ret_pc_ok_def]) >>
  conj_tac >- simp[ghost_kept_def] >>
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sp` >> simp[]) >>
  simp[not_fresh_at_def]
QED
