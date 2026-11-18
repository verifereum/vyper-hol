(* Memory resources at the actual joint target endpoint. *)
Theory augAssignFullLoadMemoryResources
Ancestors
  bodySimAugPlaceLoad bodyFullTargetDefs bodyPtrDefs stateRelProj
  assignTuplePtrLoadStep exprSimProps exprSimBuffer exprLoweringProps loweringPosts
  loweringStateRelDefs valueEncodingProps memoryValueEncoding
  ptrSafeRun ptrDiscipline contextCodegenRel codegenRel memLocDefs venomExecSemantics venomInstProofs
  venomInst venomState vyperState vyperPlaceStatePreservation
  vyperValueOperation vyperTypeInvariants compileEnv
  finite_map words pred_set list arithmetic

val load_steps = LIST_CONJ (List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc)
       [``MLOAD``, ``SLOAD``, ``TLOAD``]
  end) (CONJUNCTS step_inst_base_opcode_eqs));

Theorem augassign_memory_load_resources:
  expr_sim_inv cenv cx env es /\
  supported_target_info tops bindings bt = SOME info /\
  eval_target_place cx bt es = (INL (MemoryPlace id path),st) /\
  target_post H ctx func cenv cx es sa sb s0 st
    (PlaceR (MemoryPlace id path)) (Type ty) r s /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) r G tn s /\
  ghost_inv_at D lo d cenv cx st G tn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (?entry v. lookup_scopes id st.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INL v) /\
  is_word_type ty /\
  eval_operand (FST r) s = SOME a /\
  read_place cx (MemoryPlace id path) st = (INL cur,stc) /\
  place_type_value cx (MemoryPlace id path) stc = (INL ptv,stt)
  ==>
  stc = st /\ stt = st /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\
  value_has_type ptv cur /\
  mload (w2n a) s = typed_val_to_w256 ptv cur /\
  op_taint tn (FST r) = {} /\
  (!q. FST r = Var q ==> not_fresh_at sb q) /\
  w2n a + 32 <= s.vs_alloca_next /\
  (!j. w2n a <= j /\ j < w2n a + 32 ==> j NOTIN tn.t_mem) /\
  (!iid out. ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst iid MLOAD [FST r] [out]) s)
Proof
  strip_tac >>
  `stc = st /\ stt = st` by
    metis_tac[read_place_state, place_type_value_state] >> gvs[] >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    metis_tac[aug_place_target_entry_typed] >>
  `st.scopes = es.scopes` by metis_tac[aug_place_target_scopes] >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [target_post_def] >> strip_tac >>
  `w = a` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
  simp[place_ptr_rel_def] >> strip_tac >> gvs[] >>
  `tv0 = entry.type` by
    metis_tac[aug_place_entry_type_agrees, optionTheory.SOME_11] >> gvs[] >>
  `subscripts_type entry.type path = SOME tv /\
   k + type_memory_size tv <= type_memory_size entry.type` by
    metis_tac[mem_path_offset_sound] >>
  `cur = v /\ ptv = tv` by suspend "source" >> gvs[] >>
  `value_has_type ptv cur` by metis_tac[evaluate_subscripts_type] >>
  `type_memory_size ptv = 32` by metis_tac[word_tv_memory_size] >>
  `w2n b + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz /\
   s.vs_alloca_next < dimword (:256)` by suspend "bounds" >>
  `w2n (b + n2w k) = w2n b + k` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >> decide_tac) >>
  `ptr_covers G tn p s sz /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n b) mem) /\ allocas_from lo s` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory ptv cur (w2n b + k) mem` by
    (rpt strip_tac >> irule aug_place_path_project >>
     qexistsl_tac [`entry.value`, `path`, `entry.type`] >> simp[]) >>
  `mload (w2n b + k) s = typed_val_to_w256 ptv cur /\
   (!j. w2n b + k <= j /\ j < w2n b + k + 32 ==> j NOTIN tn.t_mem)` by
    suspend "clean" >>
  fs[target_ptr_ok_def] >>
  suspend "instruction"
QED

Resume augassign_memory_load_resources[source]:
  gvs[read_place_def, get_scopes_def, bind_def, lift_option_type_def,
      lift_sum_def, return_def, read_memory_path_def, place_type_value_def]
QED

Resume augassign_memory_load_resources[bounds]:
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule stmt_state_rel_alloca_room >> strip_tac >>
  gvs[local_ptrs_rel_def] >>
  qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >> gvs[] >>
  metis_tac[alloca_room_next_lt]
QED

Resume augassign_memory_load_resources[clean]:
  drule_all robust_typed_word_clean >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `!m. _ ==> mem_word_at _ _ = _`
        (qspec_then `s.vs_memory` mp_tac) >>
      simp[mem_agree_outside_def, mem_word_at_eq_mload, ADD_COMM]) >>
  simp[]
QED

Resume augassign_memory_load_resources[instruction]:
  fs[ptr_covers_def] >>
  `?q. FST r = Var q` by
    (Cases_on `FST r` >> gvs[op_prov_def] >> metis_tac[]) >>
  gvs[op_prov_def] >> rpt gen_tac >>
  simp[ptr_inst_ok_def, mk_inst_def] >>
  conj_tac
  >- (simp[access_ok_def, mk_inst_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, eval_operand_def] >>
      rpt strip_tac >> gvs[] >>
      gvs[mem_read_ops_def] >> decide_tac) >>
  conj_tac >- simp[taint_ok_def, mk_inst_def] >>
  simp[step_inst_non_invoke, load_steps, mk_inst_def, exec_read1_def,
       update_var_def, AllCaseEqs()]
QED

Finalise augassign_memory_load_resources
