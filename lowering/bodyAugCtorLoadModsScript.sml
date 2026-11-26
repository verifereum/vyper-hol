(* The reached qualified immutable selects an offset in constructor memory. *)
Theory bodyAugCtorLoadMods
Ancestors
  bodyWriteTargetStageMods augAssignFullImmutableValidLoad immutableRegionFrameProps
  bodyInvCodeProps bodyInvSplit bodyFullShadowBodyInv bodyFullPostsMods bodyFullTargetDefs
  assignTuplePtrLoadStep targetSubscriptMemory exprSimHypsDefs exprSimProps
  stateRelProj exprLoweringProps loweringStateRelDefs loweringPosts valueEncodingProps
  loweringSlice vyperTypeEnv vyperPlaceStatePreservation vyperStorageFootprint
  vyperState context compileEnv exprSimCopy freshWrites fragGasOriginPtr stmtSimReturn
  bodyPtrDefs stateFrame ptrDiscipline venomInst venomExecSemantics venomState
  finite_map words pred_set arithmetic

Theorem aug_ctor_word_resources_mods[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env st /\
  cenv.ce_is_ctor /\ dead_lo_ok_mods H D lo cenv cx /\
  stmt_state_rel H ctx func cenv cx st s /\
  immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor st s /\
  ghost_inv_at_mods D lo d cenv cx st G tn s /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  ALOOKUP st.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ptv) /\
  evaluate_subscripts itv iv path = INL cur /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\ is_word_type ty ==>
  subscripts_type itv path = SOME ptv /\ value_has_type ptv cur /\
  off+k+32 <= lo /\ w2n (n2w (off+k) : bytes32) = off+k /\
  mload (off+k) s = typed_val_to_w256 ptv cur /\
  mem_word_taint tn.t_mem (off+k) = {}
Proof
  strip_tac >>
  `state_well_typed st` by fs[expr_sim_inv_mods_def] >>
  drule_all_then assume_tac state_well_typed_immutables_ALOOKUP >>
  drule_all_then strip_assume_tac imms_well_typed_get_source_immutables >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  drule_all_then assume_tac evaluate_subscripts_type >>
  drule_all_then strip_assume_tac immutable_region_value_layout_mods >>
  `?tops. ALOOKUP cenv.ce_modules owner = SOME tops` by
    (drule_then assume_tac contract_inv_cenv_modules >>
     fs[immutable_region_mods_def]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory itv iv off mem` by
    (`st.immutables = st.immutables` by simp[] >>
     drule_all_then strip_assume_tac qualified_immutable_ctor_frame_mods >>
     first_assum ACCEPT_TAC) >>
  `type_memory_size ptv = 32` by metis_tac[word_tv_memory_size] >>
  `lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `s.vs_alloca_next < dimword (:256)` by
    (drule_then assume_tac stmt_state_rel_alloca_room >> metis_tac[alloca_room_next_lt]) >>
  `off+k+32 <= lo /\ off+k < dimword (:256)` by decide_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory ptv cur (off+k) mem` by
    (rpt strip_tac >> irule mem_path_offset_current_value >>
     qexistsl_tac [`iv`,`path`,`itv`] >> simp[]) >>
  drule_all_then strip_assume_tac robust_typed_word_clean >>
  `mload (off+k) s = typed_val_to_w256 ptv cur` by
    (qpat_assum `!m. _ ==> mem_word_at _ _ = _` (qspec_then `s.vs_memory` mp_tac) >>
     simp_tac bool_ss [mem_agree_outside_def,mem_word_at_eq_mload]) >>
  `mem_word_taint tn.t_mem (off+k) = {}` by
    (simp[mem_word_taint_def, EXTENSION] >> qx_gen_tac `j` >>
     Cases_on `j < 32` >> simp[] >>
     qpat_assum `!i. off+k <= i /\ i < off+k+32 ==> _` irule >> decide_tac) >>
  asm_simp_tac bool_ss [w2n_n2w, LESS_MOD] >> metis_tac[ADD_COMM]
QED

Theorem augassign_ctor_load_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env st /\
  is_word_type ty /\ storage_trace_domain cx st0 st.storage_trace /\
  (!H. valid_horizon cx st0 H st.storage_trace ==>
    dead_lo_ok_mods H (DF H) lo cenv cx /\
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt
      es sa sb s0 st (PlaceR (ImmutablePlace owner id path)) (Type ty) r G0 tn0 G tn s) /\
  local_ptrs_reserved cenv sb /\
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode (FST r) sb = (old,sc) /\
  fn_has_code sb sc func ==>
  ?off k cur ptv u G1 tn1.
    FST (SND r) = SOME LocCode /\ cenv.ce_is_ctor /\
    FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
    off+k+32 <= lo /\ eval_operand (FST r) s = SOME (n2w (off+k)) /\
    read_place cx (ImmutablePlace owner id path) st = (INL cur,st) /\
    place_type_value cx (ImmutablePlace owner id path) st = (INL ptv,st) /\
    evaluate_type (get_tenv cx) ty = SOME ptv /\ value_has_type ptv cur /\
    (!H. valid_horizon cx st0 H st.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G1,tn1)) /\
    sc.cs_current_bb = sb.cs_current_bb /\
    sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
    sb.cs_next_var <= sc.cs_next_var /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sb sc) /\
    eval_operand old u = SOME (typed_val_to_w256 ptv cur) /\
    eval_operand (FST r) u = SOME (n2w (off+k)) /\
    op_taint tn1 old = {} /\ op_prov G1 old = NONE /\
    (!q. old = Var q ==> not_fresh_at sc q) /\
    (!q. FST r = Var q ==> not_fresh_at sc q) /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!q. not_fresh_at sb q ==> lookup_var q u = lookup_var q s /\
          FLOOKUP G1 q = FLOOKUP G q /\ op_taint tn1 (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon st.storage_trace) st.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac write_target_immutable_view_mods >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  `immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor st s` by
    fs[immutable_frame_mods_def] >>
  drule_all_then strip_assume_tac aug_ctor_word_resources_mods >>
  rename1 `evaluate_subscripts itv iv path = INL cur` >>
  `read_place cx (ImmutablePlace owner id path) st = (INL cur,st) /\
   place_type_value cx (ImmutablePlace owner id path) st = (INL ptv,st)` by
    simp[read_place_def, place_type_value_def, get_immutables_def,
         get_address_immutables_def, bind_def, return_def, lift_sum_def,
         lift_option_type_def] >>
  `compile_imm_load_word T cenv.ce_imm_alloca (FST r) sb = (old,sc)` by
    fs[compile_ptr_load_def] >>
  `copy_old_operand sb (FST r) /\ op_taint tn (FST r) = {} /\
   allocas_from lo s /\ lo <= s.vs_alloca_next` by
    fs[copy_old_operand_def, target_ptr_ok_def, ghost_inv_at_mods_def] >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
       eval_operand region s = SOME 0w /\ copy_old_operand sb region /\
       op_taint tn region = {} /\ op_prov G region = NONE` by suspend "base" >>
  `w2n (n2w (off+k) : bytes32) + 32 <= lo /\
   mem_word_taint tn.t_mem (w2n (n2w (off+k) : bytes32)) = {}` by
    asm_rewrite_tac[] >>
  drule_all augassign_ctor_word_load_at >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  suspend "endpoint"
QED

Resume augassign_ctor_load_mods[base]:
  `lo <> 0` by decide_tac >>
  drule_then assume_tac stmt_state_rel_immutable_base_zero >>
  gen_tac >> strip_tac >>
  conj_tac >- fs[immutable_base_zero_def] >>
  Cases_on `region` >>
  fs[copy_old_operand_def, op_taint_def, op_prov_def, ghost_inv_at_mods_def] >>
  metis_tac[local_ptrs_reserved_imm_base]
QED

Resume augassign_ctor_load_mods[endpoint]:
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) _ [] (OK u,G1,tn1)` >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `state_frame u = _` mp_tac >>
     simp[state_frame_eq_reconstruct, venom_state_component_equality]) >>
  `eval_operand (FST r) u = eval_operand (FST r) s` by
    (irule eval_operand_old_vars >> simp[] >> qexists_tac `sb` >> simp[]) >>
  `!q. FST r = Var q ==> not_fresh_at sc q` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sb` >> simp[]) >>
  qexistsl_tac [`off`,`k`,`cur`,`ptv`,`u`,`G1`,`tn1`] >>
  asm_simp_tac bool_ss []
QED

Finalise augassign_ctor_load_mods
