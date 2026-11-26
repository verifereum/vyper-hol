(* Run the paired AugAssign RHS at the endpoint of the selected load. *)
Theory bodyAugLoadedRhsMods
Ancestors
  bodyAugReadOnlyFrameMods bodyWriteTargetStageMods bodyFullPostsMods
  gasOutcomeFullPostMods bodyFullIfExpReach exprSimWordArgs bodyMemoryDefs
  exprLoweringProps freshWrites stateFrame vyperStorageFootprint loweringPosts

(* At a particular horizon, preserve the selected destination as well as
   the linked resources.  The load does not update the source place. *)
Theorem aug_loaded_rhs_frame_at[local]:
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sT s0 mid
    (PlaceR p) (Type ty) r G0 tn0 Gtarget tt t /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sT.cs_next_var /\ sT.cs_next_var <= s1.cs_next_var /\
  return_buf_frame d cenv sa s0 /\
  fn_has_code sT s1 func /\ s1.cs_current_bb = sT.cs_current_bb /\
  s1.cs_current_insts = sT.cs_current_insts ++ emitted_insts sT s1 /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sT s1) /\
  u.vs_inst_idx = LENGTH s1.cs_current_insts /\
  state_frame u = state_frame (t with vs_inst_idx := u.vs_inst_idx) /\
  tu.t_mem = tt.t_mem /\ tu.t_stor = tt.t_stor /\
  tu.t_trans = tt.t_trans /\ tu.t_imm = tt.t_imm /\
  (!x. not_fresh_at sT x ==> lookup_var x u = lookup_var x t /\
       FLOOKUP Gu x = FLOOKUP Gtarget x /\ op_taint tu (Var x) = op_taint tt (Var x)) ==>
  (stmt_state_rel H ctx func cenv cx mid u /\
   immutable_frame_mods func cenv cx mid u /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at_mods D lo d cenv cx mid Gu tu u) /\
  (wb_frame cenv es mid sa s0 u /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
   target_ptr_ok cenv (PlaceR p) r Gu tu u /\
   write_target_location_mods cenv cx bt mid (PlaceR p) (Type ty) r Gu u /\
   op_prov Gu (FST r) = op_prov Gtarget (FST r) /\
   op_taint tu (FST r) = op_taint tt (FST r) /\
   u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
   return_buf_frame d cenv s1 u /\ local_ptrs_reserved cenv s1 /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u))
Proof
  strip_tac >> drule_then strip_assume_tac write_target_post_view_mods >>
  `local_ptrs_reserved cenv sT` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sT x` by
    metis_tac[not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sT x` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d cenv sT t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     simp[] >> metis_tac[wb_frame_vars]) >>
  drule_all_then strip_assume_tac (GEN_ALL augassign_read_only_frame_mods) >>
  simp[] >> irule aug_readonly_target_location_mods >>
  qpat_assum `write_target_location_mods _ _ _ _ _ _ _ Gtarget t` (irule_at Any) >>
  qexists_tac `sT` >> simp[]
QED

val loaded_rhs_resources =
  ``\(H : (bool # bytes32 # type_value) list # num list). stmt_state_rel H ctx func cenv cx mid u /\
        immutable_frame_mods func cenv cx mid u /\
        storage_well_formed_on cx mid (FST H) /\
        ghost_inv_at_mods (DF H) lo d cenv cx mid Gu tu u``;

val loaded_rhs_frame =
  ``wb_frame cenv es mid sa s0 u /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
    target_ptr_ok cenv (PlaceR p) r Gu tu u /\
    write_target_location_mods cenv cx bt mid (PlaceR p) (Type ty) r Gu u /\
    op_prov Gu (FST r) = op_prov Gtarget (FST r) /\
    op_taint tu (FST r) = op_taint tt (FST r) /\
    u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
    return_buf_frame d cenv s1 u /\ local_ptrs_reserved cenv s1 /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)``;

Theorem augassign_loaded_rhs_mods:
  contract_inv mods exps ctx cenv cx /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sT shadow_sa shadow_sT r s0 G0 tn0 /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sT s0 mid
      (PlaceR p) (Type ty) r G0 tn0 Gtarget tt t) /\
  (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,Gtarget,tt) [] (OK u,Gu,tu)) /\
  ci_mono sa sT /\ ci_mono sT s1 /\
  fn_has_code sT s1 func /\ s1.cs_current_bb = sT.cs_current_bb /\
  s1.cs_current_insts = sT.cs_current_insts ++ emitted_insts sT s1 /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sT s1) /\
  ~u.vs_halted /\ u.vs_current_bb = s1.cs_current_bb /\
  u.vs_inst_idx = LENGTH s1.cs_current_insts /\
  state_frame u = state_frame (t with vs_inst_idx := u.vs_inst_idx) /\
  tu.t_mem = tt.t_mem /\ tu.t_stor = tt.t_stor /\
  tu.t_trans = tt.t_trans /\ tu.t_imm = tt.t_imm /\
  (!x. not_fresh_at sT x ==> lookup_var x u = lookup_var x t /\
       FLOOKUP Gu x = FLOOKUP Gtarget x /\ op_taint tu (Var x) = op_taint tt (Var x)) /\
  lower_value compile_expr cenv ty e s1 = (rhsop,s2) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_s1 =
    (rhsop,shadow_s2) /\
  gas_shadow_state s1 shadow_s1 /\ gas_shadow_state s2 shadow_s2 /\
  fn_has_code s1 s2 func /\ fn_has_code shadow_s1 shadow_s2 shadow_func /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e mid ==>
  ^loaded_rhs_frame /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid u /\
    immutable_frame_mods func cenv cx mid u /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid Gu tu u) /\
  (!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_fmp_headroom inst s) /\
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (mid,u,Gu,tu)
    (\H res ee G tn q.
      (?v. res = INL v /\
         expr_post_mods H ctx func cenv cx e mid s1 s2 u ee v rhsop q /\
         expr_store_bound cx (post_value_type cenv e) v rhsop q /\
         q.vs_current_bb = s2.cs_current_bb /\ q.vs_inst_idx = LENGTH s2.cs_current_insts /\
         alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
         u.vs_alloca_next <= q.vs_alloca_next /\
         ghost_inv_at_mods (DF H) lo d cenv cx ee G tn q /\
         ptr_val_ok cx (post_value_type cenv e) v rhsop G tn q /\
         (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e rhsop G q)) /\
      (!x z. not_fresh_at s1 x /\ lookup_var x u = SOME z ==> lookup_var x q = SOME z) /\
      ghost_kept_at lo cenv mid s1 Gu tu u G tn)
    (\H res ee gt q. expr_exit res q /\ halt_exit H cx ee res q /\
      (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  qhdtm_x_assum `write_target_entry_mods`
    (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  `sa.cs_next_var <= sT.cs_next_var /\ sT.cs_next_var <= s1.cs_next_var` by fs[ci_mono_def] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      (^loaded_rhs_resources) H /\ ^loaded_rhs_frame` by
    (BETA_TAC >> qx_gen_tac `H` >> disch_tac >>
     irule aug_loaded_rhs_frame_at >> (metis_tac[])) >>
  pop_assum (mk_asm "loaded" o BETA_RULE) >>
  `^loaded_rhs_frame` by (asm "loaded" (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  pop_assum strip_assume_tac >>
  `!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_fmp_headroom inst s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
      (drule_then assume_tac) >>
     `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[body_inv_no_phi_mods] >>
     metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> (^loaded_rhs_resources) H` by
    (BETA_TAC >> qx_gen_tac `H` >> disch_tac >>
     asm_x "loaded" (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  pop_assum (assume_tac o BETA_RULE) >>
  conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`s1`,`s2`,`shadow_s1`,`shadow_s2`,`rhsop`,`u`,`Gu`,`tu`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> suspend "rhs_post"
QED

Resume augassign_loaded_rhs_mods[rhs_post]:
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  conj_tac >- (qexists_tac `v` >> simp[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qhdtm_x_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then assume_tac expr_post_frame >>
  rpt gen_tac >> strip_tac >> irule wb_frame_vars >>
  qpat_assum `wb_frame cenv mid _ s1 u _` (irule_at Any) >> simp[]
QED

Finalise augassign_loaded_rhs_mods
