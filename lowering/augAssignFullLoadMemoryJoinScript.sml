(* Source-query coverage and deterministic memory load composition. *)
Theory augAssignFullLoadMemoryJoin
Ancestors
  augAssignFullLoadMemoryResources augAssignFullLoadMemoryStep
  bodySimAugPlaceLoad exprSimProps loweringPosts vyperPlaceStatePreservation
  vyperValueOperation vyperState vyperTypeInvariants venomState
  compileEnv finite_map words pred_set list arithmetic

Theorem augassign_memory_load_queries:
  expr_sim_inv cenv cx env es /\
  supported_target_info tops bindings bt = SOME info /\
  eval_target_place cx bt es = (INL (MemoryPlace id path),st) /\
  target_post H ctx func cenv cx es sa sb s0 st
    (PlaceR (MemoryPlace id path)) (Type ty) r s /\
  (?entry v. lookup_scopes id st.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INL v) /\
  is_word_type ty
  ==>
  ?cur ptv.
    read_place cx (MemoryPlace id path) st = (INL cur,st) /\
    place_type_value cx (MemoryPlace id path) st = (INL ptv,st) /\
    evaluate_type (get_tenv cx) ty = SOME ptv /\
    value_has_type ptv cur
Proof
  strip_tac >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    metis_tac[aug_place_target_entry_typed] >>
  `st.scopes = es.scopes` by metis_tac[aug_place_target_scopes] >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [target_post_def] >> strip_tac >>
  qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
  simp[place_ptr_rel_def] >> strip_tac >> gvs[] >>
  `tv0 = entry.type` by
    metis_tac[aug_place_entry_type_agrees, optionTheory.SOME_11] >> gvs[] >>
  `subscripts_type entry.type path = SOME tv` by
    metis_tac[mem_path_offset_sound] >>
  `value_has_type tv v` by metis_tac[evaluate_subscripts_type] >>
  qexists_tac `v` >>
  simp[read_place_def, get_scopes_def, bind_def, lift_option_type_def,
       lift_sum_def, return_def, read_memory_path_def, place_type_value_def]
QED

Theorem augassign_memory_load_joint:
  expr_sim_inv cenv cx env es /\
  supported_target_info tops bindings bt = SOME info /\
  eval_target_place cx bt es = (INL (MemoryPlace id path),st) /\
  (?entry v. lookup_scopes id st.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INL v) /\
  is_word_type ty /\
  read_place cx (MemoryPlace id path) st = (INL cur,st) /\
  place_type_value cx (MemoryPlace id path) st = (INL ptv,st) /\
  (!H. valid_horizon cx st0 H st.storage_trace ==>
    target_post H ctx func cenv cx es sa sb s0 st
      (PlaceR (MemoryPlace id path)) (Type ty) r s /\
    target_ptr_ok cenv (PlaceR (MemoryPlace id path)) r G tn s /\
    ghost_inv_at (DF H) lo d cenv cx st G tn s) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand (FST r) s = SOME a /\
  emit_op MLOAD [FST r] sb = (old,sc) /\
  fn_has_code sb sc func /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  x = STRING #"%" (toString sb.cs_next_var) /\
  i = mk_inst sb.cs_next_id MLOAD [FST r] [x] /\
  raw = update_var x (mload (w2n a) s) s
  ==>
  ?u G1 tn1.
    !H. valid_horizon cx st0 H st.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,G1,tn1) /\
      evaluate_type (get_tenv cx) ty = SOME ptv /\
      value_has_type ptv cur /\
      eval_operand old u = SOME (typed_val_to_w256 ptv cur) /\
      eval_operand (FST r) u = SOME a /\
      op_taint tn1 old = {} /\ op_prov G1 old = NONE /\
      ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\
      state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
      tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
      tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
      (!q. not_fresh_at sb q ==> lookup_var q u = lookup_var q s /\
           FLOOKUP G1 q = FLOOKUP G q /\
           op_taint tn1 (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  qexistsl_tac [`raw with vs_inst_idx := SUC s.vs_inst_idx`,
                `step_prov PG G i raw`, `step_taint i s raw tn`] >>
  rpt gen_tac >> disch_tac >>
  first_assum (drule_then strip_assume_tac) >>
  drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    augassign_memory_load_resources >>
  disch_then (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `supported_target_info _ _ _ = _`)) >>
  simp[] >>
  disch_then drule >> strip_tac >>
  qpat_assum `evaluate_type _ _ = SOME _` (fn th => rewrite_tac[th]) >>
  qpat_assum `value_has_type _ _` (fn th => rewrite_tac[th]) >>
  qpat_assum `mload _ _ = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qspec_then `\H'. H' = H` (irule o SRULE []) augassign_mload_joint_step >>
  simp[]

QED
