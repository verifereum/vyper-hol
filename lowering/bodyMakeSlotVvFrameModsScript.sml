(* A held-address calculation frames the already-evaluated operand. *)
Theory bodyMakeSlotVvFrameMods
Ancestors
  bodyFullPostsMods bodyForRangeScalarFrameMods bodyFullUnwrapRun
  exprSimVVFrame bodyPtrDefs ptrDiscipline loweringStateRelDefs
  context venomState compileEnv finite_map
  bodyPtrSignedConvertSourceFrame loweringPosts exprSimProps

Theorem make_slot_vv_readonly_post_mods:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
  local_ptrs_reserved ce sa /\ sm.cs_next_id <= sn.cs_next_id /\
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s ==>
  vv_post_mods H ctx func ce cx e es sa sn s0 ee raw vv t
Proof
  strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[vv_post_mods_def]) >>
  `stmt_state_rel H ctx func ce cx ee t` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s`,`sa`] >> simp[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   contract_storage t = contract_storage s /\ contract_transient t = contract_transient s` by
    (qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => pure_once_rewrite_tac[th] >> simp[contract_storage_def,contract_transient_def])) >>
  `!id q sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) ==>
             lookup_var q t = lookup_var q s` by
    (rpt strip_tac >> first_x_assum irule >>
     qpat_x_assum `local_ptrs_reserved _ _` (strip_assume_tac o REWRITE_RULE[local_ptrs_reserved_def]) >>
     first_x_assum drule >> simp[]) >>
  `!n b k. local_region ce ee.scopes t n b k <=> local_region ce ee.scopes s n b k` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `immutable_frame_mods func ce cx ee t` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`s`,`sa`] >> simp[]) >>
  `vv_holds_mods ce cx (post_value_type ce e) raw vv ee t` by
    (Cases_on `vv` >> fs[vv_holds_mods_def,vv_operand_def]
     >- (irule vv_holds_vars_frame >> qexists `s` >> simp[vv_operand_def]) >>
     Cases_on `p.ptr_location = LocCode` >> fs[vv_holds_mods_def]
     >- (qpat_x_assum `immutable_holds_mods _ _ _ _ _ _ s` mp_tac >>
         simp[immutable_holds_mods_def,immutable_holds_def]) >>
     irule vv_holds_vars_frame >> qexists `s` >> simp[vv_operand_def]) >>
  `vv_place_ptr_mods ce cx ee t raw vv` by
    (Cases_on `raw` >> TRY (rename1 `vv_place_ptr_mods _ _ _ _ (PlaceR pl) _` >> Cases_on `pl`) >>
     Cases_on `vv` >> fs[vv_place_ptr_mods_def] >>
     irule vv_place_ptr_vars_frame >> qexists `s` >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `vv_at ce cx (post_value_type ce e) sa sn ee raw vv t` by
    (irule vv_at_vars_frame >> qexistsl [`s`,`sm`] >> simp[]) >>
  `post_value_type ce e <> expr_type e ==>
     vv_own ce cx (post_value_type ce e) sa sn ee raw vv t` by
    (strip_tac >> irule vv_own_vars_frame >> qexistsl [`s`,`sm`] >> simp[]) >>
  `~expr_has_effect e ==> vv_storage_live H cx vv ee t` by
    (strip_tac >> Cases_on `vv` >> fs[vv_operand_def]) >>
  `locals_kept ce es ee s0 t` by (drule_all locals_kept_mem_tail >> simp[]) >>
  `pure_frame ce func es sa s0 t <=> pure_frame ce func es sa s0 s` by
    (irule pure_frame_state_cong >> simp[]) >>
  simp[vv_post_mods_def] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >> qexists `aid` >> simp[]
QED

Theorem make_slot_vv_readonly_ptr_mods:
  ptr_vv_ok cx ty raw vv ee G tn s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  op_prov Gf (vv_operand vv) = op_prov G (vv_operand vv) /\
  op_taint tf (vv_operand vv) = op_taint tn (vv_operand vv) /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_transient = s.vs_transient ==>
  ptr_vv_ok cx ty raw vv ee Gf tf t
Proof
  Cases_on `vv` >> simp[vv_operand_def,ptr_vv_ok_def,ptr_val_ok_def,ptr_mem_ok_def]
  >- (Cases_on `o'` >> simp[op_prov_def]) >>
  Cases_on `p.ptr_operand` >> simp[op_prov_def]
QED
