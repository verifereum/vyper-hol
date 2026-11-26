(* Rebase a reached linked child across the destination ADD. *)
Theory bodyStructFieldAddMods
Ancestors
  bodyFullPostsMods bodyForRangeScalarFrameMods bodyFullAttributeAdd
  bodyPtrMakeArrayAddFrame bodyPtrMakeArrayEmission assignBasePtrOffset
  exprSimVVFrame exprSimMemDefs exprSimProps freshWrites
  emitHelperProps allocaHistory venomExecSemantics finite_map words
  context compileEnv loweringPosts loweringStateRelDefs exprLoweringProps
  bodyFullShadowBodyInv bodyPtrDefs vyperState valueEncodingDefs
  ptrDiscipline fragGasOriginPtr venomState venomInst

Theorem add_holds_frame[local]:
  vv_holds_mods ce cx ty tv vv ee s /\ t.vs_memory = s.vs_memory /\
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s ==>
  vv_holds_mods ce cx ty tv vv ee t
Proof
  Cases_on `vv` >> simp[vv_holds_mods_def, vv_operand_def]
  >- metis_tac[vv_holds_vars_frame, vv_operand_def] >>
  rename1 `LocatedValue ann p` >> Cases_on `p.ptr_location = LocCode` >>
  simp[vv_holds_mods_def, immutable_holds_mods_def] >>
  metis_tac[vv_holds_vars_frame, vv_operand_def, immutable_holds_memory_cong]
QED

Theorem add_place_frame[local]:
  vv_place_ptr_mods ce cx ee s tv vv /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!id q sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) ==>
     lookup_var q t = lookup_var q s) ==>
  vv_place_ptr_mods ce cx ee t tv vv
Proof
  Cases_on `vv` >- simp[vv_place_ptr_mods_def] >>
  Cases_on `tv`
  >~ [`vv_place_ptr_mods _ _ _ _ (PlaceR _) _`]
  >- (rename1 `PlaceR place` >> Cases_on `place` >>
      simp[vv_place_ptr_mods_def] >> rpt strip_tac >>
      irule vv_place_ptr_vars_frame >> qexists_tac `s` >> simp[] >>
      rpt strip_tac >> res_tac >> simp[]) >>
  simp[vv_place_ptr_mods_def] >> rpt strip_tac >>
  irule vv_place_ptr_vars_frame >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >> res_tac >> simp[]
QED

Theorem add_post_frame[local]:
  vv_post_mods H ctx func ce cx e es si sm s0 ee tv vv s /\
  stmt_state_rel H ctx func ce cx ee t /\
  immutable_frame_mods func ce cx ee t /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!x. not_fresh_at si x ==> lookup_var x t = lookup_var x s) /\
  local_ptrs_reserved ce si /\ sm.cs_next_id <= stop.cs_next_id ==>
  vv_post_mods H ctx func ce cx e es si stop s0 ee tv vv t
Proof
  strip_tac >>
  `!id q sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) ==>
     lookup_var q t = lookup_var q s` by metis_tac[local_ptrs_reserved_def] >>
  `!n b sz. local_region ce ee.scopes t n b sz <=>
            local_region ce ee.scopes s n b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     first_x_assum irule >> goal_assum (drule_at Any)) >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `vv_holds_mods ce cx (post_value_type ce e) tv vv ee t` by
    (irule add_holds_frame >> qexists_tac `s` >> simp[]) >>
  `vv_place_ptr_mods ce cx ee t tv vv` by
    (irule add_place_frame >> qexists_tac `s` >> simp[] >> first_assum ACCEPT_TAC) >>
  `vv_at ce cx (post_value_type ce e) si stop ee tv vv t` by
    (irule vv_at_vars_frame >> qexistsl [`s`,`sm`] >> simp[]) >>
  `post_value_type ce e <> expr_type e ==>
   vv_own ce cx (post_value_type ce e) si stop ee tv vv t` by
    (strip_tac >> irule vv_own_vars_frame >> qexistsl [`s`,`sm`] >> simp[]) >>
  `locals_kept ce es ee s0 t` by
    (irule locals_kept_mem_tail >> qexists_tac `s` >> simp[]) >>
  `pure_frame ce func es si s0 t <=> pure_frame ce func es si s0 s` by
    simp[pure_frame_state_cong] >>
  `vv_storage_live H cx vv ee t <=> vv_storage_live H cx vv ee s` by
    (Cases_on `vv` >> gvs[vv_operand_def]) >>
  simp[vv_post_mods_def] >> metis_tac[]
QED

Theorem struct_field_add_mods:
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var out,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
  ptr_covers G tn root s capacity /\ FLOOKUP G root = SOME (region_base,cap) /\
  not_fresh_at sm root /\ w2n a + off < dimword(:256) /\ off + n <= capacity /\
  local_ptrs_reserved ce si /\ si.cs_next_var <= sm.cs_next_var /\
  (!p. vv_operand vv = Var p ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es si sm s0 ee tv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (!v. tv = Value v /\ ~is_word_type (post_value_type ce e) /\
       ~is_bytestring_type (post_value_type ce e) ==>
       vv_own ce cx (post_value_type ce e) si sm ee tv vv s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es si Gi ti s0 G tn /\
  alloca_history func s /\ alloca_inv s ==>
  ?t G' tn'.
    (!D lo' explicit. allocas_from lo' s ==>
      gas_origin_ptr_path (D,lo',explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func ce cx e es si sn s0 ee tv vv t /\
      ghost_inv_at_mods (DF H) lo d ce cx ee G' tn' t) /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv t /\
    ptr_vv_ok cx (post_value_type ce e) tv vv ee G' tn' t /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e op G' t) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G' t) /\
    (!v. tv = Value v /\ ~is_word_type (post_value_type ce e) /\
         ~is_bytestring_type (post_value_type ce e) ==>
         vv_own ce cx (post_value_type ce e) si sn ee tv vv t) /\
    (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?val. read_result cx tv ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
               eval_operand (vv_operand vv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
                 val_in_memory rt val (w2n w) mem)) /\
    ghost_kept_at lo ce es si Gi ti s0 G' tn' /\
    alloca_history func t /\ ~t.vs_halted /\
    t.vs_current_bb = sn.cs_current_bb /\ t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_data_section = s.vs_data_section /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!name b sz. local_region ce ee.scopes t name b sz <=>
                 local_region ce ee.scopes s name b sz) /\
    ptr_covers G' tn' root t capacity /\ not_fresh_at sn root /\
    ptr_covers G' tn' out t n /\ not_fresh_at sn out /\
    lookup_var out t = SOME (a+n2w off) /\
    sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id
Proof
  strip_tac >>
  drule_all emit_op_fetch_boundary >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ADD [Var root; Lit (n2w off)] [out]` >>
  qabbrev_tac `u = update_var out (a+n2w off) s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G' = step_prov PG G i u` >>
  qabbrev_tac `tn' = step_taint i s u tn` >>
  suspend "run"
QED

Resume struct_field_add_mods[run]:
  `eval_operand (Var root) s = SOME a` by simp[eval_operand_def] >>
  `(!D lo' explicit. allocas_from lo' s ==>
      gas_origin_ptr_path (D,lo',explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
   FLOOKUP G' out = FLOOKUP G root /\ op_taint tn' (Var out) = {} /\
   tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
   (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))` by
    (rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule_all attribute_add_full_frame >> simp[op_prov_def]) >>
  `!x. not_fresh_at sm x ==> x <> out` by fs[Abbr `out`] >>
  `!x. not_fresh_at si x ==> x <> out` by
    (gen_tac >> disch_tac >> qpat_assum `!x. not_fresh_at sm x ==> _` irule >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `si` >> simp[]) >>
  `!p. p <> out ==> lookup_var p t = lookup_var p s` by
    simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `!p. not_fresh_at si p ==> lookup_var p t = lookup_var p s /\
    FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >> `p <> out` by (first_x_assum irule >> simp[]) >> res_tac >> simp[]) >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s` by
    (Cases_on `vv_operand vv` >>
     gvs[Abbr `t`, Abbr `u`, eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `alloca_history func t` by
    (`step_inst_base i s = OK u` by
       simp[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs,
            mk_inst_def, exec_pure2_def, eval_operand_def] >>
     `get_instruction bb s.vs_inst_idx = SOME i` by fs[Abbr `i`, Abbr `out`] >>
     `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     drule_all alloca_history_base_step >>
     simp[Abbr `i`, mk_inst_def, is_terminator_def, Abbr `t`]) >>
  qexistsl [`t`,`G'`,`tn'`] >>
  suspend "posts"
QED

Resume struct_field_add_mods[posts]:
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_data_section = s.vs_data_section /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
   contract_storage t = contract_storage s /\ contract_transient t = contract_transient s /\
   ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
   t.vs_inst_idx = LENGTH sn.cs_current_insts` by
    simp[Abbr `t`, Abbr `u`, update_var_def, contract_storage_def, contract_transient_def] >>
  `sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var` by simp[] >>
  `!name b sz. local_region ce ee.scopes t name b sz <=>
               local_region ce ee.scopes s name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     `not_fresh_at si p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     qpat_assum `!p. not_fresh_at si p ==> lookup_var p t = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `not_local_ptr ce ee.scopes out` by
    (simp[not_local_ptr_def] >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "horizon" >>
  simp[] >> suspend "evidence"
QED

Resume struct_field_add_mods[horizon]:
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac
  >- (`stmt_state_rel H ctx func ce cx ee t` by
        (simp[Abbr `t`, Abbr `u`, stmt_state_rel_inst_idx] >>
         irule stmt_state_rel_update_var >>
         fs[vv_post_mods_def]) >>
      `immutable_frame_mods func ce cx ee t` by
        (irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`s`,`si`] >>
         fs[vv_post_mods_def] >> rpt strip_tac >> res_tac >> simp[]) >>
      irule add_post_frame >> simp[] >> qexistsl [`s`,`sm`] >>
      simp[] >> rpt strip_tac >> res_tac >> simp[]) >>
  irule ghost_inv_at_mods_exterior_frame >> qexistsl [`G`,`ee`,`s`,`si`,`tn`] >>
  simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume struct_field_add_mods[evidence]:
  `!p. vv_operand vv = Var p ==> p <> out` by
    (gen_tac >> disch_tac >> qpat_assum `!x. not_fresh_at sm x ==> _` irule >>
     qpat_assum `!p. vv_operand vv = Var p ==> _` irule >> simp[]) >>
  rpt conj_tac
  >~ [`vv_store_bound _ _ _ _ _ _ _`]
  >- (irule vv_store_bound_frame_mem_src >> qexists_tac `s` >> simp[])
  >~ [`ptr_vv_ok _ _ _ _ _ _ _ _`]
  >- (unabbrev_all_tac >> irule binop_source_ptr_vv_ok >> simp[] >>
      metis_tac[])
  >- (rpt strip_tac >> unabbrev_all_tac >> irule binop_source_ptr_buf_ok >>
      gvs[vv_operand_def] >> metis_tac[])
  >- (rpt strip_tac >> unabbrev_all_tac >> irule binop_source_ptr_buf_ok >>
      gvs[vv_operand_def] >> metis_tac[])
  >- (rpt strip_tac >> irule vv_own_vars_frame >> qexistsl [`s`,`sm`] >> simp[] >>
      qpat_assum `!v. _ ==> vv_own _ _ _ _ sm _ _ _ _` (qspec_then `v` mp_tac) >> simp[])
  >~ [`ghost_kept_at _ _ _ _ _ _ _ _ _`]
  >- (qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ G tn`
        (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
      simp[ghost_kept_at_def] >> rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC >> NO_TAC) >> rpt strip_tac >>
      qpat_assum `!p. not_fresh_at si p ==> lookup_var p t = _ /\ _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!x. not_fresh_at si x ==> FLOOKUP G x = _ /\ _`
        (drule_then strip_assume_tac) >> simp[])
  >~ [`ptr_covers G' tn' root t capacity`]
  >- (`root <> out` by (qpat_assum `!x. not_fresh_at sm x ==> _` irule >> simp[]) >>
      res_tac >> fs[ptr_covers_def])
  >~ [`not_fresh_at sn root`]
  >- (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >> simp[])
  >~ [`ptr_covers G' tn' out t n`]
  >- (irule assign_base_ptr_covers_offset_address >>
      simp[] >> qexistsl [`G`,`off`,`root`,`s`,`tn`,`capacity`,`a`] >>
      simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE])
  >~ [`not_fresh_at sn out`]
  >- simp[not_fresh_at_def, Abbr `out`] >>
  simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED
Finalise struct_field_add_mods
