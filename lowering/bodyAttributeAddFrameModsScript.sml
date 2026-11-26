(* A fresh ADD changes the cursor and one variable, not the linked base value. *)
Theory bodyAttributeAddFrameMods
Ancestors
  bodyFullAttributeAdd bodyForRangeScalarFrameMods bodyFullUnwrapRun
  bodyPtrMakeArrayEmission bodyPtrSignedConvertSourceFrame
  bodyFullPostsMods exprSimVVFrame exprOperandVar exprSimProps
  exprLowering loweringPosts loweringStateRelDefs freshWrites
  allocaHistory ptrDiscipline venomState venomInst ASCIInumbers finite_map
  context compileEnv fragExec emitHelperProps vyperAST

Triviality attribute_holds_readonly:
  vv_holds_mods ce cx ty raw vv ee s /\
  t.vs_memory = s.vs_memory /\ contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s ==>
  vv_holds_mods ce cx ty raw vv ee t
Proof
  Cases_on `vv` >> simp[vv_holds_mods_def] >> strip_tac
  >- (irule vv_holds_vars_frame >> qexists `s` >> simp[])
  >> rename1 `vv_operand (LocatedValue _ p)` >> Cases_on `p.ptr_location = LocCode`
  >- (fs[vv_operand_def, vv_holds_mods_def] >>
      qpat_x_assum `immutable_holds_mods _ _ _ _ _ _ s` mp_tac >>
      simp[immutable_holds_mods_def, immutable_holds_def])
  >> fs[] >> irule vv_holds_vars_frame >> qexists `s` >> simp[]
QED

Triviality attribute_place_readonly:
  vv_place_ptr_mods ce cx ee s raw vv /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!id q sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) ==>
             lookup_var q t = lookup_var q s) ==>
  vv_place_ptr_mods ce cx ee t raw vv
Proof
  Cases_on `raw`
  >> TRY (rename1 `vv_place_ptr_mods _ _ _ _ (PlaceR pl) _` >> Cases_on `pl`)
  >> Cases_on `vv` >> simp[vv_place_ptr_mods_def] >> strip_tac
  >> irule vv_place_ptr_vars_frame >> qexists `s` >> simp[]
  >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

Triviality attribute_base_post_readonly:
  vv_post_mods H ctx func ce cx obj es sa sm s0 ee raw vv s /\
  local_ptrs_reserved ce sa /\ sm.cs_next_id <= sn.cs_next_id /\
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s ==>
  vv_post_mods H ctx func ce cx obj es sa sn s0 ee raw vv t
Proof
  strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `stmt_state_rel H ctx func ce cx ee t` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s`,`sa`] >> simp[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   contract_storage t = contract_storage s /\ contract_transient t = contract_transient s` by
    (qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => pure_once_rewrite_tac[th] >> simp[contract_storage_def, contract_transient_def])) >>
  `!id q sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) ==>
             lookup_var q t = lookup_var q s` by
    (rpt strip_tac >> first_x_assum irule >>
     qpat_x_assum `local_ptrs_reserved _ _` (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     first_x_assum drule >> simp[]) >>
  `!n b k. local_region ce ee.scopes t n b k <=> local_region ce ee.scopes s n b k` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `immutable_frame_mods func ce cx ee t` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`s`,`sa`] >> simp[]) >>
  drule_all_then assume_tac attribute_holds_readonly >>
  drule_all_then assume_tac attribute_place_readonly >>
  `vv_at ce cx (post_value_type ce obj) sa sn ee raw vv t` by
    (irule vv_at_vars_frame >> qexistsl [`s`,`sm`] >> simp[]) >>
  `post_value_type ce obj <> expr_type obj ==>
     vv_own ce cx (post_value_type ce obj) sa sn ee raw vv t` by
    (strip_tac >> irule vv_own_vars_frame >> qexistsl [`s`,`sm`] >> simp[]) >>
  `~expr_has_effect obj ==> vv_storage_live H cx vv ee t` by
    (strip_tac >> Cases_on `vv` >> fs[vv_operand_def]) >>
  `locals_kept ce es ee s0 t` by (drule_all locals_kept_mem_tail >> simp[]) >>
  `pure_frame ce func es sa s0 t <=> pure_frame ce func es sa s0 s` by
    (irule pure_frame_state_cong >> simp[]) >>
  simp[vv_post_mods_def] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >> qexists `aid` >> simp[]
QED

Triviality attribute_add_history:
  alloca_history func s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode <> ALLOCA /\
  t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb /\
  t.vs_inst_idx = SUC s.vs_inst_idx ==>
  alloca_history func t
Proof
  simp[alloca_history_def] >> strip_tac >> rpt strip_tac >> gvs[] >>
  `k < s.vs_inst_idx \/ k = s.vs_inst_idx` by decide_tac
  >- (first_x_assum irule >> simp[] >> goal_assum drule >> simp[])
  >> gvs[]
QED

Theorem attribute_add_frame_mods:
  compile_expr ce ty obj sa = (vv,sm) /\
  emit_op ADD [vv_operand vv; Lit off] sm = (dst,sn) /\
  fn_has_code sm sn func /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand (vv_operand vv) s = SOME w /\ op_taint tn (vv_operand vv) = {} /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post_mods H ctx func ce cx obj es sa sm s0 ee raw vv s /\
       ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) ==>
  ?out t G' tn'.
    dst = Var out /\ out = STRING #"%" (toString sm.cs_next_var) /\
    (!D lo' explicit. allocas_from lo' s ==>
      gas_origin_ptr_path (D,lo',explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    eval_operand (vv_operand vv) t = SOME w /\ eval_operand dst t = SOME (w + off) /\
    FLOOKUP G' out = op_prov G (vv_operand vv) /\ op_taint tn' dst = {} /\
    (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
                       op_taint tn' (Var p) = op_taint tn (Var p)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G' tn' /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post_mods H ctx func ce cx obj es sa sn s0 ee raw vv t /\
       ghost_inv_at_mods (DF H) lo d ce cx ee G' tn' t)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac emit_op_fetch_boundary >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ADD [vv_operand vv; Lit off] [tmp]` >>
  qabbrev_tac `u = update_var tmp (w + off) s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G' = step_prov PG G i u` >>
  qabbrev_tac `tn' = step_taint i s u tn` >>
  `(!D lo' explicit. allocas_from lo' s ==>
      gas_origin_ptr_path (D,lo',explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    FLOOKUP G' tmp = op_prov G (vv_operand vv) /\ op_taint tn' dst = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. p <> tmp ==> FLOOKUP G' p = FLOOKUP G p /\
                       op_taint tn' (Var p) = op_taint tn (Var p))` by
    (map_every (fn tm => qpat_assum tm
       (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (i = _)`,`Abbrev (u = _)`,`Abbrev (t = _)`,
        `Abbrev (G' = _)`,`Abbrev (tn' = _)`] >>
     drule_all attribute_add_full_frame >> disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >> `x <> STRING #"%" (toString sm.cs_next_var)` by
       (fs[not_fresh_at_def] >> first_x_assum irule >> simp[]) >>
     simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE, EQ_SYM_EQ]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand (vv_operand vv) t = SOME w` by
    (`!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
       (drule (cj 1 compiler_compile_var) >> simp[]) >>
     Cases_on `vv_operand vv` >> fs[eval_operand_def] >>
     simp[Abbr `t`, Abbr `u`, update_var_def, eval_operand_def]) >>
  `alloca_history func t` by
    (irule attribute_add_history >> qexistsl [`bb`,`i`,`s`] >>
     simp[Abbr `i`, Abbr `t`, Abbr `u`, update_var_def, mk_inst_def]) >>
  qexistsl [`tmp`,`t`,`G'`,`tn'`] >>
  simp[] >> rpt conj_tac
  >- simp[Abbr `t`, Abbr `u`, eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
  >- simp[Abbr `t`, Abbr `u`, update_var_def]
  >- simp[Abbr `t`, Abbr `u`, update_var_def]
  >- simp[Abbr `t`, Abbr `u`, update_var_def]
  >- simp[Abbr `t`, Abbr `u`, update_var_def]
  >- (strip_tac >> fs[Abbr `t`, Abbr `u`, update_var_def, allocas_below_fmp_def] >>
      first_assum ACCEPT_TAC)
  >- simp[Abbr `t`, Abbr `u`, update_var_def]
  >- simp[Abbr `t`, Abbr `u`, update_var_def]
  >- (irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[])
  >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac
  >- (irule attribute_base_post_readonly >> simp[] >> qexistsl [`s`,`sm`] >> simp[] >>
      drule emitted_insts_emit_op >> simp[Abbr `t`, Abbr `u`, update_var_def])
  >> irule ghost_inv_at_mods_exterior_frame >> qexistsl [`G`,`ee`,`s`,`sa`,`tn`] >>
     simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED
