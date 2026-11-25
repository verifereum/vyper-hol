(* The loop body has already landed and popped its scope. Only the
   saved counter and its temporary are written on the back edge. *)
Theory bodyForRangeIncrementMods
Ancestors
  bodyForRangeHeaderMods bodyForRangeScalarFrameMods bodyFullForRange
  bodyFullIfExpReach bodyFullShared allocaHistory exprSimOperands
  exprLoweringProps stmtSimDefs stmtSimProps loweringPosts venomInst
  venomInstProps venomState finite_map fragGasOriginPtr fragExec
  ptrDiscipline bodyPtrDefs stmtSimForParts integer_word
  bodyFullShadowBodyInv bodySimFull

Theorem range_increment_header_mods:
  n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\ Num (n2 - n1) <= bound /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  k + LENGTH (a::rs) = Num (n2 - n1) /\
  a::rs = GENLIST (\j. Value (IntV (n1 + &(k + j)))) (LENGTH (a::rs)) /\
  lookup_block incr_lbl func.fn_blocks = SOME
    <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [cv]; mk_inst i3 JMP [Label cond_lbl] []]|> /\
  s.vs_current_bb = incr_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa cv /\ ~not_fresh_at sa nv /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  cv <> nv /\ p <> cv /\ p <> nv /\ ev <> cv /\ ev <> nv /\
  lookup_var cv s = SOME (i2w (n1 + &k)) /\ lookup_var ev s = SOME (i2w n2) /\
  lookup_var p s = SOME w /\ FLOOKUP s.vs_allocas aid = SOME (w2n w,sz) /\
  ptr_covers G tn p s sz /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  op_taint tn (Var ev) = {} /\ op_prov G (Var ev) = NONE /\
  body_const_cells_agree_mods mods cx env ee /\
  expr_sim_inv_mods mods cenv cx env ee /\ lookup_scopes id ee.scopes = NONE /\
  storage_trace_domain cx st0 ee.storage_trace /\
  stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
  storage_well_formed_on cx ee (FST H) /\
  ret_pc_ok cenv sa s /\ return_buf_frame d cenv sb0 s /\
  return_buf_sep d cenv ee s /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn s ==>
  let v = i2w (n1 + &k) + 1w;
      t = jump_to cond_lbl (update_var cv v (update_var nv v s));
      G1 = DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv});
      tn1 = tn with t_var := tn.t_var |+ (nv,{}) |+ (cv,{})
  in
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
    range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
      sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p aid sz w
      H rs ee G1 tn1 t
Proof
  strip_tac >> simp[LET_THM, Excl "DRESTRICT_DRESTRICT"] >>
  qabbrev_tac `v = i2w (n1 + &k) + (1w:bytes32)` >>
  qabbrev_tac `u = update_var cv v (update_var nv v s)` >>
  qabbrev_tac `t = jump_to cond_lbl u` >>
  qabbrev_tac `G1 = DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (nv,{}) |+ (cv,{})` >>
  conj_asm1_tac >- suspend "path" >>
  `!x. x <> cv /\ x <> nv ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
     op_taint tn1 (Var x) = op_taint tn (Var x)` by
    simp[Abbr `t`, Abbr `u`, Abbr `G1`, Abbr `tn1`, jump_to_def, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >> `x <> cv /\ x <> nv` by (conj_tac >> CCONTR_TAC >> gvs[]) >>
     first_x_assum drule >> simp[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_inst_idx = 0 /\ t.vs_current_bb = cond_lbl /\ ~t.vs_halted /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    simp[Abbr `t`, Abbr `u`, jump_to_def, update_var_def] >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by simp[Abbr `tn1`] >>
  `lookup_var cv t = SOME (i2w (n1 + &(k + 1))) /\
   op_taint tn1 (Var cv) = {} /\ op_prov G1 (Var cv) = NONE` by
    simp[Abbr `t`, Abbr `u`, Abbr `v`, Abbr `G1`, Abbr `tn1`,
         jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
         FLOOKUP_DRESTRICT, op_prov_def, op_taint_def, i2w_counter_suc] >>
  `lookup_var ev t = SOME (i2w n2) /\ op_taint tn1 (Var ev) = {} /\
   op_prov G1 (Var ev) = NONE` by
    (`FLOOKUP G ev = NONE` by fs[op_prov_def] >>
     qpat_assum `!x. x <> cv /\ x <> nv ==> _` (qspec_then `ev` mp_tac) >>
     simp[op_prov_def]) >>
  `lookup_var p t = SOME w /\ ptr_covers G1 tn1 p t sz` by
    (`lookup_var p t = lookup_var p s /\ FLOOKUP G1 p = FLOOKUP G p /\
       op_taint tn1 (Var p) = op_taint tn (Var p)` by
       (qpat_assum `!x. x <> cv /\ x <> nv ==> _` irule >> simp[]) >>
     qpat_x_assum `ptr_covers G tn p s sz` mp_tac >> simp[ptr_covers_def]) >>
  drule_all range_suffix_cons_mods >> strip_tac >>
  simp[range_header_mods_def] >>
  conj_tac >-
    (qexists_tac `k + 1` >>
     qpat_x_assum `rs = GENLIST _ _` mp_tac >>
     simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  suspend "frames"
QED

Resume range_increment_header_mods[path]:
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by fs[range_outer_frame_mods_def] >>
  simp[Abbr `t`, Abbr `u`, Abbr `G1`, Abbr `tn1`, Abbr `v`] >>
  irule (REWRITE_RULE [DRESTRICT_DRESTRICT] range_full_increment_path) >>
  simp[get_instruction_def] >>
  qexistsl [`i1`,`i2`,`i3`] >> simp[]
QED

Resume range_increment_header_mods[frames]:
  `not_local_ptr cenv ee.scopes cv /\ not_local_ptr cenv ee.scopes nv` by
    (conj_tac >> irule fresh_not_local_ptr >> qexists `sa` >> simp[]) >>
  conj_tac >- suspend "relation" >>
  conj_tac >-
    (irule immutable_frame_mods_exterior_frame >>
     goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
     qexists `sa` >> simp[]) >>
  conj_tac >-
    (irule ret_pc_ok_frame >> goal_assum (drule_at (Pat `ret_pc_ok _ _ _`)) >>
     simp[]) >>
  conj_tac >- suspend "buffer" >>
  conj_tac >- suspend "separation" >>
  conj_tac >-
    (irule ghost_inv_at_mods_exterior_frame >>
     goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
     qexists `sa` >> simp[]) >>
  conj_tac >-
    (qpat_assum `gas_origin_ptr_path _ _ _ (OK t,_,_)`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     qpat_assum `!fn inst u. frag_reachable ctx func s fn inst u ==> _`
       (pure_rewrite_tac o single o EQT_INTRO) >> simp[]) >>
  suspend "outer"
QED

Resume range_increment_header_mods[relation]:
  simp[Abbr `t`, Abbr `u`, stmt_state_rel_jump_to] >>
  irule stmt_state_rel_update_var >> simp[] >>
  irule stmt_state_rel_update_var >> simp[]
QED

Resume range_increment_header_mods[buffer]:
  Cases_on `d` >- fs[return_buf_frame_def] >>
  PairCases_on `x` >> fs[return_buf_frame_def] >>
  `not_fresh_at sa x'` by first_assum drule >> simp[]
QED

Resume range_increment_header_mods[separation]:
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t` by
    (rpt strip_tac >> gvs[return_buf_sep_def, allocas_from_def] >>
     first_assum ACCEPT_TAC) >>
  irule return_buf_sep_locals_kept >> simp[] >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ s` (irule_at Any) >>
  qexists `sa` >> simp[]
QED

Resume range_increment_header_mods[outer]:
  qhdtm_x_assum `range_outer_frame_mods` mp_tac >>
  simp[range_outer_frame_mods_def] >> strip_tac >>
  `alloca_frame cenv es0 sa s0 cenv ee u` by
    (simp[Abbr `u`] >> irule alloca_frame_update_var >> simp[] >>
     irule alloca_frame_update_var >> simp[]) >>
  `alloca_frame cenv es0 sa s0 cenv ee t` by
    (irule alloca_frame_same_state >> qexists `u` >>
     simp[NoAsms, Abbr `t`, jump_to_def] >> first_assum ACCEPT_TAC) >>
  `alloca_history func t` by
    (irule alloca_history_jump >> simp[] >> qexists `s` >> simp[]) >>
  `allocas_below_fmp t = allocas_below_fmp s` by
    simp[Abbr `t`, Abbr `u`, jump_to_def, update_var_def, allocas_below_fmp_def] >>
  simp[] >> first_assum ACCEPT_TAC
QED

Finalise range_increment_header_mods
