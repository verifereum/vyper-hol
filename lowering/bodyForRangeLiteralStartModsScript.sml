(* The literal setup starts just after the loop-slot allocation. Neither
   endpoint runs target expression code, and neither changes source state. *)
Theory bodyForRangeLiteralStartMods
Ancestors
  bodyForRangeHeaderMods bodyForRangeScalarFrameMods bodyFullForRange
  bodyFullIfExpReach bodyFullShared allocaHistory exprSimOperands
  exprLoweringProps stmtSimDefs stmtSimProps loweringPosts venomInst
  venomInstProps venomState finite_map fragGasOriginPtr fragExec
  ptrDiscipline bodyPtrDefs stmtSimForParts integer_word
  bodyFullShadowBodyInv bodySimFull supportedStmts vyperTypeValues
  vyperValueOperation vyperInterpreter vyperTypeSystem vyperAST bodyMemoryDefs vyperState

val _ = Parse.hide "body";

Theorem range_literal_source_mods[local]:
  supported_iterator tops typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound /\
  is_int_type typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  well_typed_expr env (Literal a1 (IntL n1)) /\ expr_type (Literal a1 (IntL n1)) = typ /\
  well_typed_expr env (Literal a2 (IntL n2)) /\ expr_type (Literal a2 (IntL n2)) = typ ==>
  n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\ Num (n2 - n1) = bound /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) ee =
    (INL (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))),ee) /\
  eval_stmt cx (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) ee =
    eval_for cx tyv id body (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))) ee
Proof
  simp[supported_iterator_def, well_typed_expr_def, expr_type_def] >> strip_tac >>
  `value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2)` by
    (conj_tac >> irule (REWRITE_RULE[evaluate_literal_def]
       (Q.INST [`lit` |-> `IntL k`] well_typed_literal_sound)) >>
     qexistsl [`get_tenv cx`, `typ`] >> fs[]) >>
  `Num (n2 - n1) < dimword (:256)` by
    (qpat_assum `evaluate_type _ _ = SOME tyv`
       (mp_then Any mp_tac stmtSimForRangeTheory.range_end_words) >> simp[]) >>
  simp[eval_iterator_range_lit] >>
  pure_once_rewrite_tac[evaluate_def] >>
  simp[LET_THM, lift_option_type_def, lift_option_def, bind_def, ignore_bind_def,
       eval_iterator_range_lit, return_def, check_def, assert_def,
       vyperValueTheory.compatible_bound_def]
QED

(* Select the scalar landing using only the machine inputs. The indexed
   source and ghost frames are needed afterwards, at each requested horizon. *)
Theorem range_literal_start_core[local]:
  supported_iterator tops typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound /\
  is_int_type typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  well_typed_expr env (Literal a1 (IntL n1)) /\ expr_type (Literal a1 (IntL n1)) = typ /\
  well_typed_expr env (Literal a2 (IntL n2)) /\ expr_type (Literal a2 (IntL n2)) = typ /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst j0 JMP [Label entry_lbl] []) /\
  lookup_block entry_lbl func.fn_blocks = SOME
    <|bb_label := entry_lbl; bb_instructions :=
      [mk_inst j1 ASSIGN [Lit (i2w n1)] [cv];
       mk_inst j2 ADD [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev];
       mk_inst j3 JMP [Label cond_lbl] []]|> /\
  ~s.vs_halted /\ cv <> ev /\ p <> cv /\ p <> ev /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa cv /\ ~not_fresh_at sa ev /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sb0.cs_next_var /\
  lookup_var p s = SOME w /\ FLOOKUP s.vs_allocas aid = SOME (w2n w,sz) /\
  ptr_covers G tn p s sz /\
  body_const_cells_agree_mods mods cx env ee /\
  expr_sim_inv_mods mods cenv cx env ee /\ lookup_scopes id ee.scopes = NONE /\
  storage_trace_domain cx st0 ee.storage_trace /\
  allocas_from lo s /\
  ret_pc_ok cenv sa s /\ return_buf_frame d cenv sa s /\
  return_buf_sep d cenv ee s /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn s ==>
  let rs = GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)) in
    eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) ee = (INL rs,ee) /\
    eval_stmt cx (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) ee =
      eval_for cx tyv id body rs ee /\
    ?t G' tn'.
      ~t.vs_halted /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
      (!H. stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
        storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s ==>
        range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
          sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p aid sz w H rs ee G' tn' t)
Proof
  strip_tac >> simp[LET_THM] >>
  drule_all range_literal_source_mods >>
  disch_then (qspecl_then [`id`, `ee`, `body`] strip_assume_tac) >> simp[] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by fs[range_outer_frame_mods_def] >>
  drule_all range_literal_entry_full >>
  disch_then (qspecl_then [`G`, `tn`]
    (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac)) >>
  qexistsl [`t`,`G'`,`tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (gen_tac >> first_assum irule) >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!D explicit PG. gas_origin_ptr_path _ _ [] _`
    (qspecl_then [`DF H`,`explicit`,`PG`] assume_tac) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >> `x <> cv /\ x <> ev` by (conj_tac >> CCONTR_TAC >> gvs[]) >>
     first_x_assum drule >> simp[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
   t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp` by
    simp[jump_to_def, update_var_def] >>
  `tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm` by simp[] >>
  `lookup_var p t = SOME w /\ ptr_covers G' tn' p t sz` by
    (qpat_assum `!x. x <> cv /\ x <> ev ==> _` (qspec_then `p` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     pure_rewrite_tac[ptr_covers_def] >>
     qpat_x_assum `ptr_covers G tn p s sz` (mp_tac o PURE_REWRITE_RULE[ptr_covers_def]) >>
     simp[]) >>
  qpat_x_assum `Num (n2 - n1) = bound` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `t = jump_to _ _` kall_tac >>
  qpat_x_assum `G' = DRESTRICT _ _` kall_tac >>
  qpat_x_assum `tn' = _ with t_var := _` kall_tac >>
  irule range_header_init_mods >> simp[op_prov_def] >>
  suspend "frames"
QED

Resume range_literal_start_core[frames]:
  `not_local_ptr cenv ee.scopes cv /\ not_local_ptr cenv ee.scopes ev` by
    (conj_tac >> irule fresh_not_local_ptr >> qexists `sa` >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ee t` by simp[] >>
  `immutable_frame_mods func cenv cx ee t` by
    (irule immutable_frame_mods_exterior_frame >>
     goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
     qexists `sa` >> simp[]) >>
  `ret_pc_ok cenv sa t` by
    (irule ret_pc_ok_frame >> goal_assum (drule_at (Pat `ret_pc_ok _ _ _`)) >> simp[]) >>
  `return_buf_frame d cenv sb0 t` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >> simp[]) >>
  `return_buf_sep d cenv ee t` by suspend "separation" >>
  `ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' t` by
    (irule ghost_inv_at_mods_exterior_frame >>
     goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
     qexists `sa` >> simp[]) >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    (qpat_assum `gas_origin_ptr_path _ _ _ (OK t,_,_)`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     qpat_assum `!fn inst u. frag_reachable ctx func s fn inst u ==> _`
       (pure_rewrite_tac o single o EQT_INTRO) >> simp[]) >>
  `range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G' tn' t` by suspend "outer" >>
  simp[] >> first_assum ACCEPT_TAC
QED

Resume range_literal_start_core[separation]:
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t` by
    (rpt strip_tac >> gvs[return_buf_sep_def, allocas_from_def] >>
     first_assum ACCEPT_TAC) >>
  irule return_buf_sep_locals_kept >> simp[] >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ s` (irule_at Any) >>
  qexists `sa` >> simp[]
QED

Resume range_literal_start_core[outer]:
  qhdtm_x_assum `range_outer_frame_mods` mp_tac >>
  simp[range_outer_frame_mods_def] >> strip_tac >>
  `alloca_frame cenv es0 sa s0 cenv ee t` by
    (first_x_assum irule >> simp[]) >>
  `alloca_history func t` by
    (irule alloca_history_jump >> simp[] >> qexists `s` >> simp[]) >>
  `allocas_below_fmp t = allocas_below_fmp s` by simp[allocas_below_fmp_def] >>
  simp[] >> first_assum ACCEPT_TAC
QED

Finalise range_literal_start_core[local]

Theorem range_literal_start_mods:
  supported_iterator tops typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound /\
  is_int_type typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  well_typed_expr env (Literal a1 (IntL n1)) /\ expr_type (Literal a1 (IntL n1)) = typ /\
  well_typed_expr env (Literal a2 (IntL n2)) /\ expr_type (Literal a2 (IntL n2)) = typ /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst j0 JMP [Label entry_lbl] []) /\
  lookup_block entry_lbl func.fn_blocks = SOME
    <|bb_label := entry_lbl; bb_instructions :=
      [mk_inst j1 ASSIGN [Lit (i2w n1)] [cv];
       mk_inst j2 ADD [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev];
       mk_inst j3 JMP [Label cond_lbl] []]|> /\
  ~s.vs_halted /\ cv <> ev /\ p <> cv /\ p <> ev /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa cv /\ ~not_fresh_at sa ev /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sb0.cs_next_var /\
  lookup_var p s = SOME w /\ FLOOKUP s.vs_allocas aid = SOME (w2n w,sz) /\
  ptr_covers G tn p s sz /\
  body_const_cells_agree_mods mods cx env ee /\
  expr_sim_inv_mods mods cenv cx env ee /\ lookup_scopes id ee.scopes = NONE /\
  storage_trace_domain cx st0 ee.storage_trace /\
  stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
  storage_well_formed_on cx ee (FST H) /\
  ret_pc_ok cenv sa s /\ return_buf_frame d cenv sa s /\
  return_buf_sep d cenv ee s /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn s ==>
  let rs = GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)) in
    eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) ee = (INL rs,ee) /\
    eval_stmt cx (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) ee =
      eval_for cx tyv id body rs ee /\
    ?t G' tn'.
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
      range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
        sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p aid sz w H rs ee G' tn' t
Proof
  strip_tac >> simp[LET_THM] >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  drule_all_then (Q.ISPECL_THEN [`explicit`,`body`,`PG`,`DF`] strip_assume_tac)
    (SIMP_RULE std_ss [LET_THM] range_literal_start_core) >>
  simp[] >> qexistsl [`t`,`G'`,`tn'`] >> simp[]
QED

Theorem range_literal_start_uniform_mods:
  supported_iterator tops typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound /\
  is_int_type typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  well_typed_expr env (Literal a1 (IntL n1)) /\ expr_type (Literal a1 (IntL n1)) = typ /\
  well_typed_expr env (Literal a2 (IntL n2)) /\ expr_type (Literal a2 (IntL n2)) = typ /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst j0 JMP [Label entry_lbl] []) /\
  lookup_block entry_lbl func.fn_blocks = SOME
    <|bb_label := entry_lbl; bb_instructions :=
      [mk_inst j1 ASSIGN [Lit (i2w n1)] [cv];
       mk_inst j2 ADD [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev];
       mk_inst j3 JMP [Label cond_lbl] []]|> /\
  ~s.vs_halted /\ cv <> ev /\ p <> cv /\ p <> ev /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa cv /\ ~not_fresh_at sa ev /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sb0.cs_next_var /\
  lookup_var p s = SOME w /\ FLOOKUP s.vs_allocas aid = SOME (w2n w,sz) /\
  ptr_covers G tn p s sz /\
  body_const_cells_agree_mods mods cx env ee /\
  expr_sim_inv_mods mods cenv cx env ee /\ lookup_scopes id ee.scopes = NONE /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  ret_pc_ok cenv sa s /\ return_buf_frame d cenv sa s /\ return_buf_sep d cenv ee s /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn s ==>
  let rs = GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)) in
    eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) ee = (INL rs,ee) /\
    eval_stmt cx (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) ee =
      eval_for cx tyv id body rs ee /\
    ?t G' tn'. ~t.vs_halted /\
      (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
          sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p aid sz w H rs ee G' tn' t)
Proof
  strip_tac >> simp[LET_THM] >>
  `allocas_from lo s` by
    (`valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
       fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     fs[ghost_inv_at_mods_def]) >>
  drule_all_then (Q.ISPECL_THEN [`explicit`,`body`,`PG`,`DF`] strip_assume_tac)
    (SIMP_RULE std_ss [LET_THM] range_literal_start_core) >>
  simp[] >> qexistsl [`t`,`G'`,`tn'`] >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  first_assum irule >> simp[]
QED
