(* Checked array-round control boundaries. The header transports the shared
   invariant to the element-installation block without erasing the path. *)
Theory forPtrArrayAssemble
Ancestors forPtrArrayTerminal forPtrArrayInvariant forPtrArrayPrepare forPtrArrayFinish
  forPtrRangePrepare stmtSimForArrayLoop bodyPtrDefs venomState
  ptrDiscipline finite_map exprLoweringProps ghostPcTransportPtr stmtFragPtr compileEnv stmtSimProps loweringPosts
  forPtrRangeSource forPtrRangeRound forPtrRoundCleanup gasExemptCert
  gasSummaryComposePtr vyperState fragGasPathPtr exprSimWordArgs vyperInterpreter
Libs monadsyntax

Theorem for_array_unequal_header_ptr:
  lookup_block cond_lbl func.fn_blocks =
    SOME <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []]|> /\
  n = LENGTH vs /\ n < dimword (:256) /\ k < LENGTH vs /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond_lbl st s0 G0 tn0 d name snapshot k es G tn s /\
  ~ctx_has_dalloca ctx /\ not_local_ptr cenv es.scopes dv /\
  idx <> dv /\ p <> dv /\ bp <> dv /\
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) ==>
  gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))
    (OK (jump_to stmts_lbl (update_var dv 0w s))) /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    stmts_lbl st s0 G0 tn0 d name snapshot k es
    (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))
    (jump_to stmts_lbl (update_var dv 0w s))
Proof
  strip_tac >> drule for_array_inv_header_ptr >> strip_tac >>
  `(n2w k : bytes32) <> n2w n` by
    (simp[wordsTheory.n2w_11] >> simp[arithmeticTheory.LESS_MOD] >> decide_tac) >>
  conj_tac
  >- (drule_all (SRULE [op_prov_def] for_array_header_test_path_ptr) >> simp[]) >>
  `!q. cenv.ce_return_buf <> SOME (PtrVar (Var dv) q)` by metis_tac[] >>
  `ghost_inv d cenv cx es (DRESTRICT G (COMPL {dv}))
    (tn with t_var := tn.t_var |+ (dv,{})) (update_var dv 0w s)` by
    (irule for_scalar_overwrite_ghost >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (update_var dv 0w s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  `ghost_inv d cenv cx es (DRESTRICT G (COMPL {dv}))
    (tn with t_var := tn.t_var |+ (dv,{}))
    (jump_to stmts_lbl (update_var dv 0w s))` by
    simp[jump_to_def, ghost_inv_jump_to] >>
  fs[for_array_inv_ptr_def, array_loop_inv_def] >>
  simp[for_array_inv_ptr_def, array_loop_inv_def, stmt_state_rel_jump_to,
       ret_pc_ok_jump_to] >>
  fs[lookup_var_def, eval_operand_def, op_taint_def] >>
  simp[jump_to_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  conj_tac
  >- (fs[ret_pc_ok_def, lookup_var_def] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      `x <> dv` by metis_tac[] >> simp[FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac
  >- (fs[ptr_covers_def, lookup_var_def, op_taint_def] >>
      simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  conj_tac
  >- (fs[ptr_covers_def, lookup_var_def, op_taint_def] >>
      simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  conj_tac
  >- (fs[local_region_def, not_local_ptr_def, lookup_var_def] >>
      rpt strip_tac >> `p' <> dv` by metis_tac[] >>
      gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac >> rpt strip_tac >> `x <> dv` by metis_tac[] >>
  simp[] >> metis_tac[]
QED


Theorem for_array_prepare_inputs_ptr:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride (Var bp)
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    stmts_lbl st s0 G0 tn0 d name snapshot k es G tn s /\
  k < LENGTH vs /\ snapshot.type = ArrayTV tv (Fixed n) /\
  snapshot.value = ArrayV (SArrayV kvs) /\
  vs = array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs) /\ n = LENGTH vs /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var bp) arrsz) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  w2n arr_base + k * stride < dimword (:256) /\
  st.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) ==>
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv (EL k vs)
    et (get_tenv cx) sa sb0 idx (Var bp) arr_base k stride ov ep j3 j4 bb sb0
Proof
  strip_tac >> drule_all for_array_inv_element_ptr >> strip_tac >>
  `val_in_memory tv (EL k vs) (w2n arr_base + k*stride) s.vs_memory` by
    (fs[array_for_code_def] >> first_x_assum irule >>
     simp[mem_agree_outside_def]) >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (irule for_array_code_top_ext_ptr >> goal_assum (drule_at Any) >>
     fs[for_array_inv_ptr_def, array_loop_inv_def]) >>
  drule cenv_top_ext_return_pc >> disch_tac >>
  `ret_pc_ok bc sb0 s` by
    (irule ret_pc_ok_frame >>
     qexistsl_tac [`cenv`, `s`, `st`] >>
     fs[for_array_inv_ptr_def, array_loop_inv_def, cenv_top_ext_def] >>
     decide_tac) >>
  irule array_for_code_entry_inputs >> goal_assum (drule_at Any) >>
  fs[for_array_inv_ptr_def] >> goal_assum (drule_at Any) >>
  simp[] >> fs[cenv_top_ext_def] >> metis_tac[]
QED

Theorem for_array_prepare_from_inv_ptr:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride (Var bp)
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    stmts_lbl st s0 G0 tn0 d name snapshot k es G tn s /\
  k < LENGTH vs /\ snapshot.type = ArrayTV tv (Fixed n) /\
  snapshot.value = ArrayV (SArrayV kvs) /\
  vs = array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs) /\ n = LENGTH vs /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var bp) arrsz) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  w2n arr_base + k * stride < dimword (:256) /\
  st.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\ ~ctx_has_dalloca ctx /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) ==>
  ?gf tf s2.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 gf tf (OK s2) /\
    array_entry_ready ctx func bc cx es id tv (EL k vs) sb0 sa ov ep sb0 s s2 /\
    ghost_inv d bc cx (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes)
      gf tf s2 /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
      FLOOKUP gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep` by metis_tac[] >>
  drule_all for_array_prepare_inputs_ptr >> disch_tac >>
  drule_all for_array_inv_element_ptr >> strip_tac >>
  `stride = type_memory_size tv` by fs[array_for_code_def] >>
  fs[for_array_inv_ptr_def] >>
  drule for_array_round_prepare_ptr >>
  disch_then drule >> simp[arithmeticTheory.MULT_COMM] >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] mp_tac) >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem for_array_prepared_control_ptr:
  array_for_code func cenv bc ty stmts id et tv n stride (Var bp)
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    stmts_lbl st s0 G0 tn0 d name snapshot k es G tn s /\
  array_entry_ready ctx func bc cx es id tv (EL k vs) sb0 sa ov ep sb0 s s2 /\
  (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
    FLOOKUP gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!x. not_fresh_at st x ==> not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) ==>
  ptr_covers gf tf p s2 sz /\
  ptr_covers gf tf bp s2 (LENGTH vs * type_memory_size tv) /\
  lookup_var idx s2 = SOME (n2w k) /\ lookup_var bp s2 = SOME arr_base /\
  lookup_var p s2 = SOME dst /\ FLOOKUP gf idx = NONE /\
  op_taint tf (Var idx) = {} /\
  FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok cenv st s2 /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x s2 = SOME v) /\
  (!x. not_fresh_at st x ==> FLOOKUP gf x = FLOOKUP G0 x /\
    op_taint tf (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  `not_fresh_at sa idx /\ idx <> ov /\ idx <> ep /\
   not_fresh_at sa p /\ p <> ov /\ p <> ep /\
   not_fresh_at sa bp /\ bp <> ov /\ bp <> ep` by fs[array_for_code_def] >>
  fs[for_array_inv_ptr_def] >>
  `lookup_var idx s2 = SOME (n2w k) /\
   eval_operand (Var bp) s2 = SOME arr_base /\ lookup_var p s2 = SOME dst /\
   FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
   ret_pc_ok cenv st s2` by
    (drule_all (SRULE [] (Q.INST [`saved_base` |-> `Var bp`]
       array_entry_ready_runtime)) >> simp[]) >>
  `FLOOKUP gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p) /\
   FLOOKUP gf bp = FLOOKUP G bp /\ op_taint tf (Var bp) = op_taint tn (Var bp) /\
   FLOOKUP gf idx = FLOOKUP G idx /\ op_taint tf (Var idx) = op_taint tn (Var idx)` by
    metis_tac[] >>
  `ptr_covers gf tf p s2 sz /\
   ptr_covers gf tf bp s2 (LENGTH vs * type_memory_size tv)` by
    (gvs[ptr_covers_def, array_loop_inv_def, eval_operand_def]) >>
  simp[] >> fs[array_entry_ready_def, eval_operand_def] >>
  conj_tac >> rpt strip_tac >> metis_tac[]
QED

Theorem for_array_round_entry_ptr:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride (Var bp)
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond_lbl st s0 G0 tn0 d name snapshot k es G tn s /\
  LENGTH vs < dimword (:256) /\ k < LENGTH vs /\
  snapshot.type = ArrayTV tv (Fixed n) /\ snapshot.value = ArrayV (SArrayV kvs) /\
  vs = array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs) /\ n = LENGTH vs /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var bp) arrsz) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  w2n arr_base + k * stride < dimword (:256) /\
  st.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\ ~ctx_has_dalloca ctx /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!x. not_fresh_at st x ==> not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) ==>
  ?gf tf s2.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 gf tf (OK s2) /\
    stmt_state_rel ctx func bc cx
      (es with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
        gas_obs := []|>) s2 /\
    ghost_inv d bc cx
      (es with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
        gas_obs := []|>) gf tf s2 /\
    ~s2.vs_halted /\ s2.vs_current_bb = sb0.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
    ptr_covers gf tf p s2 sz /\
    ptr_covers gf tf bp s2 (LENGTH vs * type_memory_size tv) /\
    lookup_var idx s2 = SOME (n2w k) /\ lookup_var bp s2 = SOME arr_base /\
    lookup_var p s2 = SOME dst /\ FLOOKUP gf idx = NONE /\
    op_taint tf (Var idx) = {} /\
    FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
      lookup_var x s2 = SOME v) /\
    (!x. not_fresh_at st x ==> FLOOKUP gf x = FLOOKUP G0 x /\
      op_taint tf (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  `not_local_ptr cenv es.scopes dv /\ idx <> dv /\ p <> dv /\ bp <> dv` by
    fs[array_for_code_def] >>
  `(!x. not_fresh_at st x ==> x <> dv) /\
   (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
       cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
       not_fresh_at sa x /\ x <> ov /\ x <> ep)` by metis_tac[] >>
  drule array_for_code_condition >> disch_tac >>
  drule_at (Pos (el 5)) for_array_unequal_header_ptr >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (qspec_then `PG` mp_tac) >>
  (impl_tac >- (simp[IgnAsm `vs = _`] >> metis_tac[])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ G tn s 0 Gh th (OK sh)` >>
  drule_all for_array_prepare_from_inv_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "control"
QED

Resume for_array_round_entry_ptr[control]:
  `(!x. not_fresh_at st x ==> not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
   (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
     not_fresh_at sa x /\ x <> ov /\ x <> ep)` by metis_tac[] >>
  drule_all for_array_prepared_control_ptr >> strip_tac >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 gf tf (OK s2)` by
    (drule_all gas_path_ptr_then >> simp[IgnAsm `vs = _`]) >>
  qexistsl_tac [`gf`, `tf`, `s2`] >>
  simp[IgnAsm `vs = _`, stmt_state_rel_gas_obs, ghost_inv_gas_obs] >>
  fs[array_entry_ready_def, IgnAsm `vs = _`] >>
  `es with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
      gas_obs := []|> =
   (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes)
      with gas_obs := []` by (Cases_on `es` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  rewrite_tac[stmt_state_rel_gas_obs, ghost_inv_gas_obs] >> simp[IgnAsm `vs = _`]
QED
Finalise for_array_round_entry_ptr

Theorem for_array_round_ptr:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride (Var bp)
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  stmt_frag_ptr d ctx PG func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
    (es with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
      gas_obs := []|>) /\
  stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = (bc',sb1) /\
  (!j ei G tn s. Inv j ei G tn s <=>
    for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
      cond_lbl st s0 G0 tn0 d name snapshot j ei G tn s) /\
  (!ei G tn s. Done ei G tn s <=>
    for_array_done_ptr ctx func cenv cx exit_lbl st s0 G0 tn0 d ei G tn s) /\
  supported_stmts tops bindings stmts /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty stmts = SOME env' /\
  iterator_unmodified (Array (Name aty name)) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  LENGTH vs < dimword (:256) /\ k < LENGTH vs /\
  snapshot.type = ArrayTV tv (Fixed n) /\ snapshot.value = ArrayV (SArrayV kvs) /\
  vs = array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs) /\ n = LENGTH vs /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var bp) arrsz) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  w2n arr_base + k * stride < dimword (:256) /\
  st.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\ ~ctx_has_dalloca ctx /\
  ~bc.ce_is_ctor /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!x. not_fresh_at st x ==> not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep /\
    x <> idx /\ x <> nv) /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  Inv k es G tn s /\
  gas_admissible (eval_for cx tv id stmts (DROP k vs)) (stmt_res_ok lctx) es ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (do push_scope_with_var id tv (EL k vs);
        finally (try (do eval_stmts cx stmts; return F od)
          handle_loop_exception) pop_scope od) (es,s,G,tn)
    (\res ee gf tf t. ?broke. res = INL broke /\
      (broke ==> Done ee gf tf t) /\ (~broke ==> Inv (SUC k) ee gf tf t))
    (\res ee gt r. ?ex. res = INR ex /\
      !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) (INR ex) gt r)
Proof
  strip_tac >>
  `for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond_lbl st s0 G0 tn0 d name snapshot k es G tn s` by metis_tac[] >>
  `!x. not_fresh_at st x ==> not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep` by
    metis_tac[] >>
  drule_all for_array_round_entry_ptr >> disch_then (qspec_then `PG` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `stmt_frag_ptr _ _ _ _ _ _ _ _ _ _ ei` >>
  `lookup_scopes id es.scopes = NONE /\ lookup_scopes name es.scopes = SOME snapshot` by
    fs[for_array_inv_ptr_def, array_loop_inv_def, IgnAsm `vs = _`] >>
  `gas_admissible (eval_stmts cx stmts)
    (stmt_res_ok (InLoop exit_lbl incr_lbl)) ei` by
    (drule_all for_range_body_admissible >> simp[Abbr `ei`, IgnAsm `vs = _`]) >>
  `bc.ce_return_buf = cenv.ce_return_buf` by
    (fs[Once array_for_code_def, IgnAsm `vs = _`] >>
     qpat_x_assum `bc with <|ce_vars := _; ce_dynarray_capacity := _; ce_var_type := _|> = cenv`
       (mp_tac o Q.AP_TERM `\ce:compile_env. ce.ce_return_buf`) >> simp[]) >>
  `!x z. bc.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sb0 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     simp[IgnAsm `vs = _`] >> metis_tac[]) >>
  drule_all for_array_callback_contract_ptr >> strip_tac >>
  suspend "outcome"
QED

Resume for_array_round_ptr[outcome]:
  qmatch_goalsub_abbrev_tac `gas_outcome_ptr _ _ _ _ _ _ Qround Rround` >>
  dxrule for_outcome_source_evidence_ptr >> disch_then assume_tac >>
  drule_then (qspecl_then [`k`, `Inv`, `Done`] mp_tac) (Q.INST
    [`Q'` |-> `\res ee gf tf t.
      (res = INL ARB \/ res = INR ContinueException \/ res = INR BreakException) /\
      ee.scopes <> [] /\
      (res = INR BreakException ==> Done (ee with scopes := TL ee.scopes) gf tf t) /\
      (res <> INR BreakException ==> Inv (SUC k) (ee with scopes := TL ee.scopes) gf tf t)`]
    for_outcome_zero_suffix_ptr) >>
  (impl_tac >- suspend "finish") >> disch_tac >>
  drule_at_then (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)
    (qspecl_then [`Rround`, `Qround`] mp_tac)
    (Q.INST [`Q'` |-> `Qround`, `R'` |-> `Rround`] for_body_cleanup_outcome_ptr) >>
  (impl_tac >- (simp[Abbr `ei`, IgnAsm `vs = _`] >> conj_tac
    >- (rpt gen_tac >> strip_tac >>
        fs[IgnAsm `vs = _`] >> qpat_x_assum `res = _` SUBST_ALL_TAC >>
        simp[Abbr `Qround`, IgnAsm `vs = _`] >> fs[IgnAsm `vs = _`] >> metis_tac[]) >>
    rpt gen_tac >> strip_tac >>
    drule for_body_exit_cleanup_ptr >> disch_then (qspec_then `TL ee.scopes` strip_assume_tac) >>
    simp[Abbr `Rround`, IgnAsm `vs = _`] >> gen_tac >>
    `ee with <|scopes := TL ee.scopes; gas_obs := tail|> =
     ee with <|gas_obs := tail; scopes := TL ee.scopes|>` by
      (Cases_on `ee` >> simp[]) >> asm_rewrite_tac[])) >>
  disch_tac >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (push_scope_with_var id tv (EL k vs)) (es,s,G,tn) [] (INL ())
    (ei with gas_obs := es.gas_obs) gf tf (OK s2)` by
    (simp[gas_marked_exec_ptr_def, Abbr `ei`, IgnAsm `vs = _`,
      push_scope_with_var_def, bind_def, push_scope_def, new_variable_def,
      return_def] >> Cases_on `es` >> simp[evaluation_state_fn_updates, IgnAsm `vs = _`]) >>
  rewrite_tac[ignore_bind_def] >> irule gas_outcome_ptr_bind_normal >>
  goal_assum (drule_at Any) >> simp[Abbr `ei`, IgnAsm `vs = _`] >>
  reverse conj_tac
  >- (qpat_x_assum `gas_outcome_ptr _ _ _ _ (finally _ _) _ _ _` mp_tac >>
      simp[ignore_bind_def, IgnAsm `vs = _`]) >>
  rpt strip_tac >> drule gas_exempt_cert_bind_unit >> simp[IgnAsm `vs = _`] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Resume for_array_round_ptr[finish]:
  rpt gen_tac >> strip_tac >> fs[IgnAsm `vs = _`] >>
  `!x. not_fresh_at st x ==> not_fresh_at sb0 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     simp[IgnAsm `vs = _`] >> metis_tac[]) >>
  `(!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
   (!x. not_fresh_at st x ==> FLOOKUP G' x = FLOOKUP G0 x /\
     op_taint tn' (Var x) = op_taint tn0 (Var x))` by metis_tac[] >>
  `lookup_var bp t = SOME arr_base /\ lookup_var p t = SOME dst /\
   FLOOKUP t.vs_allocas ainst.inst_id = SOME (w2n dst,sz)` by
    (fs[array_for_code_def, IgnAsm `vs = _`] >>
     `not_fresh_at sb0 bp /\ not_fresh_at sb0 p` by
       metis_tac[not_fresh_at_mono] >> metis_tac[]) >>
  `ret_pc_ok cenv st t` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s2`, `st`] >>
     simp[IgnAsm `vs = _`]) >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >> simp[Abbr `ei`, IgnAsm `vs = _`] >>
  disch_tac >>
  `(res = INL () ==> ~block_is_terminated sb1) /\
   (!r q. cenv.ce_return_buf = SOME (PtrVar (Var r) q) ==> not_fresh_at st r)` by
    metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`esk` |-> `es with gas_obs := obs`]
    for_array_callback_finish_ptr)) >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `res = INL () \/ res = INR ContinueException \/ res = INR BreakException` by
    (qpat_x_assum `stmt_lands _ _ res t` mp_tac >>
     simp[stmt_lands_def, IgnAsm `vs = _`] >> metis_tac[]) >>
  goal_assum (drule_at Any) >> simp[IgnAsm `vs = _`] >>
  Cases_on `res = INR BreakException` >> gvs[IgnAsm `vs = _`] >> metis_tac[]
QED
Finalise for_array_round_ptr
