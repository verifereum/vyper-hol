(* Dynamic pointer control uses the saved length register, not a fixed bound. *)
Theory forPtrDynArrayLoop
Ancestors forPtrArrayAssemble forPtrRounds whitelistForIterDynLoop
  forPtrDynArrayPrepare forPtrDynArrayFinish forPtrRangeCallback list fragGasPathPtr
  forPtrControl forPtrRangeTerminal forPtrArrayInvariant bodyPtrDefs
  venomState venomInst ptrDiscipline finite_map fragExec
  forPtrRangePrepare stmtSimForArrayLoop ghostPcTransportPtr stmtSimProps
  exprLoweringProps exprSimWordArgs compileEnv loweringStateRelDefs loweringPosts stmtFragPtr
  forPtrRangeRound forPtrRoundCleanup forPtrRangeSource forPtrSourceScopes
  gasSummaryComposePtr gasExemptCert vyperState vyperInterpreter gasOutcome
Libs monadsyntax

Theorem for_dynarray_header_path_ptr[local]:
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; Var lv] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label bod] []]|> /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var lv s = SOME (n2w n) /\
  op_taint tn (Var idx) = {} /\ FLOOKUP G idx = NONE /\
  op_taint tn (Var lv) = {} /\ FLOOKUP G lv = NONE ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))
    (OK (jump_to (if (n2w k : bytes32) = n2w n then exit else bod)
      (update_var dv (if (n2w k : bytes32) = n2w n then 1w else 0w) s)))
Proof
  strip_tac >> irule for_counter_test_path_ptr >> simp[] >>
  qexistsl_tac [`Var lv`, `idx`, `j1`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond;
       cs_current_insts := []; cs_next_id := j1 |>`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond;
       cs_current_insts := [mk_inst j1 EQ [Var idx; Var lv] [dv];
         mk_inst j2 JNZ [Var dv; Label exit; Label bod] []] |>`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond;
       cs_current_insts := [mk_inst j1 EQ [Var idx; Var lv] [dv]];
       cs_next_id := j2 |>`] >>
  simp[fn_has_code_def, emitted_blocks_def, eval_operand_def, op_prov_def]
QED

Theorem for_dynarray_terminal_ptr:
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; Var lv] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label bod] []]|> /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond st s0 G0 tn0 d name snapshot (LENGTH vs) es G tn s /\
  lookup_var lv s = SOME (n2w (LENGTH vs)) /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  ~ctx_has_dalloca ctx /\ not_local_ptr cenv es.scopes dv /\
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) ==>
  ?t gf tf.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 gf tf (OK t) /\
    for_array_done_ptr ctx func cenv cx exit st s0 G0 tn0 d
      (es with gas_obs := []) gf tf t
Proof
  strip_tac >> drule for_array_inv_header_ptr >> strip_tac >>
  `!q. cenv.ce_return_buf <> SOME (PtrVar (Var dv) q)` by metis_tac[] >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))
    (OK (jump_to exit (update_var dv 1w s)))` by
    (drule_all for_dynarray_header_path_ptr >> simp[]) >>
  drule_all for_header_exit_transport_ptr >>
  disch_then (qspec_then `exit` strip_assume_tac) >>
  drule_all for_header_exit_old_frame >>
  disch_then (qspec_then `exit` strip_assume_tac) >>
  qexistsl_tac [`jump_to exit (update_var dv 1w s)`,
    `DRESTRICT G (COMPL {dv})`, `tn with t_var := tn.t_var |+ (dv,{})`] >>
  simp[for_array_done_ptr_def, jump_to_def, update_var_def]
QED

Theorem for_dynarray_unequal_header_ptr:
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; Var lv] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label bod] []]|> /\
  LENGTH vs < dimword (:256) /\ k < LENGTH vs /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond st s0 G0 tn0 d name snapshot k es G tn s /\
  lookup_var lv s = SOME (n2w (LENGTH vs)) /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  ~ctx_has_dalloca ctx /\ not_local_ptr cenv es.scopes dv /\
  idx <> dv /\ p <> dv /\ bp <> dv /\ lv <> dv /\
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) ==>
  gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))
    (OK (jump_to bod (update_var dv 0w s))) /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    bod st s0 G0 tn0 d name snapshot k es
    (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))
    (jump_to bod (update_var dv 0w s)) /\
  lookup_var lv (jump_to bod (update_var dv 0w s)) = SOME (n2w (LENGTH vs)) /\
  FLOOKUP (DRESTRICT G (COMPL {dv})) lv = NONE /\
  op_taint (tn with t_var := tn.t_var |+ (dv,{})) (Var lv) = {}
Proof
  strip_tac >> drule for_array_inv_header_ptr >> strip_tac >>
  `(n2w k : bytes32) <> n2w (LENGTH vs)` by
    (simp[wordsTheory.n2w_11] >> simp[arithmeticTheory.LESS_MOD] >> decide_tac) >>
  conj_tac
  >- (drule_all for_dynarray_header_path_ptr >> simp[]) >>
  reverse conj_tac
  >- gvs[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
          FLOOKUP_DRESTRICT, op_taint_def] >>
  `!q. cenv.ce_return_buf <> SOME (PtrVar (Var dv) q)` by metis_tac[] >>
  `ghost_inv d cenv cx es (DRESTRICT G (COMPL {dv}))
    (tn with t_var := tn.t_var |+ (dv,{})) (update_var dv 0w s)` by
    (irule for_scalar_overwrite_ghost >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (update_var dv 0w s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  `ghost_inv d cenv cx es (DRESTRICT G (COMPL {dv}))
    (tn with t_var := tn.t_var |+ (dv,{}))
    (jump_to bod (update_var dv 0w s))` by
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

(* Lift the finite installation frame to the registers used by the round. *)
Theorem for_dynarray_prepared_control_ptr[local]:
  dynarray_for_code func cenv bc ty stmts id et tv stride (Var bp)
    p sz ainst idx dv ov tot ep nv lv cond exit bod incr
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    bod st s0 G0 tn0 d name snapshot k es G tn s /\
  st.cs_next_var <= sa.cs_next_var /\
  (!x. not_fresh_at st x ==> x <> ov /\ x <> tot /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  s2.vs_allocas = s.vs_allocas /\
  (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
    lookup_var x s2 = lookup_var x s /\ FLOOKUP gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) ==>
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
  `not_fresh_at sa idx /\ not_fresh_at sa bp /\ not_fresh_at sa p /\
   idx <> ov /\ idx <> tot /\ idx <> ep /\
   bp <> ov /\ bp <> tot /\ bp <> ep /\
   p <> ov /\ p <> tot /\ p <> ep` by
    fs[dynarray_for_code_def, ALL_DISTINCT] >>
  `!x. not_fresh_at st x ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  `lookup_var idx s2 = lookup_var idx s /\
   lookup_var bp s2 = lookup_var bp s /\ lookup_var p s2 = lookup_var p s /\
   FLOOKUP gf idx = FLOOKUP G idx /\ op_taint tf (Var idx) = op_taint tn (Var idx) /\
   FLOOKUP gf bp = FLOOKUP G bp /\ op_taint tf (Var bp) = op_taint tn (Var bp)` by
    metis_tac[] >>
  qhdtm_assum `for_array_inv_ptr`
    (strip_assume_tac o PURE_REWRITE_RULE [for_array_inv_ptr_def, array_loop_inv_def]) >>
  `ptr_covers gf tf bp s2 (LENGTH vs * type_memory_size tv)` by
    (fs[ptr_covers_def]) >>
  fs[eval_operand_def]
  >- (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s`, `st`] >> simp[] >>
      rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >> metis_tac[]
QED

Theorem for_dynarray_round_start_ptr[local]:
  dynarray_for_code func cenv bc ty stmts id et tv stride (Var bp)
    p sz ainst idx dv ov tot ep nv lv cond exit bod incr
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond st s0 G0 tn0 d name snapshot k es G tn s /\
  lookup_var lv s = SOME (n2w (LENGTH vs)) /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  LENGTH vs < dimword (:256) /\ k < LENGTH vs /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  (!es' H un u.
    for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
      bod st s0 G0 tn0 d name snapshot k es' H un u ==>
    ptr_covers H un bp u (32+(k+1)*stride) /\
    (!m. mem_agree_outside un.t_mem u.vs_memory m ==>
      val_in_memory tv (EL k vs) (w2n arr_base+32+k*stride) m)) /\
  w2n arr_base+32+k*stride < dimword (:256) /\
  st.cs_next_var <= sa.cs_next_var /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\ ~ctx_has_dalloca ctx /\
  lookup_block bod func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!x. not_fresh_at st x ==> x <> dv /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
    cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  not_fresh_at sa lv ==>
  ?gf tf s2.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 gf tf (OK s2) /\
    stmt_state_rel ctx func bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes) s2 /\
    ghost_inv d bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes) gf tf s2 /\
    ~s2.vs_halted /\ s2.vs_current_bb = bod /\
    s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    ptr_covers gf tf p s2 sz /\
    ptr_covers gf tf bp s2 (LENGTH vs * type_memory_size tv) /\
    lookup_var idx s2 = SOME (n2w k) /\ lookup_var bp s2 = SOME arr_base /\
    lookup_var p s2 = SOME dst /\ FLOOKUP gf idx = NONE /\ op_taint tf (Var idx) = {} /\
    FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    lookup_var lv s2 = SOME (n2w (LENGTH vs)) /\
    FLOOKUP gf lv = NONE /\ op_taint tf (Var lv) = {} /\
    ret_pc_ok cenv st s2 /\
    (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==> lookup_var x s2 = SOME v) /\
    (!x. not_fresh_at st x ==> FLOOKUP gf x = FLOOKUP G0 x /\
      op_taint tf (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  `not_local_ptr cenv es.scopes dv /\ idx <> dv /\ p <> dv /\ bp <> dv /\ lv <> dv /\
   lv <> ov /\ lv <> tot /\ lv <> ep` by fs[dynarray_for_code_def, ALL_DISTINCT] >>
  `!x. not_fresh_at st x ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  `lookup_block cond func.fn_blocks = SOME <|bb_label := cond;
    bb_instructions := [mk_inst j1 EQ [Var idx; Var lv] [dv];
      mk_inst j2 JNZ [Var dv; Label exit; Label bod] []]|>` by fs[dynarray_for_code_def] >>
  `(!x. not_fresh_at st x ==> x <> dv) /\
   (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
     cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x)` by metis_tac[] >>
  drule_all for_dynarray_unequal_header_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ G tn s 0 Gh th (OK sh)` >>
  `ptr_covers Gh th bp sh (32+(k+1)*stride) /\
   (!m. mem_agree_outside th.t_mem sh.vs_memory m ==>
     val_in_memory tv (EL k vs) (w2n arr_base+32+k*stride) m)` by metis_tac[] >>
  `!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
    cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep` by metis_tac[] >>
  drule_all for_dynarray_round_entry_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  suspend "frame"
QED
Resume for_dynarray_round_start_ptr[frame]:
  `(!x. not_fresh_at st x ==> x <> ov /\ x <> tot /\ x <> ep) /\
   (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x)` by
    metis_tac[] >>
  drule_all for_dynarray_prepared_control_ptr >> strip_tac >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 gf tf (OK s2)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  qexistsl_tac [`gf`, `tf`, `s2`] >> simp[]
QED
Finalise for_dynarray_round_start_ptr

Theorem for_dynarray_round_ptr:
  dynarray_for_code func cenv bc ty stmts id et tv stride (Var bp)
    p sz ainst idx dv ov tot ep nv lv cond exit bod incr
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  stmt_frag_ptr d ctx PG func cx (InLoop exit incr) RetQ bc
    (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts)
    (es with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
      gas_obs := []|>) /\
  stmts_env bc (InLoop exit incr) ty stmts sb0 = (bc',sb1) /\
  supported_stmts tops bindings stmts /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty stmts = SOME env' /\
  iterator_unmodified (Array (Name aty name)) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  LENGTH vs < dimword (:256) /\ k < LENGTH vs /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  (!es' H un u.
    for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
      bod st s0 G0 tn0 d name snapshot k es' H un u ==>
    ptr_covers H un bp u (32+(k+1)*stride) /\
    (!m. mem_agree_outside un.t_mem u.vs_memory m ==>
      val_in_memory tv (EL k vs) (w2n arr_base+32+k*stride) m)) /\
  w2n arr_base+32+k*stride < dimword (:256) /\
  st.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\ ~ctx_has_dalloca ctx /\ ~bc.ce_is_ctor /\
  lookup_block bod func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!x. not_fresh_at st x ==> x <> dv /\ x <> ov /\ x <> tot /\ x <> ep /\
    x <> idx /\ x <> nv) /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
    cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  not_fresh_at sa lv /\
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond st s0 G0 tn0 d name snapshot k es G tn s /\
  lookup_var lv s = SOME (n2w (LENGTH vs)) /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  gas_admissible (eval_for cx tv id stmts (MAP Value (DROP k vs))) (stmt_res_ok lctx) es ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (do push_scope_with_var id tv (EL k vs);
        finally (try (do eval_stmts cx stmts; return F od)
          handle_loop_exception) pop_scope od) (es,s,G,tn)
    (\res ee gf tf t. ?broke. res = INL broke /\
      (broke ==> for_array_done_ptr ctx func cenv cx exit st s0 G0 tn0 d ee gf tf t) /\
      (~broke ==> for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
        cond st s0 G0 tn0 d name snapshot (SUC k) ee gf tf t /\
        lookup_var lv t = SOME (n2w (LENGTH vs)) /\ FLOOKUP gf lv = NONE /\
        op_taint tf (Var lv) = {}))
    (\res ee gt r. ?ex. res = INR ex /\
      !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) (INR ex) gt r)
Proof
  strip_tac >>
  `!x. not_fresh_at st x ==> x <> dv /\ x <> ov /\ x <> tot /\ x <> ep` by
    metis_tac[] >>
  drule_all for_dynarray_round_start_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `stmt_frag_ptr _ _ _ _ _ _ _ _ _ _ ei` >>
  `lookup_scopes id es.scopes = NONE /\ lookup_scopes name es.scopes = SOME snapshot` by
    fs[for_array_inv_ptr_def, array_loop_inv_def] >>
  `gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr)) ei` by
    (drule_all for_range_body_admissible >> simp[Abbr `ei`]) >>
  `bc.ce_return_buf = cenv.ce_return_buf /\ bc.ce_return_pc = cenv.ce_return_pc /\
   sb0.cs_current_bb = bod /\ fn_has_code sb0 sb1 func /\
   local_ptrs_reserved bc sb0 /\ ~block_is_terminated sb0 /\ fn_inst_ids_distinct func` by
    (fs[dynarray_for_code_def] >>
     qpat_x_assum `bc with <|ce_vars := _; ce_dynarray_capacity := _; ce_var_type := _|> = cenv`
       mp_tac >> simp[compile_env_component_equality]) >>
  `(!x. not_fresh_at st x ==> not_fresh_at sb0 x) /\
   (!x z. bc.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sb0 x)` by
    (conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> metis_tac[not_fresh_at_mono]) >>
  `ret_pc_ok bc sb0 s2` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s2`, `st`] >> simp[]) >>
  `stmt_state_rel ctx func bc cx ei s2 /\ ghost_inv d bc cx ei gf tf s2` by
    (conj_tac
     >- (drule (iffRL stmt_state_rel_gas_obs) >>
         disch_then (qspec_then `[]` assume_tac) >>
         fs[Abbr `ei`, Excl "stmt_state_rel_gas_obs"]) >>
     drule (iffRL ghost_inv_gas_obs) >>
     disch_then (qspec_then `[]` assume_tac) >>
     fs[Abbr `ei`, Excl "ghost_inv_gas_obs"]) >>
  qpat_x_assum `stmt_frag_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_ptr_def] >>
  disch_then (qspecl_then [`sb0`, `sb1`, `s2`, `gf`, `tf`, `bc'`] mp_tac) >>
  simp[] >> strip_tac >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (push_scope_with_var id tv (EL k vs)) (es,s,G,tn) [] (INL ())
    (ei with gas_obs := es.gas_obs) gf tf (OK s2)` by
    (simp[gas_marked_exec_ptr_def, Abbr `ei`,
      push_scope_with_var_def, bind_def, push_scope_def, new_variable_def,
      return_def] >> Cases_on `es` >> simp[evaluation_state_fn_updates]) >>
  suspend "outcome"
QED
Resume for_dynarray_round_ptr[outcome]:
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_ptr_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (gvs[gas_summary_ptr_at_marked]
      >- suspend "callback_normal" >>
      suspend "callback_exit") >>
  suspend "callback_exempt"
QED
Resume for_dynarray_round_ptr[callback_normal]:
  qhdtm_assum `gas_marked_exec_ptr`
    (strip_assume_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
  `not_fresh_at sb0 idx /\ not_fresh_at sb0 bp /\ not_fresh_at sb0 p /\
   not_fresh_at sb0 lv` by
    (fs[dynarray_for_code_def] >> metis_tac[not_fresh_at_mono]) >>
  `lookup_var idx t = SOME (n2w k) /\ lookup_var bp t = SOME arr_base /\
   lookup_var p t = SOME dst /\ FLOOKUP G' idx = NONE /\
   op_taint tn' (Var idx) = {} /\ lookup_var lv t = SOME (n2w (LENGTH vs)) /\
   FLOOKUP G' lv = NONE /\ op_taint tn' (Var lv) = {} /\
   ptr_covers G' tn' bp t (LENGTH vs * type_memory_size tv)` by
    (fs[ptr_covers_def] >> metis_tac[]) >>
  `ret_pc_ok cenv st t` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s2`, `st`] >> simp[]) >>
  `(!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
   (!x. not_fresh_at st x ==> FLOOKUP G' x = FLOOKUP G0 x /\
     op_taint tn' (Var x) = op_taint tn0 (Var x))` by metis_tac[] >>
  qabbrev_tac `esk = es with gas_obs := gas_explicit left s2.vs_gas_readings` >>
  `eval_stmts cx stmts (esk with scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: esk.scopes) =
    (res, es_end with gas_obs := [])` by
    (qpat_x_assum `!tail. eval_stmts _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[Abbr `ei`, Abbr `esk`]) >>
  `lookup_scopes id esk.scopes = NONE /\ lookup_scopes name esk.scopes = SOME snapshot /\
   not_local_ptr bc (FEMPTY :: esk.scopes) p` by simp[Abbr `esk`] >>
  drule_all fresh_body_scope_shape >> strip_tac >>
  `cenv_top_ext cenv bc ((FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: esk.scopes)` by
    (`cenv_top_ext cenv bc (FEMPTY :: esk.scopes)` by
       (drule dynarray_for_code_scope_frame >>
        disch_then (qspec_then `esk.scopes` mp_tac) >> simp[]) >>
     qpat_x_assum `cenv_top_ext cenv bc _` mp_tac >>
     simp[cenv_top_ext_def] >> metis_tac[]) >>
  `st.cs_next_var <= sb0.cs_next_var /\
   (!r q. cenv.ce_return_buf = SOME (PtrVar (Var r) q) ==> not_fresh_at st r) /\
   (res = INL () ==> ~block_is_terminated sb1)` by simp[] >>
  `stmt_state_rel ctx func cenv'' cx (es_end with gas_obs := []) t` by
    simp[stmt_state_rel_gas_obs] >>
  `?fin gh th.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G' tn' t 0 gh th (OK fin) /\
    (res = INR BreakException ==>
      for_array_done_ptr ctx func cenv cx exit st s0 G0 tn0 d
        ((es_end with gas_obs := []) with scopes := rest) gh th fin) /\
    (res <> INR BreakException ==>
      for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
        cond st s0 G0 tn0 d name snapshot (SUC k)
        ((es_end with gas_obs := []) with scopes := rest) gh th fin /\
      lookup_var lv fin = SOME (n2w (LENGTH vs)) /\
      FLOOKUP gh lv = NONE /\ op_taint th (Var lv) = {})` by
    (irule for_dynarray_callback_finish_ptr >> simp[] >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >>
     goal_assum (drule_at (Pat `dynarray_for_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >>
     qexistsl_tac [`aty`, `bindings`, `bound`, `cenv''`, `elem`, `env`, `env'`, `ret_ty`, `tops`] >>
     fs[] >> metis_tac[]) >>
  `es_end.scopes = sc :: rest` by fs[] >>
  qpat_assum `gas_marked_exec_ptr _ _ _ (eval_stmts _ _) _ _ _ _ _ _ _`
    (mp_then Any mp_tac for_exec_zero_suffix_ptr) >>
  disch_then drule >> strip_tac >>
  qpat_assum `gas_marked_exec_ptr _ _ _ (eval_stmts _ _) _ _ _ _ _ _ _`
    (mp_then Any mp_tac for_body_cleanup_exec_ptr) >>
  simp[] >> strip_tac >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (ignore_bind (push_scope_with_var id tv (EL k vs))
      (finally (try (ignore_bind (eval_stmts cx stmts) (return F))
        handle_loop_exception) pop_scope))
    (es,s,G,tn) ([] ++ left)
    (case res of INL u => INL F | INR ex =>
      if ex = BreakException then INL T else
      if ex = ContinueException then INL F else INR ex)
    (es_end with scopes := rest) gh th (OK fin)` by
    (rewrite_tac[ignore_bind_def] >>
     irule gas_marked_exec_ptr_bind_normal >>
     goal_assum (drule_at Any) >> simp[Abbr `ei`] >>
     simp[GSYM ignore_bind_def]) >>
  fs[APPEND] >>
  qexists_tac `left` >> disj1_tac >>
  goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disj1_tac >>
  fs[stmt_lands_def] >> gvs[]
QED
Resume for_dynarray_round_ptr[callback_exit]:
  `es_end.scopes <> []` by
    (irule for_body_marked_scope_ptr >> goal_assum (drule_at Any) >>
     simp[Abbr `ei`]) >>
  Cases_on `es_end.scopes` >> fs[] >>
  rename1 `es_end.scopes = sc :: rest` >>
  drule for_body_exit_cleanup_ptr >>
  disch_then (qspec_then `rest` strip_assume_tac) >> gvs[] >>
  qpat_assum `gas_marked_exec_ptr _ _ _ (eval_stmts _ _) _ _ _ _ _ _ _`
    (mp_then Any mp_tac for_body_cleanup_exec_ptr) >> simp[] >> strip_tac >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (ignore_bind (push_scope_with_var id tv (EL k vs))
      (finally (try (ignore_bind (eval_stmts cx stmts) (return F))
        handle_loop_exception) pop_scope))
    (es,s,G,tn) ([] ++ left) (INR ex)
    (es_end with scopes := rest) G' tn' r` by
    (rewrite_tac[ignore_bind_def] >> irule gas_marked_exec_ptr_bind_normal >>
     goal_assum (drule_at Any) >> simp[Abbr `ei`] >>
     simp[GSYM ignore_bind_def]) >>
  fs[APPEND] >> qexists_tac `left` >> disj1_tac >>
  goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disj2_tac >> simp[]
QED
Resume for_dynarray_round_ptr[callback_exempt]:
  `ee.scopes <> []` by
    (irule for_body_exempt_scope >> goal_assum (drule_at Any) >>
     simp[Abbr `ei`]) >>
  Cases_on `ee.scopes` >> fs[] >> rename1 `ee.scopes = sc :: rest` >>
  qexists_tac `left` >> disj2_tac >>
  qexistsl_tac [`err`, `ee with scopes := rest`, `leaf`, `finish'`] >>
  irule for_round_exempt_cert_ptr >> simp[] >>
  goal_assum (drule_at (Pat `gas_exempt_cert _ _ _ _ _ _ _ _`)) >>
  simp[GSYM ignore_bind_def, Abbr `ei`] >>
  fs[] >> goal_assum (drule_at Any)
QED
Finalise for_dynarray_round_ptr
