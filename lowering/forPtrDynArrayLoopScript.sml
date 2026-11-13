(* Dynamic pointer control uses the saved length register, not a fixed bound. *)
Theory forPtrDynArrayLoop
Ancestors forPtrArrayAssemble forPtrRounds whitelistForIterDynLoop
  forPtrDynArrayPrepare forPtrDynArrayFinish
  forPtrControl forPtrRangeTerminal forPtrArrayInvariant bodyPtrDefs
  venomState venomInst ptrDiscipline finite_map fragExec
  forPtrRangePrepare stmtSimForArrayLoop ghostPcTransportPtr stmtSimProps
  exprLoweringProps compileEnv loweringStateRelDefs loweringPosts stmtFragPtr

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
