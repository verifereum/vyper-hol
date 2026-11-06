(* Exhaustion executes only the equal header and exit jump. *)
Theory forPtrRangeTerminal
Ancestors forPtrRangePrepare forPtrRangeBackedge stmtSimForParts stmtFragPtr
  exprLoweringProps bodyPtrDefs venomState ptrDiscipline finite_map
  stmtSimForLoop compileEnv loweringPosts exprSimWordArgs

Theorem for_header_exit_transport_ptr:
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  not_local_ptr cenv es.scopes dv /\
  (!sz. cenv.ce_return_buf <> SOME (PtrVar (Var dv) sz)) ==>
  stmt_state_rel ctx func cenv cx (es with gas_obs := [])
    (jump_to exit_lbl (update_var dv 1w s)) /\
  ghost_inv d cenv cx (es with gas_obs := [])
    (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))
    (jump_to exit_lbl (update_var dv 1w s))
Proof
  strip_tac >> rewrite_tac[stmt_state_rel_gas_obs, ghost_inv_gas_obs] >>
  conj_tac
  >- (rewrite_tac[stmt_state_rel_jump_to] >>
      irule stmt_state_rel_update_var >> simp[]) >>
  rewrite_tac[jump_to_def, ghost_inv_jump_to] >>
  irule for_scalar_overwrite_ghost >> simp[]
QED

Theorem for_header_exit_old_frame:
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x s = SOME v) /\
  (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x (jump_to lbl (update_var dv 1w s)) = SOME v) /\
  (!x. not_fresh_at st x ==>
    FLOOKUP (DRESTRICT G (COMPL {dv})) x = FLOOKUP G0 x /\
    op_taint (tn with t_var := tn.t_var |+ (dv,{})) (Var x) =
      op_taint tn0 (Var x))
Proof
  strip_tac >> conj_tac >> rpt strip_tac >>
  `x <> dv` by metis_tac[] >>
  simp[lookup_var_def, jump_to_def, update_var_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
  fs[lookup_var_def, op_taint_def] >> metis_tac[]
QED

Theorem for_range_terminal_ptr:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  n1 <= n2 /\ s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  lookup_var cv s = SOME (i2w (n1 + &Num (n2 - n1))) /\
  lookup_var ev s = SOME (i2w n2) /\
  FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
  (!r q. cenv.ce_return_buf = SOME (PtrVar (Var r) q) ==> not_fresh_at st r) /\
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x s = SOME v) /\
  (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  ?t gf tf.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 gf tf (OK t) /\
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx (es with gas_obs := []) t /\
    ghost_inv d cenv cx (es with gas_obs := []) gf tf t /\
    (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
      lookup_var x t = SOME v) /\
    (!x. not_fresh_at st x ==> FLOOKUP gf x = FLOOKUP G0 x /\
      op_taint tf (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  `lookup_var cv s = SOME (i2w n2)` by metis_tac[i2w_counter_end] >>
  `not_local_ptr cenv es.scopes dv` by fs[for_code_def] >>
  `!q. cenv.ce_return_buf <> SOME (PtrVar (Var dv) q)` by metis_tac[] >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0
     (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))
     (OK (jump_to exit_lbl (update_var dv 1w s)))` by
    (`lookup_block cond_lbl func.fn_blocks =
       SOME <| bb_label := cond_lbl;
         bb_instructions := [mk_inst j1 EQ [Var cv; Var ev] [dv];
           mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |>` by
       fs[for_code_def] >>
     drule_all (SRULE [op_prov_def] for_header_test_path_ptr) >>
     simp[i2w_counter_end]) >>
  drule_all for_header_exit_transport_ptr >>
  disch_then (qspec_then `exit_lbl` strip_assume_tac) >>
  drule_all for_header_exit_old_frame >>
  disch_then (qspec_then `exit_lbl` strip_assume_tac) >>
  qexistsl_tac [`jump_to exit_lbl (update_var dv 1w s)`,
    `DRESTRICT G (COMPL {dv})`, `tn with t_var := tn.t_var |+ (dv,{})`] >>
  simp[jump_to_def, update_var_def]
QED
