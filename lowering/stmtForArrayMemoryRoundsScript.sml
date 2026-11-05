Theory stmtForArrayMemoryRounds
Ancestors
  stmtForArrayControlMemory stmtForArrayMemoryRoundSupport
  stmtSimForArrayLoop stmtSimProps exprLoweringProps bodyMemoryDefs loweringPosts compileEnv
  venomState allocaHistory fragGasMode fragGasPathMem finite_map list arithmetic

Definition array_round_frame_def:
  array_round_frame d func cenv caller orig s <=>
    return_buf_frame d cenv caller s /\ alloca_history func s /\
    orig.vs_alloca_next <= s.vs_alloca_next /\
    (!x w. not_fresh_at caller x /\ lookup_var x orig = SOME w ==>
      lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP orig.vs_allocas aid = SOME b ==>
      FLOOKUP s.vs_allocas aid = SOME b)
End

Definition array_round_inv_def:
  array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst cond caller orig k es s <=>
    array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
      ainst cond caller k es s /\
    array_round_frame d func cenv caller orig s
End

Definition array_round_done_def:
  array_round_done d ctx func cenv cx caller orig exit es s <=>
    s.vs_current_bb = exit /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    stmt_state_rel ctx func cenv cx es s /\ ret_pc_ok cenv caller s /\
    array_round_frame d func cenv caller orig s
End

Theorem array_round_frame_transport:
  array_round_frame d func cenv caller orig s /\
  alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  (!x w. not_fresh_at caller x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
    FLOOKUP t.vs_allocas aid = SOME b) ==>
  array_round_frame d func cenv caller orig t
Proof
  rw[array_round_frame_def]
  >- (irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `s`, `caller`] >> simp[]) >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem array_round_last:
  !d ctx func cenv cx P vs id idx saved_base base p dst sz ainst cond caller
   orig es s dv j1 j2 exit stmts_lbl.
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; Lit (n2w (LENGTH vs))] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label stmts_lbl] []]|> /\
  array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst cond caller orig (LENGTH vs) es s /\
  LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) /\
  (!x. not_fresh_at caller x ==> x <> dv) /\
  fn_inst_ids_distinct func ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      array_round_done d ctx func cenv cx caller orig exit
        (es with gas_obs := []) t
Proof
  rw[array_round_inv_def] >>
  `alloca_history func s` by fs[array_round_frame_def] >>
  drule array_condition_boundary_mem >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  rename1 `gas_path_mem ctx func s 0 (OK t)` >>
  qexists_tac `t` >> conj_tac
  >- simp[gas_marked_path_def] >>
  `array_round_frame d func cenv caller orig t` by
    (irule array_round_frame_transport >> simp[] >> qexists_tac `s` >> simp[] >>
     rpt strip_tac >> metis_tac[]) >>
  fs[array_round_done_def, array_loop_inv_def, state_rel_gas_obs]
QED

Theorem array_round_increment:
  !d ctx func cenv cx P vs id idx saved_base base p dst sz ainst cond caller
   orig k es s incr nv i1 i2 i3.
  lookup_block incr func.fn_blocks =
    SOME <|bb_label := incr; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond] []]|> /\
  array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst incr caller orig k es s /\ k < LENGTH vs /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes nv /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  (!x. not_fresh_at caller x ==> x <> idx /\ x <> nv) /\
  fn_inst_ids_distinct func ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
        ainst cond caller orig (SUC k) es t
Proof
  rw[array_round_inv_def] >>
  `alloca_history func s` by fs[array_round_frame_def] >>
  drule array_increment_boundary_mem >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  rename1 `gas_path_mem ctx func s 0 (OK t)` >>
  qexists_tac `t` >> simp[gas_marked_path_def, ADD1] >>
  irule array_round_frame_transport >> simp[] >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem array_round_break:
  stmt_lands (InLoop exit incr) sb (INR BreakException) s /\
  ~s.vs_halted /\ stmt_state_rel ctx func cenv cx es s /\
  ret_pc_ok cenv caller s /\ array_round_frame d func cenv caller orig s ==>
  array_round_done d ctx func cenv cx caller orig exit es s
Proof
  simp[stmt_lands_def, array_round_done_def]
QED

Theorem array_round_postbody_entry:
  !d ctx func cenv cx P vs id idx saved_base base p dst sz ainst caller
   orig k es s exit incr sb sj r.
  stmt_lands (InLoop exit incr) sb r s /\
  (r = INL () \/ r = INR ContinueException) /\ ~s.vs_halted /\
  (r = INL () ==> ~block_is_terminated sb) /\
  (~block_is_terminated sb ==>
    sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
    sj.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id JMP [Label incr] []] /\ fn_has_code sb sj func) /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst incr caller k es (jump_to incr s) /\
  array_round_frame d func cenv caller orig s ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
      ainst incr caller orig k es t
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `r = INL ()`
  >- (qexists_tac `jump_to incr s` >> conj_tac
      >- (fs[stmt_lands_def] >> simp[gas_marked_path_def] >>
          irule emit_jump_zero_path_mem >> simp[] >>
          qexistsl_tac [`sb`, `sj`] >> simp[]) >>
      simp[array_round_inv_def] >>
      fs[array_round_frame_def, return_buf_frame_jump_to, jump_to_def,
         lookup_var_def, alloca_history_def]) >>
  qexists_tac `s` >> conj_tac
  >- (simp[gas_marked_path_def] >> irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  fs[stmt_lands_def, array_round_inv_def, array_loop_inv_def,
     stmt_state_rel_jump_to, ret_pc_ok_jump_to, jump_to_def,
     eval_operand_def, lookup_var_def]
QED
