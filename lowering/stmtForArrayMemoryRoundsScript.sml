Theory stmtForArrayMemoryRounds
Ancestors
  stmtForArrayControlMemory stmtForArrayMemoryRoundSupport
  stmtSimForArrayLoop stmtSimProps exprLoweringProps bodyMemoryDefs loweringPosts compileEnv
  venomState allocaHistory fragGasMode fragGasPathMem finite_map list arithmetic
  stmtForArrayMemoryCopy stmtForArrayMemoryBodyEntry rich_list emitHelper venomInst
  bodyDeclMemoryCounted stmtLowering

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

Theorem array_round_live:
  !d ctx func cenv cx P vs id idx saved_base base p dst sz ainst cond caller
   orig k es s dv j1 j2 exit stmts_lbl.
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; Lit (n2w (LENGTH vs))] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label stmts_lbl] []]|> /\
  array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst cond caller orig k es s /\ k < LENGTH vs /\
  LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) /\
  (!x. not_fresh_at caller x ==> x <> dv) /\
  fn_inst_ids_distinct func ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
        ainst stmts_lbl caller orig k es t
Proof
  rw[array_round_inv_def] >>
  `alloca_history func s` by fs[array_round_frame_def] >>
  drule array_condition_boundary_mem >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  rename1 `gas_path_mem ctx func s 0 (OK t)` >>
  qexists_tac `t` >> simp[gas_marked_path_def] >>
  irule array_round_frame_transport >> simp[] >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem array_iter_copy_no_gas[local]:
  compile_iter_elem_copy ce src dst stride LocMemory F ty ty sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Cases_on `is_word_type ty`
  >- (gvs[compile_iter_elem_copy_def, emit_op_def, emit_void_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
      strip_tac >> gvs[emitted_insts_def, mk_inst_def] >>
      rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  simp[compile_iter_elem_copy_def] >> strip_tac >>
  irule compile_store_memory_same_no_gas >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem array_round_copy_entry:
  !ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
   idx saved_base arr_base k stride ov ep j3 j4 bb.
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  w2n arr_base + k * stride + stride <= s.vs_alloca_next /\
  w2n dst + stride <= s.vs_alloca_next /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> x <> ov) /\ not_fresh_at sa ep /\ not_fresh_at sa p /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0 /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  alloca_history func s /\ alloca_inv s ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\ alloca_history func t /\
    stmt_state_rel ctx func bc cx
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
          :: es.scopes) t /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
      lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all array_for_body_entry_run >>
  disch_then (qspecl_then [`j3`, `j4`] strip_assume_tac) >>
  `run_inst_seq_mem_ok sb0.cs_current_insts s` by
    (`!x. x = ep \/ x = p ==> not_fresh_at sa x` by metis_tac[] >>
     drule_all array_body_prefix_mem_ok >>
     disch_then (qspecl_then [`j4`, `j3`] mp_tac) >> simp[]) >>
  `run_inst_seq sb0.cs_current_insts s = OK t` by gvs[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    sb0.cs_current_insts` by simp[mk_inst_def, is_terminator_def] >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb0)` by
    (irule array_iter_copy_no_gas >> goal_assum (drule_at Any)) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) sb0.cs_current_insts) = 0` by
    (simp[mk_inst_def] >> fs[EVERY_FILTER, FILTER_EQ_NIL, EVERY_MEM]) >>
  `isPREFIX sb0.cs_current_insts (DROP s.vs_inst_idx bb.bb_instructions)`
    by (qpat_assum `s.vs_inst_idx = 0` (fn th => rewrite_tac[th, DROP_0]) >>
        first_assum ACCEPT_TAC) >>
  drule_all array_prefix_counted_history >> simp[] >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb0.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx] >>
  fs[venom_state_component_equality, lookup_var_def]
QED
