(* Finite frame trace for the allocation-identity collision witness. *)
Theory concretizePtrCollisionReach
Ancestors concretizePtrCollision contextRawReachable unitMemInv venomExecSemantics
  venomInst list ptrDiscipline contextCodegenRel
Libs wordsLib

Datatype:
  collision_config = <| cc_stack : call_frame list;
    cc_params : (num # num) option list;
    cc_prov : (string, num # num) fmap;
    cc_taint : taint;
    cc_fn : ir_function;
    cc_inst : instruction;
    cc_state : venom_state |>
End

Definition collision_config_at_def:
  collision_config_at q stk PG G tn fn inst s <=>
    stk = q.cc_stack /\ PG = q.cc_params /\ G = q.cc_prov /\
    tn = q.cc_taint /\ fn = q.cc_fn /\ inst = q.cc_inst /\ s = q.cc_state
End

Definition collision_rc0_def:
  collision_rc0 = <| cc_stack := []; cc_params := []; cc_prov := FEMPTY;
    cc_taint := entry_taint; cc_fn := collision_main;
    cc_inst := mk_inst 1 ALLOCA [Lit (32w:256 word)] ["p"];
    cc_state := collision_start |>
End

(* post is the primitive step result, before instruction-index advancement. *)
Definition collision_rc_next_def:
  collision_rc_next q post inst = q with
    <| cc_prov := step_prov q.cc_params q.cc_prov q.cc_inst post;
       cc_taint := step_taint q.cc_inst q.cc_state post q.cc_taint;
       cc_inst := inst;
       cc_state := post with vs_inst_idx := SUC q.cc_state.vs_inst_idx |>
End

Definition collision_rc1_def:
  collision_rc1 = collision_rc_next collision_rc0 collision_raw_allocated
    (mk_inst 2 MSTORE [Var "p"; Lit (0w:256 word)] [])
End

Definition collision_rc2_def:
  collision_rc2 = collision_rc_next collision_rc1
    (collision_raw_call_a with vs_inst_idx := 1)
    (mk_inst 3 INVOKE [Label "a"] [])
End

Definition collision_rc_call_def:
  collision_rc_call q fn s inst =
    <| cc_stack := <| cf_fn := q.cc_fn; cf_inst := q.cc_inst;
         cf_state := q.cc_state; cf_params := q.cc_params;
         cf_prov := q.cc_prov; cf_tvar := q.cc_taint.t_var |> :: q.cc_stack;
       cc_params := [];
       cc_prov := FEMPTY;
       cc_taint := q.cc_taint with t_var := FEMPTY;
       cc_fn := fn; cc_inst := inst; cc_state := s |>
End

Definition collision_rc3_def:
  collision_rc3 = collision_rc_call collision_rc2 collision_a collision_raw_a_entry
    (mk_inst 106 RETPC_PARAM [Lit (0w:256 word)] ["a_rpc"])
End

Definition collision_rc4_def:
  collision_rc4 = collision_rc_next collision_rc3 collision_raw_a_rpc
    (mk_inst 100 ALLOCA [Lit (32w:256 word)] ["a_p"])
End

Definition collision_rc5_def:
  collision_rc5 = collision_rc_next collision_rc4 collision_raw_a_allocated
    (mk_inst 101 MSTORE [Var "a_p"; Lit (0w:256 word)] [])
End

Definition collision_rc6_def:
  collision_rc6 = collision_rc_next collision_rc5 collision_raw_a_stored
    (mk_inst 102 RET [Var "a_rpc"] [])
End

Definition collision_rc_ret_def:
  collision_rc_ret q s inst =
    q with <| cc_stack := TL q.cc_stack;
      cc_params := (HD q.cc_stack).cf_params;
      cc_prov := DRESTRICT (HD q.cc_stack).cf_prov
        (COMPL (set (HD q.cc_stack).cf_inst.inst_outputs));
      cc_taint := q.cc_taint with t_var :=
        DRESTRICT (HD q.cc_stack).cf_tvar
          (COMPL (set (HD q.cc_stack).cf_inst.inst_outputs));
      cc_fn := (HD q.cc_stack).cf_fn; cc_inst := inst; cc_state := s |>
End

Definition collision_rc7_def:
  collision_rc7 = collision_rc_ret collision_rc6 collision_raw_call_b
    (mk_inst 4 INVOKE [Label "b"] [])
End

Definition collision_rc8_def:
  collision_rc8 = collision_rc_call collision_rc7 collision_b collision_raw_b_entry
    (mk_inst 107 RETPC_PARAM [Lit (0w:256 word)] ["b_rpc"])
End

Definition collision_rc9_def:
  collision_rc9 = collision_rc_next collision_rc8 collision_raw_b_rpc
    (mk_inst 100 ALLOCA [Lit (64w:256 word)] ["b_p"])
End

Definition collision_rc10_def:
  collision_rc10 = collision_rc_next collision_rc9 collision_raw_b_allocated
    (mk_inst 103 ADD [Var "b_p"; Lit (32w:256 word)] ["b_q"])
End

Definition collision_rc11_def:
  collision_rc11 = collision_rc_next collision_rc10 collision_raw_b_added
    (mk_inst 104 MSTORE [Var "b_q"; Lit (1w:256 word)] [])
End

Definition collision_rc12_def:
  collision_rc12 = collision_rc_next collision_rc11 collision_raw_b_stored
    (mk_inst 105 RET [Var "b_rpc"] [])
End

Definition collision_rc13_def:
  collision_rc13 = collision_rc_ret collision_rc12 collision_raw_load
    (mk_inst 5 MLOAD [Var "p"] ["x"])
End

Definition collision_rc14_def:
  collision_rc14 = collision_rc_next collision_rc13
    (collision_raw_branch with vs_inst_idx := 4)
    (mk_inst 6 JNZ [Var "x"; Label "bad"; Label "exit"] [])
End

Definition collision_rc15_def:
  collision_rc15 = collision_rc14 with
    <| cc_prov := entry_prov collision_main collision_exit_entry collision_rc14.cc_prov;
       cc_taint := entry_taint_vars collision_main collision_exit_entry collision_rc14.cc_taint;
       cc_inst := mk_inst 9 STOP [] []; cc_state := collision_exit_entry |>
End

Definition collision_raw_configs_def:
  collision_raw_configs =
    [collision_rc0; collision_rc1; collision_rc2; collision_rc3;
     collision_rc4; collision_rc5; collision_rc6; collision_rc7;
     collision_rc8; collision_rc9; collision_rc10; collision_rc11;
     collision_rc12; collision_rc13; collision_rc14; collision_rc15]
End

Definition collision_raw_envelope_def:
  collision_raw_envelope stk PG G tn fn inst s <=>
    ?q. MEM q collision_raw_configs /\
      collision_config_at q stk PG G tn fn inst s
End

Theorem collision_source_entry:
  collision_ctx.ctx_entry = SOME "main" /\
  lookup_function "main" collision_ctx.ctx_functions = SOME collision_main /\
  fn_entry_label collision_main = SOME "main" /\
  enters_block collision_main
    (collision_start with <| vs_prev_bb := NONE; vs_current_bb := "main";
                            vs_inst_idx := 0 |>) collision_start /\
  active_inst collision_main (mk_inst 1 ALLOCA [Lit (32w:256 word)] ["p"])
    collision_start
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac
  >- (rewrite_tac[contextCodegenRelTheory.enters_block_def] >>
      qexistsl [`collision_main_bb`, `collision_start`] >> EVAL_TAC) >>
  rewrite_tac[contextCodegenRelTheory.active_inst_def] >>
  qexists_tac `collision_main_bb` >> EVAL_TAC
QED

Theorem collision_rc_states:
  collision_rc0.cc_state = collision_start /\
  collision_rc1.cc_state = (collision_raw_allocated with vs_inst_idx := 1) /\
  collision_rc2.cc_state = collision_raw_call_a /\
  collision_rc3.cc_state = collision_raw_a_entry /\
  collision_rc4.cc_state = (collision_raw_a_rpc with vs_inst_idx := 1) /\
  collision_rc5.cc_state = (collision_raw_a_allocated with vs_inst_idx := 2) /\
  collision_rc6.cc_state = (collision_raw_a_stored with vs_inst_idx := 3) /\
  collision_rc7.cc_state = collision_raw_call_b /\
  collision_rc8.cc_state = collision_raw_b_entry /\
  collision_rc9.cc_state = (collision_raw_b_rpc with vs_inst_idx := 1) /\
  collision_rc10.cc_state = (collision_raw_b_allocated with vs_inst_idx := 2) /\
  collision_rc11.cc_state = (collision_raw_b_added with vs_inst_idx := 3) /\
  collision_rc12.cc_state = (collision_raw_b_stored with vs_inst_idx := 4) /\
  collision_rc13.cc_state = collision_raw_load /\
  collision_rc14.cc_state = collision_raw_branch /\
  collision_rc15.cc_state = collision_exit_entry
Proof
  EVAL_TAC
QED

Theorem collision_rc_functions:
  collision_rc0.cc_fn = collision_main /\
  collision_rc1.cc_fn = collision_main /\
  collision_rc2.cc_fn = collision_main /\
  collision_rc3.cc_fn = collision_a /\
  collision_rc4.cc_fn = collision_a /\
  collision_rc5.cc_fn = collision_a /\
  collision_rc6.cc_fn = collision_a /\
  collision_rc7.cc_fn = collision_main /\
  collision_rc8.cc_fn = collision_b /\
  collision_rc9.cc_fn = collision_b /\
  collision_rc10.cc_fn = collision_b /\
  collision_rc11.cc_fn = collision_b /\
  collision_rc12.cc_fn = collision_b /\
  collision_rc13.cc_fn = collision_main /\
  collision_rc14.cc_fn = collision_main /\
  collision_rc15.cc_fn = collision_main
Proof
  EVAL_TAC
QED

Theorem collision_active_main:
  active_inst collision_main inst s <=>
    (s.vs_current_bb = "main" /\ s.vs_inst_idx < 6 /\
     EL s.vs_inst_idx collision_main_bb.bb_instructions = inst) \/
    (s.vs_current_bb = "bad" /\ s.vs_inst_idx < 2 /\
     EL s.vs_inst_idx
       [mk_inst 7 MLOAD [Lit (1024w:256 word)] ["bad_x"]; mk_inst 8 STOP [] []] = inst) \/
    (s.vs_current_bb = "exit" /\ s.vs_inst_idx = 0 /\ inst = mk_inst 9 STOP [] [])
Proof
  simp[contextCodegenRelTheory.active_inst_def, collision_main_def,
    collision_main_bb_def, venomInstTheory.mk_raw_function_def,
    LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  eq_tac >> rpt strip_tac >> gvs[]
QED

Theorem collision_active_a:
  active_inst collision_a inst s <=>
    s.vs_current_bb = "a" /\ s.vs_inst_idx < 4 /\
    EL s.vs_inst_idx collision_raw_a_bb.bb_instructions = inst
Proof
  simp[contextCodegenRelTheory.active_inst_def, collision_a_def,
    collision_raw_a_bb_def, venomInstTheory.mk_raw_function_def]
QED

Theorem collision_active_b:
  active_inst collision_b inst s <=>
    s.vs_current_bb = "b" /\ s.vs_inst_idx < 5 /\
    EL s.vs_inst_idx collision_raw_b_bb.bb_instructions = inst
Proof
  simp[contextCodegenRelTheory.active_inst_def, collision_b_def,
    collision_raw_b_bb_def, venomInstTheory.mk_raw_function_def]
QED

Theorem collision_config_next:
  collision_config_at q stk PG G tn fn inst s ==>
  collision_config_at (collision_rc_next q post inst') stk PG
    (step_prov PG G inst post) (step_taint inst s post tn) fn inst'
    (post with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[collision_config_at_def, collision_rc_next_def] >> rpt strip_tac >> gvs[]
QED

Theorem collision_envelope_initial:
  collision_raw_envelope [] [] FEMPTY entry_taint collision_main
    (mk_inst 1 ALLOCA [Lit (32w:256 word)] ["p"]) collision_start
Proof
  rewrite_tac[collision_raw_envelope_def] >>
  qexists_tac `collision_rc0` >>
  simp[collision_raw_configs_def, collision_config_at_def, collision_rc0_def]
QED

Theorem collision_rc_instructions:
  collision_rc0.cc_inst = mk_inst 1 ALLOCA [Lit (32w:256 word)] ["p"] /\
  collision_rc1.cc_inst = mk_inst 2 MSTORE [Var "p"; Lit (0w:256 word)] [] /\
  collision_rc2.cc_inst = mk_inst 3 INVOKE [Label "a"] [] /\
  collision_rc3.cc_inst = mk_inst 106 RETPC_PARAM [Lit (0w:256 word)] ["a_rpc"] /\
  collision_rc4.cc_inst = mk_inst 100 ALLOCA [Lit (32w:256 word)] ["a_p"] /\
  collision_rc5.cc_inst = mk_inst 101 MSTORE [Var "a_p"; Lit (0w:256 word)] [] /\
  collision_rc6.cc_inst = mk_inst 102 RET [Var "a_rpc"] [] /\
  collision_rc7.cc_inst = mk_inst 4 INVOKE [Label "b"] [] /\
  collision_rc8.cc_inst = mk_inst 107 RETPC_PARAM [Lit (0w:256 word)] ["b_rpc"] /\
  collision_rc9.cc_inst = mk_inst 100 ALLOCA [Lit (64w:256 word)] ["b_p"] /\
  collision_rc10.cc_inst = mk_inst 103 ADD [Var "b_p"; Lit (32w:256 word)] ["b_q"] /\
  collision_rc11.cc_inst = mk_inst 104 MSTORE [Var "b_q"; Lit (1w:256 word)] [] /\
  collision_rc12.cc_inst = mk_inst 105 RET [Var "b_rpc"] [] /\
  collision_rc13.cc_inst = mk_inst 5 MLOAD [Var "p"] ["x"] /\
  collision_rc14.cc_inst = mk_inst 6 JNZ [Var "x"; Label "bad"; Label "exit"] [] /\
  collision_rc15.cc_inst = mk_inst 9 STOP [] []
Proof
  EVAL_TAC
QED

Definition collision_next_edges_def:
  collision_next_edges =
    [(collision_rc0, collision_raw_allocated, collision_rc1);
     (collision_rc1, collision_raw_call_a with vs_inst_idx := 1, collision_rc2);
     (collision_rc3, collision_raw_a_rpc, collision_rc4);
     (collision_rc4, collision_raw_a_allocated, collision_rc5);
     (collision_rc5, collision_raw_a_stored, collision_rc6);
     (collision_rc8, collision_raw_b_rpc, collision_rc9);
     (collision_rc9, collision_raw_b_allocated, collision_rc10);
     (collision_rc10, collision_raw_b_added, collision_rc11);
     (collision_rc11, collision_raw_b_stored, collision_rc12);
     (collision_rc13, collision_raw_branch with vs_inst_idx := 4, collision_rc14)]
End

Theorem collision_next_edge_configs:
  MEM (q, post, q') collision_next_edges ==>
  q' = collision_rc_next q post q'.cc_inst
Proof
  simp[collision_next_edges_def] >> rpt strip_tac >>
  gvs[collision_rc_instructions] >>
  simp[collision_rc1_def, collision_rc2_def, collision_rc4_def,
    collision_rc5_def, collision_rc6_def, collision_rc9_def, collision_rc10_def,
    collision_rc11_def, collision_rc12_def, collision_rc14_def]
QED

Theorem collision_next_edge_steps:
  MEM (q, post, q') collision_next_edges ==>
  !fuel. step_inst fuel collision_ctx q.cc_inst q.cc_state = OK post
Proof
  simp[collision_next_edges_def] >> rpt strip_tac >>
  gvs[collision_rc_instructions, collision_rc_states] >>
  once_rewrite_tac[step_inst_def] >>
  simp[venomInstTheory.mk_inst_def,
    SRULE [venomInstTheory.mk_inst_def] collision_initial_allocations,
    SRULE [venomInstTheory.mk_inst_def] collision_initial_stores,
    SRULE [venomInstTheory.mk_inst_def] collision_raw_a_steps,
    SRULE [venomInstTheory.mk_inst_def] collision_raw_b_steps,
    SRULE [venomInstTheory.mk_inst_def] collision_loads_diverge]
QED

Theorem collision_raw_rows_memory:
  EVERY (\q. raw_mem_ok collision_ctx q.cc_fn q.cc_inst q.cc_state)
    collision_raw_configs
Proof
  simp[collision_raw_configs_def, collision_rc_functions,
    collision_rc_instructions, collision_rc_states] >> EVAL_TAC
QED

Theorem collision_raw_rows_active:
  EVERY (\q. active_inst q.cc_fn q.cc_inst q.cc_state) collision_raw_configs
Proof
  simp[collision_raw_configs_def, collision_rc_functions,
    collision_rc_instructions, collision_rc_states,
    collision_active_main, collision_active_a, collision_active_b] >> EVAL_TAC
QED

Theorem collision_source_entry_inv:
  collision_ctx.ctx_entry = SOME name /\
  lookup_function name collision_ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (collision_start with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                            vs_inst_idx := 0 |>) s /\ active_inst fn inst s ==>
  collision_config_at collision_rc0 [] [] FEMPTY entry_taint fn inst s
Proof
  simp[CONJUNCT1 collision_source_entry] >> rpt strip_tac >>
  gvs[cj 2 collision_source_entry, cj 3 collision_source_entry] >>
  fs[contextCodegenRelTheory.enters_block_def] >>
  gvs[collision_main_def, venomInstTheory.mk_raw_function_def,
    lookup_block_def, FIND_thm, collision_start_def,
    venomStateTheory.init_venom_state_def, venomExecSemanticsTheory.eval_phis_def,
    venomExecSemanticsTheory.phi_prefix_length_def,
    venomInstTheory.mk_inst_def, collision_active_main] >>
  simp[collision_config_at_def, collision_rc0_def, collision_start_def,
    venomStateTheory.init_venom_state_def, venomInstTheory.mk_inst_def,
    collision_main_def, collision_main_bb_def, mk_raw_function_def]
QED

Theorem collision_next_edge_total:
  MEM q collision_raw_configs /\ ~is_terminator q.cc_inst.inst_opcode /\
  q.cc_inst.inst_opcode <> INVOKE ==>
  ?post q'. MEM (q,post,q') collision_next_edges
Proof
  simp[collision_raw_configs_def, collision_next_edges_def,
    collision_rc_instructions, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  gvs[collision_rc_instructions, mk_inst_def, is_terminator_def] >> metis_tac[]
QED

Theorem collision_next_edge_target:
  MEM (q,post,q') collision_next_edges ==>
  q'.cc_fn = q.cc_fn /\
  q'.cc_state = (post with vs_inst_idx := SUC q.cc_state.vs_inst_idx) /\
  (!inst. active_inst q.cc_fn inst
      (post with vs_inst_idx := SUC q.cc_state.vs_inst_idx) <=> inst = q'.cc_inst)
Proof
  simp[collision_next_edges_def] >> rpt strip_tac >> gvs[] >>
  simp[collision_rc_functions, collision_rc_states, collision_rc_instructions,
    collision_active_main, collision_active_a, collision_active_b] >>
  EVAL_TAC >> simp[]
QED

Theorem collision_next_edge_members:
  MEM (q,post,q') collision_next_edges ==>
  MEM q collision_raw_configs /\ MEM q' collision_raw_configs
Proof
  simp[collision_next_edges_def, collision_raw_configs_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem collision_envelope_next:
  collision_raw_envelope stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel collision_ctx inst s = OK s' /\
  active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  collision_raw_envelope stk PG (step_prov PG G inst s')
    (step_taint inst s s' tn) fn inst'
    (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >> fs[collision_raw_envelope_def] >>
  gvs[collision_config_at_def] >>
  drule_all collision_next_edge_total >>
  disch_then (qx_choose_then `post` (qx_choose_then `qnext` strip_assume_tac)) >>
  drule collision_next_edge_steps >>
  disch_then (qspec_then `fuel` assume_tac) >> gvs[] >>
  drule collision_next_edge_target >> strip_tac >> gvs[] >>
  rewrite_tac[collision_raw_envelope_def] >> qexists_tac `qnext` >>
  conj_tac >- metis_tac[collision_next_edge_members] >>
  drule collision_next_edge_configs >>
  disch_then (fn th => once_rewrite_tac[th]) >>
  simp[collision_config_at_def, collision_rc_next_def]
QED

Theorem collision_envelope_memory:
  collision_raw_envelope stk PG G tn fn inst s ==> raw_mem_ok collision_ctx fn inst s
Proof
  simp[collision_raw_envelope_def] >> rpt strip_tac >>
  mp_tac collision_raw_rows_memory >> simp[EVERY_MEM] >>
  disch_then drule >> gvs[collision_config_at_def]
QED

Theorem collision_envelope_active:
  collision_raw_envelope stk PG G tn fn inst s ==> active_inst fn inst s
Proof
  simp[collision_raw_envelope_def] >> rpt strip_tac >>
  mp_tac collision_raw_rows_active >> simp[EVERY_MEM] >>
  disch_then drule >> gvs[collision_config_at_def]
QED
