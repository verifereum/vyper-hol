Theory o1MakeSsaSeedProbe
Ancestors
  o1MakeSsaShapeProbe o1MakeSsaClosure o1SourceUnitCheck
  o1MakeSsaReachable o1PassContract makeSsaCurrentDefs irSupply unitShapeDefs
  venomInst list

(* Header visitation allocates the original spelling before the loop writer. *)
Definition seed_probe_loop_def:
  seed_probe_loop = mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [
       mk_inst 0 JMP [Label "header"] []] |>;
    <| bb_label := "header"; bb_instructions := [
       mk_inst 1 JNZ [Lit (n2w 1);Label "body";Label "exit"] []] |>;
    <| bb_label := "body"; bb_instructions := [
       mk_inst 2 RETPC_PARAM [Lit (n2w 0)] ["r"];
       mk_inst 3 JMP [Label "header"] []] |>;
    <| bb_label := "exit"; bb_instructions := [
       mk_inst 4 RET [Var "r"] []] |>]
End

Definition seed_probe_supply_def:
  seed_probe_supply = probe_supply with <| irs_next_inst := 5;
    irs_used_inst_ids := [0;1;2;3;4]; irs_used_vars := ["r"];
    irs_used_labels := ["entry";"header";"body";"exit"] |>
End

Theorem seed_probe_loop_eval:
  MAP (\bb. (bb.bb_label,
    MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs)) bb.bb_instructions))
    (FST (make_ssa_current_fn seed_probe_supply seed_probe_loop)).fn_blocks =
  [("entry",[(JMP,[Label "header"],[])]);
   ("header",[(PHI,[Label "entry";Var "r";Label "body";Var "formal_var_0"],["r"]);
              (JNZ,[Lit (n2w 1);Label "body";Label "exit"],[])]);
   ("body",[(RETPC_PARAM,[Lit (n2w 0)],["formal_var_0"]);(JMP,[Label "header"],[])]);
   ("exit",[(RET,[Var "r"],[])])]
Proof
  EVAL_TAC
QED

Definition seed_probe_loop_result_def:
  seed_probe_loop_result = mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "header"] []] |>;
    <| bb_label := "header"; bb_instructions := [
       mk_inst 5 PHI [Label "entry";Var "r";Label "body";Var "formal_var_0"] ["r"];
       mk_inst 1 JNZ [Lit (n2w 1);Label "body";Label "exit"] []] |>;
    <| bb_label := "body"; bb_instructions := [
       mk_inst 2 RETPC_PARAM [Lit (n2w 0)] ["formal_var_0"];
       mk_inst 3 JMP [Label "header"] []] |>;
    <| bb_label := "exit"; bb_instructions := [mk_inst 4 RET [Var "r"] []] |>]
End

Theorem seed_probe_loop_result_eq:
  FST (make_ssa_current_fn seed_probe_supply seed_probe_loop) = seed_probe_loop_result
Proof
  EVAL_TAC
QED

Theorem seed_probe_loop_edges:
  fn_cfg_edge seed_probe_loop "entry" "header" /\
  fn_cfg_edge seed_probe_loop "header" "body" /\
  fn_cfg_edge seed_probe_loop "header" "exit" /\
  fn_cfg_edge seed_probe_loop "body" "header"
Proof
  simp[venomWfTheory.fn_cfg_edge_def, seed_probe_loop_def, mk_raw_function_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, LEFT_AND_OVER_OR,
       RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC
QED

Theorem seed_probe_loop_all_reachable:
  !l. MEM l ["entry";"header";"body";"exit"] ==> fn_reachable seed_probe_loop l
Proof
  rpt strip_tac >> simp[venomWfTheory.fn_reachable_def] >>
  qexists_tac `"entry"` >> (conj_tac >- EVAL_TAC) >>
  gvs[] >> metis_tac[relationTheory.RTC_RULES, seed_probe_loop_edges]
QED

Theorem seed_probe_loop_reachable:
  reachable_fn seed_probe_loop = seed_probe_loop
Proof
  mp_tac seed_probe_loop_all_reachable >>
  simp[seed_probe_loop_def, mk_raw_function_def, mk_inst_def] >> strip_tac >>
  simp[reachable_fn_def, seed_probe_loop_def, mk_raw_function_def,
       reachable_inst_def, mk_inst_def]
QED

Theorem seed_probe_loop_input_retpc:
  retpc_shape_ok seed_probe_loop
Proof
  `retpc_var seed_probe_loop "r"` by
    (simp[retpc_var_def] >> irule copy_phi_var_seed >>
     qexists_tac `mk_inst 2 RETPC_PARAM [Lit (n2w 0)] ["r"]` >> EVAL_TAC) >>
  pop_assum mp_tac >>
  simp[retpc_shape_ok_def, seed_probe_loop_reachable, seed_probe_loop_def,
       mk_raw_function_def, fn_insts_def, fn_insts_blocks_def, mk_inst_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS]
QED

Theorem seed_probe_loop_closure:
  retpc_var seed_probe_loop_result "formal_var_0" /\
  retpc_var seed_probe_loop_result "r"
Proof
  conj_asm1_tac
  >- (simp[retpc_var_def] >> irule copy_phi_var_seed >>
      qexists_tac `mk_inst 2 RETPC_PARAM [Lit (n2w 0)] ["formal_var_0"]` >> EVAL_TAC) >>
  simp[retpc_var_def] >> irule copy_phi_var_phi >>
  qexistsl_tac [`mk_inst 5 PHI [Label "entry";Var "r";Label "body";Var "formal_var_0"] ["r"]`,
                `"formal_var_0"`] >>
  simp[GSYM retpc_var_def] >> EVAL_TAC
QED

Theorem seed_probe_loop_result_reachability:
  fn_reachable seed_probe_loop_result = fn_reachable seed_probe_loop
Proof
  `fn_cfg_edge seed_probe_loop_result = fn_cfg_edge seed_probe_loop` by
    (simp[FUN_EQ_THM, venomWfTheory.fn_cfg_edge_def, seed_probe_loop_result_def,
          seed_probe_loop_def, mk_raw_function_def, mk_inst_def,
          LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC >> simp[]) >>
  `fn_entry_label seed_probe_loop_result = fn_entry_label seed_probe_loop` by EVAL_TAC >>
  simp[FUN_EQ_THM, venomWfTheory.fn_reachable_def]
QED

Theorem seed_probe_loop_result_preds:
  reachable_preds seed_probe_loop_result "header" = ["entry";"body"]
Proof
  `MAP (\bb. bb.bb_label) seed_probe_loop_result.fn_blocks =
    ["entry";"header";"body";"exit"]` by EVAL_TAC >>
  simp[reachable_preds_def, seed_probe_loop_result_reachability,
       seed_probe_loop_all_reachable] >>
  simp[venomWfTheory.fn_cfg_edge_def, seed_probe_loop_result_def,
       mk_raw_function_def, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  EVAL_TAC
QED

Theorem seed_probe_loop_result_reachable:
  reachable_fn seed_probe_loop_result = seed_probe_loop_result
Proof
  `!l. MEM l ["entry";"header";"body";"exit"] ==>
    fn_reachable seed_probe_loop_result l` by
    simp[seed_probe_loop_result_reachability, seed_probe_loop_all_reachable] >>
  mp_tac seed_probe_loop_result_preds >> pop_assum mp_tac >>
  simp[seed_probe_loop_result_def, mk_raw_function_def, mk_inst_def] >>
  rpt strip_tac >>
  simp[reachable_fn_def, seed_probe_loop_result_def, mk_raw_function_def,
       reachable_inst_def, mk_inst_def] >> EVAL_TAC
QED

Theorem seed_probe_loop_output_retpc:
  retpc_shape_ok (FST (make_ssa_current_fn seed_probe_supply seed_probe_loop))
Proof
  rewrite_tac[seed_probe_loop_result_eq, retpc_shape_ok_def,
              seed_probe_loop_result_reachable] >>
  mp_tac seed_probe_loop_closure >>
  simp[seed_probe_loop_result_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, mk_inst_def, GSYM AND_IMP_INTRO,
       DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS] >>
  rpt strip_tac >> qexists_tac `"formal_var_0"` >> simp[]
QED

(* A source can be read before its unique writer even in one block. *)
Definition seed_probe_chain_def:
  seed_probe_chain = mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [
       mk_inst 0 ASSIGN [Var "r"] ["q"];
       mk_inst 1 RETPC_PARAM [Lit (n2w 0)] ["r"];
       mk_inst 2 RET [Var "q"] []] |>]
End

Definition seed_probe_chain_supply_def:
  seed_probe_chain_supply = probe_supply with <| irs_next_inst := 3;
    irs_used_inst_ids := [0;1;2]; irs_used_labels := ["entry"] |>
End

Theorem seed_probe_chain_eval:
  FST (make_ssa_current_fn seed_probe_chain_supply seed_probe_chain) = seed_probe_chain
Proof
  EVAL_TAC
QED

Theorem seed_probe_chain_closure:
  retpc_var seed_probe_chain "r" /\ retpc_var seed_probe_chain "q"
Proof
  conj_asm1_tac
  >- (simp[retpc_var_def] >> irule copy_phi_var_seed >>
      qexists_tac `mk_inst 1 RETPC_PARAM [Lit (n2w 0)] ["r"]` >> EVAL_TAC) >>
  simp[retpc_var_def] >> irule copy_phi_var_assign >>
  qexistsl_tac [`mk_inst 0 ASSIGN [Var "r"] ["q"]`, `"r"`] >>
  simp[GSYM retpc_var_def] >> EVAL_TAC
QED

Theorem seed_probe_chain_reachable:
  reachable_fn seed_probe_chain = seed_probe_chain
Proof
  `fn_reachable seed_probe_chain "entry"` by
    (simp[venomWfTheory.fn_reachable_def] >> qexists_tac `"entry"` >>
     simp[relationTheory.RTC_REFL] >> EVAL_TAC) >>
  pop_assum mp_tac >>
  simp[seed_probe_chain_def, mk_raw_function_def, mk_inst_def] >> strip_tac >>
  simp[reachable_fn_def, seed_probe_chain_def, mk_raw_function_def,
       reachable_inst_def, mk_inst_def]
QED

Theorem seed_probe_chain_retpc:
  retpc_shape_ok seed_probe_chain /\
  retpc_shape_ok (FST (make_ssa_current_fn seed_probe_chain_supply seed_probe_chain))
Proof
  rewrite_tac[seed_probe_chain_eval] >> simp[] >>
  rewrite_tac[retpc_shape_ok_def, seed_probe_chain_reachable] >>
  mp_tac seed_probe_chain_closure >>
  simp[seed_probe_chain_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, mk_inst_def, GSYM AND_IMP_INTRO,
       DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS]
QED

Definition seed_probe_reverse_def:
  seed_probe_reverse = probe_diamond with fn_blocks :=
    [EL 0 probe_diamond.fn_blocks; EL 2 probe_diamond.fn_blocks;
     EL 1 probe_diamond.fn_blocks; EL 3 probe_diamond.fn_blocks]
End

Theorem seed_probe_reverse_eval:
  MAP (\bb. (bb.bb_label,
    MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs)) bb.bb_instructions))
    (FST (make_ssa_current_fn probe_supply seed_probe_reverse)).fn_blocks =
  [("entry",[(JNZ,[Lit (n2w 1);Label "left";Label "right"],[])]);
   ("right",[(RETPC_PARAM,[Lit (n2w 0)],["formal_var_0"]);(JMP,[Label "join"],[])]);
   ("left",[(ASSIGN,[Var "r"],["q"]);(JMP,[Label "join"],[])]);
   ("join",[(PHI,[Label "right";Var "formal_var_0";Label "left";Var "r"],["r"]);
            (RET,[Var "r"],[])])]
Proof
  EVAL_TAC
QED

(* A disconnected block remains unrenamed; full closure is deliberately larger
   than reachable closure.  This is not a failure of demanded-version closure. *)
Definition seed_probe_dead_block_def:
  seed_probe_dead_block = <| bb_label := "dead"; bb_instructions := [
    mk_inst 3 ASSIGN [Var "r"] ["dead_q"]; mk_inst 4 STOP [] []] |>
End

Definition seed_probe_dead_def:
  seed_probe_dead = seed_probe_chain with fn_blocks :=
    seed_probe_chain.fn_blocks ++ [seed_probe_dead_block]
End

Definition seed_probe_dead_supply_def:
  seed_probe_dead_supply = probe_supply with <| irs_next_inst := 5;
    irs_used_inst_ids := [0;1;2;3;4]; irs_used_vars := ["r";"q";"dead_q"];
    irs_used_labels := ["entry";"dead"] |>
End

Theorem seed_probe_dead_eval:
  FST (make_ssa_current_fn seed_probe_dead_supply seed_probe_dead) = seed_probe_dead
Proof
  EVAL_TAC
QED

Theorem seed_probe_dead_no_edges:
  !a b. ~fn_cfg_edge seed_probe_dead a b
Proof
  simp[venomWfTheory.fn_cfg_edge_def, seed_probe_dead_def, seed_probe_dead_block_def,
       seed_probe_chain_def, mk_raw_function_def, LEFT_AND_OVER_OR,
       RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC >> simp[]
QED

Theorem seed_probe_dead_reachability:
  fn_reachable seed_probe_dead l <=> l = "entry"
Proof
  simp[venomWfTheory.fn_reachable_def, seed_probe_dead_no_edges] >>
  `fn_entry_label seed_probe_dead = SOME "entry"` by EVAL_TAC >>
  simp[] >> once_rewrite_tac[relationTheory.RTC_CASES1] >>
  simp[seed_probe_dead_no_edges] >> metis_tac[]
QED

Theorem seed_probe_dead_reachable:
  reachable_fn seed_probe_dead = seed_probe_chain
Proof
  simp[reachable_fn_def, seed_probe_dead_reachability, seed_probe_dead_def,
       seed_probe_chain_def, seed_probe_dead_block_def, mk_raw_function_def,
       reachable_inst_def, mk_inst_def]
QED

Theorem seed_probe_dead_closure:
  retpc_var seed_probe_dead "dead_q"
Proof
  `retpc_var seed_probe_dead "r"` by
    (simp[retpc_var_def] >> irule copy_phi_var_seed >>
     qexists_tac `mk_inst 1 RETPC_PARAM [Lit (n2w 0)] ["r"]` >> EVAL_TAC) >>
  simp[retpc_var_def] >> irule copy_phi_var_assign >>
  qexistsl_tac [`mk_inst 3 ASSIGN [Var "r"] ["dead_q"]`, `"r"`] >>
  simp[GSYM retpc_var_def] >> EVAL_TAC
QED

Theorem seed_probe_dead_reachable_not_closure:
  ~retpc_var (reachable_fn seed_probe_dead) "dead_q"
Proof
  simp[seed_probe_dead_reachable, retpc_var_def, copy_phi_var_bad_set] >>
  qexists_tac `{"dead_q"}` >>
  simp[cp_bad_set_def, seed_probe_chain_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem seed_probe_dead_includes_chain:
  !x. retpc_var seed_probe_chain x ==> retpc_var seed_probe_dead x
Proof
  simp[retpc_var_def] >> rpt strip_tac >>
  drule copy_phi_var_mono >> disch_then (qspec_then `seed_probe_dead` irule) >>
  simp[seed_probe_dead_def, seed_probe_chain_def, seed_probe_dead_block_def,
       mk_raw_function_def, fn_insts_def, fn_insts_blocks_def] >> metis_tac[]
QED

Theorem seed_probe_dead_retpc:
  retpc_shape_ok seed_probe_dead /\
  retpc_shape_ok (FST (make_ssa_current_fn seed_probe_dead_supply seed_probe_dead))
Proof
  `retpc_var seed_probe_dead "r" /\ retpc_var seed_probe_dead "q"` by
    metis_tac[seed_probe_chain_closure, seed_probe_dead_includes_chain] >>
  rewrite_tac[seed_probe_dead_eval] >> simp[] >>
  rewrite_tac[retpc_shape_ok_def, seed_probe_dead_reachable] >>
  mp_tac seed_probe_chain_closure >> ntac 2 (pop_assum mp_tac) >>
  simp[seed_probe_dead_def, seed_probe_chain_def, seed_probe_dead_block_def,
       mk_raw_function_def, fn_insts_def, fn_insts_blocks_def, mk_inst_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS]
QED
