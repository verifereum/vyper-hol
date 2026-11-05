Theory o1MakeSsaShapeProbe
Ancestors
  o1PassContract makeSsaCurrentDefs irSupply unitShapeDefs venomInst list o1MakeSsaReachable

(* A return-PC use precedes its unique writer along one arm. *)
Definition probe_diamond_def:
  probe_diamond = mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [
       mk_inst 0 JNZ [Lit (n2w 1); Label "left"; Label "right"] []] |>;
    <| bb_label := "left"; bb_instructions := [
       mk_inst 1 ASSIGN [Var "r"] ["q"];
       mk_inst 2 JMP [Label "join"] []] |>;
    <| bb_label := "right"; bb_instructions := [
       mk_inst 3 RETPC_PARAM [Lit (n2w 0)] ["r"];
       mk_inst 4 JMP [Label "join"] []] |>;
    <| bb_label := "join"; bb_instructions := [
       mk_inst 5 RET [Var "r"] []] |>]
End

Definition probe_supply_def:
  probe_supply = <| irs_next_inst := 6; irs_next_var := 0;
    irs_next_label := 0; irs_used_inst_ids := [0;1;2;3;4;5];
    irs_used_vars := ["r";"q"];
    irs_used_labels := ["entry";"left";"right";"join"] |>
End

Theorem probe_diamond_output:
  MAP (\bb. (bb.bb_label,
    MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs)) bb.bb_instructions))
    (FST (make_ssa_current_fn probe_supply probe_diamond)).fn_blocks =
  [("entry",[(JNZ,[Lit (n2w 1); Label "left"; Label "right"],[])]);
   ("left",[(ASSIGN,[Var "r"],["q"]);(JMP,[Label "join"],[])]);
   ("right",[(RETPC_PARAM,[Lit (n2w 0)],["formal_var_0"]);(JMP,[Label "join"],[])]);
   ("join",[(PHI,[Label "left";Var "r";Label "right";Var "formal_var_0"],["r"]);
            (RET,[Var "r"],[])])]
Proof
  EVAL_TAC
QED

Theorem probe_diamond_seed:
  retpc_var probe_diamond "r"
Proof
  simp[retpc_var_def] >> irule copy_phi_var_seed >>
  qexists_tac `mk_inst 3 RETPC_PARAM [Lit (n2w 0)] ["r"]` >>
  EVAL_TAC
QED

Theorem probe_diamond_edges:
  fn_cfg_edge probe_diamond "entry" "left" /\
  fn_cfg_edge probe_diamond "entry" "right" /\
  fn_cfg_edge probe_diamond "left" "join"
Proof
  simp[venomWfTheory.fn_cfg_edge_def, probe_diamond_def,
       mk_raw_function_def, GSYM AND_IMP_INTRO, DISJ_IMP_THM,
       LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC
QED

Theorem probe_diamond_labels_reachable:
  !l. MEM l ["entry";"left";"right";"join"] ==>
      fn_reachable probe_diamond l
Proof
  rpt strip_tac >>
  simp[venomWfTheory.fn_reachable_def] >>
  qexists_tac `"entry"` >>
  (conj_tac >- EVAL_TAC) >>
  gvs[] >> metis_tac[relationTheory.RTC_RULES, probe_diamond_edges]
QED

Theorem probe_diamond_reachable:
  reachable_fn probe_diamond = probe_diamond
Proof
  mp_tac probe_diamond_labels_reachable >>
  simp[probe_diamond_def, mk_raw_function_def, mk_inst_def] >> strip_tac >>
  simp[reachable_fn_def, probe_diamond_def, mk_raw_function_def,
       reachable_inst_def, mk_inst_def]
QED

Theorem probe_diamond_retpc_input:
  retpc_shape_ok probe_diamond
Proof
  rewrite_tac[retpc_shape_ok_def, probe_diamond_reachable] >>
  mp_tac probe_diamond_seed >>
  simp[probe_diamond_def, mk_raw_function_def, mk_inst_def] >> strip_tac >>
  simp[retpc_shape_ok_def, probe_diamond_reachable,
       probe_diamond_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, mk_inst_def, GSYM AND_IMP_INTRO,
       DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS,
       probe_diamond_seed]
QED

(* Existing seeded/self-referential PHI, including a dead predecessor. *)
Definition probe_existing_def:
  probe_existing = mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [
       mk_inst 0 JNZ [Lit (n2w 1); Label "left"; Label "right"] []] |>;
    <| bb_label := "left"; bb_instructions := [
       mk_inst 1 JMP [Label "join"] []] |>;
    <| bb_label := "right"; bb_instructions := [
       mk_inst 2 RETPC_PARAM [Lit (n2w 0)] ["r"];
       mk_inst 3 JMP [Label "join"] []] |>;
    <| bb_label := "join"; bb_instructions := [
       mk_inst 4 PHI [Label "left";Var "y";Label "right";Var "r";
                      Label "dead";Var "y"] ["y"];
       mk_inst 5 RET [Var "y"] []] |>;
    <| bb_label := "dead"; bb_instructions := [
       mk_inst 6 JMP [Label "join"] []] |>]
End

Theorem probe_existing_output:
  MAP (\bb. (bb.bb_label,
    MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs)) bb.bb_instructions))
    (FST (make_ssa_current_fn (probe_supply with <| irs_next_inst := 7;
        irs_used_inst_ids := [0;1;2;3;4;5;6];
        irs_used_vars := ["r";"y"];
        irs_used_labels := ["entry";"left";"right";"join";"dead"] |>)
                             probe_existing)).fn_blocks =
  [("entry",[(JNZ,[Lit (n2w 1);Label "left";Label "right"],[])]);
   ("left",[(JMP,[Label "join"],[])]);
   ("right",[(RETPC_PARAM,[Lit (n2w 0)],["r"]);(JMP,[Label "join"],[])]);
   ("join",[(PHI,[Label "left";Var "y";Label "right";Var "r";
                   Label "dead";Var "formal_var_0"],["formal_var_0"]);
            (ASSIGN,[Var "formal_var_0"],["y"]);
            (RET,[Var "formal_var_0"],[])]);
   ("dead",[(JMP,[Label "join"],[])])]
Proof
  EVAL_TAC
QED

Theorem probe_diamond_opaque:
  opaque_use_ok probe_diamond
Proof
  simp[opaque_use_ok_def, probe_diamond_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def, retpc_use_ok_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS]
QED

Theorem probe_diamond_shape:
  fn_shape_ok probe_diamond
Proof
  rewrite_tac[fn_shape_ok_def, probe_diamond_retpc_input,
              probe_diamond_opaque] >> EVAL_TAC
QED

Theorem probe_diamond_wf:
  wf_function probe_diamond /\ fn_inst_wf probe_diamond
Proof
  EVAL_TAC
QED

Definition probe_diamond_result_def:
  probe_diamond_result = mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [
       mk_inst 0 JNZ [Lit (n2w 1); Label "left"; Label "right"] []] |>;
    <| bb_label := "left"; bb_instructions := [
       mk_inst 1 ASSIGN [Var "r"] ["q"];
       mk_inst 2 JMP [Label "join"] []] |>;
    <| bb_label := "right"; bb_instructions := [
       mk_inst 3 RETPC_PARAM [Lit (n2w 0)] ["formal_var_0"];
       mk_inst 4 JMP [Label "join"] []] |>;
    <| bb_label := "join"; bb_instructions := [
       mk_inst 6 PHI [Label "left";Var "r";Label "right";Var "formal_var_0"] ["r"];
       mk_inst 5 RET [Var "r"] []] |>]
End

Theorem probe_diamond_result_eq:
  FST (make_ssa_current_fn probe_supply probe_diamond) = probe_diamond_result
Proof
  EVAL_TAC
QED

Theorem probe_diamond_result_edges:
  fn_cfg_edge probe_diamond_result = fn_cfg_edge probe_diamond
Proof
  simp[FUN_EQ_THM, venomWfTheory.fn_cfg_edge_def, probe_diamond_result_def,
       probe_diamond_def, mk_raw_function_def, mk_inst_def,
       LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC >> simp[]
QED


Theorem probe_diamond_result_labels_reachable:
  !l. MEM l ["entry";"left";"right";"join"] ==>
      fn_reachable probe_diamond_result l
Proof
  `fn_entry_label probe_diamond_result = fn_entry_label probe_diamond` by EVAL_TAC >>
  mp_tac probe_diamond_labels_reachable >>
  simp[venomWfTheory.fn_reachable_def, probe_diamond_result_edges]
QED

Theorem probe_diamond_result_all_reachable:
  !bb. MEM bb probe_diamond_result.fn_blocks ==>
       fn_reachable probe_diamond_result bb.bb_label
Proof
  rpt strip_tac >> irule probe_diamond_result_labels_reachable >>
  pop_assum mp_tac >> simp[probe_diamond_result_def, mk_raw_function_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem probe_diamond_result_preds:
  reachable_preds probe_diamond_result "join" = ["left";"right"]
Proof
  simp[reachable_preds_all_reachable, probe_diamond_result_all_reachable] >>
  simp[probe_diamond_result_edges, probe_diamond_result_def, mk_raw_function_def,
       venomWfTheory.fn_cfg_edge_def, probe_diamond_def,
       LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC
QED

Theorem probe_diamond_result_inst_fixed:
  !bb i. MEM bb probe_diamond_result.fn_blocks /\ MEM i bb.bb_instructions ==>
    reachable_inst probe_diamond_result bb.bb_label i = i
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM bb probe_diamond_result.fn_blocks` mp_tac >>
  CONV_TAC (LAND_CONV EVAL) >> strip_tac >>
  gvs[mk_inst_def, reachable_inst_def, probe_diamond_result_preds] >> EVAL_TAC
QED

Theorem probe_diamond_result_reachable:
  reachable_fn probe_diamond_result = probe_diamond_result
Proof
  irule reachable_fn_fixed >>
  simp[probe_diamond_result_all_reachable, probe_diamond_result_inst_fixed]
QED

Theorem probe_diamond_result_seed:
  retpc_var probe_diamond_result "formal_var_0"
Proof
  simp[retpc_var_def] >> irule copy_phi_var_seed >>
  qexists_tac `mk_inst 3 RETPC_PARAM [Lit (n2w 0)] ["formal_var_0"]` >> EVAL_TAC
QED

Theorem probe_diamond_result_phi:
  retpc_var probe_diamond_result "r"
Proof
  simp[retpc_var_def] >> irule copy_phi_var_phi >>
  qexistsl_tac [`mk_inst 6 PHI
    [Label "left";Var "r";Label "right";Var "formal_var_0"] ["r"]`,
    `"formal_var_0"`] >>
  simp[GSYM retpc_var_def, probe_diamond_result_seed] >> EVAL_TAC
QED

Theorem probe_diamond_retpc_output:
  retpc_shape_ok (FST (make_ssa_current_fn probe_supply probe_diamond))
Proof
  rewrite_tac[probe_diamond_result_eq, retpc_shape_ok_def,
              probe_diamond_result_reachable] >>
  mp_tac probe_diamond_result_seed >> mp_tac probe_diamond_result_phi >>
  simp[probe_diamond_result_def, mk_raw_function_def, mk_inst_def] >>
  rpt strip_tac >>
  gvs[probe_diamond_result_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, mk_inst_def, GSYM AND_IMP_INTRO,
       DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS] >>
  qexists_tac `"r"` >> simp[]
QED
