Theory o1MakeSsaConnectivityProbe
Ancestors
  o1MakeSsaSeedProbe o1MakeSsaShapeProbe o1MakeSsaTreeBoundary
  o1MakeSsaClosure o1MakeSsaActualNames o1SourceUnitCheck o1PassContract
  makeSsaCurrentDefs unitShapeDefs venomInst list

(* Six-block nested loop: merge and header can both acquire a PHI for r.
   The body is the unique original writer; paths may read r before it. *)
Definition connectivity_nested_def:
  connectivity_nested = mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "header"] []] |>;
    <| bb_label := "header"; bb_instructions := [
      mk_inst 1 JNZ [Lit (n2w 1);Label "inner";Label "exit"] []] |>;
    <| bb_label := "inner"; bb_instructions := [
      mk_inst 2 JNZ [Lit (n2w 1);Label "body";Label "merge"] []] |>;
    <| bb_label := "body"; bb_instructions := [
      mk_inst 3 RETPC_PARAM [Lit (n2w 0)] ["r"];
      mk_inst 4 JMP [Label "merge"] []] |>;
    <| bb_label := "merge"; bb_instructions := [mk_inst 5 JMP [Label "header"] []] |>;
    <| bb_label := "exit"; bb_instructions := [mk_inst 6 RET [Var "r"] []] |>]
End

Definition connectivity_supply_def:
  connectivity_supply = probe_supply with <| irs_next_inst := 7;
    irs_used_inst_ids := [0;1;2;3;4;5;6]; irs_used_vars := ["r"];
    irs_used_labels := ["entry";"header";"inner";"body";"merge";"exit"] |>
End

Theorem connectivity_nested_eval:
  MAP (\bb. (bb.bb_label,
    MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs)) bb.bb_instructions))
    (FST (make_ssa_current_fn connectivity_supply connectivity_nested)).fn_blocks =
    [("entry",[(JMP,[Label "header"],[])]);
     ("header",[(PHI,[Label "entry"; Var "r"; Label "merge"; Var "formal_var_0"],["r"]);
                (JNZ,[Lit 1w; Label "inner"; Label "exit"],[])]);
     ("inner",[(JNZ,[Lit 1w; Label "body"; Label "merge"],[])]);
     ("body",[(RETPC_PARAM,[Lit 0w],["formal_var_1"]); (JMP,[Label "merge"],[])]);
     ("merge",[(PHI,[Label "inner"; Var "r"; Label "body"; Var "formal_var_1"],["formal_var_0"]);
               (JMP,[Label "header"],[])]);
     ("exit",[(RET,[Var "r"],[])])]
Proof
  EVAL_TAC
QED

Theorem connectivity_nested_wf:
  wf_function connectivity_nested
Proof
  EVAL_TAC
QED

Theorem connectivity_nested_closure:
  let out = FST (make_ssa_current_fn connectivity_supply connectivity_nested) in
  copy_phi_var RETPC_PARAM out "formal_var_1" /\
  copy_phi_var RETPC_PARAM out "formal_var_0" /\
  copy_phi_var RETPC_PARAM out "r"
Proof
  simp[LET_THM] >> conj_asm1_tac
  >- (irule copy_phi_var_seed >>
      qexists_tac `HD (EL 3 (FST (make_ssa_current_fn connectivity_supply connectivity_nested)).fn_blocks).bb_instructions` >>
      EVAL_TAC) >>
  conj_asm1_tac
  >- (irule copy_phi_var_phi >>
      qexistsl_tac [`HD (EL 4 (FST (make_ssa_current_fn connectivity_supply connectivity_nested)).fn_blocks).bb_instructions`, `"formal_var_1"`] >>
      simp[] >> EVAL_TAC) >>
  irule copy_phi_var_phi >>
  qexistsl_tac [`HD (EL 1 (FST (make_ssa_current_fn connectivity_supply connectivity_nested)).fn_blocks).bb_instructions`, `"formal_var_0"`] >>
  simp[] >> EVAL_TAC
QED

Theorem connectivity_nested_saturation:
  copy_phi_vars RETPC_PARAM
    (FST (make_ssa_current_fn connectivity_supply connectivity_nested)) =
    ["formal_var_1";"formal_var_0";"r"]
Proof
  EVAL_TAC
QED

Theorem connectivity_nested_edges:
  !fn. (fn = connectivity_nested \/
        fn = FST (make_ssa_current_fn connectivity_supply connectivity_nested)) ==>
  fn_cfg_edge fn "entry" "header" /\
  fn_cfg_edge fn "header" "inner" /\
  fn_cfg_edge fn "header" "exit" /\
  fn_cfg_edge fn "inner" "body" /\
  fn_cfg_edge fn "inner" "merge"
Proof
  rpt strip_tac >> gvs[] >>
  simp[venomWfTheory.fn_cfg_edge_def] >> EVAL_TAC >>
  simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC
QED

Theorem connectivity_nested_reachability:
  !fn l. (fn = connectivity_nested \/
          fn = FST (make_ssa_current_fn connectivity_supply connectivity_nested)) /\
         MEM l ["entry";"header";"inner";"body";"merge";"exit"] ==>
         fn_reachable fn l
Proof
  rpt gen_tac >> strip_tac >>
  `fn_entry_label fn = SOME "entry"` by (gvs[] >> EVAL_TAC) >>
  `fn_cfg_edge fn "entry" "header" /\
   fn_cfg_edge fn "header" "inner" /\
   fn_cfg_edge fn "header" "exit" /\
   fn_cfg_edge fn "inner" "body" /\
   fn_cfg_edge fn "inner" "merge"` by metis_tac[connectivity_nested_edges] >>
  `(fn_cfg_edge fn)^* "entry" "header"` by
    metis_tac[relationTheory.RTC_RULES] >>
  `(fn_cfg_edge fn)^* "entry" "inner"` by
    metis_tac[relationTheory.RTC_RULES_RIGHT1] >>
  simp[venomWfTheory.fn_reachable_def] >>
  gvs[] >> metis_tac[relationTheory.RTC_RULES_RIGHT1]
QED

Theorem connectivity_nested_input_reachable:
  reachable_fn connectivity_nested = connectivity_nested
Proof
  `!l. MEM l ["entry";"header";"inner";"body";"merge";"exit"] ==>
       fn_reachable connectivity_nested l` by
    metis_tac[connectivity_nested_reachability] >>
  pop_assum mp_tac >>
  simp[connectivity_nested_def, mk_raw_function_def, mk_inst_def] >> strip_tac >>
  simp[reachable_fn_def, connectivity_nested_def, mk_raw_function_def,
       reachable_inst_def, mk_inst_def]
QED

Theorem connectivity_nested_input_retpc:
  retpc_shape_ok connectivity_nested
Proof
  `retpc_var connectivity_nested "r"` by
    (simp[retpc_var_def] >> irule copy_phi_var_seed >>
     qexists_tac `mk_inst 3 RETPC_PARAM [Lit 0w] ["r"]` >> EVAL_TAC) >>
  pop_assum mp_tac >>
  simp[retpc_shape_ok_def, connectivity_nested_input_reachable,
       connectivity_nested_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, mk_inst_def, GSYM AND_IMP_INTRO,
       DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS]
QED

(* Retain instruction IDs only to rewrite beneath noncomputable reachability. *)
Theorem connectivity_nested_result:
  FST (make_ssa_current_fn connectivity_supply connectivity_nested) =
  mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "header"] []] |>;
    <| bb_label := "header"; bb_instructions := [
      mk_inst 8 PHI [Label "entry";Var "r";Label "merge";Var "formal_var_0"] ["r"];
      mk_inst 1 JNZ [Lit 1w;Label "inner";Label "exit"] []] |>;
    <| bb_label := "inner"; bb_instructions := [
      mk_inst 2 JNZ [Lit 1w;Label "body";Label "merge"] []] |>;
    <| bb_label := "body"; bb_instructions := [
      mk_inst 3 RETPC_PARAM [Lit 0w] ["formal_var_1"];
      mk_inst 4 JMP [Label "merge"] []] |>;
    <| bb_label := "merge"; bb_instructions := [
      mk_inst 7 PHI [Label "inner";Var "r";Label "body";Var "formal_var_1"] ["formal_var_0"];
      mk_inst 5 JMP [Label "header"] []] |>;
    <| bb_label := "exit"; bb_instructions := [mk_inst 6 RET [Var "r"] []] |>]
Proof
  EVAL_TAC
QED

Theorem connectivity_nested_output_edges:
  !l m. fn_cfg_edge (FST (make_ssa_current_fn connectivity_supply connectivity_nested)) l m <=>
    (l = "entry" /\ m = "header") \/
    (l = "header" /\ MEM m ["inner";"exit"]) \/
    (l = "inner" /\ MEM m ["body";"merge"]) \/
    (l = "body" /\ m = "merge") \/
    (l = "merge" /\ m = "header")
Proof
  rpt gen_tac >> simp[venomWfTheory.fn_cfg_edge_def] >> EVAL_TAC >>
  simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC >>
  simp[] >> metis_tac[]
QED

Theorem connectivity_nested_output_preds:
  let out = FST (make_ssa_current_fn connectivity_supply connectivity_nested) in
  reachable_preds out "header" = ["entry";"merge"] /\
  reachable_preds out "merge" = ["inner";"body"]
Proof
  simp[LET_THM] >>
  `!bb. MEM bb (FST (make_ssa_current_fn connectivity_supply connectivity_nested)).fn_blocks ==>
        fn_reachable (FST (make_ssa_current_fn connectivity_supply connectivity_nested)) bb.bb_label` by
    (rpt strip_tac >> irule connectivity_nested_reachability >>
     simp[connectivity_nested_result, mk_raw_function_def] >>
     pop_assum mp_tac >> simp[connectivity_nested_result, mk_raw_function_def] >>
     rpt strip_tac >> gvs[]) >>
  simp[o1MakeSsaReachableTheory.reachable_preds_all_reachable] >>
  simp[connectivity_nested_output_edges] >>
  rewrite_tac[connectivity_nested_result] >> EVAL_TAC
QED

Theorem connectivity_nested_output_reachable:
  reachable_fn (FST (make_ssa_current_fn connectivity_supply connectivity_nested)) =
  FST (make_ssa_current_fn connectivity_supply connectivity_nested)
Proof
  `!l. MEM l ["entry";"header";"inner";"body";"merge";"exit"] ==>
    fn_reachable (FST (make_ssa_current_fn connectivity_supply connectivity_nested)) l` by
    metis_tac[connectivity_nested_reachability] >>
  mp_tac connectivity_nested_output_preds >> pop_assum mp_tac >>
  simp[LET_THM, connectivity_nested_result, mk_raw_function_def, mk_inst_def] >>
  rpt strip_tac >>
  simp[reachable_fn_def, connectivity_nested_result, mk_raw_function_def,
       reachable_inst_def, mk_inst_def] >> EVAL_TAC
QED

Theorem connectivity_nested_reachable_closure:
  !x. MEM x ["formal_var_1";"formal_var_0";"r"] ==>
  copy_phi_var RETPC_PARAM
    (reachable_fn (FST (make_ssa_current_fn connectivity_supply connectivity_nested))) x
Proof
  simp[connectivity_nested_output_reachable] >>
  mp_tac connectivity_nested_closure >> simp[LET_THM] >> metis_tac[]
QED

(* The dead predecessor's seed is deliberately not a reachable seed when
   live_seed=F.  Such a failure of reachable input shape is not a counterexample. *)
Definition connectivity_dead_def:
  connectivity_dead live_seed linked = mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "live"] []] |>;
    <| bb_label := "live"; bb_instructions :=
      (if live_seed then [mk_inst 1 RETPC_PARAM [Lit 0w] ["r"]] else []) ++
      [mk_inst 2 RET [Var "r"] []] |>;
    <| bb_label := "dead"; bb_instructions :=
      (if live_seed then [mk_inst 3 ASSIGN [Var "r"] ["q"]]
       else [mk_inst 3 RETPC_PARAM [Lit 0w] ["r"]]) ++
      [if linked then mk_inst 4 JMP [Label "live"] [] else mk_inst 4 STOP [] []] |>]
End

Definition connectivity_dead_supply_def:
  connectivity_dead_supply = probe_supply with <| irs_next_inst := 5;
    irs_used_inst_ids := [0;1;2;3;4]; irs_used_vars := ["r";"q"];
    irs_used_labels := ["entry";"live";"dead"] |>
End

Theorem connectivity_dead_eval:
  !live_seed linked.
  MAP (\bb. (bb.bb_label, MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs)) bb.bb_instructions))
    (FST (make_ssa_current_fn connectivity_dead_supply (connectivity_dead live_seed linked))).fn_blocks =
  if ~live_seed /\ linked then
    [("entry",[(JMP,[Label "live"],[])]);
     ("live",[(PHI,[Label "entry";Var "r";Label "dead";Var "formal_var_0"],["r"]);
              (RET,[Var "r"],[])]);
     ("dead",[(RETPC_PARAM,[Lit 0w],["formal_var_0"]);(JMP,[Label "live"],[])])]
  else MAP (\bb. (bb.bb_label, MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs)) bb.bb_instructions))
       (connectivity_dead live_seed linked).fn_blocks
Proof
  Cases >> Cases >> EVAL_TAC
QED

Theorem connectivity_dead_tree:
  !live_seed linked.
  dom_tree_postorder (current_dom_tree (connectivity_dead live_seed linked)) =
  ["dead";"live";"entry"]
Proof
  Cases >> Cases >> EVAL_TAC
QED

Theorem connectivity_dead_wf:
  !live_seed linked. wf_function (connectivity_dead live_seed linked)
Proof
  Cases >> Cases >> EVAL_TAC
QED

Theorem connectivity_dead_result:
  !live_seed linked.
  FST (make_ssa_current_fn connectivity_dead_supply (connectivity_dead live_seed linked)) =
  if ~live_seed /\ linked then
    mk_raw_function "entry" [
      <| bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "live"] []] |>;
      <| bb_label := "live"; bb_instructions := [
        mk_inst 5 PHI [Label "entry";Var "r";Label "dead";Var "formal_var_0"] ["r"];
        mk_inst 2 RET [Var "r"] []] |>;
      <| bb_label := "dead"; bb_instructions := [
        mk_inst 3 RETPC_PARAM [Lit 0w] ["formal_var_0"];
        mk_inst 4 JMP [Label "live"] []] |>]
  else connectivity_dead live_seed linked
Proof
  Cases >> Cases >> EVAL_TAC
QED

Theorem connectivity_dead_edges:
  !live_seed linked out l m.
  (out = connectivity_dead live_seed linked \/
   out = FST (make_ssa_current_fn connectivity_dead_supply (connectivity_dead live_seed linked))) ==>
  (fn_cfg_edge out l m <=>
   (l = "entry" /\ m = "live") \/ (linked /\ l = "dead" /\ m = "live"))
Proof
  Cases >> Cases >> rpt strip_tac >> gvs[] >>
  simp[venomWfTheory.fn_cfg_edge_def] >> EVAL_TAC >>
  simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC >>
  simp[] >> metis_tac[]
QED

Theorem connectivity_dead_reachability:
  !live_seed linked out l.
  (out = connectivity_dead live_seed linked \/
   out = FST (make_ssa_current_fn connectivity_dead_supply (connectivity_dead live_seed linked))) ==>
  (fn_reachable out l <=> MEM l ["entry";"live"])
Proof
  rpt gen_tac >> strip_tac >>
  `fn_entry_label out = SOME "entry"` by
    (gvs[] >> Cases_on `live_seed` >> Cases_on `linked` >> EVAL_TAC) >>
  `!l m. fn_cfg_edge out l m <=>
    (l = "entry" /\ m = "live") \/ (linked /\ l = "dead" /\ m = "live")` by
    metis_tac[connectivity_dead_edges] >> gvs[] >>
  simp[venomWfTheory.fn_reachable_def] >>
  once_rewrite_tac[relationTheory.RTC_CASES1] >> simp[] >>
  once_rewrite_tac[relationTheory.RTC_CASES1] >> simp[] >> metis_tac[]
QED

Theorem connectivity_dead_input_reachable:
  !live_seed linked.
  reachable_fn (connectivity_dead live_seed linked) =
  mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "live"] []] |>;
    <| bb_label := "live"; bb_instructions :=
      (if live_seed then [mk_inst 1 RETPC_PARAM [Lit 0w] ["r"]] else []) ++
      [mk_inst 2 RET [Var "r"] []] |>]
Proof
  rpt gen_tac >>
  `!l. fn_reachable (connectivity_dead live_seed linked) l <=> MEM l ["entry";"live"]` by
    metis_tac[connectivity_dead_reachability] >>
  simp[reachable_fn_def, connectivity_dead_def, mk_raw_function_def] >>
  Cases_on `live_seed` >> simp[reachable_inst_def, mk_inst_def]
QED

Theorem connectivity_nested_opaque:
  opaque_use_ok connectivity_nested
Proof
  simp[opaque_use_ok_def, connectivity_nested_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def, retpc_use_ok_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS]
QED

Theorem connectivity_nested_shape:
  fn_shape_ok connectivity_nested
Proof
  rewrite_tac[fn_shape_ok_def, connectivity_nested_input_retpc,
              connectivity_nested_opaque] >> EVAL_TAC
QED

Theorem connectivity_nested_output_retpc:
  retpc_shape_ok (FST (make_ssa_current_fn connectivity_supply connectivity_nested))
Proof
  rewrite_tac[retpc_shape_ok_def, connectivity_nested_output_reachable] >>
  mp_tac connectivity_nested_closure >>
  simp[LET_THM, GSYM retpc_var_def, connectivity_nested_result,
       mk_raw_function_def, fn_insts_def, fn_insts_blocks_def, mk_inst_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS] >>
  rpt strip_tac >> qexists_tac `"r"` >> simp[]
QED

Theorem connectivity_dead_output_preds:
  reachable_preds
    (FST (make_ssa_current_fn connectivity_dead_supply (connectivity_dead F T))) "live" =
    ["entry"]
Proof
  `!l. fn_reachable
    (FST (make_ssa_current_fn connectivity_dead_supply (connectivity_dead F T))) l <=>
    MEM l ["entry";"live"]` by metis_tac[connectivity_dead_reachability] >>
  simp[reachable_preds_def] >>
  `!l m. fn_cfg_edge
    (FST (make_ssa_current_fn connectivity_dead_supply (connectivity_dead F T))) l m <=>
    (l = "entry" /\ m = "live") \/ (l = "dead" /\ m = "live")` by
    metis_tac[connectivity_dead_edges] >>
  simp[] >> rewrite_tac[connectivity_dead_result] >> EVAL_TAC
QED

Theorem connectivity_dead_output_reachable:
  reachable_fn
    (FST (make_ssa_current_fn connectivity_dead_supply (connectivity_dead F T))) =
  mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "live"] []] |>;
    <| bb_label := "live"; bb_instructions := [
      mk_inst 5 PHI [Label "entry";Var "r"] ["r"];
      mk_inst 2 RET [Var "r"] []] |>]
Proof
  `!l. fn_reachable
    (FST (make_ssa_current_fn connectivity_dead_supply (connectivity_dead F T))) l <=>
    MEM l ["entry";"live"]` by metis_tac[connectivity_dead_reachability] >>
  mp_tac connectivity_dead_output_preds >> pop_assum mp_tac >>
  simp[connectivity_dead_result, mk_raw_function_def, mk_inst_def] >>
  rpt strip_tac >>
  simp[reachable_fn_def, connectivity_dead_result, mk_raw_function_def,
       reachable_inst_def, mk_inst_def] >> EVAL_TAC
QED

Theorem connectivity_dead_seed_closure:
  copy_phi_var RETPC_PARAM
    (FST (make_ssa_current_fn connectivity_dead_supply (connectivity_dead F T))) "formal_var_0" /\
  copy_phi_var RETPC_PARAM
    (FST (make_ssa_current_fn connectivity_dead_supply (connectivity_dead F T))) "r"
Proof
  conj_asm1_tac
  >- (irule copy_phi_var_seed >>
      qexists_tac `mk_inst 3 RETPC_PARAM [Lit 0w] ["formal_var_0"]` >> EVAL_TAC) >>
  irule copy_phi_var_phi >>
  qexistsl_tac [`mk_inst 5 PHI [Label "entry";Var "r";Label "dead";Var "formal_var_0"] ["r"]`, `"formal_var_0"`] >>
  simp[] >> EVAL_TAC
QED

Theorem connectivity_dead_reachable_bad:
  cp_bad_set RETPC_PARAM
    (reachable_fn (FST (make_ssa_current_fn connectivity_dead_supply (connectivity_dead F T)))) {"r"}
Proof
  simp[connectivity_dead_output_reachable, cp_bad_set_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def, GSYM AND_IMP_INTRO,
       DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem connectivity_dead_reachable_not_closure:
  ~copy_phi_var RETPC_PARAM
    (reachable_fn (FST (make_ssa_current_fn connectivity_dead_supply (connectivity_dead F T)))) "r"
Proof
  simp[copy_phi_var_bad_set] >> qexists_tac `{"r"}` >>
  simp[connectivity_dead_reachable_bad]
QED

Theorem connectivity_dead_input_missing_seed:
  !linked. ~retpc_var (reachable_fn (connectivity_dead F linked)) "r"
Proof
  gen_tac >> simp[connectivity_dead_input_reachable, retpc_var_def,
                   copy_phi_var_bad_set] >> qexists_tac `{"r"}` >>
  simp[cp_bad_set_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, mk_inst_def, GSYM AND_IMP_INTRO,
       DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem connectivity_dead_input_invalid:
  !linked. ~retpc_shape_ok (connectivity_dead F linked)
Proof
  gen_tac >> strip_tac >>
  qspec_then `linked` mp_tac connectivity_dead_input_missing_seed >>
  rewrite_tac[connectivity_dead_input_reachable] >>
  fs[retpc_shape_ok_def] >>
  qpat_x_assum `!inst. _ ==> ?front x. _` (qspec_then `mk_inst 2 RET [Var "r"] []` mp_tac) >>
  simp[connectivity_dead_input_reachable, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, mk_inst_def, APPEND_EQ_CONS]
QED

Theorem connectivity_dead_live_seed:
  !linked. retpc_var (connectivity_dead T linked) "r" /\
           retpc_var (connectivity_dead T linked) "q"
Proof
  gen_tac >> conj_asm1_tac
  >- (simp[retpc_var_def] >> irule copy_phi_var_seed >>
      qexists_tac `mk_inst 1 RETPC_PARAM [Lit 0w] ["r"]` >>
      Cases_on `linked` >> EVAL_TAC) >>
  simp[retpc_var_def] >> irule copy_phi_var_assign >>
  qexistsl_tac [`mk_inst 3 ASSIGN [Var "r"] ["q"]`, `"r"`] >>
  simp[GSYM retpc_var_def] >> Cases_on `linked` >> EVAL_TAC
QED

Theorem connectivity_dead_live_reachable_seed:
  !linked. retpc_var (reachable_fn (connectivity_dead T linked)) "r"
Proof
  gen_tac >> simp[retpc_var_def] >> irule copy_phi_var_seed >>
  qexists_tac `mk_inst 1 RETPC_PARAM [Lit 0w] ["r"]` >>
  rewrite_tac[connectivity_dead_input_reachable] >> EVAL_TAC
QED

Theorem connectivity_dead_live_shape:
  !linked. retpc_shape_ok (connectivity_dead T linked)
Proof
  gen_tac >> mp_tac (Q.SPEC `linked` connectivity_dead_live_seed) >>
  mp_tac (Q.SPEC `linked` connectivity_dead_live_reachable_seed) >>
  rewrite_tac[retpc_shape_ok_def] >>
  simp[connectivity_dead_input_reachable, connectivity_dead_def,
       mk_raw_function_def, fn_insts_def, fn_insts_blocks_def, mk_inst_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS] >>
  Cases_on `linked` >> simp[mk_inst_def]
QED

(* Excluded-label control: unlike the three-block chain, no tree child. *)
Definition connectivity_excluded_def:
  connectivity_excluded = mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [mk_inst 0 RET [Var "r"] []] |>;
    <| bb_label := "dead"; bb_instructions := [
      mk_inst 1 RETPC_PARAM [Lit 0w] ["r"];mk_inst 2 STOP [] []] |>]
End

Theorem connectivity_excluded_eval:
  FST (make_ssa_current_fn connectivity_dead_supply connectivity_excluded) =
  connectivity_excluded /\
  dom_tree_postorder (current_dom_tree connectivity_excluded) = ["entry"] /\
  wf_function connectivity_excluded
Proof
  EVAL_TAC
QED

(* Bounded semantic case table (11 functions, largest has six blocks):
   Reused fixtures:
   - probe_diamond / seed_probe_reverse: one-arm seed, use-before-writer;
     seed formal_var_0 reaches join output r (and old use q in full graph).
     Block permutation changes PHI pair order, not the seed escape.
   - seed_probe_chain: identity; seed r reaches prior copy q.
   - seed_probe_loop: header r has self-edge and body formal_var_0 escape;
     full and reachable graphs agree (SeedProbe certifies retpc shape).
   - seed_probe_dead: untouched disconnected copy dead_q belongs only to
     full closure, and is absent in reachable closure; input retpc is checked.
   New fixtures:
   - connectivity_nested: input fn_shape_ok checked.  Header r and merge
     formal_var_0 form an SCC; body formal_var_1 is the seed escape.  All
     blocks and PHI pairs survive reachable_fn; concrete closure paths and
     output retpc_shape_ok are checked.  r is first allocated by a PHI,
     NOT by the unique original writer.
   - connectivity_dead T T / T F: all three labels are visited, including
     the unreachable copy.  Final output is unchanged; full closure has
     r and q, reachable closure has seed r.  Input retpc shape is checked.
   - connectivity_dead F T: dead seed is actually visited and renamed to
     formal_var_0; live PHI r <- {entry:r,dead:formal_var_0}.  Full closure
     contains both.  reachable_preds retains only entry, producing r<-r;
     cp_bad_set {r} proves the reachable output has no seed connection.
     This is NOT a contract counterexample: the reachable input RET r
     already lacks a seed (connectivity_dead_input_invalid).
   - connectivity_dead F F: writer visited but first reuses r; identity.
     Reachable input also lacks a seed, so it cannot bear on the contract.
   - connectivity_excluded: two-block excluded-label control; seed block
     is NOT visited, and output is unchanged.  wf checked; no claim of
     input contract shape is made for this control.

   No contract counterexample was found.  These finite results do not
   establish universal connectivity.  In a universal source-component
   proof, the nested SCC needs an incoming edge from the body seed, not
   a timestamp decrease along its r/formal_var_0 cycle.  Reachable graphs
   additionally need an escape whose predecessor pair survives filtering;
   the dead-seed example shows this requirement cannot be omitted or
   deduced from full-function connectivity alone. *)
