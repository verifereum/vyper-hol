Theory makeSsaCurrentPrefixCompatibility
Ancestors
  makeSsaCurrentPrefixMaps makeSsaDefs venomInst finite_map

(* A source surviving as a direct demand collides with the pulled-back
   demand for a different source-level PHI output. *)
Theorem current_prefix_direct_collision_probe:
  current_prefix_back [mk_inst 0 ASSIGN [Var "src"] ["dst"]]
    (FEMPTY |+ ("dst","v") |+ ("src","w")) "src" "v" /\
  current_prefix_back [mk_inst 0 ASSIGN [Var "src"] ["dst"]]
    (FEMPTY |+ ("dst","v") |+ ("src","w")) "src" "w"
Proof
  simp[current_prefix_back_def, current_prefix_pull_def, mk_inst_def] >> EVAL_TAC
QED

Theorem current_prefix_two_copies_collision_probe:
  current_prefix_back
    [mk_inst 0 ASSIGN [Var "src"] ["dst1"];
     mk_inst 1 ASSIGN [Var "src"] ["dst2"]]
    (FEMPTY |+ ("dst1","v") |+ ("dst2","w")) "src" "v" /\
  current_prefix_back
    [mk_inst 0 ASSIGN [Var "src"] ["dst1"];
     mk_inst 1 ASSIGN [Var "src"] ["dst2"]]
    (FEMPTY |+ ("dst1","v") |+ ("dst2","w")) "src" "w"
Proof
  simp[current_prefix_back_def, current_prefix_pull_def, mk_inst_def] >> EVAL_TAC
QED

Theorem current_prefix_collisions_not_functional:
  ~current_prefix_functional
    (current_prefix_back [mk_inst 0 ASSIGN [Var "src"] ["dst"]]
      (FEMPTY |+ ("dst","v") |+ ("src","w"))) /\
  ~current_prefix_functional
    (current_prefix_back
      [mk_inst 0 ASSIGN [Var "src"] ["dst1"];
       mk_inst 1 ASSIGN [Var "src"] ["dst2"]]
      (FEMPTY |+ ("dst1","v") |+ ("dst2","w")))
Proof
  mp_tac current_prefix_direct_collision_probe >>
  mp_tac current_prefix_two_copies_collision_probe >>
  simp[current_prefix_functional_def] >> rpt strip_tac >>
  qexistsl_tac [`"src"`, `"v"`, `"w"`] >> simp[]
QED

(* Both original PHIs can collapse to one external source.  Their endpoint
   owners are the two distinct original output variables, not src's owner. *)
Theorem current_prefix_cleanup_shared_source_probe:
  simplify_current_phi
    (mk_inst 0 PHI [Label "left"; Var "src"; Label "right"; Var "src"] ["dst1"]) =
    mk_inst 0 ASSIGN [Var "src"] ["dst1"] /\
  simplify_current_phi
    (mk_inst 1 PHI [Label "left"; Var "src"; Label "right"; Var "src"] ["dst2"]) =
    mk_inst 1 ASSIGN [Var "src"] ["dst2"]
Proof
  simp[current_prefix_back_def, current_prefix_pull_def, mk_inst_def] >> EVAL_TAC
QED
