(* Production-fuel diagnostics only: no universal bound is inferred. *)
Theory concretizeAnalysisFuelProbe
Ancestors concretizeAnalysisBoundary concretizeAnalysisBoundaryProbe venomWf
Libs wordsLib

Definition fuel_probe_ml_def:
  fuel_probe_ml fn bp =
    ml_iterate_fuel (concretize_memloc_fuel fn) bp (K [])
      (\a. if get_alloca_size fn a = 0 then NONE
           else SOME (get_alloca_size fn a)) []
      (cfg_analyze fn) fn FEMPTY FEMPTY
End

Theorem fuel_probe_loop_ssa:
  ssa_form boundary_loop
Proof
  EVAL_TAC
QED

Theorem fuel_probe_late_ssa:
  ssa_form boundary_late
Proof
  EVAL_TAC
QED

(* Existing fixtures expose two distinct effects: the loop's offsets widen
   to NONE, while the branch fixture needs an additional traversal. *)
Theorem fuel_probe_bp_fixed:
  bp_one_pass boundary_loop (cfg_analyze boundary_loop).cfg_dfs_pre
    (boundary_bp boundary_loop) = (F, boundary_bp boundary_loop) /\
  bp_one_pass boundary_late (cfg_analyze boundary_late).cfg_dfs_pre
    (boundary_bp boundary_late) = (F, boundary_bp boundary_late)
Proof
  simp[boundary_loop_base, boundary_late_base]
QED

Theorem fuel_probe_loop_ml_fixed:
  ml_one_pass (boundary_bp boundary_loop) (K [])
    (\a. if get_alloca_size boundary_loop a = 0 then NONE
         else SOME (get_alloca_size boundary_loop a)) []
    (cfg_analyze boundary_loop) boundary_loop
    (FST (fuel_probe_ml boundary_loop (boundary_bp boundary_loop)))
    (SND (fuel_probe_ml boundary_loop (boundary_bp boundary_loop))) =
    (F, FST (fuel_probe_ml boundary_loop (boundary_bp boundary_loop)),
        SND (fuel_probe_ml boundary_loop (boundary_bp boundary_loop)))
Proof
  rewrite_tac[boundary_loop_bp] >> EVAL_TAC >>
  simp[finite_mapTheory.FUPDATE_EQ, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem fuel_probe_late_ml_fixed:
  ml_one_pass (boundary_bp boundary_late) (K [])
    (\a. if get_alloca_size boundary_late a = 0 then NONE
         else SOME (get_alloca_size boundary_late a)) []
    (cfg_analyze boundary_late) boundary_late
    (FST (fuel_probe_ml boundary_late (boundary_bp boundary_late)))
    (SND (fuel_probe_ml boundary_late (boundary_bp boundary_late))) =
    (F, FST (fuel_probe_ml boundary_late (boundary_bp boundary_late)),
        SND (fuel_probe_ml boundary_late (boundary_bp boundary_late)))
Proof
  rewrite_tac[boundary_late_bp] >> EVAL_TAC >>
  simp[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Both operands of the last ADD/SUB become tracked, even though p reaches
   the join through a PHI and q through a different branch.  This is a
   transfer-guard diagnostic, not a claim of pointer-discipline validity. *)
Definition fuel_diamond_def:
  fuel_diamond = mk_raw_function "main"
    [<| bb_label := "main"; bb_instructions :=
       [mk_inst 1 ALLOCA [Lit (32w:256 word)] ["p"];
        mk_inst 2 JNZ [Lit 1w; Label "left"; Label "right"] []] |>;
     <| bb_label := "left"; bb_instructions :=
       [mk_inst 3 ASSIGN [Var "p"] ["x"];
        mk_inst 4 JMP [Label "join"] []] |>;
     <| bb_label := "right"; bb_instructions :=
       [mk_inst 5 ALLOCA [Lit 32w] ["q"];
        mk_inst 6 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
       [mk_inst 7 PHI [Label "left"; Var "x"; Label "right"; Var "q"] ["v"];
        mk_inst 8 ADD [Var "v"; Var "q"] ["a"];
        mk_inst 9 SUB [Var "v"; Var "q"] ["b"];
        mk_inst 10 STOP [] []] |>]
End

Theorem fuel_diamond_ssa:
  ssa_form fuel_diamond
Proof
  EVAL_TAC
QED

Theorem fuel_diamond_guard:
  bp_get_ptrs (boundary_bp fuel_diamond) "a" = [] /\
  bp_get_ptrs (boundary_bp fuel_diamond) "b" = [] /\
  bp_bases (boundary_bp fuel_diamond) "v" =
    {Allocation 1; Allocation 5}
Proof
  rewrite_tac[boundary_bp_def, bp_bases_def] >> EVAL_TAC >> simp[]
QED

Theorem fuel_diamond_bp_fixed:
  bp_one_pass fuel_diamond (cfg_analyze fuel_diamond).cfg_dfs_pre
    (boundary_bp fuel_diamond) = (F, boundary_bp fuel_diamond)
Proof
  rewrite_tac[boundary_bp_def] >> EVAL_TAC >>
  simp[finite_mapTheory.FUPDATE_EQ, finite_mapTheory.FUPDATE_COMMUTES]
QED

(* A concrete path is enough to reject dominance; no CFG traversal order is
   a substitute for this availability condition. *)
Theorem fuel_late_path_bypasses_definition:
  is_fn_path boundary_late ["entry"; "use"] /\
  fn_entry_label boundary_late = SOME "entry" /\
  ~MEM "def" ["entry"; "use"]
Proof
  EVAL_TAC >> qexists `HD boundary_late.fn_blocks` >> EVAL_TAC
QED

Theorem fuel_late_not_dominates:
  ~fn_dominates boundary_late "def" "use"
Proof
  simp[fn_dominates_def] >> disj2_tac >>
  qexists `["entry"; "use"]` >>
  simp[fuel_late_path_bypasses_definition]
QED

Theorem fuel_late_unavailable:
  ~def_available_at boundary_late (EL 1 boundary_late.fn_blocks)
    (SOME (mk_inst 5 ASSIGN [Var "x"] ["y"])) "x"
Proof
  strip_tac >> gvs[def_available_at_def] >>
  mp_tac fuel_late_not_dominates >>
  gvs[boundary_late_def, venomInstTheory.mk_raw_function_def,
      venomInstTheory.mk_inst_def]
QED
