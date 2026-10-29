(* Production-step regression probes (not the abstract reference interpreter).
 * Arbitrary instruction ids deliberately differ from original list indices. *)
Theory fmpIndexedProbe
Ancestors
  fmpReclaimProps

Definition indexed_probe_fn_def:
  indexed_probe_fn fn = fn with fn_blocks :=
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 70 DALLOCA [Lit 32w] ["old"];
       mk_inst 90 DALLOCA [Lit 32w] ["new"];
       mk_inst 100 ADD [Var "cap"; Lit 32w] ["derived"]] |>]
End
Definition indexed_probe_env_def:
  (indexed_probe_env:fmp_base_env) = FEMPTY |+ ("old",[70]) |+ ("new",[90])
End
Definition indexed_probe_state_def:
  indexed_probe_state = fmp_empty_reclaim_state with frs_stack := ["new";"old"]
End
Definition indexed_probe_live_def:
  indexed_probe_live vars = <| ds_inst := FEMPTY |+ (("entry",0),vars);
                              ds_boundary := FEMPTY |>
End

Theorem indexed_probe_reclaim_opcodes:
  MAP (\op. fmp_is_reclaim_point FEMPTY (mk_inst 1 op [] []))
    [DALLOCA; JMP; JNZ; DJMP; GETFMP; SETFMP; RETFMP; DRET; INVOKE] =
    [T;T;T;T;F;F;F;F;F]
Proof
  EVAL_TAC
QED

Theorem indexed_probe_invoke_summaries:
  let infos = FEMPTY |+ ("needs",<|fi_needs_fmp := T; fi_publishes_fmp := F|>)
                    |+ ("publishes",<|fi_needs_fmp := T; fi_publishes_fmp := T|>) in
  MAP (\name.
    (fmp_is_reclaim_point infos (mk_inst 1 INVOKE [Label name] []),
     fmp_clears_marks infos (mk_inst 1 INVOKE [Label name] [])))
     ["needs";"publishes";"unresolved"] = [(T,F);(T,T);(F,F)]
Proof
  EVAL_TAC
QED

Theorem indexed_probe_partial_pop:
  fmp_pop_at FEMPTY (indexed_probe_fn fn) (indexed_probe_live ["old"])
    indexed_probe_env ("entry",0) (mk_inst 400 JNZ [] []) indexed_probe_state =
      (["new"],["old"]) /\
  fmp_pop_at FEMPTY (indexed_probe_fn fn) (indexed_probe_live ["new"])
    indexed_probe_env ("entry",0) (mk_inst 400 JMP [] []) indexed_probe_state =
      ([],["new";"old"]) /\
  fmp_pop_at FEMPTY (indexed_probe_fn fn) (indexed_probe_live [])
    indexed_probe_env ("entry",0) (mk_inst 400 DJMP [] [])
      (indexed_probe_state with frs_stack := ["new";"unknown";"old"]) =
      (["new"],["unknown";"old"])
Proof
  EVAL_TAC
QED

Theorem indexed_probe_pop_before_push:
  fmp_reclaim_step FEMPTY (indexed_probe_fn fn) (indexed_probe_live [])
    indexed_probe_env ("entry",0) (mk_inst 400 DALLOCA [Lit 32w] ["fresh"])
      (SOME indexed_probe_state) =
      (SOME "old", SOME (fmp_empty_reclaim_state with frs_stack := ["fresh"]))
Proof
  EVAL_TAC
QED

Theorem indexed_probe_current_captures:
  fmp_pop_at FEMPTY (indexed_probe_fn fn) (indexed_probe_live ["derived"])
    indexed_probe_env ("entry",0) (mk_inst 400 JMP [] []) indexed_probe_state =
      (["new";"old"],[]) /\
  fmp_pop_at FEMPTY (indexed_probe_fn fn) (indexed_probe_live ["derived"])
    indexed_probe_env ("entry",0) (mk_inst 400 JMP [] [])
      (indexed_probe_state with frs_captures := ["cap"]) =
      ([],["new";"old"])
Proof
  EVAL_TAC
QED

Theorem indexed_probe_effects:
  fmp_apply_effect FEMPTY (mk_inst 400 GETFMP [] ["cap"])
    indexed_probe_state = (indexed_probe_state with frs_captures := ["cap"]) /\
  fmp_apply_effect FEMPTY (mk_inst 400 SETFMP [Var "old"] [])
    (indexed_probe_state with frs_captures := ["cap"]) = fmp_empty_reclaim_state /\
  fmp_apply_effect FEMPTY (mk_inst 400 RETFMP [Var "old"] [])
    indexed_probe_state = indexed_probe_state /\
  fmp_apply_effect FEMPTY (mk_inst 400 DRET [] [])
    indexed_probe_state = indexed_probe_state
Proof
  EVAL_TAC
QED

Theorem indexed_probe_invoke_steps:
  let infos = FEMPTY |+ ("needs",<|fi_needs_fmp := T; fi_publishes_fmp := F|>)
                    |+ ("publishes",<|fi_needs_fmp := T; fi_publishes_fmp := T|>) in
  fmp_reclaim_step infos (indexed_probe_fn fn) (indexed_probe_live [])
    indexed_probe_env ("entry",0) (mk_inst 400 INVOKE [Label "needs"] [])
      (SOME indexed_probe_state) = (SOME "old", SOME fmp_empty_reclaim_state) /\
  fmp_reclaim_step infos (indexed_probe_fn fn) (indexed_probe_live [])
    indexed_probe_env ("entry",0) (mk_inst 400 INVOKE [Label "publishes"] [])
      (SOME (indexed_probe_state with frs_captures := ["cap"])) =
      (SOME "old", SOME fmp_empty_reclaim_state) /\
  fmp_reclaim_step infos (indexed_probe_fn fn) (indexed_probe_live [])
    indexed_probe_env ("entry",0) (mk_inst 400 INVOKE [Label "unresolved"] [])
      (SOME indexed_probe_state) = (NONE, SOME indexed_probe_state)
Proof
  EVAL_TAC
QED

Theorem indexed_probe_join:
  (fmp_reclaim_join
    (indexed_probe_state with frs_captures := ["cap"])
    (indexed_probe_state with <|frs_stack := ["new";"other"];
                               frs_captures := ["cap2"]|>)).frs_stack = ["new"] /\
  MEM "cap" (fmp_reclaim_join
    (indexed_probe_state with frs_captures := ["cap"])
    (indexed_probe_state with frs_captures := ["cap2"])).frs_captures /\
  MEM "cap2" (fmp_reclaim_join
    (indexed_probe_state with frs_captures := ["cap"])
    (indexed_probe_state with frs_captures := ["cap2"])).frs_captures
Proof
  EVAL_TAC
QED

Theorem indexed_probe_unreachable:
  fmp_scan_candidates FEMPTY (indexed_probe_fn fn) (indexed_probe_live [])
    indexed_probe_env <|ds_inst := FEMPTY; ds_boundary := FEMPTY|> "entry"
      [mk_inst 400 JNZ [] []] 0 = []
Proof
  EVAL_TAC
QED

Theorem indexed_probe_original_indices:
  let states = <|ds_inst := FEMPTY |+ (("entry",0),SOME indexed_probe_state);
                ds_boundary := FEMPTY|> in
  fmp_scan_candidates FEMPTY (indexed_probe_fn fn) (indexed_probe_live [])
    indexed_probe_env states "entry" [mk_inst 400 JNZ [] []] 0 =
      [(("entry",0),"old")]
Proof
  EVAL_TAC
QED

Definition indexed_probe_linear_def:
  indexed_probe_linear fn = fn with fn_blocks :=
    [<|bb_label := "entry"; bb_instructions :=
      [mk_inst 70 DALLOCA [Lit 32w] ["old"];
       mk_inst 90 DALLOCA [Lit 32w] ["new"];
       mk_inst 400 JMP [Label "exit"] []]|>;
     <|bb_label := "exit"; bb_instructions := [mk_inst 500 STOP [] []]|>]
End

Theorem indexed_probe_production_analysis:
  OPTION_MAP (\states. fmp_collect_candidates FEMPTY (indexed_probe_linear fn)
    (liveness_analyze (indexed_probe_linear fn)) indexed_probe_env states
    (indexed_probe_linear fn).fn_blocks)
      (fmp_reclaim_states FEMPTY (indexed_probe_linear fn)) =
    SOME [(("entry",1),"old");(("entry",2),"new")]
Proof
  EVAL_TAC
QED

val _ = List.app (fn (name,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle dependency in " ^ name))
  (DB.thms "fmpIndexedProbe");
