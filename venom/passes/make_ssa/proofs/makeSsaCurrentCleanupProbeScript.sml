(* Actual output-prefix consumer of the sequential cleanup runner.
   These are bounded checks, not a general MakeSSA simulation. *)
Theory makeSsaCurrentCleanupProbe
Ancestors
  makeSsaCurrentCleanupRuntime makeSsaCurrentAlignmentProbe
  makeSsaCurrentSimDefs venomExecSemantics venomState stateFrame

Definition current_probe_copies_def:
  current_probe_copies =
    TAKE 1 (DROP (LENGTH (collect_phis
      (EL 1 (FST (make_ssa_current_fn current_probe_supply
        current_probe_loop)).fn_blocks).bb_instructions))
      (EL 1 (FST (make_ssa_current_fn current_probe_supply
        current_probe_loop)).fn_blocks).bb_instructions)
End

Theorem current_probe_copies_shape:
  EVERY current_cleanup_shape current_probe_copies /\
  LENGTH current_probe_copies = 1
Proof
  EVAL_TAC >> simp[]
QED

Theorem current_probe_copies_run:
  !prev. prev = "E" \/ prev = "D" ==>
  current_copies_run current_probe_copies
    (update_var "formal_var_0" (if prev = "E" then 1w else 2w)
      (current_probe_incoming prev)) = OK (current_probe_ready prev)
Proof
  rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem current_probe_cleanup_execution:
  !prev. prev = "E" \/ prev = "D" ==>
  ?post.
    eval_phis (current_probe_incoming prev)
      (EL 1 (FST (make_ssa_current_fn current_probe_supply
        current_probe_loop)).fn_blocks).bb_instructions = OK post /\
    current_copies_run current_probe_copies post = OK (current_probe_ready prev) /\
    execution_frame (current_probe_ready prev) = execution_frame post /\
    lookup_var "formal_var_0" (current_probe_ready prev) =
      SOME (if prev = "E" then 1w else 2w) /\
    lookup_var "v" (current_probe_ready prev) =
      SOME (if prev = "E" then 1w else 2w) /\
    lookup_var "a" (current_probe_ready prev) = SOME 1w /\
    lookup_var "b" (current_probe_ready prev) = SOME 2w
Proof
  gen_tac >> disch_tac >>
  qexists_tac `update_var "formal_var_0" (if prev = "E" then 1w else 2w)
    (current_probe_incoming prev)` >>
  conj_tac >- metis_tac[current_probe_whole_prefix] >>
  conj_asm1_tac >- metis_tac[current_probe_copies_run] >>
  conj_tac
  >- metis_tac[current_copies_run_frame, current_probe_copies_shape] >>
  metis_tac[current_probe_ready_values]
QED
