Theory fnPlanLineageInventory
Ancestors
  fnPlanLineageReplay stackPlanGen stackModel list rich_list

(* Stack-only comparison; state-field agreement is a separate obligation. *)
Definition bottom_dead_equiv_def:
  bottom_dead_equiv xs ys <=>
    ?m n core.
      xs = REPLICATE m dead_stack_marker ++ core /\
      ys = REPLICATE n dead_stack_marker ++ core /\
      ~MEM dead_stack_marker core
End

Theorem bottom_dead_equiv_refl:
  !xs. ~MEM dead_stack_marker xs ==> bottom_dead_equiv xs xs
Proof
  rpt strip_tac >> simp[bottom_dead_equiv_def] >>
  qexistsl_tac [`0`, `0`, `xs`] >> simp[]
QED

Theorem bottom_dead_equiv_sym:
  !xs ys. bottom_dead_equiv xs ys ==> bottom_dead_equiv ys xs
Proof
  simp[bottom_dead_equiv_def] >> metis_tac[]
QED

Theorem bottom_dead_equiv_depth:
  !xs ys op. bottom_dead_equiv xs ys /\ op <> dead_stack_marker ==>
    stack_get_depth op xs = stack_get_depth op ys
Proof
  rpt gen_tac >> simp[bottom_dead_equiv_def] >> rpt strip_tac >>
  gvs[stack_get_depth_bottom_dead]
QED

Theorem bottom_dead_equiv_below_all_live:
  !xs ys op inputs.
    bottom_dead_equiv xs ys /\ op <> dead_stack_marker ==>
    below_all_live op inputs xs = below_all_live op inputs ys
Proof
  rpt strip_tac >>
  `stack_get_depth op xs = stack_get_depth op ys` by
    metis_tac[bottom_dead_equiv_depth] >>
  simp[below_all_live_def] >>
  Cases_on `stack_get_depth op ys` >> simp[] >>
  `!v. stack_get_depth (Var v) xs = stack_get_depth (Var v) ys` by
    (gen_tac >> irule bottom_dead_equiv_depth >>
     simp[dead_stack_marker_def]) >>
  simp[]
QED

(* Negative interface probe: coverage cannot replace physical swap bounds.
   This is not a counterexample to lineage_state_block_plan. *)
Theorem short_stack_swap_prefix_probe[local]:
  stack_swap 2 [dead_stack_marker; Var "a"] <>
    dead_stack_marker :: stack_swap 2 [Var "a"]
Proof
  EVAL_TAC
QED

Theorem bottom_dead_equiv_physical:
  !xs ys ops.
    bottom_dead_equiv xs ys /\ ~MEM dead_stack_marker ops ==>
    FILTER (\op. IS_SOME (stack_get_depth op xs)) ops =
    FILTER (\op. IS_SOME (stack_get_depth op ys)) ops
Proof
  Induct_on `ops` >> simp[] >> rpt strip_tac >>
  `stack_get_depth h xs = stack_get_depth h ys` by
    metis_tac[bottom_dead_equiv_depth] >>
  first_x_assum drule >> simp[] >> disch_then SUBST1_TAC >> simp[]
QED

(* Mixed stack/spill inventory: only the spilled target is restored, and the
   dead bottom extension does not change emitted code. *)
Theorem mixed_restore_prefix_probe[local]:
  FST (restore_spilled_plan [Var "a"; Var "b"]
    ((init_plan_state 0) with <|
      ps_stack := [Var "a"];
      ps_spilled := FEMPTY |+ (Var "b", 0) |>)) = [SORestore 0] /\
  FST (restore_spilled_plan [Var "a"; Var "b"]
    ((init_plan_state 0) with <|
      ps_stack := [dead_stack_marker; Var "a"];
      ps_spilled := FEMPTY |+ (Var "b", 0) |>)) = [SORestore 0]
Proof
  EVAL_TAC
QED
