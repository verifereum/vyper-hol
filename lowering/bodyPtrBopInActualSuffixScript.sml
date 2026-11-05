Theory bodyPtrBopInActualSuffix
Ancestors
  bodyPtrBopInUnit bodyPtrBopInUnitBody bodyPtrBopInLocalSuffix
  bodyPtrBopInCompareBoundary fragExec finite_map

(* Compiler boundary fixtures name the real block prefix and local bindings. *)
Definition actual_suffix_start_def:
  actual_suffix_start sel = (equality_bodies_state sel) with
    <| cs_next_var := 14; cs_next_id := 23;
       cs_current_insts := FILTER (\i. i.inst_id < 23)
         (equality_bodies_state sel).cs_current_insts |>
End

Definition actual_suffix_end_def:
  actual_suffix_end sel = (equality_bodies_state sel) with
    <| cs_next_var := 15; cs_next_id := 24;
       cs_current_insts := FILTER (\i. i.inst_id <= 23)
         (equality_bodies_state sel).cs_current_insts |>
End

Theorem actual_membership_suffix:
  compile_expr (cenv with ce_vars := FEMPTY |+
      ("x",PtrVar (Var "%10") 64) |+ ("y",PtrVar (Var "%13") 64))
    (BaseT BoolT) local_membership_fixture (actual_suffix_start sel) =
    (StackValue (BaseT BoolT) (Var "%14"),actual_suffix_end sel)
Proof
  EVAL_TAC
QED

Theorem actual_membership_contained:
  fn_has_code (actual_suffix_start sel) (actual_suffix_end sel)
    (equality_runtime_function sel)
Proof
  rewrite_tac[fn_has_code_def] >> conj_tac
  >- (EVAL_TAC >> simp[]) >>
  qexists_tac `THE (lookup_block "fn_probe" (equality_runtime_function sel).fn_blocks)` >>
  EVAL_TAC
QED

Theorem actual_suffix_last:
  LAST (actual_suffix_end sel).cs_current_insts =
    <| inst_id := 23; inst_opcode := EQ;
       inst_operands := [Var "%10"; Var "%13"]; inst_outputs := ["%14"] |>
Proof
  EVAL_TAC
QED

Theorem actual_suffix_access_rejected:
  FLOOKUP G "%10" = SOME (64,64) /\
  FLOOKUP G "%13" = SOME (128,64) ==>
  ~access_ok lo G (equality_runtime_function sel)
    (LAST (actual_suffix_end sel).cs_current_insts) s
Proof
  strip_tac >> rewrite_tac[actual_suffix_last] >>
  irule different_sites_comparison_access_rejected >> simp[] >>
  metis_tac[]
QED
