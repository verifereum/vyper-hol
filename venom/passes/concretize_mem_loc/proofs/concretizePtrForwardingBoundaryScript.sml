Theory concretizePtrForwardingBoundary
Ancestors
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape contextCodegenRel
  concretizeMemLocDefs passSharedDefs venomInst list finite_map

Theorem ptr_forwarding_step_back:
  step_back_assign i op = SOME op' ==>
  step_back_assign (concretize_inst_with_positions p i) op = SOME op'
Proof
  Cases_on `i.inst_opcode = ALLOCA`
  >- (Cases_on `i.inst_outputs` >>
      simp[concretize_inst_with_positions_def] >>
      rename1 `i.inst_outputs = out::rest` >>
      Cases_on `rest` >> simp[concretize_inst_with_positions_def] >>
      Cases_on `FLOOKUP p (Allocation i.inst_id)` >>
      Cases_on `op` >>
      gvs[step_back_assign_def, mk_assign_inst_def, mk_nop_inst_def,
          AllCaseEqs()]) >>
  simp[concretize_positions_unchanged]
QED

Theorem ptr_forwarding_same_after_rewrite:
  !xs x y.
  EVERY (\i. i.inst_opcode = NOP ==> i.inst_outputs = []) xs /\
  same_after_assigns xs x y ==>
  same_after_assigns
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions p) xs)) x y
Proof
  Induct_on `xs` >- simp[same_after_assigns_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `x = y`
  >- (gvs[] >> Cases_on `FILTER (\i. i.inst_opcode <> NOP)
         (MAP (concretize_inst_with_positions p) (h::xs))` >>
      simp[same_after_assigns_def]) >>
  gvs[same_after_assigns_def] >>
  Cases_on `step_back_assign h x` >> gvs[] >>
  Cases_on `step_back_assign h y` >> gvs[] >>
  imp_res_tac ptr_forwarding_step_back >>
  Cases_on `(concretize_inst_with_positions p h).inst_opcode = NOP`
  >- (Cases_on `h.inst_opcode = ALLOCA`
      >- (Cases_on `x` >> Cases_on `y` >>
          gvs[step_back_assign_def, AllCaseEqs()]) >>
      gvs[concretize_positions_unchanged] >>
      Cases_on `x` >> Cases_on `y` >>
      gvs[step_back_assign_def]) >>
  simp[same_after_assigns_def]
QED

Theorem ptr_forwarding_assign_interval:
  EVERY (\i. i.inst_opcode = ASSIGN) xs ==>
  FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions p) xs) = xs
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >>
  simp[concretize_positions_unchanged]
QED

(* Backward order: the latest copy causes two unequal operands to meet;
   an earlier allocation must then be irrelevant, present or missing. *)
Theorem ptr_forwarding_alloca_prefix_eval:
  same_after_assigns
    [<|inst_id := 2; inst_opcode := ASSIGN;
        inst_operands := [Var "a"]; inst_outputs := ["b"]|>;
     <|inst_id := 1; inst_opcode := ALLOCA;
        inst_operands := [Lit 32w]; inst_outputs := ["a"]|>]
    (Var "b") (Var "a") /\
  same_after_assigns
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions (FEMPTY |+ (Allocation 1,64)))
        [<|inst_id := 2; inst_opcode := ASSIGN;
            inst_operands := [Var "a"]; inst_outputs := ["b"]|>;
         <|inst_id := 1; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["a"]|>]))
    (Var "b") (Var "a") /\
  same_after_assigns
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions FEMPTY)
        [<|inst_id := 2; inst_opcode := ASSIGN;
            inst_operands := [Var "a"]; inst_outputs := ["b"]|>;
         <|inst_id := 1; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["a"]|>]))
    (Var "b") (Var "a")
Proof
  EVAL_TAC
QED

Theorem ptr_forwarding_nop_prefix_eval:
  same_after_assigns
    [<|inst_id := 3; inst_opcode := NOP;
        inst_operands := []; inst_outputs := []|>;
     <|inst_id := 2; inst_opcode := ASSIGN;
        inst_operands := [Var "a"]; inst_outputs := ["b"]|>]
    (Var "b") (Var "a") /\
  same_after_assigns
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions FEMPTY)
        [<|inst_id := 3; inst_opcode := NOP;
            inst_operands := []; inst_outputs := []|>;
         <|inst_id := 2; inst_opcode := ASSIGN;
            inst_operands := [Var "a"]; inst_outputs := ["b"]|>]))
    (Var "b") (Var "a")
Proof
  EVAL_TAC
QED

Theorem ptr_forwarding_overwritten_alloca_eval:
  same_after_assigns
    [<|inst_id := 3; inst_opcode := ASSIGN;
        inst_operands := [Var "a"]; inst_outputs := ["b"]|>;
     <|inst_id := 2; inst_opcode := ASSIGN;
        inst_operands := [Lit 0w]; inst_outputs := ["a"]|>;
     <|inst_id := 1; inst_opcode := ALLOCA;
        inst_operands := [Lit 32w]; inst_outputs := ["a"]|>]
    (Var "b") (Lit 0w) /\
  same_after_assigns
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions (FEMPTY |+ (Allocation 1,64)))
        [<|inst_id := 3; inst_opcode := ASSIGN;
            inst_operands := [Var "a"]; inst_outputs := ["b"]|>;
         <|inst_id := 2; inst_opcode := ASSIGN;
            inst_operands := [Lit 0w]; inst_outputs := ["a"]|>;
         <|inst_id := 1; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["a"]|>]))
    (Var "b") (Lit 0w)
Proof
  EVAL_TAC
QED
