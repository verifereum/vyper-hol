(* Supply expansion: structural and semantic segment interfaces. *)
Theory singleUseExpansionSupplySim
Ancestors
  singleUseExpansionSupplyProofs singleUseExpansionDefs irSupply
  stateFrame venomExecProps venomWf venomInst

(* Control indices are related separately by segment alignment. *)
Definition sue_state_rel_def:
  sue_state_rel protected st tt <=>
    execution_frame st = execution_frame tt /\
    st.vs_current_bb = tt.vs_current_bb /\
    st.vs_prev_bb = tt.vs_prev_bb /\
    (!v. v IN protected ==> FLOOKUP st.vs_vars v = FLOOKUP tt.vs_vars v)
End

Theorem sue_state_rel_refl[simp]:
  sue_state_rel protected st st
Proof
  simp[sue_state_rel_def]
QED

Theorem sue_state_rel_trans:
  sue_state_rel protected st tt /\ sue_state_rel protected tt uu ==>
  sue_state_rel protected st uu
Proof
  simp[sue_state_rel_def] >> metis_tac[]
QED

Theorem sue_state_rel_fresh_write:
  sue_state_rel protected st tt /\ ~(v IN protected) ==>
  sue_state_rel protected st (tt with vs_vars := tt.vs_vars |+ (v,w))
Proof
  simp[sue_state_rel_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

(* Shape plus the exact supply delta records allocation order without
   identifying it with the order in which the prefix executes. *)
Theorem sue_expand_ops_supply_prefix:
  !dfg inst s ops k assigns new_ops s'.
    ir_supply_inst_ok s /\
    sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') ==>
    EVERY (\a. a.inst_opcode = ASSIGN /\ LENGTH a.inst_outputs = 1) assigns /\
    s'.irs_used_vars = FLAT (MAP (\a. a.inst_outputs) assigns) ++
                       s.irs_used_vars /\
    ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs) assigns)) /\
    EVERY (\v. ~MEM v s.irs_used_vars)
          (FLAT (MAP (\a. a.inst_outputs) assigns))
Proof
  Induct_on `ops`
  >- (rpt strip_tac >> gvs[sue_expand_ops_supply_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `sue_expand_ops_supply dfg inst s ops (k + 1)` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s ops (k + 1) =
           (more_assigns,more_ops,s1)` >>
  `sue_supply_extends s s1` by
    metis_tac[sue_expand_ops_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `~sue_needs_assign dfg inst k`
  >- gvs[sue_expand_ops_supply_def] >>
  Cases_on `h`
  >- (Cases_on `sue_alloc_assign_supply s1 (Lit c)` >>
      PairCases_on `r` >>
      drule_all sue_alloc_assign_supply_contract >> strip_tac >>
      drule sue_alloc_assign_supply_shape >> strip_tac >>
      gvs[Once sue_expand_ops_supply_def] >>
      metis_tac[listTheory.MEM_REVERSE, listTheory.MEM_APPEND])
  >- (Cases_on `LENGTH (dfg_get_uses dfg s'') = 1 /\
                 sue_count_remaining (Var s'') ops = 0`
      >- gvs[sue_expand_ops_supply_def] >>
      Cases_on `sue_alloc_assign_supply s1 (Var s'')` >>
      PairCases_on `r` >>
      drule_all sue_alloc_assign_supply_contract >> strip_tac >>
      drule sue_alloc_assign_supply_shape >> strip_tac >>
      gvs[Once sue_expand_ops_supply_def] >>
      metis_tac[listTheory.MEM_REVERSE, listTheory.MEM_APPEND]) >>
  gvs[sue_expand_ops_supply_def]
QED

Theorem sue_expand_inst_supply_skip:
  sue_should_skip inst.inst_opcode ==>
  sue_expand_inst_supply dfg s inst = ([inst],s)
Proof
  simp[sue_expand_inst_supply_def]
QED

Theorem sue_expand_inst_supply_segment:
  ir_supply_inst_ok s /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  ?assigns new_ops.
    out = assigns ++ [inst with inst_operands := new_ops] /\
    EVERY (\a. a.inst_opcode = ASSIGN /\ LENGTH a.inst_outputs = 1) assigns /\
    s'.irs_used_vars = FLAT (MAP (\a. a.inst_outputs) assigns) ++ s.irs_used_vars /\
    ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs) assigns)) /\
    EVERY (\v. ~MEM v s.irs_used_vars)
          (FLAT (MAP (\a. a.inst_outputs) assigns))
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- (gvs[sue_expand_inst_supply_def] >>
      qexists_tac `inst.inst_operands` >> simp[]) >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >>
  gvs[sue_expand_inst_supply_def] >>
  drule_all sue_expand_ops_supply_prefix >> strip_tac >>
  qexists_tac `r0` >> simp[]
QED

Theorem sue_expand_inst_supply_nonempty:
  sue_expand_inst_supply dfg s inst = (out,s') ==> out <> []
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def]
QED

Theorem sue_expand_inst_supply_last:
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  (LAST out).inst_opcode = inst.inst_opcode /\
  (LAST out).inst_outputs = inst.inst_outputs /\
  (LAST out).inst_id = inst.inst_id
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def]
QED

(* This interface is independent of the tail and of supply well-formedness. *)
Theorem sue_expand_ops_supply_preserved_head:
  ~sue_needs_assign dfg inst k /\
  sue_expand_ops_supply dfg inst s (op::ops) k = (assigns,new_ops,s') ==>
  ?rest. new_ops = op::rest /\
    sue_expand_ops_supply dfg inst s ops (k + 1) = (assigns,rest,s')
Proof
  strip_tac >>
  Cases_on `sue_expand_ops_supply dfg inst s ops (k + 1)` >>
  PairCases_on `r` >> gvs[sue_expand_ops_supply_def]
QED

Theorem sue_expand_ops_supply_structural_head:
  (inst.inst_opcode = LOG \/ inst.inst_opcode = DRET) /\
  inst.inst_operands = op::ops /\
  sue_expand_ops_supply dfg inst s inst.inst_operands 0 =
    (assigns,new_ops,s') ==>
  ?rest. new_ops = op::rest /\
    sue_expand_ops_supply dfg inst s ops 1 = (assigns,rest,s')
Proof
  strip_tac >>
  `~sue_needs_assign dfg inst 0` by simp[sue_needs_assign_def] >>
  gvs[] >> drule_all sue_expand_ops_supply_preserved_head >> simp[]
QED

Theorem sue_expand_inst_supply_labels:
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  MAP sue_operand_label (LAST out).inst_operands =
  MAP sue_operand_label inst.inst_operands
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  metis_tac[sue_expand_ops_supply_operand_labels]
QED

(* Checked examples intentionally include no supply distinctness assumption. *)
Theorem sue_supply_two_literals_probe[local]:
  MAP (\i. i.inst_operands)
    (FST (sue_expand_inst_supply dfg
      <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
         irs_used_inst_ids := []; irs_used_vars := []; irs_used_labels := [] |>
      <| inst_id := 1; inst_opcode := ADD;
         inst_operands := [Lit 3w; Lit 4w]; inst_outputs := ["out"] |>)) =
    [[Lit 3w]; [Lit 4w]; [Var "formal_var_1"; Var "formal_var_0"]]
Proof
  EVAL_TAC
QED

Theorem sue_supply_phi_probe[local]:
  sue_expand_inst_supply dfg s
    <| inst_id := 1; inst_opcode := PHI;
       inst_operands := [Label "pred"; Var "x"]; inst_outputs := ["y"] |> =
  ([<| inst_id := 1; inst_opcode := PHI;
       inst_operands := [Label "pred"; Var "x"]; inst_outputs := ["y"] |>],s)
Proof
  simp[sue_expand_inst_supply_def, sue_should_skip_def]
QED

Theorem sue_supply_ignored_operand_probe[local]:
  MAP (\i. i.inst_operands)
    (FST (sue_expand_inst_supply
      (dfg_empty with dfg_uses := FEMPTY |+ ("x",
        [<| inst_id := 1; inst_opcode := CALLER;
            inst_operands := [Var "x"]; inst_outputs := ["y"] |>;
         <| inst_id := 2; inst_opcode := CALLER;
            inst_operands := [Var "x"]; inst_outputs := ["z"] |>]))
      <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
         irs_used_inst_ids := [1;2]; irs_used_vars := ["x";"y";"z"];
         irs_used_labels := [] |>
      <| inst_id := 1; inst_opcode := CALLER;
         inst_operands := [Var "x"]; inst_outputs := ["y"] |>)) =
    [[Var "x"]; [Var "formal_var_0"]]
Proof
  EVAL_TAC
QED

Theorem sue_supply_repeated_variable_probe[local]:
  MAP (\i. i.inst_operands)
    (FST (sue_expand_inst_supply
      (dfg_empty with dfg_uses := FEMPTY |+ ("x",
        [<| inst_id := 1; inst_opcode := ADD;
            inst_operands := [Var "x"; Var "x"]; inst_outputs := ["y"] |>;
         <| inst_id := 2; inst_opcode := STOP;
            inst_operands := [Var "x"]; inst_outputs := [] |>]))
      <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
         irs_used_inst_ids := [1;2]; irs_used_vars := ["x";"y"];
         irs_used_labels := [] |>
      <| inst_id := 1; inst_opcode := ADD;
         inst_operands := [Var "x"; Var "x"]; inst_outputs := ["y"] |>)) =
    [[Var "x"]; [Var "x"]; [Var "formal_var_1"; Var "formal_var_0"]]
Proof
  EVAL_TAC
QED

Theorem sue_expand_inst_supply_structural_head:
  (inst.inst_opcode = LOG \/ inst.inst_opcode = DRET) /\
  inst.inst_operands = op::ops /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  ?rest. (LAST out).inst_operands = op::rest
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  `~sue_needs_assign dfg inst 0` by simp[sue_needs_assign_def] >>
  drule_all sue_expand_ops_supply_preserved_head >>
  strip_tac >> simp[]
QED
