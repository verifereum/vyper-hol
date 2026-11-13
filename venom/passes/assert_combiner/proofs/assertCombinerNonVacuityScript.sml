(*
 * Assert Combiner — a concrete merge across a GAS read.
 *
 *   a = ISZERO 0; ASSERT a; g = GAS; b = ISZERO 1; ASSERT b; STOP
 *
 * satisfies the correctness theorem's premises, and the transform merges
 * the two asserts: the first becomes a NOP, the GAS read stays where it
 * was, and the second checks ISZERO (OR 0 1) through fresh supply names.
 *)
Theory assertCombinerNonVacuity
Ancestors
  assertCombinerDefs irSupply venomFnScheduleRunner venomWf venomInst list
Libs
  wordsLib

Definition ac_witness_fn_def:
  ac_witness_fn = mk_raw_function "witness"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 ISZERO [Lit 0w] ["a"];
           mk_inst 1 ASSERT [Var "a"] [];
           mk_inst 2 GAS [] ["g"];
           mk_inst 3 ISZERO [Lit 1w] ["b"];
           mk_inst 4 ASSERT [Var "b"] [];
           mk_inst 5 STOP [] []] |>]
End

Definition ac_witness_supply_def:
  ac_witness_supply = <|
    irs_next_inst := 6; irs_next_var := 0; irs_next_label := 0;
    irs_used_inst_ids := [0; 1; 2; 3; 4; 5];
    irs_used_vars := ["a"; "g"; "b"];
    irs_used_labels := ["witness"; "entry"] |>
End

Theorem ac_witness_premises:
  wf_function ac_witness_fn /\ wf_ssa ac_witness_fn /\
  fn_inst_wf ac_witness_fn /\
  ir_supply_inst_ok ac_witness_supply /\
  ir_supply_covers_fn ac_witness_supply ac_witness_fn /\
  (!inst l. MEM inst (fn_insts ac_witness_fn) /\
            MEM (Label l) inst.inst_operands ==> F)
Proof
  EVAL_TAC >> rw[] >> gvs[]
  >~ [`MEM "a" _.inst_outputs`]
  >- (qexists_tac `<|inst_id := 0; inst_opcode := ISZERO;
                    inst_operands := [Lit 0w]; inst_outputs := ["a"]|>` >>
      simp[] >> rpt strip_tac >- (Cases_on `path` >> gvs[]) >>
      qexistsl [`0`, `1`] >> EVAL_TAC)
  >~ [`MEM "b" _.inst_outputs`]
  >- (qexists_tac `<|inst_id := 3; inst_opcode := ISZERO;
                    inst_operands := [Lit 1w]; inst_outputs := ["b"]|>` >>
      simp[] >> rpt strip_tac >- (Cases_on `path` >> gvs[]) >>
      qexistsl [`3`, `4`] >> EVAL_TAC)
  >> CCONTR_TAC >> gvs[]
QED

Theorem ac_witness_merges_around_gas:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (HD (FST (ac_transform_function ac_witness_supply ac_witness_fn)).fn_blocks)
      .bb_instructions =
  [(ISZERO, [Lit 0w]); (NOP, []); (GAS, []); (ISZERO, [Lit 1w]);
   (OR, [Lit 0w; Lit 1w]); (ISZERO, [Var "formal_var_0"]);
   (ASSERT, [Var "formal_var_1"]); (STOP, [])]
Proof
  EVAL_TAC
QED
