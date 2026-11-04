(* Counterexamples to algebraic_opt's obligations as stated: inserted
   instructions reuse the rewritten instruction's inst_id, the fresh variable
   ao_<id>_<suffix> may already be defined, and the transformed run defines
   that variable, which state_equiv {} observes. *)
Theory aoCounterex
Ancestors
  algebraicOptDefs venomWf venomExecSemantics stateEquiv venomState venomInst
Libs
  wordsLib

Definition wi_def:
  wi id opc ops outs =
    <| inst_id := id; inst_opcode := opc;
       inst_operands := ops; inst_outputs := outs |>
End

Definition wb_def:
  wb lbl insts = <| bb_label := lbl; bb_instructions := insts |>
End

Definition ao_fn_def:
  ao_fn pre =
    mk_raw_function "f"
      [wb "a" (pre ++ [wi 0 EQ [Var "x"; Lit (0w - 1w)] ["z"];
                       wi 1 STOP [] []])]
End

Theorem ao_wf_witness:
  wf_function (ao_fn []) /\ ~wf_function (ao_transform_function (ao_fn []))
Proof
  EVAL_TAC
QED

Theorem ao_ssa_witness:
  ssa_form (ao_fn [wi 2 ADD [Var "x"; Var "y"] ["ao_0_not"]]) /\
  ~ssa_form (ao_transform_function
               (ao_fn [wi 2 ADD [Var "x"; Var "y"] ["ao_0_not"]]))
Proof
  EVAL_TAC
QED

Definition ao_state_def:
  ao_state = init_venom_state "a" with vs_vars := FEMPTY |+ ("x", 5w)
End

Theorem ao_run_orig:
  case run_blocks 5 ARB (ao_fn []) ao_state of
    Halt s1 => lookup_var "ao_0_not" s1 = NONE
  | _ => F
Proof
  EVAL_TAC
QED

Theorem ao_run_new:
  case run_blocks 5 ARB (ao_transform_function (ao_fn [])) ao_state of
    Halt s2 => IS_SOME (lookup_var "ao_0_not" s2)
  | _ => F
Proof
  EVAL_TAC
QED

Theorem ao_correct_witness:
  ~lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
     (run_blocks 5 ARB (ao_fn []) ao_state)
     (run_blocks 5 ARB (ao_transform_function (ao_fn [])) ao_state)
Proof
  assume_tac ao_run_orig >> assume_tac ao_run_new >>
  Cases_on `run_blocks 5 ARB (ao_fn []) ao_state` >> gvs[] >>
  Cases_on `run_blocks 5 ARB (ao_transform_function (ao_fn [])) ao_state` >>
  gvs[] >> strip_tac >>
  rpt (qpat_x_assum `Halt _ = _` (assume_tac o SYM)) >>
  gvs[lift_result_def, execution_equiv_def] >>
  first_x_assum (qspec_then `"ao_0_not"` mp_tac) >> gvs[]
QED
