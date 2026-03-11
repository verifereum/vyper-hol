(*
 * Counterexample: analysis_inst_sim_block_sim_proof is FALSE as stated.
 *
 * The theorem quantifies over all states s, including arbitrary vs_inst_idx.
 * With 1:N instruction expansion, at vs_inst_idx past the original block
 * but within the expanded block, the original returns Error while the
 * expanded block reaches a terminator and returns Halt.
 *
 * This also falsifies df_analysis_pass_correct_{,sound_,widen_sound_}proof
 * since run_function passes s (with arbitrary vs_inst_idx) to run_block.
 *
 * Tightest fix: add s.vs_inst_idx = 0 to the conclusion of all four.
 *)

Theory counterexample
Ancestors
  analysisSimDefs execEquivParamDefs execEquivParamProofs
  passSimulationDefs stateEquiv stateEquivProps
  venomExecSemantics venomInst venomState
Libs
  listTheory finite_mapTheory

(* === Concrete definitions === *)

Definition good_add_def:
  good_add = <| inst_opcode := ADD;
                inst_operands := [Lit 1w; Lit 2w];
                inst_outputs := ["x"] |>
End

Definition nop_add_def:
  nop_add = <| inst_opcode := ADD;
               inst_operands := [Lit 0w; Lit 0w];
               inst_outputs := ["y"] |>
End

Definition stop_inst_def:
  stop_inst = <| inst_opcode := STOP;
                 inst_operands := [];
                 inst_outputs := [] |>
End

Definition cex_bb_def:
  cex_bb = <| bb_instructions := [good_add; stop_inst];
              bb_label := "test" |>
End

(* Transform: non-term non-INVOKE expands to [inst; nop_add; nop_add] *)
Definition cex_f_def:
  cex_f (v:'a) (inst:instruction) =
    if is_terminator inst.inst_opcode then [inst]
    else if inst.inst_opcode = INVOKE then [inst]
    else [inst; nop_add; nop_add]
End

(* Expanded block *)
Definition cex_bb'_def:
  cex_bb' = <| bb_instructions := [good_add; nop_add; nop_add; stop_inst];
               bb_label := "test" |>
End

(* === The counterexample at vs_inst_idx = 2 === *)

(* Original: idx=2 is out of bounds for [good_add; stop_inst] *)
Theorem cex_original:
  !fuel ctx s.
    run_block fuel ctx cex_bb (s with vs_inst_idx := 2) =
    Error "block not terminated"
Proof
  simp[cex_bb_def, good_add_def, stop_inst_def] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def]
QED

(* cex_bb' is the FLAT expansion of cex_bb under cex_f *)
Theorem cex_expansion:
  cex_bb' =
    cex_bb with bb_instructions :=
      FLAT (MAPi (\idx inst. cex_f ARB inst) cex_bb.bb_instructions)
Proof
  EVAL_TAC
QED

(* Expanded: idx=2 processes nop_add (OK), then idx=3 processes STOP (Halt) *)
Theorem cex_expanded:
  !fuel ctx s.
    run_block fuel ctx cex_bb' (s with vs_inst_idx := 2) =
    Halt (s with <| vs_vars := s.vs_vars |+ ("y", 0w + 0w);
                    vs_inst_idx := 3; vs_halted := T |>)
Proof
  rpt gen_tac >>
  simp[cex_bb'_def, good_add_def, nop_add_def, stop_inst_def] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, exec_pure2_def, eval_operand_def,
       is_terminator_def, update_var_def] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, is_terminator_def, halt_state_def]
QED

(* Error vs Halt: never lift_result related *)
Theorem cex_conclusion_false:
  !R_ok R_term s.
    ~lift_result R_ok R_term (Error "block not terminated") (Halt s)
Proof
  simp[lift_result_def]
QED

(* === Full negation: analysis_inst_sim_block_sim_proof is false === *)

Theorem analysis_inst_sim_block_sim_is_false:
  ~(!(R_ok : venom_state -> venom_state -> bool)
     (R_term : venom_state -> venom_state -> bool)
     (bottom : 'a) (result : 'a df_state)
     (f : 'a -> instruction -> instruction list) bb.
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      analysis_inst_simulates R_ok R_term (\v s. T) f /\
      (!inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        lift_result R_ok R_term
          (run_block fuel ctx bb s)
          (run_block fuel ctx (analysis_block_transform bottom result f bb) s))
Proof
  simp[] >>
  qexistsl_tac [`state_equiv {"y"}`, `execution_equiv {"y"}`,
                `ARB`, `ARB`, `cex_f`, `cex_bb`] >>
  rpt conj_tac
  >- (* valid_state_rel *)
     ACCEPT_TAC (SPEC ``{"y"}`` state_equiv_execution_equiv_valid_state_rel_proof)
  >- (* R_ok trans *)
     metis_tac[state_equiv_trans]
  >- (* R_term trans *)
     metis_tac[execution_equiv_trans]
  >- (* analysis_inst_simulates *)
     (simp[analysis_inst_simulates_def, cex_f_def] >>
      rpt conj_tac
      >- (* simulation clause *)
         (rpt gen_tac >>
          Cases_on `is_terminator inst.inst_opcode`
          >- (simp[run_insts_def] >>
              Cases_on `step_inst fuel ctx inst s` >>
              simp[lift_result_def, run_insts_def,
                   state_equiv_refl, execution_equiv_refl]) >>
          Cases_on `inst.inst_opcode = INVOKE`
          >- (simp[run_insts_def] >>
              Cases_on `step_inst fuel ctx inst s` >>
              simp[lift_result_def, run_insts_def,
                   state_equiv_refl, execution_equiv_refl]) >>
          simp[run_insts_def] >>
          Cases_on `step_inst fuel ctx inst s` >>
          simp[lift_result_def, run_insts_def]
          >- (* OK: nop_adds only change "y", excluded by state_equiv {"y"} *)
             (`~is_terminator ADD` by EVAL_TAC >>
              `ADD <> INVOKE` by EVAL_TAC >>
              simp[nop_add_def, step_inst_non_invoke, step_inst_base_def,
                   exec_pure2_def, eval_operand_def, update_var_def] >>
              simp[lift_result_def, state_equiv_def, execution_equiv_def,
                   lookup_var_def, FLOOKUP_UPDATE])
          >> simp[execution_equiv_refl])
      >- simp[nop_add_def, is_terminator_def])
  >- (* operand condition: no Var operands in cex_bb *)
     (simp[cex_bb_def, good_add_def, stop_inst_def] >> rw[] >> fs[])
  >- (* Conclusion false at vs_inst_idx = 2 *)
     (qexistsl_tac [`ARB`, `ARB`] >>
      qexists_tac `s with vs_inst_idx := 2` >>
      `analysis_block_transform ARB ARB cex_f cex_bb = cex_bb'`
        by EVAL_TAC >>
      pop_assum SUBST1_TAC >>
      simp[cex_original, cex_expanded, lift_result_def])
QED