(* Diagnostic only: synthesized Halt from an initially halted frame.
   This theory does not use ircf_block_sim or its simulation theory. *)
Theory internalReturnCopyFwdHaltProbe
Ancestors
  internalReturnCopyFwdPlan reachableFnSim venomExecSemantics venomState
  venomInst ptrDiscipline passSimulationDefs finite_map words list
  o1ContractSimplifyCfgSrcFrame ctxLookupAgreeHelpers opcodeClass

Definition ircf_halt_probe_bb_def:
  ircf_halt_probe_bb : basic_block =
    <| bb_label := "main";
       bb_instructions := [
         mk_inst 1 ALLOCA [Lit 32w] ["%p"];
         mk_inst 2 MLOAD [Var "%p"] ["%v"];
         mk_inst 3 SSTORE [Lit 0w; Var "%v"] [];
         mk_inst 4 JMP [Label "sink"] []] |>
End

Definition ircf_halt_probe_fn_def:
  ircf_halt_probe_fn = mk_raw_function "main" [ircf_halt_probe_bb;
    <| bb_label := "sink";
       bb_instructions := [mk_inst 5 JMP [Label "sink"] []] |>]
End

Definition ircf_halt_probe_ctx_def:
  ircf_halt_probe_ctx : venom_context =
    <| ctx_functions := [ircf_halt_probe_fn]; ctx_entry := SOME "main";
       ctx_global_reserved := [] |>
End

Definition ircf_halt_probe_state_def:
  ircf_halt_probe_state s b = s with
    <| vs_vars := FEMPTY; vs_allocas := FEMPTY; vs_alloca_next := 0;
       vs_memory := REPLICATE 32 b; vs_halted := T;
       vs_prev_bb := NONE; vs_current_bb := "main"; vs_inst_idx := 0;
       vs_call_ctx := s.vs_call_ctx with cc_static := F |>
End

(* The lower fuel assumption is genuinely vacuous at k = 0. *)
Theorem ircf_halt_probe_fuel_zero:
  fn_sim_below D vs C C' R Rret 1
Proof
  rw[fn_sim_below_def] >> gvs[Once run_blocks_def, terminates_def]
QED

Theorem ircf_halt_probe_jump:
  step_inst k C (mk_inst 4 JMP [Label "sink"] [])
    (ircf_halt_probe_state s b) =
    OK (jump_to "sink" (ircf_halt_probe_state s b)) /\
  (jump_to "sink" (ircf_halt_probe_state s b)).vs_halted
Proof
  simp[Once step_inst_def, step_inst_base_def, mk_inst_def,
       jump_to_def, ircf_halt_probe_state_def]
QED

Theorem ircf_halt_probe_run:
  ?r. run_block k ircf_halt_probe_ctx ircf_halt_probe_bb
         (ircf_halt_probe_state s b) = Halt r /\ r.vs_halted /\
      r.vs_alloca_next = 32 /\
      FLOOKUP r.vs_allocas 1 = SOME (0,32) /\
      (r.vs_accounts r.vs_call_ctx.cc_address).storage 0w =
        word_of_bytes T 0w (REPLICATE 32 b)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, byteTheory.word_of_bytes_def,
    finite_mapTheory.FLOOKUP_UPDATE] >> CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
  simp[]
QED

Theorem ircf_halt_probe_instruction_opcodes:
  EVERY (\i. MEM i.inst_opcode [ALLOCA; MLOAD; SSTORE; JMP])
    (fn_insts ircf_halt_probe_fn)
Proof
  EVAL_TAC
QED

(* This is universal over all reachable instructions and fuels, not just
   the displayed trace.  No instruction in this context returns Halt. *)
Theorem ircf_halt_probe_no_final_taint:
  ~final_taint vs ircf_halt_probe_ctx sh tn R
Proof
  strip_tac >> fs[final_taint_def] >>
  drule scfg_frame_reachable_functions >>
  simp[ircf_halt_probe_ctx_def] >> strip_tac >> gvs[] >>
  assume_tac ircf_halt_probe_instruction_opcodes >>
  drule_all EVERY_active_inst >> simp[] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def] >> strip_tac >>
  drule step_inst_base_halt_opcodes >> simp[] >> gvs[]
QED

Theorem ircf_halt_probe_taint_within:
  taint_within D ircf_halt_probe_ctx vs
Proof
  rw[taint_within_def, ircf_halt_probe_no_final_taint] >>
  drule scfg_frame_reachable_functions >>
  simp[ircf_halt_probe_ctx_def] >> strip_tac >> gvs[] >>
  assume_tac ircf_halt_probe_instruction_opcodes >>
  drule_all EVERY_active_inst >> simp[] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[exec_alloca_def, exec_read1_def, exec_write2_def] >>
  gvs[AllCaseEqs(), update_var_def, sstore_def, jump_to_def] >>
  strip_tac >> gvs[]
QED
