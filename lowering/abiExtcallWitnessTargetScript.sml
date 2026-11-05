(* Target termination for the concrete malformed-return witness. *)
Theory abiExtcallWitnessTarget
Ancestors
  abiExtcallWitnessEntry abiExtcallWrapReachProbe fragGasPath
  venomExecProps venomExecSemantics fragExec venomInst venomInstProps

Definition witness_after_entry_def:
  witness_after_entry = reach_after_entry with vs_block_ctx := witness_s0.vs_block_ctx
End

Definition witness_after_decode_def:
  witness_after_decode = reach_final with vs_block_ctx := witness_s0.vs_block_ctx
End

Theorem witness_initial_transport:
  witness_s0 = reach_state with vs_block_ctx := witness_s0.vs_block_ctx
Proof
  EVAL_TAC
QED

Theorem witness_entry_lookup:
  lookup_block "entry" witness_func.fn_blocks = lookup_block "entry" reach_func.fn_blocks
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem witness_cont_lookup:
  lookup_block "@extcall_cont_1" witness_func.fn_blocks =
    SOME <|bb_label := "@extcall_cont_1";
      bb_instructions := witness_sb.cs_current_insts ++
        [mk_inst witness_sb.cs_next_id STOP [] []]|>
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem witness_entry_transport:
  run_block 0 ctx (THE (lookup_block "entry" reach_func.fn_blocks))
    (reach_state with vs_block_ctx := bc) =
  OK (reach_after_entry with vs_block_ctx := bc)
Proof
  CONV_TAC (LAND_CONV (RATOR_CONV (RAND_CONV
    (computeLib.RESTR_EVAL_CONV [``function_selector``])))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``function_selector``, ``exec_block``])) >>
  once_rewrite_tac[exec_block_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``function_selector``, ``exec_block``])) >>
  once_rewrite_tac[exec_block_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``function_selector``, ``exec_block``])) >>
  simp_tac (srw_ss() ++ wordsLib.SIZES_ss)
    [wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``function_selector``, ``exec_block``])) >>
  once_rewrite_tac[exec_block_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``function_selector``, ``exec_block``])) >>
  once_rewrite_tac[exec_block_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``function_selector``, ``exec_block``])) >>
  once_rewrite_tac[exec_block_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``function_selector``, ``exec_block``])) >>
  CONV_TAC (RAND_CONV (computeLib.RESTR_EVAL_CONV [``function_selector``])) >>
  simp_tac (srw_ss() ++ wordsLib.SIZES_ss)
    [wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

Theorem witness_entry_block:
  run_block 0 ctx (THE (lookup_block "entry" witness_func.fn_blocks)) witness_s0 =
    OK witness_after_entry
Proof
  once_rewrite_tac[witness_initial_transport] >>
  rewrite_tac[witness_entry_lookup, witness_entry_transport, witness_after_entry_def]
QED

Theorem witness_decode_transport:
  run_inst_seq witness_sb.cs_current_insts
    (reach_after_entry with vs_block_ctx := bc) =
    OK (reach_final with vs_block_ctx := bc)
Proof
  CONV_TAC (LAND_CONV (RATOR_CONV (RAND_CONV
    (computeLib.RESTR_EVAL_CONV [``function_selector``])))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``function_selector``])) >>
  CONV_TAC (RAND_CONV (computeLib.RESTR_EVAL_CONV [``function_selector``])) >> simp[]
QED

Theorem witness_decode_sequence:
  run_inst_seq witness_sb.cs_current_insts witness_after_entry = OK witness_after_decode
Proof
  simp[witness_after_entry_def, witness_after_decode_def, witness_decode_transport]
QED

Theorem witness_decode_control:
  witness_after_entry.vs_inst_idx = 0 /\
  witness_after_entry.vs_current_bb = "@extcall_cont_1" /\
  witness_after_decode.vs_inst_idx = 0 /\
  ~witness_after_decode.vs_halted
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem witness_decode_insts:
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    witness_sb.cs_current_insts
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Definition witness_halt_def:
  witness_halt = halt_state (witness_after_decode with
    <|vs_inst_idx := LENGTH witness_sb.cs_current_insts; vs_returndata := []|>)
End

Theorem witness_cont_exec:
  exec_block fuel ctx
    <|bb_label := "@extcall_cont_1";
      bb_instructions := witness_sb.cs_current_insts ++
        [mk_inst witness_sb.cs_next_id STOP [] []]|>
    witness_after_entry = Halt witness_halt
Proof
  mp_tac (Q.SPEC `witness_sb.cs_current_insts` exec_block_run_inst_seq) >>
  disch_then (qspec_then `witness_after_entry` mp_tac) >>
  simp[witness_decode_control, witness_decode_insts] >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  disch_then (qspec_then `<|bb_label := "@extcall_cont_1";
    bb_instructions := witness_sb.cs_current_insts ++
      [mk_inst witness_sb.cs_next_id STOP [] []]|>` mp_tac) >>
  simp[witness_decode_sequence] >> strip_tac >>
  simp[Once exec_block_def, get_instruction_def, witness_decode_control,
       listTheory.EL_APPEND_EQN, witness_halt_def,
       step_inst_def, step_inst_base_opcode_eqs, mk_inst_def]
QED

Theorem witness_entry_no_phi:
  phi_prefix_length (THE (lookup_block "entry" witness_func.fn_blocks)).bb_instructions = 0 /\
  IS_SOME (lookup_block "entry" witness_func.fn_blocks)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem witness_entry_exec:
  exec_block fuel ctx (THE (lookup_block "entry" witness_func.fn_blocks)) witness_s0 =
    OK witness_after_entry
Proof
  `run_block fuel ctx (THE (lookup_block "entry" witness_func.fn_blocks)) witness_s0 =
    OK witness_after_entry` by
    (irule run_block_fuel_mono >> simp[] >> qexists_tac `0` >> simp[witness_entry_block]) >>
  `witness_s0 with vs_inst_idx := 0 = witness_s0` by EVAL_TAC >>
  gvs[run_block_def, witness_entry_no_phi, eval_phis_no_phi]
QED

Theorem witness_cont_no_phi:
  phi_prefix_length (witness_sb.cs_current_insts ++
    [mk_inst witness_sb.cs_next_id STOP [] []]) = 0
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem witness_entry_control:
  witness_s0.vs_current_bb = "entry" /\
  ~witness_after_entry.vs_halted /\
  (witness_after_entry with vs_inst_idx := 0) = witness_after_entry
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem witness_target_halts:
  run_from 1 witness_ctx witness_func witness_s0 = Halt witness_halt
Proof
  mp_tac (Q.INST [`fuel` |-> `1`, `ctx` |-> `witness_ctx`] witness_entry_exec) >>
  mp_tac witness_entry_no_phi >>
  Cases_on `lookup_block "entry" witness_func.fn_blocks` >> simp[] >>
  rpt strip_tac >>
  simp[run_from_def, witness_entry_control] >>
  rewrite_tac[numLib.num_CONV ``1:num``, run_blocks_unfold] >>
  simp[witness_decode_control, witness_cont_lookup, run_block_def,
       witness_cont_no_phi, eval_phis_no_phi, witness_entry_control,
       witness_cont_exec]
QED

Theorem witness_target_no_abort:
  !n a t. run_from n witness_ctx witness_func witness_s0 <> Abort a t
Proof
  rpt strip_tac >>
  `run_from (n+1) witness_ctx witness_func witness_s0 = Halt witness_halt` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `1` >>
     simp[witness_target_halts]) >>
  `run_from (n+1) witness_ctx witness_func witness_s0 = Abort a t` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `n` >> simp[]) >>
  gvs[]
QED

Theorem witness_target_no_abort_path:
  !n a t. ~gas_path witness_ctx witness_func witness_s0 n (Abort a t)
Proof
  rpt strip_tac >>
  drule gas_path_exit >> simp[exit_result_def] >>
  metis_tac[witness_target_no_abort]
QED
