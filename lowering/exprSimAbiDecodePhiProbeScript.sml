(* A counted jump may stop before evaluating the destination PHIs.
   This probe concerns the transfer interface, not source simulation. *)
Theory exprSimAbiDecodePhiProbe
Ancestors
  fragGasMode fragGasPath gasCount venomInst venomState
  venomExecSemantics venomExecProofs list arithmetic

Definition abi_decode_phi_probe_fn_def:
  abi_decode_phi_probe_fn fn = fn with fn_blocks :=
    [<| bb_label := "entry";
        bb_instructions := [mk_inst 0 JMP [Label "exit"] []] |>;
     <| bb_label := "exit";
        bb_instructions := [mk_inst 1 PHI [Label "entry"; Lit 7w] ["x"];
                            mk_inst 2 STOP [] []] |>]
End

Theorem abi_decode_phi_probe_prephi_reachable:
  !ctx fn s.
    ~s.vs_halted /\ s.vs_current_bb = "entry" /\ s.vs_inst_idx = 0 ==>
    gas_marked_path F ctx (abi_decode_phi_probe_fn fn) s 0
      (OK (jump_to "exit" s)) /\
    (jump_to "exit" s).vs_current_bb = "exit" /\
    (jump_to "exit" s).vs_inst_idx = 0
Proof
  rpt gen_tac >> strip_tac >>
  reverse conj_tac >- simp[jump_to_def] >>
  rewrite_tac[gas_marked_path_def] >>
  `gas_path_edge ctx (abi_decode_phi_probe_fn fn) s 0
     (OK (jump_to "exit" s))` by
    (rewrite_tac[gas_path_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[abi_decode_phi_probe_fn_def, lookup_block_def, FIND_thm,
          get_instruction_def, step_inst_non_invoke, mk_inst_def,
          gas_count_step_def, step_jmp_behavior, is_terminator_def] >>
     metis_tac[]) >>
  `~(jump_to "exit" s).vs_halted` by simp[jump_to_def] >>
  drule (cj 2 gas_path_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_rules]
QED

Theorem abi_decode_phi_probe_successful_phi:
  !s. s.vs_current_bb = "entry" ==>
    eval_phis (jump_to "exit" s)
      [mk_inst 1 PHI [Label "entry"; Lit 7w] ["x"];
       mk_inst 2 STOP [] []] =
    OK (update_var "x" 7w (jump_to "exit" s)) /\
    phi_prefix_length
      [mk_inst 1 PHI [Label "entry"; Lit 7w] ["x"];
       mk_inst 2 STOP [] []] = 1
Proof
  simp[eval_phis_def, eval_one_phi_def, jump_to_def, mk_inst_def,
       resolve_phi_def, eval_operand_def, phi_prefix_length_def]
QED

Theorem abi_decode_phi_probe_zero_length:
  !ctx fn s. ~s.vs_halted /\ s.vs_current_bb = "entry" ==>
    gas_marked_path F ctx (abi_decode_phi_probe_fn fn) s 0 (OK s) /\
    s.vs_current_bb <> "exit"
Proof
  simp[gas_marked_path_def, gas_path_rules]
QED
