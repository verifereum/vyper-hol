(* Complete containing-function PHI boundary after positional registration. *)
Theory entryCompletedExitPhi
Ancestors
  entryReachBodyFirstEmissionGuarded externalEntryShape calldataRegistration
  entryContainingExitPhi
  compilerFirstEmission actualRegistrationCode abiDecoderPhi fragExec

Theorem entry_decoder_completed_containing_exit_phi:
  compile_abi_decode_to_buf dst src opc (Lit 0w) hi info first = ((),exit) /\
  abi_decode_source_opcode opc /\ fn_has_code first exit fn /\
  compile_register_positional_args ce args off exit = (cef,z) /\
  compile_guarded_body cef F nk ut iv stmts rt z = ((),b) /\
  ~block_is_terminated z /\ fn_has_code exit b fn ==>
  first.cs_blocks = exit.cs_blocks \/
  (!bb. lookup_block exit.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >> Cases_on `exit.cs_current_insts = []`
  >- (disj2_tac >>
      qspecl_then [`ce`,`args`,`off`,`exit`,`cef`,`z`,`nk`,`ut`,`iv`,`stmts`,
                   `rt`,`b`,`fn`] mp_tac registration_guarded_body_empty_phi >>
      simp[]) >>
  drule_all entry_decoder_nonempty_containing_exit_phi >> simp[]
QED

(* The final-exit premise of registration_list_owned_run/registration_positional_owned_run. *)
Theorem registration_completed_exit_phi:
  compile_register_positional_args ce args off st = (cef,registered) /\
  compile_guarded_body cef F nk ut iv stmts rt registered = ((),last) /\
  ~block_is_terminated registered /\ fn_has_code st last fn ==>
  (registered.cs_current_insts = [] ==>
    !bb. lookup_block registered.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >> drule register_positional_args_suffix_extends >> strip_tac >>
  `cs_extends registered last` by
    metis_tac[compile_guarded_body_labels, pairTheory.SND] >>
  qspecl_then [`st`,`registered`,`last`,`fn`] mp_tac fn_has_code_split >>
  asm_rewrite_tac[] >> strip_tac >>
  strip_tac >>
  qspecl_then [`cef`,`nk`,`ut`,`iv`,`stmts`,`rt`,`registered`,`last`,`fn`] mp_tac
    guarded_body_empty_phi >> simp[]
QED
