Theory asmOptNonemptyFinalizer
Ancestors
  asmOptNonemptyCompose asmOptNonemptyScan asmOptNonemptyIszero
  asmOptNonemptyJumpTransport asmOptNonemptyWitness list

Theorem optimize_round_terminal_witness:
  !p q ch.
  (?pre t post. p = pre ++ t::post /\ asm_terminal_op t /\
    EVERY (\i. !l. i <> AsmLabel l) post) /\
  optimize_round p = SOME (q,ch) ==>
  ?pre t post. q = pre ++ t::post /\ asm_terminal_op t /\
    EVERY (\i. !l. i <> AsmLabel l) post
Proof
  ho_match_mp_tac optimize_round_preserves_predicate >>
  rpt conj_tac
  >- MATCH_ACCEPT_TAC (GEN_ALL prune_unreachable_code_trailing_terminal)
  >- MATCH_ACCEPT_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] (GEN_ALL merge_iszero_trailing))
  >- MATCH_ACCEPT_TAC (GEN_ALL merge_jumpdests_trailing_terminal)
  >- MATCH_ACCEPT_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] prune_inefficient_jumps_trailing)
  >- MATCH_ACCEPT_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] optimize_inefficient_jumps_trailing)
  >- MATCH_ACCEPT_TAC (GEN_ALL prune_unused_jumpdests_trailing_terminal)
  >> MATCH_ACCEPT_TAC (GEN_ALL stack_peephole_opts_terminal_witness)
QED

Theorem asm_opt_finalizer_terminal_witness:
  !policy p q.
  (?pre t post. p = pre ++ t::post /\ asm_terminal_op t /\
    EVERY (\i. !l. i <> AsmLabel l) post) /\
  asm_opt_finalizer policy p = SOME q ==>
  ?pre t post. q = pre ++ t::post /\ asm_terminal_op t /\
    EVERY (\i. !l. i <> AsmLabel l) post
Proof
  ho_match_mp_tac asm_opt_finalizer_preserves_predicate >>
  MATCH_ACCEPT_TAC optimize_round_terminal_witness
QED

Theorem codegen_assembly_finalizer_nonempty:
  codegen_assembly rpolicy unit = SOME prog /\
  asm_opt_finalizer rpolicy prog = SOME prog' ==> assemble prog' <> []
Proof
  strip_tac >> drule codegen_assembly_terminal_witness >> strip_tac >>
  irule terminal_witness_assemble_nonempty >>
  irule asm_opt_finalizer_terminal_witness >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
