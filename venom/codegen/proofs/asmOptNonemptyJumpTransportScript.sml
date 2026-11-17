Theory asmOptNonemptyJumpTransport
Ancestors
  asmOptNonemptyJumps asmOptimizer

Theorem trailing_terminal_jump_window:
  asm_jump_to_next a b c ==>
  ((?pre t post. a::b::c::r = pre ++ [t] ++ post /\
      asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post) <=>
   (?pre t post. c::r = pre ++ [t] ++ post /\
      asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post))
Proof
  Cases_on `a` >> Cases_on `c` >>
  simp[asm_jump_to_next_def] >> rpt strip_tac >>
  gvs[trailing_terminal_cons]
QED

Theorem trailing_terminal_jumpi_window:
  asm_jumpi_over_jump a b c d e ==>
  ((?pre t post. a::b::c::d::e::r = pre ++ [t] ++ post /\
      asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post) <=>
   (?pre t post. AsmOp "ISZERO"::c::AsmOp "JUMPI"::e::r = pre ++ [t] ++ post /\
      asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post))
Proof
  Cases_on `a` >> Cases_on `e` >>
  simp[asm_jumpi_over_jump_def] >> rpt strip_tac >>
  gvs[trailing_terminal_cons]
QED

Theorem prune_inefficient_jumps_trailing:
  !p. (?pre t post. p = pre ++ [t] ++ post /\ asm_terminal_op t /\
      EVERY (\i. !l. i <> AsmLabel l) post) ==>
    (?pre t post. FST (prune_inefficient_jumps p) = pre ++ [t] ++ post /\
      asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post)
Proof
  recInduct prune_inefficient_jumps_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[Once prune_inefficient_jumps_def] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> IF_CASES_TAC
  >- (gvs[trailing_terminal_jump_window] >> first_assum ACCEPT_TAC)
  >> gvs[] >> match_mp_tac trailing_terminal_cons_transport >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qspec_then `b::c::rest` mp_tac prune_inefficient_jumps_no_labels >>
  simp[]
QED

Theorem optimize_inefficient_jumps_trailing:
  !p. (?pre t post. p = pre ++ [t] ++ post /\ asm_terminal_op t /\
      EVERY (\i. !l. i <> AsmLabel l) post) ==>
    (?pre t post. FST (optimize_inefficient_jumps p) = pre ++ [t] ++ post /\
      asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post)
Proof
  recInduct optimize_inefficient_jumps_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[Once optimize_inefficient_jumps_def] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> IF_CASES_TAC
  >- (gvs[trailing_terminal_jumpi_window] >> first_assum ACCEPT_TAC)
  >> gvs[] >> match_mp_tac trailing_terminal_cons_transport >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qspec_then `b::c::d::e::rest` mp_tac optimize_inefficient_jumps_no_labels >>
  simp[]
QED
