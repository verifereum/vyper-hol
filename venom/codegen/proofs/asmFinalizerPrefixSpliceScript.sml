Theory asmFinalizerPrefixSplice
Ancestors
  asmFinalizerPrefixJumpDelete asmSplice asmSymPc finalizerContract
  asmSymSem asmOptimizer asmWf asmFinalizerPrefixCompose
  asmFinalizerPrefixIszero asmFinalizerPrefixPruneJumps
  asmFinalizerPrefixInefficient asmFinalizerPrefixPeephole

(* Quotation abbreviation only; no new logical constant is introduced. *)
val transport = ``\p q.
  ?K. 0 < K /\ !env s n a.
    s.as_pc = 0 /\ sym_steps p env n (sym_init s) = SymOK a ==>
    (?m b. sym_steps q env m (sym_init s) = SymOK b /\ n <= K * (m+1)) /\
    (a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp "GAS" ==>
     ?m b. sym_steps q env m (sym_init s) = SymOK b /\
       b.sym_base.as_pc < LENGTH q /\ EL b.sym_base.as_pc q = AsmOp "GAS" /\
       b.sym_base.as_gas_readings = a.sym_base.as_gas_readings)``;

Theorem merge_iszero_prefix_transport:
  !p. asm_static_wf p ==> ^transport p (FST (merge_iszero p))
Proof
  BETA_TAC >> match_mp_tac (BETA_RULE merge_iszero_prefix_transport_conditional) >>
  conj_tac
  >- (BETA_TAC >> MATCH_ACCEPT_TAC bounded_splice_prefix_transport) >>
  MATCH_ACCEPT_TAC (BETA_RULE prefix_transport_trans)
QED

Theorem prune_jumps_prefix_transport:
  !p. asm_static_wf p ==> ^transport p (FST (prune_inefficient_jumps p))
Proof
  BETA_TAC >> match_mp_tac (BETA_RULE prune_jumps_prefix_transport_conditional) >>
  conj_tac
  >- (BETA_TAC >> MATCH_ACCEPT_TAC bounded_splice_prefix_transport) >>
  MATCH_ACCEPT_TAC (BETA_RULE prefix_transport_trans)
QED

Theorem inefficient_jumps_prefix_transport:
  !p. asm_static_wf p ==> ^transport p (FST (optimize_inefficient_jumps p))
Proof
  BETA_TAC >> match_mp_tac (BETA_RULE inefficient_jumps_prefix_transport_conditional) >>
  conj_tac
  >- (pure_rewrite_tac [LET_THM] >> BETA_TAC >>
      MATCH_ACCEPT_TAC bounded_splice_prefix_transport) >>
  MATCH_ACCEPT_TAC (BETA_RULE prefix_transport_trans)
QED

Theorem peephole_prefix_transport:
  !p q c. asm_static_wf p /\ stack_peephole_opts p = SOME(q,c) ==>
    ^transport p q
Proof
  BETA_TAC >> match_mp_tac (BETA_RULE peephole_prefix_transport_conditional) >>
  conj_tac
  >- (BETA_TAC >> MATCH_ACCEPT_TAC bounded_splice_prefix_transport) >>
  conj_tac
  >- MATCH_ACCEPT_TAC (BETA_RULE prefix_transport_refl) >>
  MATCH_ACCEPT_TAC (BETA_RULE prefix_transport_trans)
QED
