Theory lowerDloadLoadMemory
Ancestors
  lowerDloadLiveScratch lowerDloadMacroMemory

Theorem ld_live_load_memory:
  ld_alloc_account keys d0 A s t0 /\ a.inst_id IN keys /\
  allocas_non_overlapping t0 /\ alloca_next_valid t0 /\ allocas_from lo t0 /\
  lo <= t0.vs_alloca_next /\ t0.vs_alloca_next < dimword (:256) /\
  (a.inst_id NOTIN A ==> t0.vs_alloca_next + 32 < dimword (:256)) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt + sz <= lo \/
    (?j. j NOTIN keys /\ FLOOKUP t0.vs_allocas j = SOME (bt,sz))) /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_target_prefix CT [a;b;c;d] t0 un (SUC (SUC (SUC (SUC 0)))) t u /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t0 /\ (!v. off = Var v ==> v IN V) /\
  ld_byte_rel (\aa bb. (aa = bb /\ aa < lo) \/ ld_site_bytes E live aa bb)
    tn.t_mem un.t_mem (\aa. read_memory aa 1 s) (\bb. read_memory bb 1 t0) ==>
  ?z. step_inst fuel CS inst s = OK z /\
    ld_byte_rel (\aa bb. (aa = bb /\ aa < lo) \/ ld_site_bytes E live aa bb)
      (step_taint inst s z tn).t_mem u.t_mem
      (\aa. read_memory aa 1 z) (\bb. read_memory bb 1 t)
Proof
  strip_tac >> drule_all ld_live_scratch_separation >>
  disch_then (qx_choose_then `p`
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN assume_tac)))) >>
  drule_all (BETA_RULE (Q.INST
    [`R` |-> `\aa bb. (aa = bb /\ aa < lo) \/ ld_site_bytes E live aa bb`]
    ld_load_completed_byte_rel)) >>
  disch_then (qspecl_then [`fuel`,`CS`] ACCEPT_TAC)
QED
