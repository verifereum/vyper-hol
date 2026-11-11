Theory lowerDloadLoadProducer
Ancestors
  lowerDloadLoadValues lowerDloadLoadMemory lowerDloadLoadAccount
  lowerDloadLoadRepresentation lowerDloadOwnership lowerDloadRelocation
  lowerDloadAllocation ptrDiscipline finite_map pred_set

Theorem ld_load_semantic_backward:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\ av NOTIN V /\ bv NOTIN V /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  c.inst_outputs = [] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t0 /\
  (!v. off = Var v ==> v IN V) /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn inst s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  ~in_revert_forward fn s /\ dload_offset_ok CS fn inst s /\
  code_layout_valid s /\ t0.vs_code = s.vs_code /\
  eval_operand (Label "code_end") t0 =
    SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
  ld_target_prefix CT [a;b;c;d] t0 un (SUC (SUC (SUC (SUC 0)))) t u /\
  ld_alloc_account keys d0 A s t0 /\ a.inst_id IN keys /\
  allocas_non_overlapping t0 /\ alloca_next_valid t0 /\ allocas_from lo t0 /\
  lo <= t0.vs_alloca_next /\ t0.vs_alloca_next < dimword (:256) /\
  (a.inst_id NOTIN A ==> t0.vs_alloca_next + 32 < dimword (:256)) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt + sz <= lo \/
    (?j. j NOTIN keys /\ FLOOKUP t0.vs_allocas j = SOME (bt,sz))) /\
  ld_byte_rel (\aa bb. (aa = bb /\ aa < lo) \/ ld_site_bytes E live aa bb)
    tn.t_mem un.t_mem (\aa. read_memory aa 1 s) (\bb. read_memory bb 1 t0) ==>
  ?z. step_inst fuel CS inst s = OK z /\
    ld_owned_vars V E (ld_set_prov AG [out] NONE)
      (ld_set_prov (ld_set_prov AH [bv] NONE) [out] NONE)
      (step_taint inst s z tn) u z t /\
    ld_byte_rel (\aa bb. (aa = bb /\ aa < lo) \/ ld_site_bytes E live aa bb)
      (step_taint inst s z tn).t_mem u.t_mem
      (\aa. read_memory aa 1 z) (\bb. read_memory bb 1 t) /\
    ld_alloc_account keys d0 (a.inst_id INSERT A) z t /\
    (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
      bt + sz <= lo \/ (?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME (bt,sz)))
Proof
  strip_tac >>
  drule_all ld_reachable_load_owned >>
  disch_then (qspecl_then [`fuel`] strip_assume_tac) >>
  `!v. off = Var v ==> v <> av` by metis_tac[] >>
  drule_all ld_live_load_memory >>
  disch_then (qspecl_then [`fuel`,`CS`] strip_assume_tac) >> gvs[] >>
  drule_all (SRULE [] ld_load_completed_account) >> strip_tac >>
  simp[] >>
  ho_match_mp_tac (Q.INST [`n` |-> `4`] ld_load_prefix_live_representation) >>
  simp[] >> first_assum ACCEPT_TAC
QED
