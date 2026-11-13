(* Allocation-origin boundaries for same-endpoint canonical decoding. *)
Theory ctorDeployMemoryRunPtrPrefixAllocationFloor
Ancestors
  actualAllocExec ptrDiscipline venomState venomExecSemantics
  finite_map arithmetic

Theorem prefix_allocation_floor_frame:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  strip_tac >> fs[allocas_from_def] >> metis_tac[]
QED

Theorem prefix_allocation_floor_fresh:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  t.vs_allocas = s.vs_allocas |+ (id,(s.vs_alloca_next,n)) /\
  t.vs_alloca_next = s.vs_alloca_next+n ==>
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  strip_tac >> simp[allocas_from_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `id = aid` >> gvs[allocas_from_def] >> metis_tac[]
QED

Theorem prefix_allocation_floor_word_fresh:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_frontier_inv ctx fn site s /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  unit_alloca_budget ctx < dimword (:256) ==>
  ?t. step_inst_base inst s = OK t /\
    exec_alloca inst s (32w:bytes32) = OK t /\
    t = update_var out (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
        (inst.inst_id,(s.vs_alloca_next,32));
        vs_alloca_next := s.vs_alloca_next+32|>) /\
    allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  strip_tac >> drule_all actual_word_alloca_fresh_run >> strip_tac >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (irule prefix_allocation_floor_fresh >> qexistsl_tac [`inst.inst_id`,`32`,`s`] >> simp[]) >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[]
QED

Theorem prefix_allocation_floor_word_reuse:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32) ==>
  ?t. step_inst_base inst s = OK t /\
    exec_alloca inst s (32w:bytes32) = OK t /\
    t = update_var out (n2w p) s /\
    allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  strip_tac >> drule_all actual_word_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (irule prefix_allocation_floor_frame >> qexists_tac `s` >> simp[]) >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[]
QED
