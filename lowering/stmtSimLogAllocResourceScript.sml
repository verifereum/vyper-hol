(* Actual event-buffer resources; no interval allocation budget. *)
Theory stmtSimLogAllocResource
Ancestors
  abiBuiltinAllocation exprLoweringProps compileEnv venomMemDefs venomState
  venomInst finite_map words list arithmetic

Theorem log_event_buffer_resource:
  stmt_state_rel ctx func ce cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w bufsz)] /\ bufsz < dimword (:256) ==>
  ?p. ((FLOOKUP s.vs_allocas inst.inst_id = NONE /\ p = s.vs_alloca_next) \/
       FLOOKUP s.vs_allocas inst.inst_id = SOME (p,bufsz)) /\
    p+bufsz < dimword (:256) /\
    (!id b sz. id <> inst.inst_id /\ FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
      p+bufsz <= b \/ b+sz <= p)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `alloca_room ctx func s /\ alloca_inv s` by fs[stmt_state_rel_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (qexists_tac `s.vs_alloca_next` >> simp[] >> conj_tac
      >- (`inst.inst_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
          drule_all alloca_room_fresh >> simp[w2n_n2w]) >>
      gvs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME record` >>
  PairCases_on `record` >>
  `record1 = bufsz` by
    (fs[stmt_state_rel_def] >> first_x_assum drule_all >> simp[w2n_n2w]) >>
  qexists_tac `record0` >> simp[] >>
  `record0+bufsz <= s.vs_alloca_next` by
    (gvs[alloca_inv_def, alloca_next_valid_def] >>
     first_x_assum drule >> decide_tac) >>
  conj_tac >- (drule alloca_room_next_lt >> decide_tac) >>
  gvs[alloca_inv_def, allocas_non_overlapping_def] >> rpt strip_tac >>
  `inst.inst_id <> id` by simp[] >>
  first_x_assum drule_all >> decide_tac
QED

Theorem log_sum_filter_mono[local]:
  !(f:'a -> num) P P' l.
    (!y. P' y ==> P y) ==>
    SUM (MAP f (FILTER P' l)) <= SUM (MAP f (FILTER P l))
Proof
  rpt gen_tac >> strip_tac >> Induct_on `l` >> rw[] >> gvs[] >> res_tac
QED

Theorem log_sum_filter_drop[local]:
  !(f:'a -> num) P P' x l.
    MEM x l /\ P x /\ ~P' x /\ (!y. P' y ==> P y) ==>
    SUM (MAP f (FILTER P' l)) + f x <= SUM (MAP f (FILTER P l))
Proof
  rpt gen_tac >> strip_tac >> rpt (pop_assum mp_tac) >>
  Induct_on `l` >> rw[] >> gvs[] >> metis_tac[log_sum_filter_mono]
QED

(* The event buffer's ALLOCA moves its size from the pending charge to the
   frontier, so the free memory pointer keeps its room. *)
Theorem log_event_buffer_fmp_room:
  fmp_room ctx func s /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w bufsz)] /\
  bufsz < dimword (:256) ==>
  fmp_room ctx func (abi_builtin_allocate_state inst.inst_id bufsz s)
Proof
  strip_tac >> irule fmp_room_static_charge >> qexists_tac `s` >>
  simp[abi_builtin_allocate_state_def] >> IF_CASES_TAC >> simp[] >>
  simp[pending_alloca_size_def] >>
  qspecl_then
    [`alloca_lit_size`,
     `\i. i.inst_opcode = ALLOCA /\ i.inst_id NOTIN FDOM s.vs_allocas`,
     `\i. i.inst_opcode = ALLOCA /\
          i.inst_id NOTIN (inst.inst_id INSERT FDOM s.vs_allocas)`,
     `inst`, `fn_insts func`] mp_tac log_sum_filter_drop >>
  impl_tac >- gvs[FLOOKUP_DEF] >>
  `alloca_lit_size inst = bufsz` by simp[alloca_lit_size_def, w2n_n2w] >>
  simp[]
QED

Theorem log_event_buffer_room:
  alloca_room ctx func s /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w bufsz)] /\
  bufsz < dimword (:256) ==>
  alloca_room ctx func (abi_builtin_allocate_state inst.inst_id bufsz s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id = NONE`
  >- (`inst.inst_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
      drule_all alloca_room_fresh >>
      simp[abi_builtin_allocate_state_def, w2n_n2w]) >>
  simp[abi_builtin_allocate_state_def]
QED
