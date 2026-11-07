(* Structural resources only: scratch writes need not preserve state_rel. *)
Theory normalizerAllocationFrame
Ancestors
  exprLoweringProps localPtrsProps venomMemProps venomInst venomState
  venomExecSemantics allocaSiteResource venomInstProofs1 list finite_map
  exprSimCopy exprSimStorageCopy fragExec storageCopyGasPath

Theorem nonallocating_sequence_allocation_fields:
  run_inst_seq insts s = OK t /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode) insts ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  drule_at (Pos hd)
    (Q.ISPEC `\s:venom_state. (s.vs_allocas,s.vs_alloca_next)`
      run_inst_seq_preserves_field) >> simp[] >> disch_then irule >>
  rpt strip_tac >> rename1 `MEM inst insts` >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  pure_rewrite_tac[EVERY_MEM] >>
  disch_then (qspec_then `inst` mp_tac) >> asm_rewrite_tac[] >> strip_tac >>
  fs[] >> drule_all step_inst_base_preserves_alloca_state >> simp[]
QED

Theorem nonallocating_sequence_allocation_resources:
  run_inst_seq insts s = OK t /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode) insts /\
  alloca_inv s /\ alloca_room ctx func s ==>
  alloca_inv t /\ alloca_room ctx func t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all nonallocating_sequence_allocation_fields >> strip_tac >>
  metis_tac[alloca_inv_fields, alloca_room_fields]
QED

Theorem exec_alloca_recorded_sizes:
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit n] /\
  exec_alloca inst s n = OK t /\
  (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w) ==>
  !i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP t.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
      simp[exec_alloca_def, AllCaseEqs(), LET_THM] >> rpt strip_tac >>
      gvs[update_var_def, FLOOKUP_UPDATE] >>
      reverse (Cases_on `i.inst_id = inst.inst_id`) >> gvs[]
      >- metis_tac[] >>
      `i = inst` by metis_tac[fn_inst_ids_distinct_inj] >> gvs[]) >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def, AllCaseEqs(), LET_THM] >> rpt strip_tac >>
  gvs[update_var_def] >> metis_tac[]
QED

Theorem literal_alloca_structural_resources:
  alloca_inv s /\ alloca_room ctx func s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit n] /\ inst.inst_outputs = [out] /\
  (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w) ==>
  ?t b. exec_alloca inst s n = OK t /\
    alloca_inv t /\ alloca_room ctx func t /\
    lookup_var out t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,w2n n) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
    (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w)
Proof
  strip_tac >>
  `!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n` by
    metis_tac[] >>
  drule_all alloca_site_execute >> strip_tac >>
  qexistsl_tac [`t`,`b`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> irule exec_alloca_recorded_sizes >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`func`,`inst`,`n`,`s`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem allocation_fields_recorded_resources:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  alloca_inv s /\ alloca_room ctx func s /\
  (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w) ==>
  alloca_inv t /\ alloca_room ctx func t /\
  (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP t.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w)
Proof
  strip_tac >> conj_tac >- metis_tac[alloca_inv_fields] >>
  conj_tac >- metis_tac[alloca_room_fields] >>
  asm_rewrite_tac[] >> first_assum ACCEPT_TAC
QED

Theorem copy_static_allocation_resources:
  copy_static t = copy_static s /\ alloca_inv s /\ alloca_room ctx func s ==>
  alloca_inv t /\ alloca_room ctx func t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule copy_static_fields >> strip_tac >>
  metis_tac[alloca_inv_fields, alloca_room_fields]
QED

Theorem copy_prefix_allocation_resources:
  copy_prefix loc a b n s k t /\ alloca_inv s /\ alloca_room ctx func s ==>
  alloca_inv t /\ alloca_room ctx func t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> irule copy_static_allocation_resources >>
  gvs[copy_prefix_def]
QED

Theorem copy_runtime_allocation_resources:
  copy_runtime_frame sa s sb t /\ alloca_inv s /\ alloca_room ctx func s ==>
  alloca_inv t /\ alloca_room ctx func t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> gvs[copy_runtime_frame_def] >>
  drule_all copy_static_allocation_resources >> simp[]
QED

Theorem immutable_copy_allocation_frame:
  compile_imm_copy_to_memory is_ctor imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. is_ctor /\ imm = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  alloca_inv s /\ alloca_room ctx func s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    alloca_inv t /\ alloca_room ctx func t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  Cases_on `is_ctor` >> strip_tac >> fs[]
  >- (drule_all copy_ctor_run >> strip_tac >>
      drule_all copy_runtime_allocation_resources >> strip_tac >>
      rename1 `copy_runtime_frame sa s sb t` >>
      qexists_tac `t` >> gvs[copy_runtime_frame_def]) >>
  drule_all copy_runtime_run >> strip_tac >>
  drule_all copy_runtime_allocation_resources >> strip_tac >>
  rename1 `copy_runtime_frame sa s sb t` >>
  qexists_tac `t` >> gvs[copy_runtime_frame_def]
QED

Theorem storage_copy_allocation_frame_frag:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME (n2w b) /\
  n < 2**256 /\ b+32*n < 2**256 /\
  alloca_inv sbase /\ alloca_room ctx func sbase ==>
  frag_exec ctx sa sb (\s. s = sbase)
    (\t. alloca_inv t /\ alloca_room ctx func t /\
      t.vs_allocas = sbase.vs_allocas /\ t.vs_alloca_next = sbase.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase)) R
Proof
  strip_tac >>
  `frag_exec ctx sa sb (\s. s = sbase)
    (\s. copy_prefix loc a b n sbase n s /\
      (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase)) R` by
    (irule compile_storage_copy_content_frag >> simp[] >>
     qexistsl_tac [`dst`,`src`,`u`] >> simp[] >>
     metis_tac[]) >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> drule_all copy_prefix_allocation_resources >> simp[]
QED


Theorem copy_prefix_recorded_resources:
  copy_prefix loc a b n s k t /\ alloca_inv s /\ alloca_room ctx func s /\
  (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w) ==>
  (t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
  alloca_inv t /\ alloca_room ctx func t /\
  (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP t.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w)
Proof
  strip_tac >> drule_all copy_prefix_allocation_resources >> strip_tac >>
  conj_tac >- simp[] >>
  irule allocation_fields_recorded_resources >> qexists_tac `s` >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem copy_runtime_recorded_resources:
  copy_runtime_frame sa s sb t /\ alloca_inv s /\ alloca_room ctx func s /\
  (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w) ==>
  (t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)) /\
  alloca_inv t /\ alloca_room ctx func t /\
  (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP t.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w)
Proof
  strip_tac >> drule_all copy_runtime_allocation_resources >> strip_tac >>
  conj_tac >- asm_rewrite_tac[] >>
  irule allocation_fields_recorded_resources >> qexists_tac `s` >>
  simp[] >> first_assum ACCEPT_TAC
QED
