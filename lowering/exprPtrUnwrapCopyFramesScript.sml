Theory exprPtrUnwrapCopyFrames
Ancestors
  slotCopyExecution copyExecution valueEncodingProps valueEncoding
  venomState venomExecSemantics

Theorem copy_initial_runtime_frame:
  (slot_copy_initial cs s).vs_allocas = s.vs_allocas /\
  (slot_copy_initial cs s).vs_alloca_next = s.vs_alloca_next /\
  (slot_copy_initial cs s).vs_memory = s.vs_memory /\
  (slot_copy_initial cs s).vs_accounts = s.vs_accounts /\
  (slot_copy_initial cs s).vs_transient = s.vs_transient /\
  (slot_copy_initial cs s).vs_call_ctx = s.vs_call_ctx
Proof
  simp[slot_copy_initial_def, update_var_def, jump_to_def]
QED

Theorem copy_initial_external_operand:
  slot_copy_external cs op ==>
  eval_operand op (slot_copy_initial cs s) = eval_operand op s
Proof
  strip_tac >>
  `op <> Var (slot_copy_var cs 0)` by
    (fs[slot_copy_external_def] >> metis_tac[DECIDE ``0<7``]) >>
  Cases_on `op` >> gvs[slot_copy_initial_def, update_var_def, jump_to_def,
    eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem copy_condition_allocation_frame:
  (slot_copy_cond_result cs n i s).vs_allocas = s.vs_allocas /\
  (slot_copy_cond_result cs n i s).vs_alloca_next = s.vs_alloca_next
Proof
  simp[slot_copy_cond_result_def, update_var_def, jump_to_def]
QED

Theorem copy_body_allocation_frame:
  (slot_copy_body_result cs p d load i s).vs_allocas = s.vs_allocas /\
  (slot_copy_body_result cs p d load i s).vs_alloca_next = s.vs_alloca_next
Proof
  simp[slot_copy_body_result_def, update_var_def, jump_to_def, mstore_def,
       write_memory_with_expansion_def]
QED

Theorem copy_body_exterior_byte:
  w2n d + 32*n < 2**256 /\ i < n /\
  ~(w2n d+32*i <= a /\ a < w2n d+32*(i+1)) ==>
  mem_bytes_at a 1 (slot_copy_body_result cs p d load i s).vs_memory =
    mem_bytes_at a 1 s.vs_memory
Proof
  strip_tac >>
  `w2n (d+n2w i*32w) = w2n d+32*i` by
    (irule slot_copy_body_nonwrapping >> qexists `n` >> simp[]) >>
  simp[slot_copy_body_result_def, update_var_def, jump_to_def] >>
  `a+1 <= 32*i+w2n d \/ 32*i+w2n d+32 <= a` by decide_tac >>
  simp[mstore_mem_bytes_at_disjoint]
QED

Theorem copy_body_exterior_prefix:
  w2n d+32*n < 2**256 /\ i < n /\
  (!a. ~(w2n d <= a /\ a < w2n d+32*i) ==>
    mem_bytes_at a 1 s.vs_memory = mem_bytes_at a 1 r.vs_memory) ==>
  !a. ~(w2n d <= a /\ a < w2n d+32*(i+1)) ==>
  mem_bytes_at a 1 (slot_copy_body_result cs p d load i s).vs_memory =
    mem_bytes_at a 1 r.vs_memory
Proof
  rpt strip_tac >>
  `~(w2n d+32*i <= a /\ a < w2n d+32*(i+1))` by decide_tac >>
  drule_all copy_body_exterior_byte >> simp[] >>
  disch_then SUBST1_TAC >> first_x_assum irule >> decide_tac
QED
