(* Safety witnesses deliberately need not agree on memory. The bump
   pointer is retained here: coarse dse_equiv does not retain it. *)
Theory deadStoreElimSafety
Ancestors
  deadStoreElimDefs deadStoreElimMemory basePtrDefs memLocDefs venomMemDefs
  venomInst venomState venomExecSemantics venomMemProps passSharedProps passSharedDefs
  passSimulationDefs

Definition dse_safety_agrees_def:
  dse_safety_agrees s t <=>
    (!v. lookup_var v s = lookup_var v t) /\
    s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next /\
    s.vs_labels = t.vs_labels
End

Definition dse_safety_witness_def:
  dse_safety_witness safe_inv fn inst t <=>
    ?s bb. safe_inv s /\ dse_safety_agrees s t /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst
End

Theorem dse_safety_agrees_refl:
  dse_safety_agrees s s
Proof
  simp[dse_safety_agrees_def]
QED

Theorem dse_safety_witness_initial:
  safe_inv s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  dse_safety_witness safe_inv fn inst s
Proof
  simp[dse_safety_witness_def] >> metis_tac[dse_safety_agrees_refl]
QED

Theorem dse_safety_agrees_alloca_inv:
  dse_safety_agrees s t ==> (alloca_inv s <=> alloca_inv t)
Proof
  simp[dse_safety_agrees_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Theorem dse_safety_agrees_alloca_bounds:
  dse_safety_agrees s t ==>
  ((!aid base sz. FLOOKUP s.vs_allocas aid = SOME (base,sz) ==>
                   base + sz < dimword (:256)) <=>
   (!aid base sz. FLOOKUP t.vs_allocas aid = SOME (base,sz) ==>
                   base + sz < dimword (:256)))
Proof
  simp[dse_safety_agrees_def] >> metis_tac[]
QED

Theorem dse_safety_agrees_ptr_matches:
  dse_safety_agrees s t ==> (ptr_matches_var p v s <=> ptr_matches_var p v t)
Proof
  strip_tac >> Cases_on `p` >> rename1 `Ptr alloc off` >>
  Cases_on `alloc` >> Cases_on `off` >>
  gvs[ptr_matches_var_def, dse_safety_agrees_def]
QED

Theorem dse_safety_agrees_ptr_sound:
  dse_safety_agrees s t ==> (bp_ptr_sound bp s <=> bp_ptr_sound bp t)
Proof
  strip_tac >>
  drule dse_safety_agrees_ptr_matches >>
  gvs[bp_ptr_sound_def, dse_safety_agrees_def] >> metis_tac[]
QED

Theorem dse_safety_agrees_within_alloca:
  dse_safety_agrees s t ==>
  (memloc_within_alloca ml s <=> memloc_within_alloca ml t)
Proof
  simp[dse_safety_agrees_def, memloc_within_alloca_def] >> metis_tac[]
QED

Theorem dse_safety_agrees_ptrs_bounded:
  dse_safety_agrees s t ==>
  (bp_ptrs_bounded bp fn s <=> bp_ptrs_bounded bp fn t)
Proof
  strip_tac >>
  drule dse_safety_agrees_within_alloca >>
  simp[bp_ptrs_bounded_def] >> metis_tac[]
QED

Theorem dse_safety_agrees_eval_operand:
  dse_safety_agrees s t ==> eval_operand op s = eval_operand op t
Proof
  Cases_on `op` >> simp[eval_operand_def, dse_safety_agrees_def]
QED

Theorem dse_safety_agrees_accesses:
  dse_safety_agrees s t ==>
  (bp_accesses_in_own_alloca bp inst s <=> bp_accesses_in_own_alloca bp inst t)
Proof
  strip_tac >>
  drule dse_safety_agrees_eval_operand >>
  gvs[bp_accesses_in_own_alloca_def, dse_safety_agrees_def] >> metis_tac[]
QED

(* A memory-dependent safe_invariant need not hold on the projected state. *)
Theorem dse_safety_memory_probe:
  s.vs_memory = [] ==>
  dse_safety_agrees (mstore 0 1w s) s /\
  (mstore 0 1w s).vs_memory <> s.vs_memory
Proof
  strip_tac >> conj_tac
  >- simp[dse_safety_agrees_def, mstore_eq_write_mem,
          write_memory_with_expansion_def, lookup_var_def] >>
  `LENGTH (mstore 0 1w s).vs_memory = 32` by simp[LENGTH_mstore_eq] >>
  strip_tac >> gvs[]
QED

Theorem dse_safety_witness_accesses:
  dse_safety_witness safe_inv fn inst t /\
  (!s bb. safe_inv s /\
     lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME inst ==>
     bp_accesses_in_own_alloca bp inst s) ==>
  bp_accesses_in_own_alloca bp inst t
Proof
  simp[dse_safety_witness_def] >> rpt strip_tac >>
  drule_all dse_safety_agrees_accesses >> metis_tac[]
QED

(* The target cursor is independent of the original witness cursor.
   During NOP replacement it is the same index; after clearing it is the
   number of retained instructions in the original prefix. *)
Theorem dse_safety_witness_index:
  dse_safety_witness safe_inv fn inst t ==>
  dse_safety_witness safe_inv fn inst (t with vs_inst_idx := j)
Proof
  simp[dse_safety_witness_def, dse_safety_agrees_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem dse_safety_memory_witness_probe:
  s.vs_memory = [] /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  dse_safety_witness (\u. u.vs_memory = []) fn inst (mstore 0 1w s) /\
  (mstore 0 1w s).vs_memory <> []
Proof
  rpt strip_tac
  >- (simp[dse_safety_witness_def] >>
      qexistsl [`s`, `bb`] >>
      simp[dse_safety_agrees_def, mstore_eq_write_mem,
           write_memory_with_expansion_def, lookup_var_def]) >>
  `LENGTH (mstore 0 1w s).vs_memory = 32` by simp[LENGTH_mstore_eq] >>
  gvs[]
QED

Theorem dse_clear_nops_retained_instruction:
  get_instruction bb i = SOME inst /\ inst.inst_opcode <> NOP ==>
  get_instruction (clear_nops_block bb)
    (LENGTH (FILTER (\x. x.inst_opcode <> NOP) (TAKE i bb.bb_instructions))) =
    SOME inst
Proof
  simp[get_instruction_def, clear_nops_block_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- (irule filter_take_lt >> simp[]) >>
  irule filter_take_el >> simp[]
QED

(* Same-index boundary, extracted unchanged from deadStoreElimProofs. *)
Theorem get_instruction_block_map_transform:
  !f bb idx.
    get_instruction (block_map_transform f bb) idx =
    case get_instruction bb idx of NONE => NONE | SOME i => SOME (f i)
Proof
  simp[get_instruction_def, block_map_transform_def] >>
  rw[] >> simp[listTheory.EL_MAP]
QED
