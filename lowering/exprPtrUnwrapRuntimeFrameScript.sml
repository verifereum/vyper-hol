Theory exprPtrUnwrapRuntimeFrame
Ancestors
  exprPtrUnwrapCopyFrames exprPtrUnwrapFullFrames exprPtrUnwrapLoopInvariant
  exprPtrUnwrapFrames slotCopyExecution fragGasPathPtr fragGasSeqPtr
  bodyPtrDefs ptrDiscipline finite_map venomExecSemantics venomState
  compileEnv loweringStateRelDefs copyExecution arithmetic

(* Runtime companion to slot_copy_inv: projections at the same counted witness
   make downstream loop composition independent of semantic witness choices. *)
Definition slot_copy_runtime_frame_def:
  slot_copy_runtime_frame cs d i r s <=>
    s.vs_allocas = r.vs_allocas /\ s.vs_alloca_next = r.vs_alloca_next /\
    s.vs_accounts = r.vs_accounts /\ s.vs_transient = r.vs_transient /\
    s.vs_call_ctx = r.vs_call_ctx /\
    (!op. slot_copy_external cs op ==> eval_operand op s = eval_operand op r) /\
    (!a. ~(w2n d <= a /\ a < w2n d+32*i) ==>
      mem_bytes_at a 1 s.vs_memory = mem_bytes_at a 1 r.vs_memory) /\
    copy_static s = copy_static r /\
    LENGTH r.vs_memory <= LENGTH s.vs_memory /\
    (!a k. a+k <= w2n d \/ w2n d+32*i <= a ==>
      mem_bytes_at a k s.vs_memory = mem_bytes_at a k r.vs_memory)
End

Theorem slot_copy_runtime_frame_initial:
  slot_copy_runtime_frame cs d 0 s (slot_copy_initial cs s)
Proof
  simp[slot_copy_runtime_frame_def, copy_initial_runtime_frame,
       copy_initial_external_operand, copy_initial_static,
       slot_copy_initial_def, jump_to_def, update_var_def]
QED

Theorem slot_copy_runtime_frame_condition:
  slot_copy_runtime_frame cs d i r s ==>
  slot_copy_runtime_frame cs d i r (slot_copy_cond_result cs n i s)
Proof
  simp[slot_copy_runtime_frame_def, copy_condition_allocation_frame,
       slot_copy_cond_frame, slot_copy_cond_operand, copy_condition_static,
       slot_copy_cond_result_def, jump_to_def, update_var_def] >> metis_tac[]
QED

Theorem slot_copy_runtime_frame_body:
  slot_copy_runtime_frame cs d i r s /\ w2n d+32*n < 2**256 /\ i<n ==>
  slot_copy_runtime_frame cs d (i+1) r (slot_copy_body_result cs p d load i s)
Proof
  simp[slot_copy_runtime_frame_def, copy_body_allocation_frame,
       slot_copy_body_sources, slot_copy_body_operand, copy_body_static] >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >> irule copy_body_exterior_prefix >>
      (conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[])) >>
      simp[] >> qexists `n` >> simp[]) >>
  conj_tac
  >- (mp_tac (SPEC_ALL copy_body_memory_length) >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `a+k <= w2n d \/ w2n d+32*i <= a` by decide_tac >>
  `mem_bytes_at a k (slot_copy_body_result cs p d load i s).vs_memory =
    mem_bytes_at a k s.vs_memory` by
    (irule copy_body_exterior_slice >> qexists `i+1` >> simp[] >> decide_tac) >>
  simp[]
QED

Theorem copy_external_ptr_covers:
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_external cs (Var x) /\ eval_operand (Var x) s = eval_operand (Var x) r ==>
  (ptr_covers G tn x s k <=> ptr_covers G0 tn0 x r k)
Proof
  strip_tac >> irule copy_ptr_covers_transport >>
  fs[slot_copy_ghost_inv_def, eval_operand_def]
QED

Theorem slot_copy_not_fresh_external:
  not_fresh_at cs x ==> slot_copy_external cs (Var x)
Proof
  simp[not_fresh_at_def, slot_copy_external_def, slot_copy_var_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem slot_copy_semantic_frame:
  slot_copy_runtime_frame cs d n r s /\ 32*n <= nb ==>
  (!x. not_fresh_at cs x ==> lookup_var x s = lookup_var x r) /\
  copy_static s = copy_static r /\ LENGTH r.vs_memory <= LENGTH s.vs_memory /\
  (!off len. off+len <= w2n d \/ w2n d+nb <= off ==>
    mem_bytes_at off len s.vs_memory = mem_bytes_at off len r.vs_memory)
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `slot_copy_external cs (Var x)` by metis_tac[slot_copy_not_fresh_external] >>
      fs[slot_copy_runtime_frame_def] >>
      first_x_assum drule >> simp[eval_operand_def]) >>
  fs[slot_copy_runtime_frame_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED
