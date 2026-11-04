Theory lowerDloadPtrBoundary
Ancestors
  ptrDiscipline lowerDloadDefs venomExecSemantics finite_map words

Theorem exec_alloca_fresh_site:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  exec_alloca inst s amount =
    OK (update_var out (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
                   (inst.inst_id, (s.vs_alloca_next, w2n amount));
                vs_alloca_next := s.vs_alloca_next + w2n amount|>))
Proof
  simp[exec_alloca_def]
QED

Theorem exec_alloca_repeated_site:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  exec_alloca inst s amount = OK (update_var out (n2w b) s)
Proof
  simp[exec_alloca_def]
QED

Theorem merge_callee_allocation_frame:
  (merge_callee_state caller callee).vs_allocas = caller.vs_allocas /\
  (merge_callee_state caller callee).vs_alloca_next = caller.vs_alloca_next
Proof
  simp[merge_callee_state_def]
QED

Theorem positive_site_translation_order:
  0 < (sz:num) /\ b <= x /\ x <= b + sz /\
  b <= y /\ y <= b + sz ==>
  ((x + delta = y + delta <=> x = y) /\
   (x + delta < y + delta <=> x < y) /\
   b + delta <= x + delta /\ x + delta <= b + delta + sz /\
   b + delta <= y + delta /\ y + delta <= b + delta + sz)
Proof
  rpt strip_tac >> decide_tac
QED

Theorem dload_headroom_one_scratch:
  dload_headroom_ok ctx fn inst s /\ 0 < ctx_dload_count ctx ==>
  s.vs_alloca_next + 32 < dimword (:256)
Proof
  simp[dload_headroom_ok_def] >> decide_tac
QED
