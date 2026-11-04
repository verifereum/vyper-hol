Theory lowerDloadPtrBoundary
Ancestors
  ptrDiscipline lowerDloadDefs venomExecSemantics venomState finite_map words

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

Theorem positive_site_pair_unique:
  (!i j (b:num) n c m. FLOOKUP sites i = SOME (b,n) /\
     FLOOKUP sites j = SOME (c,m) /\ i <> j /\ 0 < n /\ 0 < m ==>
     b+n <= c \/ c+m <= b) /\
  FLOOKUP sites i = SOME (b,n) /\ FLOOKUP sites j = SOME (b,n) /\
  0 < n ==> i = j
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem fresh_interval_disjoint:
  (b:num)+n <= frontier ==>
  ~(?x. b <= x /\ x < b+n /\ frontier <= x /\ x < frontier+m)
Proof
  decide_tac
QED

Theorem exec_alloca_repeated_frame:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  exec_alloca inst s amount = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all exec_alloca_repeated_site >>
  simp[update_var_def] >> strip_tac >> gvs[]
QED

Theorem exec_alloca_fresh_bounded:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst s amount = OK t /\ lo <= s.vs_alloca_next /\
  (!i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
           lo <= b /\ b+n <= s.vs_alloca_next) ==>
  !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
          lo <= b /\ b+n <= t.vs_alloca_next
Proof
  strip_tac >> drule_all exec_alloca_fresh_site >>
  simp[update_var_def] >> strip_tac >> gvs[] >> rpt strip_tac >>
  Cases_on `i = inst.inst_id` >> gvs[FLOOKUP_UPDATE] >>
  first_x_assum drule >> decide_tac
QED

Theorem exec_alloca_fresh_separated:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst s amount = OK t /\
  (!i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
           b+n <= s.vs_alloca_next) /\
  (!i j b n c m. FLOOKUP s.vs_allocas i = SOME (b,n) /\
     FLOOKUP s.vs_allocas j = SOME (c,m) /\ i <> j /\ 0 < n /\ 0 < m ==>
     b+n <= c \/ c+m <= b) ==>
  !i j b n c m. FLOOKUP t.vs_allocas i = SOME (b,n) /\
     FLOOKUP t.vs_allocas j = SOME (c,m) /\ i <> j /\ 0 < n /\ 0 < m ==>
     b+n <= c \/ c+m <= b
Proof
  strip_tac >> drule_all exec_alloca_fresh_site >>
  simp[update_var_def] >> strip_tac >> gvs[] >> rpt strip_tac >>
  Cases_on `i = inst.inst_id` >> Cases_on `j = inst.inst_id` >>
  gvs[FLOOKUP_UPDATE] >> metis_tac[]
QED
