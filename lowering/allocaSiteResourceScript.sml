(* Actual-site allocation room: independent of any ABI descriptor or budget. *)
Theory allocaSiteResource
Ancestors
  exprLoweringProps localPtrsProps venomExecSemantics venomMemDefs venomState
  venomInst finite_map words arithmetic

Theorem alloca_site_fresh:
  alloca_room ctx func s /\ alloca_inv s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit n] /\ inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  ?t. exec_alloca inst s n = OK t /\
    alloca_room ctx func t /\ alloca_inv t /\
    lookup_var out t = SOME (n2w s.vs_alloca_next) /\
    t.vs_alloca_next = s.vs_alloca_next + w2n n /\
    t.vs_allocas = s.vs_allocas |+ (inst.inst_id,(s.vs_alloca_next,w2n n)) /\
    s.vs_alloca_next + w2n n < dimword (:256) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  `inst.inst_id NOTIN FDOM s.vs_allocas` by metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  drule_all alloca_room_fresh >> strip_tac >>
  qexists_tac `update_var out (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+
      (inst.inst_id,(s.vs_alloca_next,w2n n));
      vs_alloca_next := s.vs_alloca_next + w2n n|>)` >>
  `exec_alloca inst s n = OK (update_var out (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+
      (inst.inst_id,(s.vs_alloca_next,w2n n));
      vs_alloca_next := s.vs_alloca_next + w2n n|>))` by
    simp[exec_alloca_def] >>
  simp[] >> conj_tac
  >- (irule alloca_room_fields >> goal_assum (drule_at Any) >>
      simp[update_var_def]) >>
  conj_tac >- (drule_all alloca_inv_exec_alloca >> simp[]) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem alloca_site_reuse:
  alloca_room ctx func s /\ alloca_inv s /\
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  exec_alloca inst s (n:bytes32) = OK (update_var out (n2w b) s) /\
  alloca_room ctx func (update_var out (n2w b) s) /\
  alloca_inv (update_var out (n2w b) s) /\
  lookup_var out (update_var out (n2w b) s) = SOME (n2w b) /\
  (update_var out (n2w b) s).vs_allocas = s.vs_allocas /\
  (update_var out (n2w b) s).vs_alloca_next = s.vs_alloca_next /\
  b + sz <= s.vs_alloca_next
Proof
  strip_tac >> simp[exec_alloca_def, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE] >> conj_tac
  >- (irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
  conj_tac
  >- (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  gvs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]
QED

Theorem alloca_site_execute:
  alloca_room ctx func s /\ alloca_inv s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit n] /\ inst.inst_outputs = [out] /\
  (!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) ==>
  ?t b. exec_alloca inst s n = OK t /\
    alloca_room ctx func t /\ alloca_inv t /\
    lookup_var out t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,w2n n) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    b + w2n n <= t.vs_alloca_next /\
    (!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (drule_all alloca_site_fresh >> strip_tac >>
      qexistsl_tac [`t`, `s.vs_alloca_next`] >>
      simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
      Cases_on `id = inst.inst_id` >> gvs[]) >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  drule_all alloca_site_reuse >>
  disch_then (qspec_then `n` strip_assume_tac) >>
  qexistsl_tac [`update_var out (n2w pair0) s`, `pair0`] >>
  gvs[update_var_def]
QED

Theorem alloca_site_registered_below:
  alloca_inv s /\ FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
  b + sz <= s.vs_alloca_next
Proof
  simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]
QED

Theorem alloca_site_registered_disjoint:
  alloca_inv s /\ id <> other /\
  FLOOKUP s.vs_allocas id = SOME (b,sz) /\
  FLOOKUP s.vs_allocas other = SOME (p,n) ==>
  venomMemDefs$regions_disjoint (b,sz) (p,n)
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def,
    venomMemDefsTheory.regions_disjoint_def] >> metis_tac[ADD_COMM]
QED

Theorem alloca_site_fresh_protected:
  q + len <= s.vs_alloca_next ==>
  venomMemDefs$regions_disjoint (q,len) (s.vs_alloca_next,n)
Proof
  simp[venomMemDefsTheory.regions_disjoint_def]
QED

Theorem alloca_site_preserved_protection:
  alloca_inv t /\
  (!id b sz. FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
    FLOOKUP t.vs_allocas id = SOME (b,sz)) /\
  FLOOKUP s.vs_allocas parent = SOME (p,n) /\ child <> parent /\
  FLOOKUP t.vs_allocas child = SOME (b,sz) ==>
  venomMemDefs$regions_disjoint (p,n) (b,sz)
Proof
  strip_tac >> irule alloca_site_registered_disjoint >> metis_tac[]
QED

Theorem alloca_site_execute_protected:
  inst.inst_outputs = [out] /\ exec_alloca inst s (n:bytes32) = OK t /\
  q + len <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = w2n n /\ venomMemDefs$regions_disjoint (q,len) (b,sz)) /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,w2n n) ==>
  venomMemDefs$regions_disjoint (q,len) (b,w2n n)
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (gvs[exec_alloca_def, update_var_def, FLOOKUP_UPDATE] >>
      irule alloca_site_fresh_protected >> simp[]) >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  fs[exec_alloca_def] >> gvs[update_var_def] >>
  first_x_assum (qspecl_then [`pair0`, `pair1`] mp_tac) >> simp[]
QED

Theorem alloca_site32_execute:
  alloca_room ctx func s /\ alloca_inv s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit 32w] /\ inst.inst_outputs = [out] /\
  (!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32) ==>
  ?t b. exec_alloca inst s (32w:bytes32) = OK t /\
    alloca_room ctx func t /\ alloca_inv t /\
    lookup_var out t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\ b + 32 <= t.vs_alloca_next /\
    (!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  `w2n (32w:bytes32) = 32` by
    simp_tac (srw_ss()) [w2n_n2w, dimword_def,
      fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  mp_tac (Q.INST [`n` |-> `(32w:bytes32)`] alloca_site_execute) >>
  asm_rewrite_tac[]
QED

Theorem alloca_site32_reentry:
  alloca_room ctx func s /\ alloca_inv s /\
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,32) ==>
  exec_alloca inst s (32w:bytes32) = OK (update_var out (n2w b) s) /\
  alloca_room ctx func (update_var out (n2w b) s) /\
  alloca_inv (update_var out (n2w b) s) /\
  (update_var out (n2w b) s).vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all alloca_site_reuse >>
  disch_then (qspec_then `32w` strip_assume_tac) >> simp[]
QED
