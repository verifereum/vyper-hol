(* Allocation ownership for actual return-source windows.  A source window
   may occupy only a slice of its owning allocation, not its declared type. *)
Theory externalReturnWindowResource
Ancestors
  allocaSiteResource abiCallerAllocation abiEncoderProps fragExec venomState venomInst
  venomMemDefs venomExecSemantics finite_map pred_set arithmetic

Theorem return_window_owned_separate:
  alloca_inv s /\
  FLOOKUP s.vs_allocas owner = SOME (loff,capacity) /\
  loff <= sb /\ sb + cap <= loff + capacity /\ owner <> site /\
  FLOOKUP s.vs_allocas site = SOME (b,sz) ==>
  venomMemDefs$regions_disjoint (sb,cap) (b,sz)
Proof
  strip_tac >> drule_all abi_caller_allocation_separate >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

(* Only actual ALLOCA instructions in the encoder fragment are constrained.
   Size agreement is an ownership input: exec_alloca reuses registered sizes
   without checking the literal operand. *)
Theorem return_window_registered_sites:
  alloca_inv s /\
  FLOOKUP s.vs_allocas source_id = SOME (loff,capacity) /\
  loff <= sb /\ sb + cap <= loff + capacity /\
  FLOOKUP s.vs_allocas output_id = SOME (d,output_capacity) /\
  len <= output_capacity /\ source_id <> output_id /\
  (!inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids st st' ==>
     inst.inst_id <> source_id /\ inst.inst_id <> output_id) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids st st' /\
     FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32) ==>
  sb + cap <= s.vs_alloca_next /\
  d + len <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (d,len) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids st st' /\
     FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
     venomMemDefs$regions_disjoint (d,len) (b,sz))
Proof
  strip_tac >>
  `loff + capacity <= s.vs_alloca_next` by
    metis_tac[alloca_site_registered_below] >>
  `d + output_capacity <= s.vs_alloca_next` by
    metis_tac[alloca_site_registered_below] >>
  `venomMemDefs$regions_disjoint (sb,cap) (d,output_capacity)` by
    (irule return_window_owned_separate >> metis_tac[]) >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  conj_tac
  >- (fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
  `inst.inst_id <> source_id /\ inst.inst_id <> output_id` by metis_tac[] >>
  conj_tac
  >- (irule return_window_owned_separate >>
      qexistsl_tac [`capacity`, `loff`, `source_id`, `s`, `inst.inst_id`] >>
      simp[]) >>
  irule return_window_owned_separate >>
  qexistsl_tac [`output_capacity`, `d`, `output_id`, `s`, `inst.inst_id`] >>
  simp[]
QED

(* Fresh and re-entered return-buffer allocations share the same interface.
   The source needs only its actual read-window bound. *)
Theorem return_window_allocate:
  alloca_room ctx func s /\ alloca_inv s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit n] /\ inst.inst_outputs = [out] /\
  sb + cap <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = w2n n /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) ==>
  ?t b. exec_alloca inst s n = OK t /\
    alloca_room ctx func t /\ alloca_inv t /\
    lookup_var out t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,w2n n) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    b + w2n n <= t.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (b,w2n n) /\
    (!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  `!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n`
    by metis_tac[] >>
  drule_all alloca_site_execute >> strip_tac >>
  `venomMemDefs$regions_disjoint (sb,cap) (b,w2n n)` by
    (irule alloca_site_execute_protected >> metis_tac[]) >>
  qexistsl_tac [`t`, `b`] >> simp[]
QED

Theorem return_window_alloca_frame:
  inst.inst_outputs = [out] /\ exec_alloca inst s n = OK t ==>
  (!id. id <> inst.inst_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
  t.vs_pending_deletions = s.vs_pending_deletions /\
  t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
  t.vs_inst_idx = s.vs_inst_idx /\ t.vs_labels = s.vs_labels
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- gvs[exec_alloca_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  gvs[exec_alloca_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem return_window_allocated_sites:
  inst.inst_outputs = [out] /\ exec_alloca inst s n = OK t /\
  alloca_inv t /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (d,msz) /\
  len <= msz /\
  (!i. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
     i.inst_id IN frag_ids st st' ==> i.inst_id <> inst.inst_id) /\
  (!i b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
     i.inst_id IN frag_ids st st' /\
     FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==>
     sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) ==>
  !i b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_id IN frag_ids st st' /\
    FLOOKUP t.vs_allocas i.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,len) (b,sz)
Proof
  strip_tac >> drule_all return_window_alloca_frame >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `i.inst_id <> inst.inst_id` by metis_tac[] >>
  `FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz)` by metis_tac[] >>
  `sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)`
    by metis_tac[] >> simp[] >>
  `venomMemDefs$regions_disjoint (d,msz) (b,sz)` by
    (irule alloca_site_registered_disjoint >> metis_tac[]) >>
  pop_assum mp_tac >>
  simp_tac std_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem return_window_alloca_operand:
  inst.inst_outputs = [out] /\ exec_alloca inst s n = OK t /\
  op <> Var out ==> eval_operand op t = eval_operand op s
Proof
  strip_tac >> drule_all return_window_alloca_frame >> strip_tac >>
  Cases_on `op` >> gvs[eval_operand_def]
QED

Theorem return_window_allocate_entry_resources:
  alloca_room ctx func s /\ alloca_inv s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit n] /\ inst.inst_outputs = [out] /\
  sb + cap <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = w2n n /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
  len <= w2n n /\ op <> Var out /\
  (!i. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_id IN frag_ids sa se ==> i.inst_id <> inst.inst_id) /\
  (!i b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_id IN frag_ids sa se /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) ==>
  ?t d. exec_alloca inst s n = OK t /\
    alloca_room ctx func t /\ alloca_inv t /\
    lookup_var out t = SOME (n2w d) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (d,w2n n) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    d + w2n n <= t.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,w2n n) /\
    (!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    (!id. id <> inst.inst_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\
    t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx /\ t.vs_labels = s.vs_labels /\
    eval_operand op t = eval_operand op s /\
    d + len <= t.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,len) /\
    (!i b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
      i.inst_id IN frag_ids sa se /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
      venomMemDefs$regions_disjoint (d,len) (b,sz))
Proof
  strip_tac >> drule_all return_window_allocate >> strip_tac >>
  drule_all return_window_alloca_frame >> strip_tac >>
  drule_all return_window_alloca_operand >> disch_tac >>
  `b + len <= t.vs_alloca_next` by decide_tac >>
  `venomMemDefs$regions_disjoint (sb,cap) (b,len)` by
    (qpat_x_assum `venomMemDefs$regions_disjoint (sb,cap) (b,w2n n)` mp_tac >>
     simp_tac std_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qexistsl_tac [`t`, `b`] >>
  ntac 26 (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  drule_all return_window_allocated_sites >> simp[]
QED
