Theory concretizePtrOwnerSeeds
Ancestors
  concretizePtrReadOrigin concretizePtrWriteByteOrigin concretizePtrOwnerPath
  concretizePtrAllocationOwnership concretizePtrChronologicalDemand
  concretizePtrRuntimeGeneration
  concretizePtrChronologicalHistory ptrDiscipline venomInst venomState
  list rich_list finite_map

Theorem ptr_owner_view_index:
  d <= LENGTH obs.po_stack ==>
  (ptr_owner_view d obs).cf_state =
    EL (LENGTH obs.po_stack - d)
      (obs.po_state :: MAP (\f. f.cf_state) obs.po_stack)
Proof
  strip_tac >> simp[ptr_owner_view_def] >>
  Cases_on `d = LENGTH obs.po_stack` >> simp[] >>
  Cases_on `LENGTH obs.po_stack - d` >- gvs[] >>
  `LENGTH obs.po_stack - (d + 1) = n` by decide_tac >>
  simp[EL_MAP]
QED

Theorem ptr_owner_overlap_unique:
  ptr_active_alloc_geometry
    (obs.po_state :: MAP (\f. f.cf_state) obs.po_stack) /\
  d <= LENGTH obs.po_stack /\ e <= LENGTH obs.po_stack /\
  FLOOKUP (ptr_owner_view d obs).cf_state.vs_allocas aid = SOME (b,sz) /\
  FLOOKUP (ptr_owner_view e obs).cf_state.vs_allocas aid' = SOME (b',sz') /\
  b <= x /\ x < b + sz /\ b' <= x /\ x < b' + sz' ==>
  d = e /\ aid = aid'
Proof
  strip_tac >>
  `LENGTH obs.po_stack - d = LENGTH obs.po_stack - e /\ aid = aid'` by
    (irule ptr_active_alloc_unique_owner >>
     goal_assum (drule_at (Pat `ptr_active_alloc_geometry _`)) >>
     qexistsl_tac [`b`,`b'`,`sz`,`sz'`,`x`] >>
     gvs[ptr_owner_view_index]) >> decide_tac
QED

Theorem ptr_owner_view_saved[local]:
  n < LENGTH obs.po_stack ==>
  ptr_owner_view (LENGTH obs.po_stack - (n + 1)) obs = EL n obs.po_stack
Proof
  strip_tac >>
  `LENGTH obs.po_stack - n - 1 <> LENGTH obs.po_stack /\
   LENGTH obs.po_stack - (LENGTH obs.po_stack - n - 1) - 1 = n` by decide_tac >>
  simp[ptr_owner_view_def]
QED

Theorem ptr_owner_seed_identify[local]:
  ptr_active_alloc_geometry
    (obs.po_state :: MAP (\f. f.cf_state) obs.po_stack) /\
  d <= LENGTH obs.po_stack /\
  FLOOKUP (ptr_owner_view d obs).cf_state.vs_allocas aid = SOME (b,sz) /\
  b <= x /\ x < b + sz /\ b' <= x /\ x < b' + sz' /\
  ((?a. FLOOKUP obs.po_state.vs_allocas a = SOME (b',sz') /\
     Q (ptr_owner_view (LENGTH obs.po_stack) obs) a) \/
   (?n a. n < LENGTH obs.po_stack /\
     FLOOKUP (EL n obs.po_stack).cf_state.vs_allocas a = SOME (b',sz') /\
     Q (EL n obs.po_stack) a)) ==>
  Q (ptr_owner_view d obs) aid
Proof
  strip_tac
  >- (`d = LENGTH obs.po_stack /\ aid = a` by
        (irule ptr_owner_overlap_unique >>
         goal_assum (drule_at (Pat `ptr_active_alloc_geometry _`)) >>
         qexistsl_tac [`b`,`b'`,`sz`,`sz'`,`x`] >> simp[]) >> gvs[]) >>
  `LENGTH obs.po_stack - n - 1 <= LENGTH obs.po_stack` by decide_tac >>
  `d = LENGTH obs.po_stack - n - 1 /\ aid = a` by
    (irule ptr_owner_overlap_unique >>
     goal_assum (drule_at (Pat `ptr_active_alloc_geometry _`)) >>
     qexistsl_tac [`b`,`b'`,`sz`,`sz'`,`x`] >> simp[ptr_owner_view_saved]) >>
  gvs[ptr_owner_view_saved]
QED

Theorem ptr_owner_selected_read_seed:
  ptr_observation_reachable vs C obs /\ vs.vs_allocas = FEMPTY /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  d <= LENGTH obs.po_stack /\
  FLOOKUP (ptr_owner_view d obs).cf_state.vs_allocas aid = SOME (b,sz) /\
  MEM (Var v) obs.po_inst.inst_operands /\
  (inst_read_op obs.po_inst = SOME (Var v) \/ obs.po_inst.inst_opcode = INVOKE) /\
  FLOOKUP obs.po_prov v = SOME (b,sz) /\ 0 < sz ==>
  ml_read_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d obs).cf_fn)
      (cfg_analyze (ptr_owner_view d obs).cf_fn) (ptr_owner_view d obs).cf_fn)
    mems (ptr_owner_view d obs).cf_inst
Proof
  simp[ptr_observation_reachable_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_frame_alloc_geometry >> strip_tac >>
  irule (BETA_RULE (Q.INST [`Q` |-> `\f a. ml_read_gen (Allocation a)
    (bp_analyze_fuel (concretize_memloc_fuel f.cf_fn) (cfg_analyze f.cf_fn) f.cf_fn)
    mems f.cf_inst`] (SPEC_ALL ptr_owner_seed_identify))) >>
  goal_assum (drule_at (Pat `ptr_active_alloc_geometry _`)) >> simp[] >>
  qexistsl_tac [`b`,`sz`,`b`] >> simp[] >>
  drule_all ptr_frame_selected_read_seed >> metis_tac[]
QED

Theorem ptr_owner_write_byte_seed:
  ptr_observation_reachable vs C obs /\ vs.vs_allocas = FEMPTY /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  d <= LENGTH obs.po_stack /\
  FLOOKUP (ptr_owner_view d obs).cf_state.vs_allocas aid = SOME (b,sz) /\
  access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state /\
  ~in_revert_forward obs.po_fn obs.po_state /\ lo <= x /\
  b <= x /\ x < b + sz /\
  x IN range_bytes (source_memory_write_ranges obs.po_inst obs.po_state) ==>
  ml_used_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d obs).cf_fn)
      (cfg_analyze (ptr_owner_view d obs).cf_fn) (ptr_owner_view d obs).cf_fn)
    mems (ptr_owner_view d obs).cf_inst
Proof
  simp[ptr_observation_reachable_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_frame_alloc_geometry >> strip_tac >>
  drule_all ptr_write_byte_selected_site >> strip_tac >>
  rename1 `FLOOKUP obs.po_prov v = SOME (wb,ws)` >>
  `MEM (Var v) obs.po_inst.inst_operands` by metis_tac[ptr_write_op_operand] >>
  irule (BETA_RULE (Q.INST [`Q` |-> `\f a. ml_used_gen (Allocation a)
    (bp_analyze_fuel (concretize_memloc_fuel f.cf_fn) (cfg_analyze f.cf_fn) f.cf_fn)
    mems f.cf_inst`] (SPEC_ALL ptr_owner_seed_identify))) >>
  goal_assum (drule_at (Pat `ptr_active_alloc_geometry _`)) >> simp[] >>
  qexistsl_tac [`wb`,`ws`,`x`] >> simp[] >>
  drule_all ptr_frame_operand_seed >> metis_tac[]
QED
