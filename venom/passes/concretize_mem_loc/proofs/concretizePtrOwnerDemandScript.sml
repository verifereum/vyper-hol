Theory concretizePtrOwnerDemand
Ancestors
  concretizePtrImportOrigins concretizePtrKillSoundness
  concretizePtrOwnerPath concretizePtrEndpointOrigin
  concretizePtrChronologicalDemand concretizePtrChronologicalHistory
  ptrDiscipline o1PassContract venomInst list finite_map concretizeMemLocDefs
  memLocDefs venomExecSemantics opcodeClass concretizePtrLifetime
  concretizePtrReadCoverage

Theorem ptr_chrono_owner_allocation_inst:
  ptr_chrono_history vs C h endpoint /\ vs.vs_allocas = FEMPTY /\
  (!k. k < LENGTH h ==> (EL k h).po_inst.inst_opcode <> DALLOCA) /\
  j < LENGTH h /\ d <= LENGTH (EL j h).po_stack /\
  FLOOKUP (ptr_owner_view d (EL j h)).cf_state.vs_allocas aid = SOME site ==>
  ?inst. MEM inst (fn_insts (ptr_owner_view d (EL j h)).cf_fn) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = aid
Proof
  strip_tac >>
  `FLOOKUP (ptr_bottom_state d (EL j h)).vs_allocas aid = SOME site` by
    metis_tac[ptr_owner_view_state] >>
  drule_all ptr_chrono_endpoint_birth >> strip_tac >>
  `(ptr_owner_view d (EL i h)).cf_fn =
   (ptr_owner_view d (EL j h)).cf_fn` by
    (irule ptr_owner_view_interval_function >> simp[] >>
     qexistsl [`C`,`endpoint`,`vs`] >> simp[] >> decide_tac) >>
  `ptr_observation_reachable vs C (EL i h)` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL] >>
     strip_tac >> first_x_assum irule >> decide_tac) >>
  `MEM (EL i h).po_inst (fn_insts (EL i h).po_fn)` by
    (gvs[ptr_observation_reachable_def] >>
     drule ptr_frame_operand_instructions >> simp[]) >>
  qexists `(EL i h).po_inst` >> gvs[ptr_owner_view_def]
QED

Theorem ptr_chrono_write_step_success[local]:
  !C a z. ptr_chrono_step C a z ==>
    !n. inst_write_size a.po_inst = SOME n ==>
      ?fuel s'. step_inst fuel C a.po_inst a.po_state = OK s'
Proof
  rpt strip_tac >> drule ptr_write_size_ordinary >> strip_tac >>
  drule_all ptr_chrono_ordinary_step_success >> simp[]
QED

Theorem ptr_owner_interval_no_kill[local]:
  ptr_chrono_history vs C h endpoint /\ i <= j /\ j < LENGTH h /\
  (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) /\
  (!k. k < LENGTH h ==> (EL k h).po_inst.inst_opcode <> DALLOCA) /\
  (ptr_owner_view d (EL i h)).cf_fn = fn /\
  FLOOKUP (ptr_owner_view d (EL i h)).cf_state.vs_allocas aid = SOME (b,sz) /\
  b <= byte /\ byte < b + sz /\
  (!k. i <= k /\ k < j ==>
    ~in_revert_forward (EL k h).po_fn (EL k h).po_state /\
    (!n off len. inst_write_size (EL k h).po_inst = SOME n /\
      MEM (off,len) (source_memory_write_ranges (EL k h).po_inst (EL k h).po_state) ==>
      ~(off <= byte /\ byte < off + len))) /\
  o1_run_state_ok vs /\ o1_ctx_shape C /\ ~ctx_has_dalloca C /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  EVERY (\f. EVERY (\inst. inst.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  wf_function fn /\ all_reachable fn /\ ptr_discipline lo C vs /\
  ptr_bp_origins fn (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) /\
  ~MEM (Allocation aid) (MAP FST imports) ==>
  !k. i <= k /\ k < j ==>
  ~ptr_ml_can_kill (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (\a. if context_alloca_size fn imports a = 0 then NONE
         else SOME (context_alloca_size fn imports a))
    (ptr_owner_view d (EL k h)).cf_inst
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `k < LENGTH h /\ d <= LENGTH (EL k h).po_stack` by
    (conj_tac >- decide_tac >> first_x_assum irule >> decide_tac) >>
  `ptr_observation_reachable vs C (EL k h)` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL] >> metis_tac[]) >>
  Cases_on `d < LENGTH (EL k h).po_stack`
  >- (drule_all ptr_owner_view_active >> strip_tac >>
      simp[concretizePtrReadCoverageTheory.ptr_ml_can_kill_def,
           inst_write_size_def, mem_write_ops_def]) >>
  `d = LENGTH (EL k h).po_stack` by decide_tac >>
  `(ptr_owner_view d (EL i h)).cf_fn =
   (ptr_owner_view d (EL k h)).cf_fn` by
    (irule ptr_owner_view_interval_function >>
     rpt conj_tac
     >- (rpt strip_tac >> first_x_assum irule >> decide_tac)
     >- decide_tac >- decide_tac >> metis_tac[]) >>
  `(EL k h).po_fn = fn` by gvs[] >>
  `FLOOKUP (EL k h).po_state.vs_allocas aid = SOME (b,sz)` by
    (`FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = SOME (b,sz)`
       suffices_by gvs[] >>
     irule ptr_owner_view_lookup_interval >>
     conj_tac >- decide_tac >> conj_tac
     >- (qexists `i` >> simp[] >> conj_tac >> rpt strip_tac >>
         first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  simp[] >> strip_tac >>
  `?n. inst_write_size (EL k h).po_inst = SOME n` by
    metis_tac[concretizePtrReadCoverageTheory.ptr_ml_can_kill_def] >>
  `ptr_chrono_step C (EL k h) (EL (SUC k) h)` by
    (irule ptr_chrono_history_adjacent >>
     conj_tac >- decide_tac >> metis_tac[]) >>
  drule_all ptr_chrono_write_step_success >> strip_tac >>
  `MEM (EL k h).po_inst (fn_insts fn)` by
    (gvs[ptr_observation_reachable_def] >>
     drule ptr_frame_operand_instructions >> simp[]) >>
  `~in_revert_forward fn (EL k h).po_state /\
   (!off len. MEM (off,len) (source_memory_write_ranges (EL k h).po_inst (EL k h).po_state) ==>
     ~(off <= byte /\ byte < off + len))` by metis_tac[] >>
  qpat_x_assum `ptr_observation_reachable _ _ _` mp_tac >>
  simp[ptr_observation_reachable_def] >> strip_tac >>
  drule_all ptr_reachable_protected_byte_no_kill >> simp[]
QED

Theorem ptr_stage_owner_interval_no_kill:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  ptr_chrono_history vs C h endpoint /\ i <= j /\ j < LENGTH h /\
  (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) /\
  (ptr_owner_view d (EL i h)).cf_fn = fn /\
  FLOOKUP (ptr_owner_view d (EL i h)).cf_state.vs_allocas aid = SOME (b,sz) /\
  b <= byte /\ byte < b + sz /\
  (!k. i <= k /\ k < j ==>
    ~in_revert_forward (EL k h).po_fn (EL k h).po_state /\
    (!n off len. inst_write_size (EL k h).po_inst = SOME n /\
      MEM (off,len) (source_memory_write_ranges (EL k h).po_inst (EL k h).po_state) ==>
      ~(off <= byte /\ byte < off + len))) /\
  o1_run_state_ok vs /\ o1_ctx_shape C /\ ~ctx_has_dalloca C /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  EVERY (\f. EVERY (\inst. inst.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  wf_function fn /\ all_reachable fn /\ ptr_discipline lo C vs /\
  ptr_bp_origins fn (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) ==>
  !k. i <= k /\ k < j ==>
  ~ptr_ml_can_kill (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (\a. if context_alloca_size fn (imported_mems_used observed.cu_context fn) a = 0 then NONE
         else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a))
    (ptr_owner_view d (EL k h)).cf_inst
Proof
  strip_tac >>
  `!k. k < LENGTH h ==> (EL k h).po_inst.inst_opcode <> DALLOCA` by
    (rpt strip_tac >>
     `ptr_observation_reachable vs C (EL k h)` by
       (drule ptr_chrono_history_reachable >> simp[EVERY_EL] >> metis_tac[]) >>
     gvs[ptr_observation_reachable_def] >>
     drule ptr_frame_operand_instructions >> strip_tac >>
     `MEM (EL k h).po_fn C.ctx_functions` by
       metis_tac[concretizePtrParamSupportTheory.ptr_frame_current_static] >>
     qpat_x_assum `EVERY (\f. EVERY (\inst. inst.inst_opcode <> DALLOCA) (fn_insts f)) _`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(EL k h).po_fn` mp_tac) >> simp[] >>
     qexists `(EL k h).po_inst` >> simp[]) >>
  `vs.vs_allocas = FEMPTY` by
    gvs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  `d <= LENGTH (EL i h).po_stack /\ i < LENGTH h` by
    (conj_tac >- (first_x_assum irule >> decide_tac) >> decide_tac) >>
  drule_all ptr_chrono_owner_allocation_inst >> strip_tac >>
  `~MEM (Allocation aid) (MAP FST (imported_mems_used observed.cu_context fn))` by
    (gvs[] >> drule_all ptr_stage_local_not_imported >> simp[]) >>
  gen_tac >> strip_tac >> drule_all ptr_owner_interval_no_kill >> simp[]
QED
