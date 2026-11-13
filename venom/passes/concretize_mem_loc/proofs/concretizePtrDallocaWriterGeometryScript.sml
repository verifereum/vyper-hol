Theory concretizePtrDallocaWriterGeometry
Ancestors
  concretizePtrDallocaWriterProbe concretizePtrHistoricalWriteExclusion
  concretizePtrExactWriteTransport concretizePtrWriteOwnership
  concretizePtrDemandWriteExclusion concretizePtrStructuralTranscript
  concretizePtrActivationBirths concretizePtrSourceOwnership
  concretizePtrOwnerFloor concretizePtrAllocationOwnership concretizePtrChronologicalHistory
  concretizePtrOpaqueRetpc concretizePtrValueTransport
  concretizePtrWritePurity concretizePtrWriteClassification concretizePtrOwnerSeeds
  ptrDiscipline concretizePtrComparisonTransport
  concretizePtrTaggedSupport concretizePtrPlacementBounds concretizePtrPairedPrefix
  concretizePtrRequestHistory concretizeStepStructure concretizePtrStructuralTrace
  concretizePtrOwnerPath concretizePtrLifetime concretizePtrOperationalOpcodes
  venomExecSemantics venomWf venomInst unitShapeDefs o1PassContract contextCodegenRel
  venomState memLocDefs opcodeClass list finite_map option arithmetic

(* Source-directed extraction: unlike the historical reverse interface this
   boundary requires no target write coverage. *)
Theorem ptr_dalloca_forward_write_operands:
  ptr_mixed_vars births positions TG tn fn ft src tgt /\
  src.vs_labels = tgt.vs_labels /\
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst src /\ label_positions_ok inst /\ inst.inst_opcode <> DRET /\
  (!u. u IN FDOM TG ==> u IN fn_pv P fn) /\
  q IN range_bytes (step_writes inst src post) ==>
  ?ops sizeop x z xt.
    mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
    eval_operand ops.iao_ofst src = SOME x /\ eval_operand sizeop src = SOME z /\
    MEM (w2n x,w2n z) (source_memory_write_ranges inst src) /\
    eval_operand ops.iao_ofst tgt = SOME xt /\ eval_operand sizeop tgt = SOME z /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst)
      (op_taint tn ops.iao_ofst) (eval_operand ops.iao_ofst src)
      (eval_operand ops.iao_ofst tgt) /\ w2n z <> 0 /\
    op_prov TG sizeop = NONE /\ op_taint tn sizeop = {} /\
    (!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt)` by
    (drule_all ptr_mixed_vars_eval_presence >> simp[]) >>
  `?ops sizeop x z.
    mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
    eval_operand ops.iao_ofst src = SOME x /\ eval_operand sizeop src = SOME z /\
    MEM (w2n x,w2n z) (source_memory_write_ranges inst src) /\
    ((?u. ops.iao_ofst = Var u) \/ (?y. ops.iao_ofst = Lit y)) /\
    ((?u. sizeop = Var u) \/ (?y. sizeop = Lit y)) /\
    MEM ops.iao_ofst inst.inst_operands /\
    (MEM sizeop inst.inst_operands \/ (?n. sizeop = Lit n))` by
    (irule ptr_ordinary_write_descriptor >> simp[] >>
     qexistsl [`post`,`q`,`src`] >> simp[]) >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >>
     drule ptr_step_write_opcode >> simp[] >> strip_tac >> gvs[]) >>
  `ptr_nonopaque_operand fn ops.iao_ofst /\ ptr_nonopaque_operand fn sizeop` by
    (gvs[EVERY_MEM] >> metis_tac[ptr_nonopaque_operand_def]) >>
  `ptr_lookup_transport births positions (op_prov TG ops.iao_ofst)
    (op_taint tn ops.iao_ofst) (eval_operand ops.iao_ofst src)
    (eval_operand ops.iao_ofst tgt)` by
    (irule ptr_mixed_vars_eval >> simp[] >> qexistsl [`fn`,`ft`] >> gvs[]) >>
  `ptr_lookup_transport births positions (op_prov TG sizeop)
    (op_taint tn sizeop) (eval_operand sizeop src) (eval_operand sizeop tgt)` by
    (irule ptr_mixed_vars_eval >> simp[] >> qexistsl [`fn`,`ft`] >> gvs[]) >>
  `op_taint tn sizeop = {}` by (drule_all ptr_write_max_size_untainted >> simp[]) >>
  `op_prov TG sizeop = NONE` by (drule_all ptr_write_max_size_no_provenance >> simp[]) >>
  `eval_operand sizeop tgt = SOME z` by
    (gvs[ptr_lookup_transport_some, ptr_value_transport_scalar_empty]) >>
  `?xt. eval_operand ops.iao_ofst tgt = SOME xt` by
    (qpat_x_assum `!op. IS_SOME _ = _` (qspec_then `ops.iao_ofst` mp_tac) >>
     Cases_on `eval_operand ops.iao_ofst tgt` >> simp[]) >>
  `w2n z <> 0` by (drule_all ptr_step_write_max_containment >> decide_tac) >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

(* Identify the initializing write's allocation by overlap in the actual
   active cache, not by equality of historical birth addresses. *)
Theorem ptr_dalloca_source_writer_owner:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_discipline lo C vs /\ EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  ptr_active_alloc_geometry (a.po_state :: MAP (\f. f.cf_state) a.po_stack) /\
  d <= LENGTH a.po_stack /\
  FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz) /\
  EL (LENGTH a.po_stack-d) tokens = token /\
  lo <= b+k /\ k < sz /\ b+sz <= dyn_floor C vs /\
  b+k IN range_bytes (step_writes a.po_inst a.po_state post) ==>
  ?ops u off len.
    mem_write_ops a.po_inst = SOME ops /\ ops.iao_ofst = Var u /\
    FLOOKUP a.po_prov u = SOME (b,sz) /\ FLOOKUP TG u = SOME (token,aid) /\
    MEM (off,len) (source_memory_write_ranges a.po_inst a.po_state) /\
    off <= b+k /\ b+k < off+len /\ b <= off /\ off+len <= b+sz
Proof
  strip_tac >> drule_all ptr_source_step_write_owner_cases >>
  disch_then (qx_choose_then `off` (qx_choose_then `len` strip_assume_tac))
  >- (`F` by decide_tac) 
  >- (rename1 `FLOOKUP TG u = SOME (tok,other)` >>
      rename1 `FLOOKUP (ptr_owner_view e a).cf_state.vs_allocas other = SOME (ob,osz)` >>
      `d = e /\ aid = other` by
        (irule ptr_owner_overlap_unique >>
         qexistsl [`b`,`ob`,`a`,`sz`,`osz`,`b+k`] >> simp[] >> decide_tac) >>
      gvs[] >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `F` by decide_tac
QED

Theorem ptr_dalloca_initial_writer_snapshot:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\ EL w H = (tsw,rw,bw,PTw,TGw,sw,ew) ==>
  ptr_source_ownership vs C (TAKE (SUC w) h) (EL w h) tsw rw bw PTw TGw sw /\
  d <= LENGTH (EL w h).po_stack /\
  FLOOKUP (ptr_owner_view d (EL w h)).cf_state.vs_allocas aid = SOME (b,sz) /\
  EL (LENGTH (EL w h).po_stack-d) tsw = token /\
  FLOOKUP bw (token,aid) = SOME (b,sz)
Proof
  pure_rewrite_tac[ptr_demand_interval_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w <= w /\ w < LENGTH h` by decide_tac >>
  qpat_x_assum `!j. w <= j /\ j < LENGTH h ==> _`
    (qspec_then `w` strip_assume_tac) >>
  drule ptr_structural_transcript_ownership >>
  disch_then (qspec_then `w` mp_tac) >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  asm_rewrite_tac[] >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule_all ptr_source_birth_caches_slices >>
  simp[ptr_birth_slices_def] >>
  disch_then (qspecl_then [`d`,`aid`] mp_tac) >>
  gvs[]
QED

Theorem ptr_dalloca_initial_writer_owner:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\ EL w H = (tsw,rw,bw,PTw,TGw,sw,ew) /\
  ptr_observation_reachable vs C (EL w h) /\ mem_inv raw_mem_ok C vs ==>
  ?ops u off len.
    mem_write_ops (EL w h).po_inst = SOME ops /\ ops.iao_ofst = Var u /\
    FLOOKUP (EL w h).po_prov u = SOME (b,sz) /\
    FLOOKUP TGw u = SOME (token,aid) /\
    MEM (off,len) (source_memory_write_ranges (EL w h).po_inst (EL w h).po_state) /\
    off <= b+k /\ b+k < off+len /\ b <= off /\ off+len <= b+sz
Proof
  strip_tac >> drule_all ptr_dalloca_initial_writer_snapshot >> strip_tac >>
  `vs.vs_allocas = FEMPTY /\ ptr_discipline lo C vs /\
   EVERY wf_function C.ctx_functions /\
   EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
   access_ok lo (EL w h).po_prov (EL w h).po_fn (EL w h).po_inst (EL w h).po_state /\
   ~in_revert_forward (EL w h).po_fn (EL w h).po_state /\
   lo <= b+k /\ k < sz /\
   b+k IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
     (EL (SUC w) h).po_state)` by
    (fs[ptr_demand_interval_def] >>
     `w < LENGTH h` by decide_tac >>
     qpat_x_assum `!j. w <= j /\ j < LENGTH h ==> _`
       (qspec_then `w` strip_assume_tac) >>
     qpat_x_assum `!obs. MEM obs h ==> _` (qspec_then `EL w h` mp_tac) >>
     simp[MEM_EL] >>
     (impl_tac >- (qexists `w` >> simp[])) >> simp[]) >>
  `ptr_active_alloc_geometry
    ((EL w h).po_state :: MAP (\f. f.cf_state) (EL w h).po_stack)` by
    (fs[ptr_observation_reachable_def] >> drule_all ptr_frame_alloc_geometry >> simp[]) >>
  `b+sz <= dyn_floor C vs` by
    (drule_all ptr_reachable_owner_below_dyn_floor >> simp[]) >>
  drule_all ptr_dalloca_source_writer_owner >> simp[]
QED

Theorem ptr_dalloca_owned_write_forward:
  ptr_mixed_vars births positions TG tn fn ft src tgt /\
  src.vs_labels = tgt.vs_labels /\
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst src /\ label_positions_ok inst /\ inst.inst_opcode <> DRET /\
  (!u. u IN FDOM TG ==> u IN fn_pv P fn) /\
  access_ok lo G fn inst src /\ ~in_revert_forward fn src /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var u /\
  FLOOKUP G u = SOME (b,sz) /\ FLOOKUP TG u = SOME (token:num,aid) /\
  FLOOKUP births (token,aid) = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ pa+sz < dimword(:256) /\
  (MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
    LENGTH posts.vs_returndata = LENGTH postt.vs_returndata) /\
  k < sz /\ b+k IN range_bytes (step_writes inst src posts) ==>
  pa+k IN range_bytes (step_writes inst tgt postt) /\
  ?sizeop x z xt off.
    ops.iao_max_size = SOME sizeop /\
    eval_operand ops.iao_ofst src = SOME x /\ eval_operand sizeop src = SOME z /\
    eval_operand ops.iao_ofst tgt = SOME xt /\ eval_operand sizeop tgt = SOME z /\
    b+k = w2n x+off /\ pa+k = w2n xt+off /\ off < w2n z
Proof
  strip_tac >> drule_all ptr_dalloca_forward_write_operands >> strip_tac >>
  gvs[] >>
  `op_prov TG (Var u) = SOME (token,aid)` by simp[op_prov_def] >>
  `b <= w2n x /\ w2n x + w2n z <= b+sz` by
    (fs[access_ok_def] >>
     qpat_x_assum `!off len. MEM (off,len) (source_memory_write_ranges _ _) /\ _ ==> _`
       (qspecl_then [`w2n x`,`w2n z`] mp_tac) >>
     simp[op_prov_def] >> (impl_tac >- metis_tac[]) >> strip_tac >> gvs[]) >>
  `ptr_lookup_transport births positions (op_prov TG sizeop)
    (op_taint tn sizeop) (eval_operand sizeop src) (eval_operand sizeop tgt)` by
    simp[ptr_lookup_transport_some, ptr_value_transport_scalar_empty] >>
  `pa+k IN range_bytes (step_writes inst tgt postt)` by
    (`ptr_lookup_transport births positions (op_prov TG ops.iao_ofst)
        (op_taint tn ops.iao_ofst) (eval_operand ops.iao_ofst src)
        (eval_operand ops.iao_ofst tgt)` by gvs[] >>
     `eval_operand ops.iao_ofst src = SOME x /\
      op_prov TG ops.iao_ofst = SOME (token,aid) /\
      (MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
       LENGTH posts.vs_returndata = LENGTH postt.vs_returndata)` by
       (simp[] >> metis_tac[]) >>
     drule_all ptr_write_transport_owner_exact >>
     simp[]) >>
  `xt = x - n2w b + n2w pa` by
    gvs[ptr_lookup_transport_some, ptr_value_transport_def] >>
  `w2n xt = pa + (w2n x-b)` by
    (asm_rewrite_tac[] >> irule ptr_closed_relocation_value >>
     simp[] >> qexists `sz` >> simp[] >> decide_tac) >>
  `w2n x <= b+k /\ b+k < w2n x+w2n z` by
    (`eval_operand ops.iao_ofst src = SOME x` by simp[] >>
     drule_all ptr_step_write_max_containment >> simp[]) >>
  conj_tac >- gvs[ADD_COMM] >>
  qexists_tac `b+k-w2n x` >> decide_tac
QED

Theorem ptr_dalloca_writer_instruction_facts:
  ptr_observation_reachable vs C a /\ ptr_discipline lo C vs /\
  o1_ctx_shape C /\ EVERY (fn_ptr_ok P) C.ctx_functions ==>
  fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn /\
  MEM a.po_inst (fn_insts a.po_fn) /\ label_positions_ok a.po_inst /\
  a.po_inst.inst_opcode <> DRET
Proof
  strip_tac >>
  `MEM a.po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (drule (cj 1 ptr_owner_view_active) >>
     disch_then (qspec_then `LENGTH a.po_stack` mp_tac) >>
     simp[ptr_owner_view_def]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_def, MEM_fn_insts_blocks_iff, lookup_block_def] >>
     metis_tac[MEM_EL]) >>
  `a.po_inst.inst_opcode <> DRET` by
    (drule_all ptr_discipline_no_dret >> simp[]) >>
  fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM,
     inst_shape_ok_def] >> metis_tac[]
QED

Theorem ptr_dalloca_writer_forward:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  q < LENGTH done /\ EL q done = w ==>
  pa+k IN range_bytes (step_writes (EL q ht).po_inst (EL q ht).po_state
    (EL (SUC q) ht).po_state) /\
  (EL q ht).po_inst = (EL w h).po_inst /\ (EL w h).po_inst.inst_opcode <> DRET /\
  ?ops sizeop x z xt off.
    mem_write_ops (EL w h).po_inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
    eval_operand ops.iao_ofst (EL w h).po_state = SOME x /\
    eval_operand sizeop (EL w h).po_state = SOME z /\
    eval_operand ops.iao_ofst (EL q ht).po_state = SOME xt /\
    eval_operand sizeop (EL q ht).po_state = SOME z /\
    b+k = w2n x+off /\ pa+k = w2n xt+off /\ off < w2n z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~in_revert_forward (EL (EL q done) h).po_fn
      (EL (EL q done) h).po_state` by
    (fs[ptr_demand_interval_def] >>
     qpat_x_assum `!j. w <= j /\ j < LENGTH h ==> _`
       (qspec_then `w` mp_tac) >> simp[] >> decide_tac) >>
  drule_all ptr_paired_historical_event >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions /\
   EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\ k < sz /\
   b+k IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
     (EL (SUC w) h).po_state)` by fs[ptr_demand_interval_def] >>
  drule_all ptr_dalloca_writer_instruction_facts >> strip_tac >>
  gvs[] >>
  drule_all ptr_dalloca_initial_writer_snapshot >> strip_tac >>
  drule_all ptr_dalloca_initial_writer_owner >> strip_tac >>
  `!uu. uu IN FDOM TGj ==> uu IN fn_pv P (EL (EL q done) h).po_fn` by
    (qx_gen_tac `uu` >> strip_tac >>
     `?tag. FLOOKUP TGj uu = SOME tag` by metis_tac[FLOOKUP_DEF] >>
     drule_all ptr_source_tagged_var_support >> simp[]) >>
  `(EL (EL q done) h).po_state.vs_labels = (EL q ht).po_state.vs_labels` by
    metis_tac[ptr_history_content_labels] >>
  `pa+sz < dimword(:256)` by
    (drule_all ptr_stage_placements_strict_bound >> simp[]) >>
  `(EL (SUC (EL q done)) h).po_state.vs_returndata =
    (EL (SUC q) ht).po_state.vs_returndata` by
    (drule ptr_paired_prefix_samples >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule_all ptr_paired_samples_post_returndata >> simp[]) >>
  `(EL q ht).po_inst = (EL (EL q done) h).po_inst` by
    (drule ptr_step_write_opcode >> simp[] >> strip_tac >>
     simp[concretize_positions_unchanged]) >>
  `(MEM (EL (EL q done) h).po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
     LENGTH (EL (SUC (EL q done)) h).po_state.vs_returndata =
     LENGTH (EL (SUC q) ht).po_state.vs_returndata)` by simp[] >>
  drule_all ptr_dalloca_owned_write_forward >>
  strip_tac >> gvs[] >> rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

Theorem ptr_dalloca_writer_geometry:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  q < LENGTH done /\ EL q done = w ==>
  pa+k IN range_bytes (step_writes (EL q ht).po_inst (EL q ht).po_state
    (EL (SUC q) ht).po_state)
Proof
  strip_tac >> drule_all ptr_dalloca_writer_forward >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ptr_dalloca_writer_descriptor_cases[local]:
  mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop ==>
  (MEM inst.inst_opcode [MSTORE;ISTORE] ==> sizeop = Lit 32w) /\
  (inst.inst_opcode = MCOPY ==>
    ?dst src n. inst.inst_operands = [dst;src;n] /\
      ops.iao_ofst = dst /\ sizeop = n)
Proof
  strip_tac >> conj_tac >> strip_tac >>
  gvs[mem_write_ops_def, AllCaseEqs()] >> metis_tac[]
QED

(* Descriptor-level offsets are shared by every writer. Stores specialize
   their size to 32; copies use exactly the same evaluated size in both runs. *)
Theorem ptr_dalloca_writer_offsets:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  q < LENGTH done /\ EL q done = w ==>
  ?ops sizeop x z xt off.
    mem_write_ops (EL w h).po_inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
    eval_operand ops.iao_ofst (EL w h).po_state = SOME x /\
    eval_operand sizeop (EL w h).po_state = SOME z /\
    eval_operand ops.iao_ofst (EL q ht).po_state = SOME xt /\
    eval_operand sizeop (EL q ht).po_state = SOME z /\
    b+k = w2n x+off /\ pa+k = w2n xt+off /\ off < w2n z /\
    (MEM (EL w h).po_inst.inst_opcode [MSTORE;ISTORE] ==> off < 32) /\
    ((EL w h).po_inst.inst_opcode = MCOPY ==>
      ?dst src n. (EL w h).po_inst.inst_operands = [dst;src;n] /\
        ops.iao_ofst = dst /\ sizeop = n)
Proof
  strip_tac >> drule_all ptr_dalloca_writer_forward >> strip_tac >>
  drule_all ptr_dalloca_writer_descriptor_cases >> strip_tac >>
  `MEM (EL w h).po_inst.inst_opcode [MSTORE;ISTORE] ==> off < 32` by
    (strip_tac >> gvs[eval_operand_def, wordsTheory.dimword_def, venomLayoutTheory.dimindex_256]) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

(* An observation after an ordinary instruction contains the incremented
   instruction cursor, not the immediate successful post-state. *)
Theorem ptr_dalloca_chrono_ordinary_update:
  !C a z. ptr_chrono_step C a z ==>
  ~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE ==>
  ?fuel post.
    step_inst fuel C a.po_inst a.po_state = OK post /\
    z.po_taint = step_taint a.po_inst a.po_state post a.po_taint /\
    z.po_state = post with vs_inst_idx := SUC a.po_state.vs_inst_idx
Proof
  ho_match_mp_tac ptr_chrono_step_ind >> rpt conj_tac >>
  simp[ptr_observe_def] >> rpt strip_tac
  >- (qexistsl [`fuel`,`s'`] >> simp[]) >>
  gvs[step_inst_non_invoke] >>
  drule step_inst_base_intret_opcodes >> strip_tac >> gvs[is_terminator_def]
QED

Theorem ptr_dalloca_chrono_writer_update:
  ptr_chrono_step C a z /\ a.po_inst.inst_opcode <> DRET /\
  x IN range_bytes (step_writes a.po_inst a.po_state z.po_state) ==>
  ?fuel post.
    step_inst fuel C a.po_inst a.po_state = OK post /\
    z.po_taint = step_taint a.po_inst a.po_state post a.po_taint /\
    z.po_state = post with vs_inst_idx := SUC a.po_state.vs_inst_idx
Proof
  strip_tac >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    (drule ptr_step_write_opcode >> simp[] >> strip_tac >> gvs[is_terminator_def]) >>
  drule_all ptr_dalloca_chrono_ordinary_update >> simp[]
QED

Theorem ptr_dalloca_writer_updates:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  q < LENGTH done /\ EL q done = w ==>
  ?fuel post fuelT postT.
    step_inst fuel C (EL w h).po_inst (EL w h).po_state = OK post /\
    (EL (SUC w) h).po_taint =
      step_taint (EL w h).po_inst (EL w h).po_state post (EL w h).po_taint /\
    (EL (SUC w) h).po_state = post with vs_inst_idx := SUC (EL w h).po_state.vs_inst_idx /\
    step_inst fuelT C' (EL q ht).po_inst (EL q ht).po_state = OK postT /\
    (EL (SUC q) ht).po_taint =
      step_taint (EL q ht).po_inst (EL q ht).po_state postT (EL q ht).po_taint /\
    (EL (SUC q) ht).po_state = postT with vs_inst_idx := SUC (EL q ht).po_state.vs_inst_idx
Proof
  strip_tac >> drule_all ptr_dalloca_writer_forward >> strip_tac >>
  drule ptr_dalloca_demand_writer_source_edge >> strip_tac >>
  `ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry
    births PT TG saved entries H /\
   b+k IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
     (EL (SUC w) h).po_state)` by fs[ptr_demand_interval_def] >>
  `ptr_chrono_step C' (EL q ht) (EL (SUC q) ht)` by
    (drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_target >>
     disch_then (mp_tac o MATCH_MP ptr_chrono_history_adjacent) >>
     disch_then (qspec_then `q` mp_tac) >>
     drule ptr_paired_prefix_samples >>
     simp[ptr_paired_samples_def, ptr_sample_list_def]) >>
  drule_all ptr_dalloca_chrono_writer_update >> strip_tac >>
  qpat_x_assum `ptr_chrono_step C _ _` kall_tac >>
  `(EL q ht).po_inst.inst_opcode <> DRET` by simp[] >>
  drule_all ptr_dalloca_chrono_writer_update >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED
