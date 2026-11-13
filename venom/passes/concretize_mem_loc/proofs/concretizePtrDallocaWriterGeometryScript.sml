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
  list finite_map option arithmetic

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
