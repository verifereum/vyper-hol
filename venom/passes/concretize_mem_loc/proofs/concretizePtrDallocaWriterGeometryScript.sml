Theory concretizePtrDallocaWriterGeometry
Ancestors
  concretizePtrDallocaWriterProbe concretizePtrHistoricalWriteExclusion
  concretizePtrExactWriteTransport concretizePtrWriteOwnership
  concretizePtrOpaqueRetpc concretizePtrValueTransport
  concretizePtrWritePurity concretizePtrWriteClassification concretizePtrOwnerSeeds
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
