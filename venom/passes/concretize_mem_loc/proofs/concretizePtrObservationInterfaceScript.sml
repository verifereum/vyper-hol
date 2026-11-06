Theory concretizePtrObservationInterface
Ancestors
  concretizePtrHistoryCoverage concretizePtrStageBounds
  concretizePtrComparisonTransport ptrDiscipline unitMemInv
  concretizePtrPairedFields list finite_map words arithmetic

(* access_ok retains ownership even when a provenance-bearing range lies
   numerically below lo. The absent-provenance alternative is explicit. *)
Theorem ptr_access_range_classification:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  ((ranges = source_memory_read_ranges inst s /\ mops = mem_read_ops inst) \/
   (ranges = source_memory_write_ranges inst s /\ mops = mem_write_ops inst)) /\
  MEM (off,len) ranges ==>
  len = 0 \/
  (off + len <= lo /\
    ~(?ops. mops = SOME ops /\ op_prov G ops.iao_ofst <> NONE)) \/
  (?ops v b sz. mops = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G v = SOME (b,sz) /\ b <= off /\ off + len <= b + sz)
Proof
  rw[access_ok_def] >>
  Cases_on `len = 0` >> simp[] >>
  Cases_on `off + len <= lo` >>
  Cases_on `?ops. mops = SOME ops /\ op_prov G ops.iao_ofst <> NONE` >>
  gvs[] >> metis_tac[NOT_LESS_EQUAL]
QED

(* Uses the exact owned word equation; strict placement endpoint supplies
   the nonwrap condition. No target access bound is assumed. *)
Theorem ptr_owned_range_relocation_probe:
  (y:bytes32) = x - n2w b + n2w p /\
  b <= w2n x /\ w2n x + len <= b + sz /\
  p + sz < dimword(:256) ==>
  p <= w2n y /\ w2n y + len <= p + sz
Proof
  strip_tac >>
  `w2n x <= b + sz` by decide_tac >>
  drule_all ptr_closed_relocation_value >> strip_tac >> decide_tac
QED

(* Candidate ONLY: parsed and typechecked, not proved by the local probes. *)
val observation_range_transport_schema = ``
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C Ct /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom Ct = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
  ptr_stage_placements Ct positions /\
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst ==>
  in_revert_forward at.po_fn at.po_state \/
  (!off len.
    MEM (off,len) (source_memory_read_ranges at.po_inst at.po_state ++
                  source_memory_write_ranges at.po_inst at.po_state) ==>
    len = 0 \/ off + len <= lo \/
    (?aid p sz. FLOOKUP positions (Allocation aid) = SOME (p,sz) /\
      p <= off /\ off + len <= p + sz))
``;
