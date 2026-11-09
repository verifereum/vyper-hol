Theory concretizePtrWriteOwnership
Ancestors concretizePtrWriteClassification concretizePtrSourceOwnership
  concretizePtrPrefixLedger ptrDiscipline memLocDefs finite_map list arithmetic

Theorem ptr_source_write_owner_cases:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  MEM (off,len) (source_memory_write_ranges a.po_inst a.po_state) /\ len <> 0 ==>
  (off + len <= lo /\
   ~(?ops. mem_write_ops a.po_inst = SOME ops /\
      op_prov a.po_prov ops.iao_ofst <> NONE)) \/
  (?ops v token aid d b sz.
    mem_write_ops a.po_inst = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP a.po_prov v = SOME (b,sz) /\
    FLOOKUP TG v = SOME (token,aid) /\
    d <= LENGTH a.po_stack /\
    EL (LENGTH a.po_stack - d) tokens = token /\
    FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz) /\
    b <= off /\ off + len <= b + sz)
Proof
  strip_tac >>
  Cases_on `lo < off + len \/
    ?ops. mem_write_ops a.po_inst = SOME ops /\
      op_prov a.po_prov ops.iao_ofst <> NONE`
  >- (disj2_tac >>
      `?ops v b sz. mem_write_ops a.po_inst = SOME ops /\
        ops.iao_ofst = Var v /\ FLOOKUP a.po_prov v = SOME (b,sz) /\
        b <= off /\ off + len <= b + sz` by
        (gvs[access_ok_def] >> metis_tac[]) >>
      `?token aid. FLOOKUP TG v = SOME (token,aid)` by
        (drule_all ptr_source_ownership_prov_erases >>
         simp[ptr_ledger_erases_def] >> strip_tac >>
         qpat_x_assum `!v. FLOOKUP a.po_prov v = _`
           (qspec_then `v` mp_tac) >>
         Cases_on `FLOOKUP TG v` >> simp[] >>
         PairCases_on `x` >> metis_tac[]) >>
      drule_all ptr_source_ownership_live_cache >>
      strip_tac >> metis_tac[]) >>
  disj1_tac >> gvs[]
QED

Theorem ptr_source_step_write_owner_cases:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  x IN range_bytes (step_writes a.po_inst a.po_state post) ==>
  ?off len. MEM (off,len) (source_memory_write_ranges a.po_inst a.po_state) /\
    off <= x /\ x < off + len /\
    ((off + len <= lo /\
      ~(?ops. mem_write_ops a.po_inst = SOME ops /\
        op_prov a.po_prov ops.iao_ofst <> NONE)) \/
     (?ops v token aid d b sz.
       mem_write_ops a.po_inst = SOME ops /\ ops.iao_ofst = Var v /\
       FLOOKUP a.po_prov v = SOME (b,sz) /\
       FLOOKUP TG v = SOME (token,aid) /\
       d <= LENGTH a.po_stack /\
       EL (LENGTH a.po_stack - d) tokens = token /\
       FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz) /\
       b <= off /\ off + len <= b + sz))
Proof
  strip_tac >>
  qpat_x_assum `x IN _` mp_tac >> simp[ptr_step_write_range] >> strip_tac >>
  `x < off + len` by
    (Cases_on `MEM a.po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL]` >>
     Cases_on `len <= LENGTH post.vs_returndata` >>
     gvs[MIN_DEF] >> decide_tac) >>
  `len <> 0` by decide_tac >>
  drule_all ptr_source_write_owner_cases >>
  disch_tac >> qexistsl_tac [`off`,`len`] >> gvs[] >> metis_tac[]
QED
