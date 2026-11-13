Theory exprSimAbiDecodeSiteAllocation
Ancestors
  exprSimAbiDecodeSiteProvenance actualDecoderSites venomExecSemantics
  venomState venomInst finite_map pred_set arithmetic words

Theorem exec_alloca_site_progress:
  exec_alloca inst s (n:256 word) = OK t /\ inst.inst_id IN sites ==>
  abi_decode_alloc_progress sites s t
Proof
  strip_tac >>
  fs[exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def, abi_decode_alloc_progress_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >> Cases_on `inst.inst_id = id` >> gvs[]
QED

Theorem decode_site_allocation_progress:
  decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit n] /\ inst.inst_outputs = [out] /\
  inst.inst_id IN sites ==>
  ?t b. exec_alloca inst s n = OK t /\ decode_site_resources ctx func t /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,w2n n) /\
    lookup_var out t = SOME (n2w b) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    b + w2n n <= t.vs_alloca_next /\
    (!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
    t = s with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
                vs_alloca_next := t.vs_alloca_next|> /\
    abi_decode_alloc_progress sites s t
Proof
  strip_tac >> drule_all decode_site_allocation >> strip_tac >>
  qexistsl_tac [`t`, `b`] >> simp[] >>
  irule exec_alloca_site_progress >> qexistsl_tac [`inst`, `n`] >> simp[]
QED
