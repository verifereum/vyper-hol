Theory decoderProtectedScratchPtr
Ancestors decoderGhostFramePtr abiDecoderAllocation abiDecoderProtectedScratch allocationPtr
  ptrDiscipline venomExecSemantics venomState venomInst finite_map
  pred_set words list arithmetic

Theorem step_taint_protected_bytes:
  DISJOINT P tn.t_mem /\ DISJOINT P (new_site_bytes s t) /\
  DISJOINT P (written_taint tn inst s) ==>
  DISJOINT P (step_taint inst s t tn).t_mem
Proof
  strip_tac >>
  `new_site_bytes s t SUBSET new_site_bytes s t UNION written_taint tn inst s /\
   written_taint tn inst s SUBSET new_site_bytes s t UNION written_taint tn inst s`
    by SET_TAC[] >>
  drule_all step_taint_memory_bound >> simp[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >>
  metis_tac[DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_UNION]
QED

Theorem ptr_covers_protected_step:
  ptr_covers G tn x s C /\ ~MEM x inst.inst_outputs /\
  lookup_var x t = lookup_var x s /\
  DISJOINT P tn.t_mem /\ DISJOINT P (new_site_bytes s t) /\
  DISJOINT P (written_taint tn inst s) ==>
  ptr_covers (step_prov PG G inst t) (step_taint inst s t tn) x t C /\
  DISJOINT P (step_taint inst s t tn).t_mem
Proof
  metis_tac[ptr_covers_step_frame, step_taint_protected_bytes]
QED

Theorem abi_decoder_alloca_protected_bytes:
  abi_decoder_budget first last b cap s /\
  site IN abi_decoder_ids first last /\ aid IN abi_decoder_ids first last /\
  site <> aid /\ FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  step_inst_base (mk_inst aid ALLOCA [Lit 32w] [out]) s = OK t ==>
  DISJOINT {a | slot <= a /\ a < slot + 32} (new_site_bytes s t)
Proof
  strip_tac >>
  `exec_alloca (mk_inst aid ALLOCA [Lit 32w] [out]) s (32w:bytes32) = OK t` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[Once step_inst_base_def, mk_inst_def, eval_operand_def]) >>
  Cases_on `FLOOKUP s.vs_allocas aid`
  >- (mp_tac (Q.INST [`inst` |-> `mk_inst aid ALLOCA [Lit 32w] [out]`] abi_decoder_alloca32_fresh) >>
      simp[mk_inst_def] >> strip_tac >>
      `FLOOKUP t.vs_allocas site = SOME (slot,32)` by simp[FLOOKUP_UPDATE] >>
      `FLOOKUP t.vs_allocas aid = SOME (s.vs_alloca_next,32)` by simp[FLOOKUP_UPDATE] >>
      `slot + 32 <= s.vs_alloca_next \/ s.vs_alloca_next + 32 <= slot` by
        metis_tac[abi_decoder_budget_sites_disjoint] >>
      `new_site_bytes s t = {a | s.vs_alloca_next <= a /\ a < s.vs_alloca_next + 32}` by
        (irule fresh_alloca_new_site_bytes >> conj_tac >- simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >> qexistsl_tac [`aid`,`out`] >> simp[]) >>
      simp[DISJOINT_DEF, EXTENSION] >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME pair` >> PairCases_on `pair` >>
  mp_tac (Q.INST [`inst` |-> `mk_inst aid ALLOCA [Lit 32w] [out]`,
    `p` |-> `pair0`, `sz` |-> `pair1`] abi_decoder_alloca32_reuse) >>
  simp[mk_inst_def] >> strip_tac >> gvs[] >>
  simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, DISJOINT_DEF] >>
  metis_tac[]
QED
