(* Minimal allocation bounds for terminal encoders: source-state relations
   are not required to survive the encoder's scratch-memory writes. *)
Theory revertAllocationPtr
Ancestors
  allocationPtr bodyPtrDefs stmtSimDefs fragExecPtr ptrSafeRun ptrDiscipline
  venomInst venomState venomExecSemantics words finite_map loweringHalt

Theorem stmt_state_rel_alloca_bounds:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  n < dimword (:256) ==>
  (FLOOKUP s.vs_allocas id = NONE ==>
     s.vs_alloca_next + n < dimword (:256)) /\
  (!b sz. FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
     sz = n /\ b + n < dimword (:256))
Proof
  metis_tac[stmt_state_rel_alloca_fresh_bound, stmt_state_rel_alloca_site_bound]
QED

Theorem alloca_bounds_frame:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (FLOOKUP s.vs_allocas id = NONE ==>
     s.vs_alloca_next + n < dimword (:256)) /\
  (!b sz. FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
     sz = n /\ b + n < dimword (:256)) ==>
  (FLOOKUP t.vs_allocas id = NONE ==>
     t.vs_alloca_next + n < dimword (:256)) /\
  (!b sz. FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
     sz = n /\ b + n < dimword (:256))
Proof
  simp[]
QED

Theorem alloca_bounds_ptr_covers:
  (FLOOKUP s.vs_allocas id = NONE ==>
     s.vs_alloca_next + n < dimword (:256)) /\
  (!b sz. FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
     sz = n /\ b + n < dimword (:256)) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
  ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) out s1 n /\
  (p <> out /\ ptr_covers G tn p s sz ==>
    ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) p s1 sz)
Proof
  rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (irule (cj 1 fresh_alloca_ptr_covers) >> simp[] >> metis_tac[])
  >- (PairCases_on `x` >> gvs[] >>
      drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
      gvs[] >> irule (cj 1 reused_alloca_ptr_covers) >> simp[])
  >- (irule (cj 2 fresh_alloca_ptr_covers) >> simp[] >> metis_tac[])
  >> PairCases_on `x` >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> irule (cj 2 reused_alloca_ptr_covers) >> simp[]
QED

Theorem alloca_bounds_site:
  (FLOOKUP s.vs_allocas id = NONE ==>
     s.vs_alloca_next+n < dimword(:256)) /\
  (!b sz. FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
     sz=n /\ b+n < dimword(:256)) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
  FLOOKUP t.vs_allocas id = SOME (c,n) ==>
  lookup_var out t = SOME (n2w c) /\ c+n < dimword(:256)
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  PairCases_on `x` >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
