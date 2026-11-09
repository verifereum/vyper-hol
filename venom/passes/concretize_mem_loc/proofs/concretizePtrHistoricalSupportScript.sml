Theory concretizePtrHistoricalSupport
Ancestors concretizePtrTaggedSupport concretizePtrStructuralTranscript
  concretizePtrSourceOwnership ptrDiscipline finite_map list

Theorem ptr_transcript_tagged_domain_support:
  ptr_structural_transcript R vs C Ct h a ht at done tokens registry births
    PT TG saved entries H /\ j < LENGTH h /\
  EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions ==>
  !u. u IN FDOM TGj ==> u IN fn_pv P (EL j h).po_fn
Proof
  strip_tac >>
  drule ptr_structural_transcript_ownership >>
  disch_then (qspec_then `j` mp_tac) >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  rpt strip_tac >>
  `?tag. FLOOKUP TGj u = SOME tag` by metis_tac[FLOOKUP_DEF] >>
  drule_all ptr_source_tagged_var_support >> simp[]
QED
