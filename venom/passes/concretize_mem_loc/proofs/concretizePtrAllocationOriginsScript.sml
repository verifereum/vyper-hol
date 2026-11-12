Theory concretizePtrAllocationOrigins
Ancestors concretizeAnalysisBoundary venomExecSemantics venomState finite_map words

(* Cached entries are immutable; a fresh allocation inserts only at an absent key.
   This does not assert distinct addresses (in particular for zero-sized sites). *)
Theorem exec_alloca_fresh_table:
  exec_alloca inst s n = OK s' /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  s'.vs_allocas = s.vs_allocas |+
    (inst.inst_id, (s.vs_alloca_next, w2n n))
Proof
  rw[exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def]
QED

Theorem exec_alloca_lookup_preserved:
  exec_alloca inst s n = OK s' /\
  FLOOKUP s.vs_allocas aid = SOME site ==>
  FLOOKUP s'.vs_allocas aid = SOME site
Proof
  rw[exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `inst.inst_id = aid` >> gvs[]
QED

Theorem exec_alloca_id_present:
  exec_alloca inst s n = OK s' ==>
  ?site. FLOOKUP s'.vs_allocas inst.inst_id = SOME site
Proof
  rw[exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def, FLOOKUP_UPDATE]
QED
