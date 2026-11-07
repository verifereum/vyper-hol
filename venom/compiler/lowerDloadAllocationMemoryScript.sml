Theory lowerDloadAllocationMemory
Ancestors
  lowerDloadPairing lowerDloadLifetime lowerDloadRelocation
  venomExecSemantics venomState ptrDiscipline finite_map pred_set words

Theorem ld_site_bytes_insert[local]:
  owner NOTIN live ==>
  (ld_site_bytes (E |+ (owner,(bs,bt,sz))) (owner INSERT live) a b <=>
   ld_site_bytes E live a b \/ ?d. d < sz /\ a = bs+d /\ b = bt+d)
Proof
  strip_tac >> simp[ld_site_bytes_def, ld_site_entry_update] >>
  eq_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_alloca_new_bytes_lower[local]:
  i.inst_outputs = [out] /\ FLOOKUP s.vs_allocas i.inst_id = NONE /\
  exec_alloca i s n = OK s' /\ b IN new_site_bytes s s' ==>
  s.vs_alloca_next <= b
Proof
  gvs[exec_alloca_def, update_var_def, new_site_bytes_def,
      FLOOKUP_UPDATE, AllCaseEqs()] >>
  rpt strip_tac >> gvs[FLOOKUP_DEF] >>
  Cases_on `i.inst_id = aid` >> gvs[]
QED

Theorem ld_alloca_fresh_site_memory:
  i.inst_opcode = ALLOCA /\ j.inst_opcode = ALLOCA /\
  i.inst_outputs = [out] /\ j.inst_outputs = [out'] /\
  FLOOKUP s.vs_allocas i.inst_id = NONE /\
  FLOOKUP t.vs_allocas j.inst_id = NONE /\
  exec_alloca i s n = OK s' /\ exec_alloca j t n = OK t' /\
  owner NOTIN live /\ lo <= t.vs_alloca_next /\
  (!old bs bt sz. old IN live /\ ld_site_entry E old bs bt sz ==>
    bt + sz <= t.vs_alloca_next) /\
  ld_byte_rel (\a b. (a = b /\ a < lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) ==>
  ld_byte_rel
    (\a b. (a = b /\ a < lo) \/
      ld_site_bytes (E |+ (owner,(s.vs_alloca_next,t.vs_alloca_next,w2n n)))
        (owner INSERT live) a b)
    (mem_taint tn i s s') (mem_taint un j t t')
    (\a. read_memory a 1 s') (\b. read_memory b 1 t')
Proof
  strip_tac >>
  `!a b. (a = b /\ a < lo) \/ ld_site_bytes E live a b ==>
    b NOTIN new_site_bytes t t'` by
    (rpt strip_tac >>
     `b < t.vs_alloca_next` by
       (gvs[ld_site_bytes_def] >>
        `bt + sz <= t.vs_alloca_next` by metis_tac[] >> decide_tac) >>
     drule_all ld_alloca_new_bytes_lower >> decide_tac) >>
  drule_all (SRULE [] (Q.INST
    [`R` |-> `\a b. (a = b /\ a < lo) \/ ld_site_bytes E live a b`]
    ld_alloca_fresh_byte_rel)) >>
  simp[ld_site_bytes_insert, DISJ_ASSOC]
QED

Theorem ld_alloca_cached_memory:
  i.inst_opcode = ALLOCA /\ j.inst_opcode = ALLOCA /\
  i.inst_outputs = [out] /\ j.inst_outputs = [out'] /\
  FLOOKUP s.vs_allocas i.inst_id = SOME (bs,sz) /\
  FLOOKUP t.vs_allocas j.inst_id = SOME (bt,tz) /\
  exec_alloca i s n = OK s' /\ exec_alloca j t m = OK t' /\
  ld_byte_rel R tn.t_mem un.t_mem
    (\a. read_memory a 1 s) (\b. read_memory b 1 t) ==>
  ld_byte_rel R (mem_taint tn i s s') (mem_taint un j t t')
    (\a. read_memory a 1 s') (\b. read_memory b 1 t')
Proof
  strip_tac >>
  `s'.vs_memory = s.vs_memory /\ t'.vs_memory = t.vs_memory` by
    metis_tac[ld_alloca_memory] >>
  `new_site_bytes s s' = {} /\ new_site_bytes t t' = {}` by
    (gvs[exec_alloca_def, update_var_def, new_site_bytes_def,
         EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[ld_alloca_mask, read_memory_def]
QED
