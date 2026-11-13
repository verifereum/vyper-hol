(* Joint local construction at original allocation boundaries. *)
Theory o1LowerDloadJointAllocation
Ancestors
  o1LowerDloadEnvironment o1LowerDloadShared o1LowerDloadMapEvolution
  o1LowerDloadRelocationKernel venomExecSemantics venomState finite_map
  ptrDiscipline words list

Theorem ld_alloca_env_update[local]:
  ld_env_agree sites fn H tn s t /\
  FLOOKUP sites id = SOME (b,c,z) ==>
  ld_env_agree sites fn (H |+ (out,id)) tn
    (update_var out (n2w b) s) (update_var out (n2w c) t)
Proof
  simp[ld_env_agree_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `v = out` >> gvs[] >>
  pure_rewrite_tac[ld_value_agree_pointer] >>
  qexistsl_tac [`b`, `c`, `z`] >>
  asm_rewrite_tac[WORD_ADD_SUB2]
QED

Theorem ld_alloca_repeated:
  ld_env_agree sites fn H tn s t /\ ld_params_agree sites HP s t /\
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  ld_shared_agree D A tn s t /\ inst.inst_outputs = [out] /\
  t.vs_alloca_next = s.vs_alloca_next + delta /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,z) /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (c,z) /\
  FLOOKUP sites (owner,inst.inst_id) = SOME (b,c,z) ==>
  ?s1 t1. exec_alloca inst s alloc_size = OK s1 /\ exec_alloca inst t alloc_size = OK t1 /\
    ld_env_agree sites fn (H |+ (out,(owner,inst.inst_id))) tn s1 t1 /\
    ld_params_agree sites HP s1 t1 /\
    ld_memory_agree sites lo mask s1.vs_memory t1.vs_memory /\
    ld_shared_agree D A tn s1 t1 /\
    s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas /\
    s1.vs_alloca_next = s.vs_alloca_next /\ t1.vs_alloca_next = t.vs_alloca_next /\
    t1.vs_alloca_next = s1.vs_alloca_next + delta
Proof
  strip_tac >> simp[exec_alloca_def] >>
  conj_tac >- (irule ld_alloca_env_update >> metis_tac[]) >>
  gvs[ld_params_agree_def, ld_shared_agree_def, update_var_def]
QED

Theorem ld_alloca_env_extend[local]:
  ld_env_agree sites fn H tn s t /\ id NOTIN FDOM sites ==>
  ld_env_agree (sites |+ (id,(b,c,z))) fn H tn s t
Proof
  simp[ld_env_agree_def] >> rpt strip_tac >>
  irule ld_value_agree_extend >> metis_tac[]
QED

Theorem ld_alloca_params_extend[local]:
  ld_params_agree sites HP s t /\ id NOTIN FDOM sites ==>
  ld_params_agree (sites |+ (id,(b,c,z))) HP s t
Proof
  simp[ld_params_agree_def] >> rpt strip_tac >>
  irule ld_value_agree_extend >> metis_tac[]
QED

Theorem ld_alloca_fresh:
  ld_env_agree sites fn H tn s t /\ ld_params_agree sites HP s t /\
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  ld_shared_agree D A tn s t /\ inst.inst_outputs = [out] /\
  t.vs_alloca_next = s.vs_alloca_next + delta /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  FLOOKUP t.vs_allocas inst.inst_id = NONE /\
  (owner,inst.inst_id) NOTIN FDOM sites /\
  b = s.vs_alloca_next /\ c = t.vs_alloca_next /\ z = w2n alloc_size ==>
  ?s1 t1. exec_alloca inst s alloc_size = OK s1 /\
    exec_alloca inst t alloc_size = OK t1 /\
    ld_env_agree (sites |+ ((owner,inst.inst_id),(b,c,z))) fn
      (H |+ (out,(owner,inst.inst_id))) tn s1 t1 /\
    ld_params_agree (sites |+ ((owner,inst.inst_id),(b,c,z))) HP s1 t1 /\
    ld_memory_agree (sites |+ ((owner,inst.inst_id),(b,c,z))) lo
      (mask UNION {b+j | j < z}) s1.vs_memory t1.vs_memory /\
    ld_shared_agree D A tn s1 t1 /\
    s1.vs_allocas = s.vs_allocas |+ (inst.inst_id,(b,z)) /\
    t1.vs_allocas = t.vs_allocas |+ (inst.inst_id,(c,z)) /\
    FLOOKUP s1.vs_allocas inst.inst_id = SOME (b,z) /\
    FLOOKUP t1.vs_allocas inst.inst_id = SOME (c,z) /\
    s1.vs_alloca_next = b+z /\ t1.vs_alloca_next = c+z /\
    t1.vs_alloca_next = s1.vs_alloca_next + delta
Proof
  strip_tac >>
  `ld_env_agree (sites |+ ((owner,inst.inst_id),(b,c,z))) fn H tn s t` by
    (irule ld_alloca_env_extend >> metis_tac[]) >>
  `ld_params_agree (sites |+ ((owner,inst.inst_id),(b,c,z))) HP s t` by
    (irule ld_alloca_params_extend >> metis_tac[]) >>
  `ld_memory_agree (sites |+ ((owner,inst.inst_id),(b,c,z))) lo
     (mask UNION {b+j | j < z}) s.vs_memory t.vs_memory` by
    (irule ld_memory_agree_extend >> metis_tac[]) >>
  simp[exec_alloca_def] >> conj_tac
  >- (irule ld_alloca_env_update >> simp[FLOOKUP_UPDATE] >>
      gvs[ld_env_agree_def, update_var_def]) >>
  conj_tac
  >- gvs[ld_params_agree_def, update_var_def] >>
  gvs[update_var_def, ld_shared_agree_def, FLOOKUP_UPDATE]
QED
