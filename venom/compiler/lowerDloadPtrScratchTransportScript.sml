Theory lowerDloadPtrScratchTransport
Ancestors
  lowerDloadPtrAllocTransport lowerDloadPtrAlloc lowerDloadPtrAggregate
  lowerDloadPtrRel lowerDloadPtrCall lowerDloadPtrTaint ptrDiscipline
  venomExecSemantics venomState codegenRel memLocDefs finite_map list pred_set words

Theorem dload_live_site_scratch_insert[local]:
  FLOOKUP r.dr_source aid = NONE ==>
  (dload_live_site
    ((r with <|dr_target := r.dr_target |+ (aid,(front,32));
               dr_scratch := aid INSERT r.dr_scratch|>)::rs) owner id b c n <=>
   dload_live_site (r::rs) owner id b c n)
Proof
  Cases_on `owner` >> simp[dload_live_site_def, FLOOKUP_UPDATE] >>
  strip_tac >> Cases_on `id = aid` >> gvs[]
QED

Theorem scratch_alloca_fields[local]:
  a.inst_opcode = ALLOCA /\ a.inst_outputs = [tmp] /\
  exec_alloca a t (32w:bytes32) = OK t1 ==>
  (!v. v <> tmp ==> lookup_var v t1 = lookup_var v t) /\
  (!v. v <> tmp ==> FLOOKUP (step_prov PH H a t1) v = FLOOKUP H v) /\
  (!v. v <> tmp ==> FLOOKUP (step_taint a t t1 un).t_var v = FLOOKUP un.t_var v) /\
  t1.vs_memory = t.vs_memory /\ t1.vs_params = t.vs_params /\
  (step_taint a t t1 un).t_mem = un.t_mem UNION new_site_bytes t t1 /\
  (!s tn. dload_equal_environment s t /\ dload_shared_store tn un s t ==>
    dload_equal_environment s t1 /\ dload_shared_store tn (step_taint a t t1 un) s t1)
Proof
  strip_tac >> drule_all exec_alloca_memory_taint >> strip_tac >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  simp[step_prov_def, out_prov_def, set_prov_def, FLOOKUP_UPDATE,
       lookup_var_def, step_taint_def, set_var_taint_def] >>
  rpt strip_tac >>
  gvs[dload_equal_environment_def, venom_state_component_equality,
      dload_shared_store_def, adopt_reset_def, store_taint_def, imm_taint_def]
QED

Theorem scratch_boundary_assemble[local]:
  dload_boundary_core lo (r::rs) V Ws PG PH G H tn un s t cs ds /\
  a.inst_opcode = ALLOCA /\ a.inst_outputs = [tmp] /\ tmp NOTIN V /\
  exec_alloca a t (32w:bytes32) = OK t1 /\
  dload_live_layout lo s.vs_alloca_next t1.vs_alloca_next (r1::rs) /\
  dload_table_stack (r1::rs) (s::MAP (\c. c.cf_state) cs)
    (t1::MAP (\d. d.cf_state) ds) /\
  (!owner id b c n. dload_live_site (r1::rs) owner id b c n <=>
                    dload_live_site (r::rs) owner id b c n) /\
  (!x. x < lo ==> x NOTIN new_site_bytes t t1) /\
  (!owner id b c n k. dload_live_site (r::rs) owner id b c n /\ k < n ==>
     c+k NOTIN new_site_bytes t t1) ==>
  dload_boundary_core lo (r1::rs) V Ws PG PH G (step_prov PH H a t1)
    tn (step_taint a t t1 un) s t1 cs ds
Proof
  strip_tac >> drule_all scratch_alloca_fields >>
  disch_then (qspecl_then [`un`,`PH`,`H`] strip_assume_tac) >>
  `dload_vars_match (r1::rs) V G (step_prov PH H a t1)
    tn (step_taint a t t1 un) s t1` by
    (drule dload_boundary_vars >>
     simp[dload_vars_match_def] >> strip_tac >> gen_tac >> strip_tac >>
     `v <> tmp` by metis_tac[] >> simp[] >>
     `!mask p q x y. dload_value_word (r1::rs) mask p q x y <=>
                    dload_value_word (r::rs) mask p q x y` by
       (rpt gen_tac >> Cases_on `p` >> Cases_on `q` >>
        simp[dload_value_word_def] >> rename1 `dload_pointer_word _ pp qq` >>
        PairCases_on `pp` >> PairCases_on `qq` >>
        simp[dload_pointer_word_def]) >>
     gvs[]) >>
  `dload_param_values (r1::rs) PG PH s.vs_params t1.vs_params` by
    (irule dload_param_values_sites_mono >> qexists_tac `r::rs` >> simp[] >>
     drule dload_boundary_params >> simp[]) >>
  `dload_memory_match lo (r1::rs) tn (step_taint a t t1 un) s t1` by
    (drule dload_boundary_memory >> simp[dload_memory_match_def] >>
     strip_tac >> rpt strip_tac >> metis_tac[]) >>
  drule dload_boundary_environment >> strip_tac >>
  drule dload_boundary_shared_store >> strip_tac >>
  `dload_equal_environment s t1 /\
   dload_shared_store tn (step_taint a t t1 un) s t1` by metis_tac[] >>
  gvs[dload_boundary_core_def]
QED

Theorem dload_boundary_core_scratch_alloca:
  dload_boundary_core lo (r::rs) V Ws PG PH G H tn un s t cs ds /\
  r.dr_scratch = FDOM t.vs_allocas DIFF orig /\
  FDOM s.vs_allocas SUBSET orig /\ a.inst_id NOTIN orig /\
  a.inst_opcode = ALLOCA /\ a.inst_outputs = [tmp] /\ tmp NOTIN V /\
  exec_alloca a t (32w:bytes32) = OK t1 /\
  t1.vs_alloca_next < dimword (:256) ==>
  ?r1. dload_boundary_core lo (r1::rs) V Ws PG PH G (step_prov PH H a t1)
         tn (step_taint a t t1 un) s t1 cs ds /\
    r1.dr_source = r.dr_source /\ r1.dr_target = t1.vs_allocas /\
    r1.dr_scratch = a.inst_id INSERT r.dr_scratch /\
    r1.dr_scratch = FDOM t1.vs_allocas DIFF orig /\
    (!v. v <> tmp ==> lookup_var v t1 = lookup_var v t)
Proof
  strip_tac >>
  drule dload_boundary_layout >> strip_tac >>
  drule dload_boundary_tables >> strip_tac >>
  `r.dr_source = s.vs_allocas /\ r.dr_target = t.vs_allocas` by
    gvs[dload_table_stack_cons] >>
  `FLOOKUP r.dr_source a.inst_id = NONE` by
    (gvs[FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  Cases_on `FLOOKUP t.vs_allocas a.inst_id`
  >- (qexists_tac `r with <|dr_target := r.dr_target |+ (a.inst_id,(t.vs_alloca_next,32));
                           dr_scratch := a.inst_id INSERT r.dr_scratch|>` >>
      `FINITE r.dr_scratch /\ a.inst_id NOTIN r.dr_scratch` by
        (gvs[FLOOKUP_DEF]) >>
      `t1.vs_allocas = t.vs_allocas |+ (a.inst_id,(t.vs_alloca_next,32)) /\
       t1.vs_alloca_next = t.vs_alloca_next + 32` by
        gvs[exec_alloca_def, update_var_def, dimword_def] >>
      drule_all exec_alloca_fresh_new_bytes >> strip_tac >>
      drule_all dload_table_scratch_fresh >> strip_tac >>
      `dload_live_layout lo s.vs_alloca_next (t.vs_alloca_next+32)
        ((r with <|dr_target := r.dr_target |+ (a.inst_id,(t.vs_alloca_next,32));
                   dr_scratch := a.inst_id INSERT r.dr_scratch|>)::rs)` by
        (irule dload_layout_scratch_insert >> simp[]) >>
      conj_tac
      >- (irule scratch_boundary_assemble >>
          simp[] >>
          conj_tac
          >- (fs[dload_live_layout_def] >> rpt strip_tac >> decide_tac) >>
          conj_tac
          >- (qpat_x_assum `dload_live_layout _ _ (_+32) _` mp_tac >> simp[]) >>
          qexists_tac `r` >>
          qpat_x_assum `r.dr_target = _` (assume_tac o SYM) >>
          qpat_x_assum `r.dr_scratch = _` (assume_tac o SYM) >>
          simp[dload_live_site_scratch_insert] >>
          rpt strip_tac >> drule_all dload_live_site_bounds >> simp[] >>
          strip_tac >> decide_tac) >>
      simp[FDOM_FUPDATE] >> metis_tac[scratch_alloca_fields]) >>
  PairCases_on `x` >>
  qexists_tac `r` >>
  `a.inst_id IN r.dr_scratch` by gvs[FLOOKUP_DEF] >>
  `t1.vs_allocas = t.vs_allocas /\ t1.vs_alloca_next = t.vs_alloca_next` by
    gvs[exec_alloca_def, update_var_def] >>
  drule_all exec_alloca_repeated_new_bytes >> strip_tac >>
  drule_all dload_table_scratch_repeated >> strip_tac >>
  conj_tac
  >- (irule scratch_boundary_assemble >> simp[] >>
      qexists_tac `r` >> simp[]) >>
  simp[] >> conj_tac >- (ASM_SET_TAC []) >>
  drule_all scratch_alloca_fields >>
  disch_then (qspecl_then [`un`,`PH`,`H`] strip_assume_tac) >> simp[]
QED
