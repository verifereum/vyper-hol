Theory o1LowerDloadAllocationBoundary
Ancestors
  o1LowerDloadJointRelation o1LowerDloadJointFrontier
  o1LowerDloadJointAllocation o1LowerDloadScratchCount
  o1LowerDloadOccurrenceHeadroom o1LowerDloadPairedAllocation
  o1LowerDloadEnvironment o1LowerDloadMapEvolution o1LowerDloadJointGeometry
  o1LowerDloadOccurrence
  finite_map words list pred_set

Theorem ld_allocas_fresh_site[local]:
  ld_joint_allocas sites X a fn t /\ MEM aid (fn_ir_inst_ids fn) /\
  t1.vs_allocas = t.vs_allocas |+ (aid,(c,z)) ==>
  ld_joint_allocas (sites |+ ((a,aid),(b,c,z))) X a fn t1
Proof
  rewrite_tac[ld_joint_allocas_def] >> strip_tac >> rpt conj_tac
  >- (simp[FLOOKUP_UPDATE] >> rpt gen_tac >> Cases_on `aid = aid'` >>
      gvs[] >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[]
  >> simp[FLOOKUP_UPDATE] >> rpt gen_tac >> Cases_on `aid = aid'` >>
     gvs[] >> metis_tac[]
QED

Theorem ld_joint_alloca_fresh_metadata:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs /\
  callee_first names C.ctx_functions /\ active_inst fn inst s /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit amount] /\
  inst.inst_outputs = [out] /\ MEM inst.inst_id (fn_ir_inst_ids fn) /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\ step_inst fuel C inst s = OK s1 ==>
  let b = s.vs_alloca_next; c = t.vs_alloca_next; z = w2n amount;
      sites1 = sites |+ ((a,inst.inst_id),(b,c,z));
      B1 = B |+ ((a,inst.inst_id),(b,z))
  in ?t1. step_inst fuel C' inst t = OK t1 /\
    ld_joint_erasure sites1 B1 /\
    ld_joint_geometry sites1 X lo (a::MAP (\f. f.of_owner) U) /\
    ld_joint_allocas sites1 X a fn t1 /\
    s1.vs_alloca_next = b+z /\ t1.vs_alloca_next = c+z /\
    t1.vs_alloca_next < dimword (:256) /\
    t1.vs_alloca_next = s1.vs_alloca_next +
      32 * CARD {id | id IN FDOM X /\ MEM (FST id) (a::MAP (\f. f.of_owner) U)}
Proof
  rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [LET_THM] >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `s1.vs_alloca_next + 32 * ctx_dload_count C < dimword (:256)` by
    (irule ld_occurrence_shape_alloca_headroom >> metis_tac[]) >>
  drule_all ld_joint_scratch_count >> strip_tac >>
  drule ld_joint_boundary_site_frontiers >> strip_tac >>
  drule ld_joint_boundary_scratch_frontier >> strip_tac >>
  `FLOOKUP t.vs_allocas inst.inst_id = NONE` by
    metis_tac[ld_joint_original_lookup] >>
  `exec_alloca inst s amount = OK s1` by
    metis_tac[lower_dload_step_alloca] >>
  qhdtm_x_assum `ld_joint_boundary` mp_tac >>
  simp_tac bool_ss [ld_joint_boundary_def, ld_joint_frame_def] >> strip_tac >>
  `(a,inst.inst_id) NOTIN FDOM sites` by
    (`FLOOKUP B (a,inst.inst_id) = NONE` by
       (fs[occurrence_annotation_ok_def, occurrence_allocas_ok_def]) >>
     fs[ld_joint_erasure_def, FLOOKUP_DEF]) >>
  drule_all (Q.ISPEC `amount:bytes32`
    (Q.GEN `z` (SPEC_ALL lower_dload_paired_alloca_fresh))) >>
  disch_then (qspec_then `amount` strip_assume_tac) >>
  gvs[] >>
  `t1.vs_alloca_next < dimword (:256)` by decide_tac >>
  qexists_tac `t1` >> rpt conj_tac
  >- metis_tac[lower_dload_step_alloca]
  >- (gvs[ld_joint_erasure_def, FLOOKUP_UPDATE] >>
      rpt gen_tac >> Cases_on `(a,inst.inst_id) = id` >> simp[] >> metis_tac[])
  >- (`lo <= t.vs_alloca_next /\
       s.vs_alloca_next + w2n amount < dimword (:256)` by decide_tac >>
      irule ld_joint_geometry_extend_frontiers >> simp[] >> metis_tac[])
  >- (irule ld_allocas_fresh_site >> metis_tac[])
  >> simp[]
QED

Theorem ld_joint_saved_extend:
  !U stk ts. ld_joint_saved C' sites X lo U stk ts /\
  key NOTIN FDOM sites /\ ~MEM (FST key) (MAP (\f. f.of_owner) U) ==>
  ld_joint_saved C' (sites |+ (key,(b,c,z))) X lo U stk ts
Proof
  Induct >> simp[ld_joint_saved_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  `FST key <> h.of_owner` by simp[] >>
  `!aid. key <> (h.of_owner,aid)` by (rpt strip_tac >> gvs[]) >>
  qexists_tac `u` >>
  qpat_x_assum `ld_joint_frame _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp_tac bool_ss [ld_joint_frame_def] >> strip_tac >>
      rpt conj_tac
      >- (gvs[ld_env_agree_def] >> rpt strip_tac >>
          irule ld_value_agree_extend >> metis_tac[])
      >- (gvs[ld_params_agree_def] >> rpt strip_tac >>
          irule ld_value_agree_extend >> metis_tac[])
      >- (simp_tac (srw_ss()) [ld_joint_allocas_def, FLOOKUP_UPDATE] >>
          fs[ld_joint_allocas_def] >> metis_tac[])
      >> gvs[FLOOKUP_UPDATE] >> metis_tac[]
QED
