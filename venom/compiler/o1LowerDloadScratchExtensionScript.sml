(* Scratch-only allocation metadata: source sites never grow. *)
Theory o1LowerDloadScratchExtension
Ancestors
  o1LowerDloadSuppliedSegmentControl o1LowerDloadJointRelation
  o1LowerDloadAllocationBoundary o1LowerDloadScratchCount
  o1LowerDloadOccurrenceHeadroom o1LowerDloadJointFrontier o1LowerDloadOccurrence
  venomFnScheduleRunner irSupply finite_map pred_set list

Theorem ld_scratch_source_id_fresh:
  ir_supply_covers_fn u fn /\ ld_joint_scratch u fn did aid ==>
  ~MEM aid (fn_ir_inst_ids fn)
Proof
  strip_tac >> drule ld_scratch_flat_prefix >> strip_tac >>
  drule ld_supply_insts_reservations >> strip_tac >>
  gvs[ir_supply_covers_fn_def, EVERY_MEM] >> strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem ld_scratch_allocation_present:
  ld_joint_allocas sites X owner fn t /\
  FLOOKUP X (owner,did) = SOME (aid,c) ==>
  FLOOKUP t.vs_allocas aid = SOME (c,32)
Proof
  simp[ld_joint_allocas_def] >> metis_tac[]
QED

Theorem ld_scratch_allocation_absent:
  ir_supply_covers_fn u fn /\
  ld_joint_allocas sites X owner fn t /\
  (!d id c. FLOOKUP X (owner,d) = SOME (id,c) ==>
    ld_joint_scratch u fn d id) /\
  ld_joint_scratch u fn did aid /\ (owner,did) NOTIN FDOM X ==>
  FLOOKUP t.vs_allocas aid = NONE
Proof
  strip_tac >> drule_all ld_scratch_source_id_fresh >> strip_tac >>
  Cases_on `FLOOKUP t.vs_allocas aid` >> simp[] >>
  rename1 `FLOOKUP t.vs_allocas aid = SOME pair` >> PairCases_on `pair` >>
  fs[ld_joint_allocas_def] >>
  `?d. FLOOKUP X (owner,d) = SOME (aid,pair0)` by metis_tac[] >>
  `ld_joint_scratch u fn d aid` by metis_tac[] >>
  `d = did` by metis_tac[ld_joint_scratch_injective] >>
  gvs[FLOOKUP_DEF]
QED

Theorem ld_geometry_scratch_extend_frontier:
  ld_joint_geometry sites X lo owners /\ key NOTIN FDOM X /\
  MEM (FST key) owners /\ lo <= c /\ c+32 < dimword (:256) /\
  (!id b d z. FLOOKUP sites id = SOME (b,d,z) ==> d+z <= c) /\
  (!id aid d. FLOOKUP X id = SOME (aid,d) ==> d+32 <= c) ==>
  ld_joint_geometry sites (X |+ (key,(aid,c))) lo owners
Proof
  strip_tac >> simp[ld_joint_geometry_def, FLOOKUP_UPDATE] >>
  rpt conj_tac >> rpt gen_tac >>
  rpt (IF_CASES_TAC >> gvs[]) >> rpt strip_tac >>
  fs[ld_joint_geometry_def] >> metis_tac[]
QED

Theorem ld_allocas_scratch_extend:
  ld_joint_allocas sites X owner fn t /\
  (!d id b. FLOOKUP X (owner,d) = SOME (id,b) ==> ld_joint_scratch u fn d id) /\
  ld_joint_scratch u fn did aid /\ ~MEM aid (fn_ir_inst_ids fn) /\
  (owner,did) NOTIN FDOM X /\ FLOOKUP t.vs_allocas aid = NONE /\
  t1.vs_allocas = t.vs_allocas |+ (aid,(c,32)) ==>
  ld_joint_allocas sites (X |+ ((owner,did),(aid,c))) owner fn t1
Proof
  strip_tac >>
  `!d b. FLOOKUP X (owner,d) = SOME (aid,b) ==> F` by
    (rpt strip_tac >>
     `ld_joint_scratch u fn d aid` by metis_tac[] >>
     `d = did` by metis_tac[ld_joint_scratch_injective] >> gvs[FLOOKUP_DEF]) >>
  `!id b. FLOOKUP X (owner,did) <> SOME (id,b)` by simp[FLOOKUP_DEF] >>
  fs[ld_joint_allocas_def] >>
  `!b z d. FLOOKUP sites (owner,aid) <> SOME (b,d,z)` by metis_tac[] >>
  simp[FLOOKUP_UPDATE, COND_RAND, COND_RATOR, COND_EXPAND] >>
  conj_tac
  >- (map_every qx_gen_tac [`id`,`b`,`z`] >>
      Cases_on `aid = id` >> gvs[] >> eq_tac >> rpt strip_tac >>
      gvs[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_scratch_owner_filter_extend:
  ~MEM (FST key) owners ==>
  {id | id IN FDOM (X |+ (key,v)) /\ MEM (FST id) owners} =
  {id | id IN FDOM X /\ MEM (FST id) owners}
Proof
  strip_tac >> simp[EXTENSION] >> metis_tac[]
QED

Theorem ld_frame_other_scratch_extend:
  ld_joint_frame sites X lo owner older u fn fn' H HP tv s t /\
  ~MEM (FST key) (owner::older) ==>
  ld_joint_frame sites (X |+ (key,v)) lo owner older u fn fn' H HP tv s t
Proof
  strip_tac >>
  `!d. key <> (owner,d)` by (rpt strip_tac >> gvs[]) >>
  `{id | id IN FDOM (X |+ (key,v)) /\ MEM (FST id) (owner::older)} =
   {id | id IN FDOM X /\ MEM (FST id) (owner::older)}` by
    (irule ld_scratch_owner_filter_extend >> simp[]) >>
  fs[ld_joint_frame_def, ld_joint_allocas_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem ld_saved_scratch_extend:
  !U stk ts. ld_joint_saved C' sites X lo U stk ts /\
  ~MEM (FST key) (MAP (\f. f.of_owner) U) ==>
  ld_joint_saved C' sites (X |+ (key,v)) lo U stk ts
Proof
  Induct >> simp[ld_joint_saved_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qexists_tac `u` >> irule ld_frame_other_scratch_extend >> simp[] >> metis_tac[]
QED

Theorem ld_scratch_owner_credit_extend:
  key NOTIN FDOM X /\ MEM (FST key) owners ==>
  CARD {id | id IN FDOM (X |+ (key,v)) /\ MEM (FST id) owners} =
  CARD {id | id IN FDOM X /\ MEM (FST id) owners} + 1
Proof
  strip_tac >>
  `{id | id IN FDOM (X |+ (key,v)) /\ MEM (FST id) owners} =
   key INSERT {id | id IN FDOM X /\ MEM (FST id) owners}` by
    (simp[EXTENSION] >> metis_tac[]) >>
  `FINITE {id | id IN FDOM X /\ MEM (FST id) owners}` by
    (irule SUBSET_FINITE >> qexists_tac `FDOM X` >> simp[SUBSET_DEF]) >>
  simp[CARD_INSERT]
QED

Theorem ld_joint_dload_fresh_metadata:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs /\
  callee_first names C.ctx_functions /\ active_inst fn inst s /\
  inst.inst_opcode = DLOAD /\ ir_supply_covers_fn u fn /\
  ld_joint_scratch u fn inst.inst_id aid /\
  (!d id b. FLOOKUP X (a,d) = SOME (id,b) ==> ld_joint_scratch u fn d id) /\
  (a,inst.inst_id) NOTIN FDOM X /\
  t1.vs_allocas = t.vs_allocas |+ (aid,(t.vs_alloca_next,32)) /\
  t1.vs_alloca_next = t.vs_alloca_next + 32 ==>
  let X1 = X |+ ((a,inst.inst_id),(aid,t.vs_alloca_next)) in
    FLOOKUP t.vs_allocas aid = NONE /\
    t1.vs_alloca_next < dimword (:256) /\
    ld_joint_geometry sites X1 lo (a::MAP (\f. f.of_owner) U) /\
    ld_joint_allocas sites X1 a fn t1 /\
    (!d id b. FLOOKUP X1 (a,d) = SOME (id,b) ==> ld_joint_scratch u fn d id) /\
    ld_joint_saved C' sites X1 lo U stk ts /\
    t1.vs_alloca_next = s.vs_alloca_next +
      32 * CARD {id | id IN FDOM X1 /\ MEM (FST id) (a::MAP (\f. f.of_owner) U)}
Proof
  strip_tac >> simp_tac (srw_ss()) [LET_THM] >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `s.vs_alloca_next + 32 * ctx_dload_count C < dimword (:256)` by
    (irule ld_occurrence_shape_headroom >> metis_tac[]) >>
  drule_all ld_joint_scratch_credit >> strip_tac >>
  drule ld_joint_boundary_site_frontiers >> strip_tac >>
  drule ld_joint_boundary_scratch_frontier >> strip_tac >>
  `~MEM aid (fn_ir_inst_ids fn)` by metis_tac[ld_scratch_source_id_fresh] >>
  qhdtm_x_assum `ld_joint_boundary` mp_tac >>
  simp_tac bool_ss [ld_joint_boundary_def] >> strip_tac >>
  `ld_joint_allocas sites X a fn t` by fs[ld_joint_frame_def] >>
  `FLOOKUP t.vs_allocas aid = NONE` by
    (drule_all ld_scratch_allocation_absent >> simp[]) >>
  `CARD {id | id IN FDOM (X |+ ((a,inst.inst_id),(aid,t.vs_alloca_next))) /\
       MEM (FST id) (a::MAP (\f. f.of_owner) U)} =
   CARD {id | id IN FDOM X /\ MEM (FST id) (a::MAP (\f. f.of_owner) U)} + 1` by
    (irule ld_scratch_owner_credit_extend >> simp[]) >>
  fs[ld_joint_frame_def] >>
  `t.vs_alloca_next + 32 < dimword (:256)` by decide_tac >>
  `lo <= t.vs_alloca_next` by decide_tac >>
  simp[] >> rpt conj_tac
  >- (irule ld_geometry_scratch_extend_frontier >> simp[] >> metis_tac[]) 
  >- (irule ld_allocas_scratch_extend >> metis_tac[]) 
  >- (simp[FLOOKUP_UPDATE] >> rpt gen_tac >>
      Cases_on `inst.inst_id = d` >> simp[] >> metis_tac[])
  >- (irule ld_saved_scratch_extend >> fs[occurrence_annotation_ok_def]) >>
  decide_tac
QED
