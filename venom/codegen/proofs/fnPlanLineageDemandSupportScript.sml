Theory fnPlanLineageDemandSupport
Ancestors
  livenessBlockProofs livenessTransferProofs venomWfProps venomExecProps venomExecProofs passSharedDefs finite_map indexedLists list rich_list
Libs
  venomInstTheory venomWfTheory livenessDefsTheory pairTheory

Definition raw_phi_inputs_def:
  raw_phi_inputs instrs =
    FLAT (MAP (\phi. MAP SND (phi_pairs phi.inst_operands))
      (collect_phis instrs))
End

Theorem foldl_pair_updates_domain:
  !pairs m j v.
    v IN FDOM (FOLDL (\m (l,w). m |+ (w,j)) m pairs) <=>
    v IN FDOM m \/ MEM v (MAP SND pairs)
Proof
  Induct_on `pairs` >> simp[] >> rpt gen_tac >>
  PairCases_on `h` >> simp[] >> metis_tac[]
QED

Theorem foldl_phi_maps_domain:
  !items op_map matching pred v.
    v IN FDOM (FST (FOLDL
      (\(op_map,matching) (j,phi).
        (FOLDL (\m (l,w). m |+ (w,j)) op_map (phi_pairs phi.inst_operands),
         case FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) of
           NONE => matching
         | SOME (_,w) => matching |+ (j,w)))
      (op_map,matching) items)) <=>
    v IN FDOM op_map \/
    MEM v (FLAT (MAP (\item. MAP SND (phi_pairs (SND item).inst_operands)) items))
Proof
  Induct_on `items` >> simp[] >> rpt gen_tac >>
  PairCases_on `h` >> simp[foldl_pair_updates_domain] >> metis_tac[]
QED

Theorem build_phi_maps_domain:
  !pred phis v.
    v IN FDOM (FST (build_phi_maps pred phis)) <=>
    MEM v (FLAT (MAP (\phi. MAP SND (phi_pairs phi.inst_operands)) phis))
Proof
  simp[build_phi_maps_def, foldl_phi_maps_domain, MAP_MAPi,
       combinTheory.o_DEF, MAPi_EQ_MAP]
QED

Theorem foldl_phi_maps_matching:
  !items op_map matching pred i v.
    FLOOKUP (SND (FOLDL
      (\(op_map,matching) (j,phi).
        (FOLDL (\m (l,w). m |+ (w,j)) op_map (phi_pairs phi.inst_operands),
         case FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) of
           NONE => matching
         | SOME (_,w) => matching |+ (j,w)))
      (op_map,matching) items)) i = SOME v ==>
    FLOOKUP matching i = SOME v \/
    ?item. MEM item items /\ MEM (pred,v) (phi_pairs (SND item).inst_operands)
Proof
  Induct_on `items` >> simp[] >> rpt gen_tac >>
  PairCases_on `h` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac
  >- (Cases_on `FIND (\(l,w). l = pred) (phi_pairs h1.inst_operands)` >> gvs[] >>
      PairCases_on `x` >> gvs[FLOOKUP_UPDATE] >>
      Cases_on `h0 = i` >> gvs[] >>
      disj2_tac >> qexists_tac `(h0,h1)` >> simp[] >>
      drule FIND_MEM >> drule FIND_P >> simp[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem input_vars_foldl_origin:
  !base acc placed op_map matching v.
    MEM v (FST (FOLDL (\(acc,placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w],placed)
      | SOME i => if MEM i placed then (acc,placed)
          else case FLOOKUP matching i of
            NONE => (acc,placed)
          | SOME src_v => (acc ++ [src_v],i::placed))
      (acc,placed) base)) ==>
    MEM v acc \/ (MEM v base /\ FLOOKUP op_map v = NONE) \/
    ?i. FLOOKUP matching i = SOME v
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `FLOOKUP op_map h` >> simp[]
  >- (strip_tac >> first_x_assum drule >>
      simp[MEM_APPEND] >> metis_tac[]) >>
  rename1 `FLOOKUP op_map h = SOME i` >>
  Cases_on `MEM i placed` >> simp[]
  >- (strip_tac >> first_x_assum drule >> metis_tac[]) >>
  Cases_on `FLOOKUP matching i` >> simp[]
  >- (strip_tac >> first_x_assum drule >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >>
  simp[MEM_APPEND] >> metis_tac[]
QED

Theorem input_vars_from_projected_membership:
  !pred instrs base v.
    MEM v (input_vars_from pred instrs base) ==>
    (MEM v base /\ ~MEM v (raw_phi_inputs instrs)) \/
    ?phi. MEM phi (collect_phis instrs) /\
      MEM (pred,v) (phi_pairs phi.inst_operands)
Proof
  rpt gen_tac >> simp[input_vars_from_def] >>
  Cases_on `NULL (collect_phis instrs)`
  >- (gvs[NULL_EQ, raw_phi_inputs_def]) >>
  Cases_on `build_phi_maps pred (collect_phis instrs)` >>
  rename1 `build_phi_maps pred (collect_phis instrs) = (op_map,matching)` >>
  simp[Once UNCURRY] >> strip_tac >> drule input_vars_foldl_origin >>
  simp[] >> strip_tac
  >- (disj1_tac >> simp[] >>
      qspecl_then [`pred`, `collect_phis instrs`, `v`]
        mp_tac build_phi_maps_domain >>
      gvs[raw_phi_inputs_def, FLOOKUP_DEF]) >>
  disj2_tac >>
  qspecl_then [`pred`, `collect_phis instrs`, `i`, `v`]
    mp_tac livenessTransferProofsTheory.build_phi_maps_matching_mem >> gvs[]
QED

Definition demand_available_def:
  demand_available fn bb i v <=>
    ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
      MEM v di.inst_outputs /\
      fn_dominates fn db.bb_label bb.bb_label /\
      (db = bb ==> ?k. k < i /\ k < LENGTH bb.bb_instructions /\
                          EL k bb.bb_instructions = di)
End

Theorem demand_available_endpoint:
  !fn bb v.
    wf_function fn ==>
    (demand_available fn bb (LENGTH bb.bb_instructions) v <=>
     def_available_at fn bb NONE v)
Proof
  rpt gen_tac >> strip_tac >>
  simp[demand_available_def, def_available_at_def] >>
  eq_tac >> strip_tac
  >- metis_tac[] >>
  qexistsl_tac [`def_bb`, `def_inst`] >> simp[] >>
  strip_tac >> gvs[MEM_EL] >> metis_tac[]
QED

Theorem demand_available_predecessor:
  !fn pb bb v.
    wf_function fn /\ MEM pb fn.fn_blocks /\ MEM bb fn.fn_blocks /\
    fn_reachable fn pb.bb_label /\ fn_cfg_edge fn pb.bb_label bb.bb_label /\
    demand_available fn bb 0 v ==>
    def_available_at fn pb NONE v
Proof
  rpt strip_tac >> gvs[demand_available_def] >>
  `db.bb_label <> bb.bb_label` by metis_tac[same_label_same_block] >>
  `fn_dominates fn db.bb_label pb.bb_label` by
    (irule fn_dominates_predecessor >> metis_tac[]) >>
  simp[def_available_at_def] >> metis_tac[]
QED

Theorem demand_available_entry:
  !fn eb v.
    wf_function fn /\ entry_block fn = SOME eb ==>
    ~demand_available fn eb 0 v
Proof
  rpt strip_tac >> gvs[demand_available_def] >>
  `fn_entry_label fn = SOME eb.bb_label /\ MEM eb fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[entry_block_def, fn_entry_label_def]) >>
  `db.bb_label = eb.bb_label` by
    (qpat_x_assum `fn_dominates _ _ _` mp_tac >>
     simp[fn_dominates_def] >> strip_tac >>
     first_x_assum (qspec_then `[eb.bb_label]` mp_tac) >>
     simp[is_fn_path_def]) >>
  metis_tac[same_label_same_block]
QED

Theorem demand_available_before_use:
  !fn bb i v.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    i < LENGTH bb.bb_instructions /\
    def_available_at fn bb (SOME (EL i bb.bb_instructions)) v ==>
    demand_available fn bb i v
Proof
  rpt strip_tac >> gvs[def_available_at_def, demand_available_def] >>
  qexistsl_tac [`def_bb`, `def_inst`] >> simp[] >> strip_tac >>
  gvs[] >>
  `j = i` by
    (irule inst_ids_el_eq >> qexistsl_tac [`bb`, `fn`] >>
     gvs[wf_function_def]) >>
  qexists_tac `i'` >> simp[]
QED

Theorem demand_available_step_back:
  !fn bb i v.
    demand_available fn bb (SUC i) v /\
    ~MEM v (EL i bb.bb_instructions).inst_outputs ==>
    demand_available fn bb i v
Proof
  rpt strip_tac >> gvs[demand_available_def] >>
  qexistsl_tac [`db`, `di`] >> simp[] >> strip_tac >> gvs[] >>
  `k <> i` by metis_tac[] >>
  qexists_tac `k` >> simp[]
QED

Theorem collect_phis_all_prefix:
  !instrs i.
    i < LENGTH instrs /\ (EL i instrs).inst_opcode = PHI /\
    (!j. j < i ==> (EL j instrs).inst_opcode = PHI) ==>
    MEM (EL i instrs) (collect_phis instrs)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `i` >>
  simp[collect_phis_def] >> strip_tac >> gvs[] >>
  `h.inst_opcode = PHI` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[] >> disj2_tac >> first_x_assum irule >> simp[] >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]
QED

Theorem block_phi_mem_collect:
  !bb i.
    bb_well_formed bb /\ i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = PHI ==>
    MEM (EL i bb.bb_instructions) (collect_phis bb.bb_instructions)
Proof
  rpt strip_tac >> irule collect_phis_all_prefix >> simp[] >>
  rpt strip_tac >>
  Cases_on `(EL j bb.bb_instructions).inst_opcode = PHI` >> simp[] >>
  `i < j` by (irule phi_before_non_phi >> metis_tac[arithmeticTheory.LESS_TRANS]) >>
  decide_tac
QED

Theorem instruction_use_demand:
  !fn bb i v.
    wf_function fn /\ def_dominates_uses fn /\ MEM bb fn.fn_blocks /\
    i < LENGTH bb.bb_instructions /\
    MEM v (inst_uses (EL i bb.bb_instructions)) ==>
    demand_available fn bb i v \/ MEM v (raw_phi_inputs bb.bb_instructions)
Proof
  rpt strip_tac >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  qpat_x_assum `def_dominates_uses fn` mp_tac >>
  simp[def_dominates_uses_def] >>
  disch_then (drule_then drule) >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = PHI` >> simp[]
  >- (strip_tac >> disj2_tac >>
      `MEM (EL i bb.bb_instructions) (collect_phis bb.bb_instructions)` by
        (irule block_phi_mem_collect >> metis_tac[wf_function_bb_well_formed]) >>
      gvs[phi_edge_uses_wf_def, inst_uses_def] >>
      drule phi_well_formed_uses_pairs >> strip_tac >>
      simp[raw_phi_inputs_def, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  strip_tac >> disj1_tac >> irule demand_available_before_use >> simp[] >>
  first_x_assum irule >> gvs[inst_uses_def] >>
  metis_tac[MEM_operand_vars_eq_Var]
QED

Theorem liveness_block_backward_demand:
  !n fn bb cfg st i v.
    n = LENGTH bb.bb_instructions - i /\ i <= LENGTH bb.bb_instructions /\
    wf_function fn /\ def_dominates_uses fn /\ MEM bb fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    EVERY (demand_available fn bb (LENGTH bb.bb_instructions))
      (liveness_out fn.fn_blocks cfg bb.bb_label st) /\
    MEM v (df_at [] (liveness_block fn.fn_blocks cfg bb.bb_label st)
      bb.bb_label i) ==>
    demand_available fn bb i v \/ MEM v (raw_phi_inputs bb.bb_instructions)
Proof
  Induct
  >- (rpt strip_tac >>
      `i = LENGTH bb.bb_instructions` by decide_tac >> gvs[] >>
      `liveness_instrs fn.fn_blocks bb.bb_label = bb.bb_instructions` by
        simp[liveness_instrs_def] >>
      gvs[GSYM liveness_block_exit, EVERY_MEM] >> metis_tac[]) >>
  rpt strip_tac >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  `liveness_instrs fn.fn_blocks bb.bb_label = bb.bb_instructions` by
    simp[liveness_instrs_def] >>
  `MEM v (liveness_transfer fn.fn_blocks (EL i bb.bb_instructions)
     (df_at [] (liveness_block fn.fn_blocks cfg bb.bb_label st)
        bb.bb_label (SUC i)))` by
    metis_tac[liveness_block_transfer] >>
  Cases_on `MEM v (inst_uses (EL i bb.bb_instructions))`
  >- (irule instruction_use_demand >> simp[]) >>
  gvs[liveness_transfer_def, livenessProofsTheory.live_update_mem,
      inst_defs_def] >>
  `demand_available fn bb (SUC i) v \/
     MEM v (raw_phi_inputs bb.bb_instructions)` by
    (first_x_assum irule >> simp[] >>
     `SUC i <= LENGTH bb.bb_instructions /\
      n = LENGTH bb.bb_instructions - SUC i` by decide_tac >>
     simp[] >> qexistsl_tac [`cfg`, `st`] >> simp[]) >>
  metis_tac[demand_available_step_back]
QED

Theorem liveness_block_entry_demand:
  !fn bb cfg st v.
    wf_function fn /\ def_dominates_uses fn /\ MEM bb fn.fn_blocks /\
    EVERY (demand_available fn bb (LENGTH bb.bb_instructions))
      (liveness_out fn.fn_blocks cfg bb.bb_label st) /\
    MEM v (df_at [] (liveness_block fn.fn_blocks cfg bb.bb_label st)
      bb.bb_label 0) ==>
    demand_available fn bb 0 v \/ MEM v (raw_phi_inputs bb.bb_instructions)
Proof
  rpt strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  irule liveness_block_backward_demand >> simp[] >>
  qexistsl_tac [`cfg`, `st`] >> simp[]
QED

(* Once the PHI prefix is past, no raw-PHI exception is needed. *)
Theorem liveness_block_ordinary_suffix_demand:
  !fn bb cfg st i.
    wf_function fn /\ def_dominates_uses fn /\ MEM bb fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    i <= LENGTH bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode <> PHI) (DROP i bb.bb_instructions) /\
    EVERY (demand_available fn bb (LENGTH bb.bb_instructions))
      (liveness_out fn.fn_blocks cfg bb.bb_label st) ==>
    EVERY (demand_available fn bb i)
      (df_at [] (liveness_block fn.fn_blocks cfg bb.bb_label st) bb.bb_label i)
Proof
  rpt gen_tac >> measureInduct_on `LENGTH bb.bb_instructions - i` >> rpt strip_tac >>
  `liveness_instrs fn.fn_blocks bb.bb_label = bb.bb_instructions` by
    simp[liveness_instrs_def] >>
  Cases_on `i = LENGTH bb.bb_instructions`
  >- gvs[GSYM liveness_block_exit] >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >> rename1 `MEM v (df_at _ _ _ i)` >>
  `MEM v (liveness_transfer fn.fn_blocks (EL i bb.bb_instructions)
     (df_at [] (liveness_block fn.fn_blocks cfg bb.bb_label st)
        bb.bb_label (SUC i)))` by metis_tac[liveness_block_transfer] >>
  `(EL i bb.bb_instructions).inst_opcode <> PHI /\
    EVERY (\inst. inst.inst_opcode <> PHI) (DROP (SUC i) bb.bb_instructions)` by
    (Cases_on `DROP i bb.bb_instructions` >- gvs[] >>
     drule DROP_CONS_EL >> strip_tac >> gvs[]) >>
  Cases_on `MEM v (inst_uses (EL i bb.bb_instructions))`
  >- (`MEM (EL i bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
      qpat_x_assum `def_dominates_uses fn` mp_tac >>
      simp[def_dominates_uses_def] >>
      disch_then (drule_then drule) >> simp[] >> strip_tac >>
      irule demand_available_before_use >> simp[] >>
      first_x_assum irule >> gvs[inst_uses_def] >>
      metis_tac[MEM_operand_vars_eq_Var]) >>
  gvs[liveness_transfer_def, livenessProofsTheory.live_update_mem, inst_defs_def] >>
  `EVERY (demand_available fn bb (SUC i))
     (df_at [] (liveness_block fn.fn_blocks cfg bb.bb_label st) bb.bb_label (SUC i))` by
    (first_x_assum irule >> simp[] >> decide_tac) >>
  `demand_available fn bb (SUC i) v` by metis_tac[EVERY_MEM] >>
  metis_tac[demand_available_step_back]
QED

Theorem demand_available_mono:
  !fn bb i j v. i <= j /\ demand_available fn bb i v ==>
    demand_available fn bb j v
Proof
  rpt strip_tac >> gvs[demand_available_def] >>
  qexistsl_tac [`db`, `di`] >> simp[] >> strip_tac >> gvs[] >>
  qexists_tac `k` >> simp[] >> decide_tac
QED

Theorem current_output_demand_available_suc:
  !fn bb i v.
    wf_function fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\ MEM v (EL i bb.bb_instructions).inst_outputs ==>
    demand_available fn bb (SUC i) v
Proof
  rpt strip_tac >> simp[demand_available_def] >>
  qexistsl_tac [`bb`, `EL i bb.bb_instructions`] >> simp[EL_MEM] >>
  conj_tac
  >- (simp[fn_dominates_def] >> rpt strip_tac >> metis_tac[LAST_MEM]) >>
  qexists_tac `i` >> simp[]
QED
