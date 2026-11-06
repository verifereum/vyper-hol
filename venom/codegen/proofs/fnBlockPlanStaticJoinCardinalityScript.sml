Theory fnBlockPlanStaticJoinCardinality
Ancestors
  fnBlockPlanStaticOffsetLive indexedLists finite_map livenessDefs list venomWf stackPlanGen venomInst
  fnBlockPlanStaticDistinct

(* Input selection inspects only the domain of the edge's matching map
   when deciding whether to append a slot.  The selected names are irrelevant. *)
Theorem phi_input_fold_length[local]:
  !live om mm1 mm2 acc1 acc2 placed.
    FDOM mm1 = FDOM mm2 /\ LENGTH acc1 = LENGTH acc2 ==>
    LENGTH (FST (FOLDL (\(acc, done) v.
      case FLOOKUP om v of
        NONE => (acc ++ [v], done)
      | SOME i => if MEM i done then (acc, done)
                  else case FLOOKUP mm1 i of
                         NONE => (acc, done)
                       | SOME src => (acc ++ [src], i :: done))
      (acc1,placed) live)) =
    LENGTH (FST (FOLDL (\(acc, done) v.
      case FLOOKUP om v of
        NONE => (acc ++ [v], done)
      | SOME i => if MEM i done then (acc, done)
                  else case FLOOKUP mm2 i of
                         NONE => (acc, done)
                       | SOME src => (acc ++ [src], i :: done))
      (acc2,placed) live))
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >> simp[] >>
  Cases_on `FLOOKUP om h`
  >- (simp[] >> first_x_assum irule >> simp[]) >> simp[] >>
  rename1 `FLOOKUP om h = SOME i` >> Cases_on `MEM i placed`
  >- (simp[] >> first_x_assum irule >> simp[]) >> simp[] >>
  Cases_on `FLOOKUP mm1 i` >> Cases_on `FLOOKUP mm2 i` >> simp[] >>
  gvs[FLOOKUP_DEF] >> first_x_assum irule >> simp[]
QED

Theorem phi_maps_fold_edge_domains[local]:
  !items pred1 pred2 om mm1 mm2.
    FDOM mm1 = FDOM mm2 /\
    EVERY (\(i,phi).
      IS_SOME (FIND (\(l,v). l = pred1) (phi_pairs phi.inst_operands)) =
      IS_SOME (FIND (\(l,v). l = pred2) (phi_pairs phi.inst_operands))) items ==>
    FST (FOLDL (\(op_map,matching) (i,phi).
      (FOLDL (\m (l,v). m |+ (v,i)) op_map (phi_pairs phi.inst_operands),
       case FIND (\(l,v). l = pred1) (phi_pairs phi.inst_operands) of
         NONE => matching | SOME (_,v) => matching |+ (i,v)))
      (om,mm1) items) =
    FST (FOLDL (\(op_map,matching) (i,phi).
      (FOLDL (\m (l,v). m |+ (v,i)) op_map (phi_pairs phi.inst_operands),
       case FIND (\(l,v). l = pred2) (phi_pairs phi.inst_operands) of
         NONE => matching | SOME (_,v) => matching |+ (i,v)))
      (om,mm2) items) /\
    FDOM (SND (FOLDL (\(op_map,matching) (i,phi).
      (FOLDL (\m (l,v). m |+ (v,i)) op_map (phi_pairs phi.inst_operands),
       case FIND (\(l,v). l = pred1) (phi_pairs phi.inst_operands) of
         NONE => matching | SOME (_,v) => matching |+ (i,v)))
      (om,mm1) items)) =
    FDOM (SND (FOLDL (\(op_map,matching) (i,phi).
      (FOLDL (\m (l,v). m |+ (v,i)) op_map (phi_pairs phi.inst_operands),
       case FIND (\(l,v). l = pred2) (phi_pairs phi.inst_operands) of
         NONE => matching | SOME (_,v) => matching |+ (i,v)))
      (om,mm2) items))
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `h` >>
  rename1 `(i,phi) :: items` >> simp[] >> strip_tac >>
  Cases_on `FIND (\(l,v). l = pred1) (phi_pairs phi.inst_operands)` >>
  Cases_on `FIND (\(l,v). l = pred2) (phi_pairs phi.inst_operands)` >>
  gvs[] >> first_x_assum irule >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[])
QED

(* Duplicate source names and overlap with ordinary live-in do not affect
   edge cardinality. Only existence of a selected source for each PHI matters. *)
Theorem input_vars_from_edge_length:
  !instrs live pred1 pred2.
    EVERY (\phi.
      IS_SOME (FIND (\(l,v). l = pred1) (phi_pairs phi.inst_operands)) =
      IS_SOME (FIND (\(l,v). l = pred2) (phi_pairs phi.inst_operands)))
      (collect_phis instrs) ==>
    LENGTH (input_vars_from pred1 instrs live) =
    LENGTH (input_vars_from pred2 instrs live)
Proof
  rpt strip_tac >>
  `FST (build_phi_maps pred1 (collect_phis instrs)) =
   FST (build_phi_maps pred2 (collect_phis instrs)) /\
   FDOM (SND (build_phi_maps pred1 (collect_phis instrs))) =
   FDOM (SND (build_phi_maps pred2 (collect_phis instrs)))` by
    (simp[build_phi_maps_def] >> irule phi_maps_fold_edge_domains >>
     simp[EVERY_MEM, indexedListsTheory.MEM_MAPi, pairTheory.FORALL_PROD] >>
     gvs[EVERY_MEM] >> metis_tac[EL_MEM]) >>
  Cases_on `build_phi_maps pred1 (collect_phis instrs)` >>
  Cases_on `build_phi_maps pred2 (collect_phis instrs)` >> gvs[] >>
  simp[input_vars_from_def] >>
  Cases_on `NULL (collect_phis instrs)` >- simp[] >> simp[] >>
  simp[distinct_pair_projection] >>
  irule phi_input_fold_length >> simp[]
QED

Theorem find_pair_source_exists[local]:
  !pairs pred. (?p. MEM p pairs /\ FST p = pred) ==>
    IS_SOME (FIND (\(l,v). l = pred) pairs)
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `h` >>
  rename1 `(lbl,v) :: pairs` >>
  Cases_on `lbl = pred` >> simp[FIND_thm] >> metis_tac[pairTheory.FST]
QED

Theorem phi_edge_matching_exists[local]:
  !fn bb phi pred.
    phi_edge_uses_wf fn bb phi /\ fn_cfg_edge fn pred bb.bb_label ==>
    IS_SOME (FIND (\(l,v). l = pred) (phi_pairs phi.inst_operands))
Proof
  rpt strip_tac >> irule find_pair_source_exists >>
  gvs[phi_edge_uses_wf_def] >> metis_tac[]
QED

Theorem ready_input_vars_from_edge_length:
  !fn bb pred1 pred2 live.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    fn_cfg_edge fn pred1 bb.bb_label /\ fn_cfg_edge fn pred2 bb.bb_label ==>
    LENGTH (input_vars_from pred1 bb.bb_instructions live) =
    LENGTH (input_vars_from pred2 bb.bb_instructions live)
Proof
  rpt strip_tac >> irule input_vars_from_edge_length >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[livenessProofsTheory.collect_phis_mem] >>
  `phi_edge_uses_wf fn bb phi` by
    (gvs[codegen_ready_fn_def, def_dominates_uses_def] >> metis_tac[]) >>
  metis_tac[phi_edge_matching_exists]
QED

(* Replay marker-prefix diagnostic:
   Edge cardinality is independent of source names, including duplicates within
   one PHI and overlap with ordinary live-in. def_dominates_uses supplies the
   matching-domain hypothesis on each actual edge; disjoint PHI uses are not
   needed for length equality.

   The remaining regional invariant would bound the replay incoming height by
   the height of the DFS incoming state, for every lineage_state at a label
   having a CFG path to a RET. Initial case: both stacks are empty. Singleton
   predecessor: successful-root coupling identifies the DFS parent; signed
   whole-block accounting could transport an established incoming bound.
   Join case: the DFS incoming stack is exactly its edge target stack, and
   ready_input_vars_from_edge_length equates the two target lengths. The
   lineage join admission still permits an arbitrary marker prefix, so the
   required residual fact is that this prefix is empty (or, equivalently here,
   replay incoming height is at most the edge target length).

   There is no unconditional marker-free cleanup step for that induction:
   lineage_state_step existentially overrides ps_cleanup_promised. Even in a
   RET-reaching region, where inventory_ret_cleanup_not_safe rules out the
   height-safe disjunct, promised=T makes clean_stack_plan's ok true. It can
   silently replace retained slots by markers, or mark the entire stack when
   inputs are empty. ret_cleanup_plan_unpromised requires an unpromised input
   and therefore does not apply to this arbitrary override. JMP reordering
   supplies the target suffix, not elimination of an older marker prefix.
   Ordinary instruction marker-free preservation also requires a marker-free
   input. Equal full block_ops must therefore be used to rule out the bad
   cleanup transition or to compensate its height effect. No such coupled
   cleanup/whole-block theorem is supplied by the cardinality argument.
   This is a missing replay interface, not a counterexample to the frozen
   obligation: the equal-code premise has not been falsified by this analysis.
*)
