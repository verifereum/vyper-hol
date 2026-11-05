Theory fnPlanLineagePhiRealization
Ancestors
  fnPlanLineagePhiTemporal fnPlanLineagePhiClasses fnPlanLineagePhiSlots
  fnPlanLineagePhiMaps finite_map list

Definition phi_slot_cell_def:
  (phi_slot_cell lm rm (INL v) = PhiCommon (Var v)) /\
  (phi_slot_cell lm rm (INR i) =
    PhiOriginal i (Var (THE (FLOOKUP lm i))) (Var (THE (FLOOKUP rm i))))
End

Theorem phi_slot_cells_projection:
  !slots. MAP (phi_cell_value left) (MAP (phi_slot_cell lm rm) slots) =
    MAP Var (MAP (phi_slot_realize (if left then lm else rm)) slots)
Proof
  Induct >> simp[] >> Cases_on `h` >>
  simp[phi_slot_cell_def, phi_cell_value_def, phi_slot_realize_def] >>
  Cases_on `left` >> simp[]
QED

Theorem native_slot_cells_tagged:
  !p q phis base.
  phi_uses_disjoint phis /\
  (!v i. MEM v base /\ FLOOKUP (FST (build_phi_maps p phis)) v = SOME i ==>
    IS_SOME (FLOOKUP (SND (build_phi_maps p phis)) i) /\
    IS_SOME (FLOOKUP (SND (build_phi_maps q phis)) i)) ==>
  phi_origin_tagged (native_phi_class p phis)
    (MAP (phi_slot_cell (SND (build_phi_maps p phis))
                        (SND (build_phi_maps q phis)))
      (phi_slot_trace (FST (build_phi_maps p phis)) base))
Proof
  rpt gen_tac >> strip_tac >>
  simp[phi_origin_tagged_def, listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rpt gen_tac >> strip_tac >> Cases_on `x`
  >- (gvs[phi_slot_cell_def, native_phi_class_def, phi_slot_trace_inl_mem]) >>
  simp[phi_slot_cell_def] >>
  rename1 `MEM (INR i) (phi_slot_trace _ live)` >>
  `?v. MEM v live /\ FLOOKUP (FST (build_phi_maps p phis)) v = SOME i` by
    metis_tac[phi_slot_trace_inr_mem] >>
  `i < LENGTH phis` by metis_tac[build_phi_maps_operand_range] >>
  `IS_SOME (FLOOKUP (SND (build_phi_maps p phis)) i) /\
   IS_SOME (FLOOKUP (SND (build_phi_maps q phis)) i)` by metis_tac[] >>
  conj_tac >> irule native_phi_matching_class >> simp[]
QED

Theorem native_slot_cells_classes:
  !p q phis base.
  phi_uses_disjoint phis /\
  (!v i. MEM v base /\ FLOOKUP (FST (build_phi_maps p phis)) v = SOME i ==>
    IS_SOME (FLOOKUP (SND (build_phi_maps p phis)) i) /\
    IS_SOME (FLOOKUP (SND (build_phi_maps q phis)) i)) ==>
  phi_origin_classes (native_phi_class p phis)
    (MAP (phi_slot_cell (SND (build_phi_maps p phis))
                        (SND (build_phi_maps q phis)))
      (phi_slot_trace (FST (build_phi_maps p phis)) base))
Proof
  rpt strip_tac >> irule phi_origin_tagged_classes >>
  irule native_slot_cells_tagged >> metis_tac[]
QED

Theorem slot_cells_class_coverage:
  !base op_map i lm rm.
  (?v. MEM v base /\ FLOOKUP op_map v = SOME i) ==>
  MEM (PhiOriginal i (Var (THE (FLOOKUP lm i))) (Var (THE (FLOOKUP rm i))))
    (MAP (phi_slot_cell lm rm) (phi_slot_trace op_map base))
Proof
  rpt gen_tac >> strip_tac >> rename1 `MEM v live` >>
  `MEM (INR i) (phi_slot_trace op_map live)` by
    metis_tac[phi_slot_trace_inr_mem] >>
  drule_then (qspec_then `phi_slot_cell lm rm` mp_tac) listTheory.MEM_MAP_f >>
  simp[phi_slot_cell_def]
QED

Theorem input_vars_from_cells_projection:
  !live src instrs op_map lm rm left.
  ~NULL (collect_phis instrs) /\
  build_phi_maps src (collect_phis instrs) =
    (op_map, if left then lm else rm) /\
  (!v i. MEM v live /\ FLOOKUP op_map v = SOME i ==>
    IS_SOME (FLOOKUP (if left then lm else rm) i)) ==>
  MAP (phi_cell_value left)
    (MAP (phi_slot_cell lm rm) (phi_slot_trace op_map live)) =
  MAP Var (input_vars_from src instrs live)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all input_vars_from_slot_factor >>
  simp[phi_slot_cells_projection]
QED

(* This equivalence fixes the orientation: slot order is bottom-to-top,
   exactly the order of input_vars_from, not its reversal. The arbitrary
   lower prefix is not certified by this logical realization theorem. *)
Theorem input_vars_from_cells_suffix:
  !live src instrs op_map lm rm left stk prefix.
  ~NULL (collect_phis instrs) /\
  build_phi_maps src (collect_phis instrs) =
    (op_map, if left then lm else rm) /\
  (!v i. MEM v live /\ FLOOKUP op_map v = SOME i ==>
    IS_SOME (FLOOKUP (if left then lm else rm) i)) ==>
  (stk = prefix ++ MAP Var (input_vars_from src instrs live) <=>
   stk = prefix ++ MAP (phi_cell_value left)
     (MAP (phi_slot_cell lm rm) (phi_slot_trace op_map live)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all input_vars_from_cells_projection >> simp[]
QED

(* Physical-entry producer audit (C3.2.2.29).

   Existing generate_block_plan_jmp_suffix in fnPlanLineageSuffix exports:
     generate_block_plan ... bb ps = SOME (ops,ps') /\
     non_param_insts bb <> [] /\
     (LAST (non_param_insts bb)).inst_opcode = JMP /\
     join_target_ops ... bb.bb_label (LAST (non_param_insts bb)) = SOME targets
       ==> ?prefix. ps'.ps_stack = prefix ++ targets.
   join_target_ops_def identifies targets, for [Label lbl] and a successful
   lookup, as MAP Var (input_vars_from bb.bb_label target_bb.bb_instructions
     (live_vars_at liveness lbl 0)). Its orientation is already the one in
   input_vars_from_cells_suffix. No reversal of slot order is justified or
   needed; stack_get_phi_depth searches REVERSE of that physical suffix.

   reachable_phi_live_entry_representative supplies, for each PHI index,
   an incoming pair (p,w) with w live at entry. build_phi_maps_operand_class
   then yields base-class membership, and phi_slot_trace_inr_mem yields the
   slot. reachable_phi_incoming_activated exports selected incoming value
   membership in input_vars_from; reachable_phi_incoming_live_out exports
   analyzed predecessor live-out membership. Neither exports a stack equation.

   Still missing: connect the successful predecessor JMP suffix through the
   frozen DFS/lineage successor relations to the actual pre-PHI state; produce
   both matching-map totalities on actual edges; and instantiate a common base
   and op_map with analyzed liveness. Non-JMP single-predecessor and entry cases
   require separate entry-shape reasoning. These logical projection theorems
   prove neither arbitrary physical entry coverage nor residual/spill-map
   agreement, and do not justify a remaining-class schedule induction.
*)

Theorem phi_slot_cells_origin_count:
  !slots i lm rm.
    phi_origin_count i (MAP (phi_slot_cell lm rm) slots) =
    LENGTH (FILTER (\s. s = INR i) slots)
Proof
  Induct >> simp[phi_origin_count_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[phi_slot_cell_def] >>
  Cases_on `y = i` >> fs[phi_origin_count_def]
QED

Theorem phi_slot_trace_origin_unique:
  !op_map base lm rm i.
    phi_origin_count i (MAP (phi_slot_cell lm rm) (phi_slot_trace op_map base)) <= 1 /\
    phi_origin_count i (REVERSE (MAP (phi_slot_cell lm rm) (phi_slot_trace op_map base))) <= 1
Proof
  simp[phi_origin_count_reverse, phi_slot_cells_origin_count, phi_slot_trace_inr_count]
QED
