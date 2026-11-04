Theory fnPlanLineagePhiSlots
Ancestors
  livenessDefs finite_map stackModel list rich_list

(* The trace depends on PHI operand classes, not the selected edge. *)
Definition phi_slot_step_def:
  phi_slot_step (op_map : (string, num) fmap) (acc : (string + num) list, placed) v =
    case FLOOKUP op_map v of
      NONE => (acc ++ [INL v], placed)
    | SOME i => if MEM i placed then (acc, placed)
                else (acc ++ [INR i], i :: placed)
End

Definition phi_slot_trace_def:
  phi_slot_trace op_map base = FST (FOLDL (phi_slot_step op_map) ([], []) base)
End

Definition phi_slot_realize_def:
  (phi_slot_realize (matching : (num, string) fmap) (INL v) = v) /\
  (phi_slot_realize matching (INR i) = THE (FLOOKUP matching i))
End

Theorem phi_slot_fold_factor:
  !base acc placed.
    (!v i. MEM v base /\ FLOOKUP op_map v = SOME i ==>
      IS_SOME (FLOOKUP matching i)) ==>
    FOLDL (\(out, seen) v.
      case FLOOKUP op_map v of
        NONE => (out ++ [v], seen)
      | SOME i => if MEM i seen then (out, seen)
                  else case FLOOKUP matching i of
                    NONE => (out, seen)
                  | SOME w => (out ++ [w], i :: seen))
      (MAP (phi_slot_realize matching) acc, placed) base =
    (MAP (phi_slot_realize matching) (FST (FOLDL (phi_slot_step op_map) (acc, placed) base)),
      SND (FOLDL (phi_slot_step op_map) (acc, placed) base))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `!v i. MEM v base' /\ FLOOKUP op_map v = SOME i ==>
    IS_SOME (FLOOKUP matching i)` by metis_tac[listTheory.MEM] >>
  simp[phi_slot_step_def] >> Cases_on `FLOOKUP op_map h`
  >- (simp[] >>
      first_x_assum (qspecl_then [`acc ++ [INL h]`, `placed`] mp_tac) >>
      simp[phi_slot_realize_def] >> metis_tac[]) >>
  rename1 `FLOOKUP op_map h = SOME idx` >>
  `IS_SOME (FLOOKUP matching idx)` by metis_tac[listTheory.MEM] >>
  Cases_on `FLOOKUP matching idx` >> gvs[] >>
  Cases_on `MEM idx placed`
  >- (simp[] >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  simp[] >>
  first_x_assum (qspecl_then [`acc ++ [INR idx]`, `idx :: placed`] mp_tac) >>
  simp[phi_slot_realize_def] >> metis_tac[]
QED

Theorem input_vars_from_slot_factor:
  !base.
  ~NULL (collect_phis instrs) /\
  build_phi_maps src (collect_phis instrs) = (op_map, matching) /\
  (!v i. MEM v base /\ FLOOKUP op_map v = SOME i ==>
    IS_SOME (FLOOKUP matching i)) ==>
  input_vars_from src instrs base =
    MAP (phi_slot_realize matching) (phi_slot_trace op_map base)
Proof
  qx_gen_tac `live` >> strip_tac >>
  qspecl_then [`live`, `[]`, `[]`] mp_tac phi_slot_fold_factor >>
  simp[phi_slot_trace_def, input_vars_from_def] >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then SUBST1_TAC >> simp[]
QED

Theorem slot_realization_predicates:
  !slots. EVERY (\s. P (f s) = Q (g s)) slots ==>
    MAP P (MAP f slots) = MAP Q (MAP g slots)
Proof
  Induct >> simp[] >> metis_tac[]
QED

Theorem stack_find_predicate_vector:
  !xs ys. MAP P xs = MAP Q ys ==> stack_find P xs = stack_find Q ys
Proof
  Induct >- (Cases >> simp[stack_find_def]) >>
  gen_tac >> Cases >> simp[stack_find_def] >> rpt strip_tac >> gvs[] >>
  `stack_find P xs = stack_find Q t` by
    (first_x_assum irule >> simp[]) >> simp[]
QED

Theorem slot_realization_reverse_search:
  EVERY (\s. P (f s) = Q (g s)) slots ==>
  stack_find P (REVERSE (MAP f slots)) =
    stack_find Q (REVERSE (MAP g slots))
Proof
  strip_tac >> irule stack_find_predicate_vector >>
  simp[MAP_REVERSE] >>
  irule slot_realization_predicates >> first_assum ACCEPT_TAC
QED

Theorem input_vars_from_slot_length:
  !base.
  ~NULL (collect_phis instrs) /\
  build_phi_maps src (collect_phis instrs) = (op_map, matching) /\
  (!v i. MEM v base /\ FLOOKUP op_map v = SOME i ==>
    IS_SOME (FLOOKUP matching i)) ==>
  LENGTH (input_vars_from src instrs base) = LENGTH (phi_slot_trace op_map base)
Proof
  rpt strip_tac >> drule_all input_vars_from_slot_factor >> simp[]
QED
