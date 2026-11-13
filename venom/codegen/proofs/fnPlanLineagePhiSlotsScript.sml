Theory fnPlanLineagePhiSlots
Ancestors
  livenessDefs finite_map stackModel list rich_list stackPlanGen fnPlanLineagePhiMaps

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

Theorem phi_slot_fold_inr_mem[local]:
  !base acc placed i.
  MEM (INR i) (FST (FOLDL (phi_slot_step op_map) (acc,placed) base)) <=>
  MEM (INR i) acc \/
    (~MEM i placed /\ ?v. MEM v base /\ FLOOKUP op_map v = SOME i)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[phi_slot_step_def] >> Cases_on `FLOOKUP op_map h`
  >- simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  rename1 `FLOOKUP op_map h = SOME idx` >>
  Cases_on `MEM idx placed` >> simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  qpat_x_assum `!acc placed i. _` kall_tac >> metis_tac[]
QED

Theorem phi_slot_fold_inl_mem[local]:
  !base acc placed v.
  MEM (INL v) (FST (FOLDL (phi_slot_step op_map) (acc,placed) base)) <=>
  MEM (INL v) acc \/ (MEM v base /\ FLOOKUP op_map v = NONE)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[phi_slot_step_def] >> Cases_on `FLOOKUP op_map h`
  >- (simp[] >> Cases_on `v = h` >> gvs[]) >>
  rename1 `FLOOKUP op_map h = SOME idx` >>
  Cases_on `MEM idx placed` >> simp[] >>
  Cases_on `v = h` >> gvs[]
QED

Theorem phi_slot_trace_inr_mem:
  !op_map base i. MEM (INR i) (phi_slot_trace op_map base) <=>
  ?v. MEM v base /\ FLOOKUP op_map v = SOME i
Proof
  simp[phi_slot_trace_def, phi_slot_fold_inr_mem]
QED

Theorem phi_slot_trace_inl_mem:
  !op_map base v. MEM (INL v) (phi_slot_trace op_map base) <=>
  MEM v base /\ FLOOKUP op_map v = NONE
Proof
  simp[phi_slot_trace_def, phi_slot_fold_inl_mem]
QED

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

(* Local interface audit: repeats within one PHI do not create extra slots.
   These are map tests, not a reachable-state or temporal preservation proof. *)
Definition phi_slot_audit_phis_def:
  phi_slot_audit_phis =
    [mk_inst 0 PHI [Label "L"; Var "a"; Label "R"; Var "a"] ["x"];
     mk_inst 1 PHI [Label "L"; Var "b"; Label "R"; Var "c"] ["y"]]
End

Theorem phi_slot_audit_maps[local]:
  FST (build_phi_maps "L" phi_slot_audit_phis) =
    FST (build_phi_maps "R" phi_slot_audit_phis) /\
  phi_slot_trace (FST (build_phi_maps "L" phi_slot_audit_phis))
    ["a"; "b"; "c"; "pass"; "a"] = [INR 0; INR 1; INL "pass"] /\
  MAP (\i. FLOOKUP (SND (build_phi_maps "L" phi_slot_audit_phis)) i) [0;1] =
    [SOME "a"; SOME "b"] /\
  MAP (\i. FLOOKUP (SND (build_phi_maps "R" phi_slot_audit_phis)) i) [0;1] =
    [SOME "a"; SOME "c"] /\
  input_vars_from "L" phi_slot_audit_phis ["a";"b";"c";"pass";"a"] =
    ["a";"b";"pass"] /\
  input_vars_from "R" phi_slot_audit_phis ["a";"b";"c";"pass";"a"] =
    ["a";"c";"pass"] /\
  phi_uses_disjoint phi_slot_audit_phis
Proof
  EVAL_TAC
QED

Theorem phi_slot_audit_search[local]:
  MAP (\v. MEM v ["b";"c"])
    (input_vars_from "L" phi_slot_audit_phis ["a";"b";"c";"pass";"a"]) =
    [F;T;F] /\
  MAP (\v. MEM v ["b";"c"])
    (input_vars_from "R" phi_slot_audit_phis ["a";"b";"c";"pass";"a"]) =
    [F;T;F] /\
  stack_find (\v. MEM v ["b";"c"]) (REVERSE
    (input_vars_from "L" phi_slot_audit_phis ["a";"b";"c";"pass";"a"])) = SOME 1 /\
  stack_find (\v. MEM v ["b";"c"]) (REVERSE
    (input_vars_from "R" phi_slot_audit_phis ["a";"b";"c";"pass";"a"])) = SOME 1
Proof
  EVAL_TAC
QED

(* Producer audit (C3.2.2.6). The signatures below are proposed obligations,
   NOT theorems proved by the bounded tests above.

   (a) !p q phis. FST (build_phi_maps p phis) =
                     FST (build_phi_maps q phis).
   No WF premise is needed: the first component's update ignores the second
   accumulator and source label. Proof should use a generic FOLDL projection,
   once, not unfold build_phi_maps at every consumer.

   (b) An edge-indexed map boundary should expose, for i < LENGTH phis:
       FLOOKUP (SND (build_phi_maps p phis)) i =
         OPTION_MAP SND (FIND (\lv. FST lv = p)
                            (phi_pairs (EL i phis).inst_operands)).
   In addition the first map must have the range bound
       FLOOKUP (FST (build_phi_maps p phis)) v = SOME i ==>
       i < LENGTH phis.
   Totality then follows from named predecessor coverage. Its existing
   producer is venomWf.phi_edge_uses_wf_def (lines 593-607), obtained via
   def_dominates_uses_def for every collected PHI. collect_phis_mem in
   livenessTransferProofs supplies membership and opcode. Connecting actual
   cfg_preds_of to fn_cfg_edge still needs the analyzed CFG boundary.
   livenessTransferProofs.build_phi_maps_matching_mem and
   livenessLocalProofs.lv_phi_op_map_char are LOCAL inversion lemmas, not
   exported index/totality interfaces; neither proves the proposed boundary.

   (c) Let om = FST (build_phi_maps p phis), mm = SND (...).
   Under EVERY (\phi. phi_well_formed phi.inst_operands) phis,
   phi_uses_disjoint phis, edge coverage, i < LENGTH phis, and
   MEM s (phi_slot_trace om live), the needed statement is
       MEM (Var (phi_slot_realize mm s))
           (FILTER is_var_operand (EL i phis).inst_operands) <=> s = INR i.
   Restricting s to emitted slots is essential: an arbitrary INL incoming
   name would falsify this equivalence. Well-formed operand pairs identify
   inst_uses with pair values; disjointness prevents map overwrite by a
   different PHI. Same-PHI repeated operands are allowed and tested above.
   phi_operands_ready_def / phi_block_ready_def supply disjointness whenever
   the function has any PHIs. They do not themselves assert this search fact.

   (d) A sufficient entry-slot producer is
       (?v. MEM v (live_vars_at (liveness_analyze fn) lbl 0) /\
            FLOOKUP om v = SOME i) ==>
       MEM (INR i) (phi_slot_trace om
                       (live_vars_at (liveness_analyze fn) lbl 0)).
   This is a generic trace emission fact, independent of matching. Establishing
   its antecedent for EACH reachable PHI is still a separate obligation.
   live_vars_at_uses and live_vars_at_propagate in livenessAnalysisProps give
   uses at their instruction and backward propagation only if not killed.
   Thus propagation through earlier PHIs needs an incoming witness not among
   their outputs. Neither phi_uses_disjoint nor phi_block_ready states that
   no-output-alias fact. A blanket ban would be too strong for loop-carried
   names: the frozen task allows incoming names that equal PHI outputs.
   The available global producer candidate is def_available_at together with
   SSA uniqueness and a first-entry path; this audit has NOT proved it.

   Even (a)-(d) only cover entry searches. Earlier PHIs rename slots and may
   delete dead outputs; proving that their new output cannot shadow a later
   PHI's incoming set requires a temporal alias/liveness argument. Readiness
   excludes incoming names live AFTER the whole prefix, not all intermediate
   alias patterns. No global freshness assumption or reachable counterexample
   is inferred here. Persistent spills, cleanup windows and allocator framing
   remain outside this local map audit.
*)

Theorem phi_slot_trace_class_mem:
  !base. phi_uses_disjoint phis ==>
  (MEM (INR i) (phi_slot_trace (FST (build_phi_maps p phis)) base) <=>
   i < LENGTH phis /\ ?v l. MEM v base /\
     MEM (l,v) (phi_pairs (EL i phis).inst_operands))
Proof
  gen_tac >> strip_tac >>
  simp[phi_slot_trace_inr_mem, build_phi_maps_operand_class] >> metis_tac[]
QED

Theorem phi_slot_fold_inr_count:
  !base acc placed i op_map.
    LENGTH (FILTER (\s. s = INR i)
      (FST (FOLDL (phi_slot_step op_map) (acc,placed) base))) <=
    LENGTH (FILTER (\s. s = INR i) acc) + (if MEM i placed then 0 else 1)
Proof
  Induct >> rpt gen_tac
  >- simp[] >>
  simp[phi_slot_step_def] >>
  Cases_on `FLOOKUP op_map h` >> simp[]
  >- (first_x_assum (qspecl_then [`acc ++ [INL h]`, `placed`, `i`, `op_map`] mp_tac) >>
      simp[listTheory.FILTER_APPEND_DISTRIB]) >>
  rename1 `FLOOKUP op_map h = SOME j` >>
  Cases_on `MEM j placed` >> simp[] >>
  first_x_assum (qspecl_then [`acc ++ [INR j]`, `j::placed`, `i`, `op_map`] mp_tac) >>
  Cases_on `i = j` >> Cases_on `MEM i placed` >>
  gvs[listTheory.FILTER_APPEND_DISTRIB]
QED

Theorem phi_slot_trace_inr_count:
  !op_map base i.
    LENGTH (FILTER (\s. s = INR i) (phi_slot_trace op_map base)) <= 1
Proof
  rpt gen_tac >> rename1 `phi_slot_trace om xs` >>
  qspecl_then [`xs`, `[]`, `[]`, `i`, `om`] mp_tac phi_slot_fold_inr_count >>
  simp[phi_slot_trace_def]
QED
