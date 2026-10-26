(*
 * Venom unit-transform boundary (PLAN §5.8, D17-D20).
 * TOP-LEVEL: unit_result_rel, ctx_transform_correct,
 *   checked_unit_transform_correct, o1_initial_state_ok,
 *   inst_mem_below_frontier, raw_unit_memory_ok.
 * Forward simulation only, from ONE initial state; no GAS-reading list.
 * Successful runs compare observable_equiv, including executed requests.
 * Aborts compare neither states nor requests: REVERT alone must stay REVERT.
 * Raw memory uses the corrected post-PHI/incremented-index/callee-entry
 * reachability package, not an invariant on unincremented step results.
 *)
Theory unitTransformDefs
Ancestors
  venomCompilerTypes passSimulationDefs stateEquiv contextCodegenRel contextReachability
  venomExecSemantics venomState finite_map words list

(* ===== Forward terminating-run contract ===== *)

Definition unit_result_rel_def:
  unit_result_rel res res' <=>
    case (res, res') of
      (Halt s, Halt s') => observable_equiv s s'
    | (Abort a s, Abort a' s') => (a = Revert_abort ==> a' = Revert_abort)
    | _ => F
End

Definition ctx_transform_correct_def:
  ctx_transform_correct ctx ctx' s <=>
    !fuel. terminates (run_context fuel ctx s) ==>
      ?fuel'. unit_result_rel (run_context fuel ctx s)
                             (run_context fuel' ctx' s)
End

Definition checked_unit_transform_correct_def:
  checked_unit_transform_correct
    (pipeline : resolved_compiler_policy -> compilation_unit ->
                pipeline_output option)
    rpolicy (unit : compilation_unit) s <=>
    ?out. pipeline rpolicy unit = SOME out /\
      ctx_transform_correct unit.cu_context out.po_unit.cu_context s
End

Theorem unit_result_rel_Halt:
  unit_result_rel (Halt s) res <=>
    ?s'. res = Halt s' /\ observable_equiv s s'
Proof
  Cases_on `res` >> simp[unit_result_rel_def]
QED

Theorem unit_result_rel_Abort:
  unit_result_rel (Abort a s) res <=>
    ?a' s'. res = Abort a' s' /\ (a = Revert_abort ==> a' = Revert_abort)
Proof
  Cases_on `res` >> simp[unit_result_rel_def]
QED

Theorem unit_result_rel_nonterminal:
  ~unit_result_rel (OK s) res /\
  ~unit_result_rel (IntRet vals s) res /\
  ~unit_result_rel (Error err) res /\
  ~unit_result_rel res (OK s) /\
  ~unit_result_rel res (IntRet vals s) /\
  ~unit_result_rel res (Error err)
Proof
  Cases_on `res` >> simp[unit_result_rel_def]
QED

Theorem unit_result_rel_terminates:
  unit_result_rel res res' ==> terminates res /\ terminates res'
Proof
  Cases_on `res` >> Cases_on `res'` >>
  simp[unit_result_rel_def, terminates_def]
QED

(* The forward boundary supplies a terminating output at possibly different
 * fuel; it says nothing about a nonterminating raw run. *)
Theorem ctx_transform_correct_forward:
  ctx_transform_correct ctx ctx' s /\ terminates (run_context fuel ctx s) ==>
  ?fuel'. unit_result_rel (run_context fuel ctx s)
                         (run_context fuel' ctx' s) /\
          terminates (run_context fuel' ctx' s)
Proof
  metis_tac[ctx_transform_correct_def, unit_result_rel_terminates]
QED

Theorem checked_unit_transform_correct_success:
  pipeline rpolicy unit = SOME out ==>
  (checked_unit_transform_correct pipeline rpolicy unit s <=>
   ctx_transform_correct unit.cu_context out.po_unit.cu_context s)
Proof
  simp[checked_unit_transform_correct_def]
QED

(* ===== Initial allocation frontier and raw-run memory ===== *)

Definition o1_initial_state_ok_def:
  o1_initial_state_ok vs <=>
    vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\ vs.vs_memory = [] /\
    vs.vs_allocas = FEMPTY /\ vs.vs_alloca_next = 0
End

Definition inst_mem_below_frontier_def:
  inst_mem_below_frontier inst s <=>
    EVERY (\(off,len). len = 0 \/ off + len <= s.vs_alloca_next)
      (source_memory_read_ranges inst s ++ source_memory_write_ranges inst s)
End

Definition raw_unit_memory_ok_def:
  raw_unit_memory_ok ctx vs <=>
    ?Inv. codegen_reachability_package Inv ctx vs /\
      !fn inst s. Inv ctx fn inst s ==>
        s.vs_alloca_next < dimword (:256) /\ inst_mem_below_frontier inst s
End

(* Boundary elimination keeps all three corrected reachability clauses. *)
Theorem raw_unit_memory_ok_invariant:
  raw_unit_memory_ok ctx vs ==>
  ?Inv. codegen_reachability_package Inv ctx vs /\
        reachability_closed Inv ctx /\
        (!fn inst s. Inv ctx fn inst s ==>
          s.vs_alloca_next < dimword (:256) /\ inst_mem_below_frontier inst s)
Proof
  rw[raw_unit_memory_ok_def] >> qexists_tac `Inv` >>
  fs[codegen_reachability_package_def] >> first_assum ACCEPT_TAC
QED

(* The existential invariant is equivalent to checking the least closure.
 * Keep the entry witness: a context without one has no package even when
 * its raw instruction relation is empty. *)
Theorem raw_unit_memory_ok_iff_raw_reachable:
  raw_unit_memory_ok ctx vs <=>
  (?name fn lbl.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl) /\
  (!fn inst s. raw_inst_reachable vs ctx fn inst s ==>
    s.vs_alloca_next < dimword (:256) /\ inst_mem_below_frontier inst s)
Proof
  cheat
QED
