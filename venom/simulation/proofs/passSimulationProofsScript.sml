(*
 * Pass Simulation Framework — Proofs
 *
 * KEY THEOREMS:
 *   lift_result_refl         — R reflexive ⟹ lift_result R reflexive
 *   lift_result_trans        — R transitive ⟹ lift_result R transitive
 *   inst_sim_block_sim    — instruction sim → block sim
 *   block_sim_function    — block sim → function correctness
 *   conditional_inst_sim  — partial transforms → full inst sim
 *   block_sim_compose     — composition of block simulations
 *
 * Helper:
 *   lookup_block_map      — lookup in MAP'd block list
 *)

Theory passSimulationProofs
Ancestors
  passSimulationDefs

(* If bt preserves labels, lookup in MAP'd list = MAP of lookup *)
Theorem lookup_block_map_proof:
  !lbl bbs bt.
    (!bb. (bt bb).bb_label = bb.bb_label) ==>
    lookup_block lbl (MAP bt bbs) =
      OPTION_MAP bt (lookup_block lbl bbs)
Proof
  cheat
QED

Theorem lift_result_refl_proof:
  !(R : venom_state -> venom_state -> bool).
    (!s. R s s) ==>
    !r. lift_result R r r
Proof
  cheat
QED

Theorem lift_result_trans_proof:
  !(R : venom_state -> venom_state -> bool).
    (!s1 s2 s3. R s1 s2 /\ R s2 s3 ==> R s1 s3) ==>
    !r1 r2 r3. lift_result R r1 r2 /\ lift_result R r2 r3 ==>
               lift_result R r1 r3
Proof
  cheat
QED

(* KEY THEOREM: If f simulates every instruction, then block_map_transform f
   simulates every block. Proof by run_block induction. *)
Theorem inst_sim_block_sim_proof:
  !(R : venom_state -> venom_state -> bool) f.
    inst_simulates R f ==>
    block_simulates R (block_map_transform f)
Proof
  cheat
QED

(* KEY THEOREM: If bt simulates every block and preserves labels,
   then the transformed function produces R-related results.
   Proof by induction on fuel. *)
Theorem block_sim_function_proof:
  !(R : venom_state -> venom_state -> bool) bt.
    block_simulates R bt /\
    (!bb. (bt bb).bb_label = bb.bb_label) ==>
    !fuel fn s.
      lift_result R (run_function fuel fn s)
                 (run_function fuel (function_map_transform bt fn) s)
Proof
  cheat
QED

(* If f simulates instructions satisfying P, and is identity on others,
   then f simulates all instructions. *)
Theorem conditional_inst_sim_proof:
  !(R : venom_state -> venom_state -> bool) f P.
    (!s. R s s) /\
    (!inst s. P inst ==>
       lift_result R (step_inst inst s) (step_inst (f inst) s)) /\
    (!inst. P inst ==>
       is_terminator inst.inst_opcode =
       is_terminator (f inst).inst_opcode) /\
    (!inst. ~P inst ==> f inst = inst) ==>
    inst_simulates R f
Proof
  cheat
QED

(* If bt1 and bt2 both simulate, so does their composition.
   Needs R transitive. *)
Theorem block_sim_compose_proof:
  !(R : venom_state -> venom_state -> bool) bt1 bt2.
    (!s1 s2 s3. R s1 s2 /\ R s2 s3 ==> R s1 s3) /\
    block_simulates R bt1 /\ block_simulates R bt2 ==>
    block_simulates R (bt2 o bt1)
Proof
  cheat
QED
