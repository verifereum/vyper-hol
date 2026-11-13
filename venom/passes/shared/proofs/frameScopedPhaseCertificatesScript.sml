Theory frameScopedPhaseCertificates
Ancestors framePhaseCertificates frameIndexedComposition frameIndexedCertificates
          frameFiniteExecution

(* Q describes instruction/block segments; U describes completed function runs.
   The PHI witness h is linked explicitly, never universally reindexed. *)
Definition scoped_phase_phi_def:
  scoped_phase_phi Run A R BlockPair PhiLink <=>
    !(g:'g) fn fn' s t bb phi.
    Run g fn fn' s t /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi ==>
    ?(h:'g) bb' phi'.
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    eval_phis t bb'.bb_instructions = OK phi' /\ BlockPair bb bb' /\
    indexed_entry A R h
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) /\
    PhiLink g h fn fn' s t bb bb' phi phi'
End

Definition scoped_phase_pop_def:
  scoped_phase_pop A R Q U PushRel <=>
    !(g:'g) i j s t fn fn' cs ct (c:'g) (d:'g) ret post ret' post' out.
    indexed_entry A R g s t /\ PushRel g i j s t fn fn' cs ct c /\
    U c d (IntRet ret post) (IntRet ret' post') /\
    bind_outputs i.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s post)) = SOME out ==>
    ?(h:'g) out'. bind_outputs j.inst_outputs ret'.iret_values
      (adopt_return_fmp ret' (merge_callee_state t post')) = SOME out' /\
    Q g h (OK out) (OK out')
End

Definition scoped_phase_call_exit_def:
  scoped_phase_call_exit A R Q U PushRel <=>
    !(g:'g) i j s t fn fn' cs ct (c:'g) (d:'g) r r'.
    indexed_entry A R g s t /\ PushRel g i j s t fn fn' cs ct c /\
    U c d r r' /\ ((?p. r = Halt p) \/ (?a p. r = Abort a p)) ==>
    ?(h:'g). Q g h r r'
End

(* These premises name the actual PHI entry and actual completed blocks.
   There is no arbitrary h and no recursive target run in the boundary. *)
Definition scoped_phase_block_return_def:
  scoped_phase_block_return C C' Run Q PhiLink <=>
    !(g:'g) h k fn fn' s t bb bb' phi phi' u v.
    Run g fn fn' s t /\ PhiLink g h fn fn' s t bb bb' phi phi' /\
    finite_block C bb
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) (OK u) /\
    finite_block C' bb'
      (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) (OK v) /\
    Q h k (OK u) (OK v) /\ ~u.vs_halted ==>
    Run k fn fn' u v
End

Definition scoped_phase_run_next_def:
  scoped_phase_run_next C C' Run Q U PhiLink <=>
    !(g:'g) h k d fn fn' s t bb bb' phi phi' u v r r'.
    Run g fn fn' s t /\ PhiLink g h fn fn' s t bb bb' phi phi' /\
    finite_block C bb
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) (OK u) /\
    finite_block C' bb'
      (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) (OK v) /\
    Q h k (OK u) (OK v) /\ ~u.vs_halted /\ U k d r r' ==>
    U g d r r'
End

Definition scoped_phase_run_halt_def:
  scoped_phase_run_halt C C' Run Q U PhiLink <=>
    !(g:'g) h k fn fn' s t bb bb' phi phi' u v.
    Run g fn fn' s t /\ PhiLink g h fn fn' s t bb bb' phi phi' /\
    finite_block C bb
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) (OK u) /\
    finite_block C' bb'
      (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) (OK v) /\
    Q h k (OK u) (OK v) /\ u.vs_halted ==>
    U g k (Halt u) (Halt v)
End

Definition scoped_phase_run_exit_def:
  scoped_phase_run_exit C C' Run Q U PhiLink <=>
    !(g:'g) h k fn fn' s t bb bb' phi phi' r r'.
    Run g fn fn' s t /\ PhiLink g h fn fn' s t bb bb' phi phi' /\
    finite_block C bb
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) r /\
    finite_block C' bb'
      (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) r' /\
    Q h k r r' /\ (!u. r <> OK u) ==>
    U g k r r'
End

(* finite_step_strongind constructor ledger:
   base: indexed_base, Q shape.
   invoke_return: phase_push, callee U shape, scoped_phase_pop.
   invoke_exit: phase_push, callee U shape, scoped_phase_call_exit.
   block_term: indexed_lookup, Q shape/halted/halt.
   block_next: indexed_lookup, Q ok_exit/increment/admin_entry/splice.
   block_exit: indexed_lookup, Q shape.
   run_next: scoped_phase_phi, block Q shape/halted, linked block_return,
             recursive U, scoped_phase_run_next.
   run_halt: scoped_phase_phi, block Q shape/halted, scoped_phase_run_halt.
   run_exit: scoped_phase_phi, block Q shape, scoped_phase_run_exit.
   All target finite constructors are built by the driver; none of these
   run certificates postulates a target recursive finite_run derivation. *)
Definition scoped_phase_contract_def:
  scoped_phase_contract C C' A R Run BlockPair InstPair Q U PushRel Admin PhiLink <=>
    indexed_outcome_shape Q /\ indexed_outcome_shape U /\ indexed_ok_exit A R Q /\
    indexed_base A R InstPair Q /\
    phase_push C C' A R Run InstPair PushRel /\
    scoped_phase_pop A R Q U PushRel /\ scoped_phase_call_exit A R Q U PushRel /\
    indexed_lookup A R BlockPair InstPair /\
    indexed_admin_entry A R Admin /\ indexed_admin_refl Admin /\
    indexed_splice Q Admin /\ indexed_halted Q /\ indexed_halt Q /\
    indexed_increment A R BlockPair InstPair Q Admin /\
    scoped_phase_phi Run A R BlockPair PhiLink /\
    scoped_phase_block_return C C' Run Q PhiLink /\
    scoped_phase_run_next C C' Run Q U PhiLink /\
    scoped_phase_run_halt C C' Run Q U PhiLink /\
    scoped_phase_run_exit C C' Run Q U PhiLink
End

Definition scoped_phase_simulates_def:
  scoped_phase_simulates C C' A R Run BlockPair InstPair Q U <=>
    (!i s r (g:'g) j t.
       finite_step C i s r /\ indexed_entry A R g s t /\ InstPair g i j ==>
       ?(h:'g) r'. finite_step C' j t r' /\ Q g h r r') /\
    (!bb s r g bb' t.
       finite_block C bb s r /\ indexed_entry A R g s t /\ BlockPair bb bb' ==>
       ?(h:'g) r'. finite_block C' bb' t r' /\ Q g h r r') /\
    (!fn s r g fn' t.
       finite_run C fn s r /\ Run g fn fn' s t ==>
       ?(h:'g) r'. finite_run C' fn' t r' /\ U g h r r')
End

Theorem scoped_phase_pop_elim:
  scoped_phase_pop A R Q U PushRel /\ indexed_entry A R g s t /\
  PushRel g i j s t fn fn' cs ct c /\
  U c d (IntRet ret post) (IntRet ret' post') /\
  bind_outputs i.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s post)) = SOME out ==>
  ?(h:'g) out'. bind_outputs j.inst_outputs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state t post')) = SOME out' /\
  Q g h (OK out) (OK out')
Proof
  simp[scoped_phase_pop_def] >> metis_tac[]
QED

Theorem scoped_phase_call_exit_elim:
  scoped_phase_call_exit A R Q U PushRel /\ indexed_entry A R g s t /\
  PushRel g i j s t fn fn' cs ct c /\ U c d r r' /\
  ((?p. r = Halt p) \/ (?a p. r = Abort a p)) ==>
  ?(h:'g). Q g h r r'
Proof
  simp[scoped_phase_call_exit_def] >> metis_tac[]
QED

(* Projection probes: block output has entry restoration, while run output
   has only shape. No indexed_ok_exit U or universal PHI transport is required. *)
Theorem scoped_phase_contract_outputs:
  scoped_phase_contract C C' A R Run BlockPair InstPair Q U PushRel Admin PhiLink ==>
  indexed_outcome_shape Q /\ indexed_outcome_shape U /\ indexed_ok_exit A R Q
Proof
  simp[scoped_phase_contract_def]
QED

Theorem scoped_phase_phi_witness:
  scoped_phase_phi Run A R BlockPair PhiLink /\ Run g fn fn' s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK phi ==>
  ?(h:'g) bb' phi'.
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  eval_phis t bb'.bb_instructions = OK phi' /\ BlockPair bb bb' /\
  indexed_entry A R h
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) /\
  PhiLink g h fn fn' s t bb bb' phi phi'
Proof
  simp[scoped_phase_phi_def] >> metis_tac[]
QED

val _ = export_theory();
