Theory framePhaseCertificates
Ancestors frameIndexedComposition frameIndexedCertificates frameFiniteExecution
          venomExecSemantics venomExecProps stepWriteFootprintForward
          contextCodegenRel

(* A function restart is not a block continuation.  In particular a terminal
   suffix may be entered by block recursion but never by run_blocks. *)
Definition phase_entry_def:
  phase_entry A R X mode s t <=>
    case mode of
      INL g => indexed_entry A R g s t
    | INR c => X c s t
End

Definition phase_run_entry_def:
  phase_run_entry A R FnPair mode fn fn' s t <=>
    ?g. mode = INL g /\ indexed_entry A R g s t /\ FnPair fn fn'
End

Theorem phase_run_entry_projection:
  phase_run_entry A R FnPair mode fn fn' s t ==>
  phase_entry A R X mode s t /\ FnPair fn fn'
Proof
  simp[phase_run_entry_def] >> rpt strip_tac >> simp[phase_entry_def]
QED

Theorem phase_exceptional_entry:
  phase_entry A R X (INR c) s t <=> X c s t
Proof
  simp[phase_entry_def]
QED

Theorem phase_exceptional_not_run:
  ~phase_run_entry A R FnPair (INR c) fn fn' s t
Proof
  simp[phase_run_entry_def]
QED

(* The three run constructors need PHI preparation; the block constructors
   do not.  The continuation prefix clause is the same as indexed_phi_prefix,
   but its antecedent is deliberately the stronger Run relation. *)
Definition phase_phi_prefix_def:
  phase_phi_prefix Run A R BlockPair Q <=>
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
    (!d r r'. Q h d r r' ==> Q g d r r')
End

(* The two invoke constructors need run entry for the callee.  The other
   seven constructors do not perform a push. *)
Definition phase_push_def:
  phase_push C C' A R Run InstPair PushRel <=>
    !(g:'g) i j s t name ops fn args cs.
    indexed_entry A R g s t /\ InstPair g i j /\
    i.inst_opcode = INVOKE /\ decode_invoke i = SOME (name,ops) /\
    lookup_function name C.ctx_functions = SOME fn /\
    eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs ==>
    ?name' ops' fn' args' ct (c:'g).
    j.inst_opcode = INVOKE /\ decode_invoke j = SOME (name',ops') /\
    lookup_function name' C'.ctx_functions = SOME fn' /\
    eval_operands ops' t = SOME args' /\ setup_callee fn' args' t = SOME ct /\
    PushRel g i j s t fn fn' cs ct c /\ Run c fn fn' cs ct
End

(* Only run_next uses this boundary.  indexed_ok_exit still applies to
   intermediate instructions, but must NOT imply Run.  The two completed
   block derivations below distinguish these obligations. *)
Definition phase_block_return_def:
  phase_block_return C C' Run BlockPair Q <=>
    !(g:'g) (h:'g) (k:'g) fn fn' s t bb bb' phi phi' u v.
    Run g fn fn' s t /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    eval_phis s bb.bb_instructions = OK phi /\
    eval_phis t bb'.bb_instructions = OK phi' /\ BlockPair bb bb' /\
    finite_block C bb
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) (OK u) /\
    finite_block C' bb'
      (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) (OK v) /\
    Q h k (OK u) (OK v) /\ ~u.vs_halted ==>
    Run k fn fn' u v
End

(* Phase-typed induction target.  This is a specification, not an assumed
   theorem: the generic driver must derive it from certificates. *)
Definition phase_simulates_def:
  phase_simulates C C' A R Run BlockPair InstPair Q <=>
    (!i s r (g:'g) j t.
       finite_step C i s r /\ indexed_entry A R g s t /\ InstPair g i j ==>
       ?(h:'g) r'. finite_step C' j t r' /\ Q g h r r') /\
    (!bb s r g bb' t.
       finite_block C bb s r /\ indexed_entry A R g s t /\ BlockPair bb bb' ==>
       ?(h:'g) r'. finite_block C' bb' t r' /\ Q g h r r') /\
    (!fn s r g fn' t.
       finite_run C fn s r /\ Run g fn fn' s t ==>
       ?(h:'g) r'. finite_run C' fn' t r' /\ Q g h r r')
End

(* These are boundary probes, not a simulation theorem.  The mutual lifting
   statement will use indexed_entry for finite_step and finite_block, and Run
   for finite_run.  Base uses indexed_base; invoke uses phase_push and the
   existing pop/call_exit; block term/next/exit use the existing indexed
   lookup, halt, increment, ok_exit and splice; run next/halt/exit use
   phase_phi_prefix, with phase_block_return needed only for run_next. *)
Theorem phase_phi_prefix_from_uniform:
  indexed_phi_prefix A R FnPair BlockPair Q /\
  (!g fn fn' s t. Run g fn fn' s t ==>
     indexed_entry A R g s t /\ FnPair fn fn') ==>
  phase_phi_prefix Run A R BlockPair Q
Proof
  simp[phase_phi_prefix_def, indexed_phi_prefix_def] >> metis_tac[]
QED

Theorem phase_push_forgets_run:
  phase_push C C' A R Run InstPair PushRel /\
  (!g fn fn' s t. Run g fn fn' s t ==>
    indexed_entry A R g s t /\ FnPair g fn fn') ==>
  indexed_push C C' A R FnPair InstPair PushRel
Proof
  simp[phase_push_def, indexed_push_def] >> metis_tac[]
QED

(* A PHI-free prefix does not guard run entry.  This test holds at EVERY
   cursor, including the cursor after an exempt copy. *)
Theorem phase_nonphi_exceptional_probe:
  i.inst_opcode <> PHI /\ X c s t ==>
  eval_phis s (i::rest) = OK s /\
  phase_entry A R X (INR c) s t /\
  ~phase_run_entry A R FnPair (INR c) fn fn' s t
Proof
  simp[eval_phis_def, phase_entry_def, phase_run_entry_def]
QED

(* A completed OK block resets its cursor to zero.  An exceptional OK
   retains the positive preincrement corridor cursor; thus completed-block
   restoration follows without memory agreement or a run-entry requirement
   on intermediate OKs.  REVERT will produce Abort rather than such an OK. *)
Theorem phase_block_return_by_positive_cursor:
  indexed_ok_exit (\g s. T) (phase_entry A R X) Q /\
  (!c u v. X c u v ==> 0 < u.vs_inst_idx) ==>
  phase_block_return C C' (phase_run_entry A R FnPair) BlockPair Q
Proof
  simp[phase_block_return_def] >> rpt strip_tac >>
  `u.vs_inst_idx = 0` by
    (qpat_x_assum `finite_block C bb _ (OK u)` mp_tac >>
     simp[finite_block_iff] >> metis_tac[exec_block_OK_inst_idx_0]) >>
  `phase_entry A R X k u v` by
    (fs[indexed_ok_exit_def, indexed_entry_def] >> metis_tac[]) >>
  Cases_on `k` >>
  gvs[phase_entry_def, phase_run_entry_def] >>
  first_x_assum drule >> simp[]
QED

(* Begins is a source-only ghost recording the block entry of the segment
   represented by h.  It must be established at PHI preparation and retained
   by splice; no target execution is hidden in this boundary. *)
Definition phase_terminal_origins_def:
  phase_terminal_origins C Begins Q <=>
    !h c bb p u v.
    Begins h bb p /\ Q h (INR c) (OK u) (OK v) ==>
    ~finite_block C bb p (OK u)
End

Theorem phase_terminal_origins_from_revert_forward:
  (!h c bb p u v. Begins h bb p /\ Q h (INR c) (OK u) (OK v) ==>
    revert_forward_at bb p.vs_inst_idx) ==>
  phase_terminal_origins C Begins Q
Proof
  simp[phase_terminal_origins_def] >> rpt strip_tac >>
  `revert_forward_at bb p.vs_inst_idx` by metis_tac[] >>
  gvs[finite_block_iff] >>
  drule revert_forward_at_no_normal >> metis_tac[]
QED

Theorem phase_completed_block_restores_run:
  indexed_ok_exit (\g s. T) (phase_entry A R X) Q /\
  phase_terminal_origins C Begins Q /\ Begins h bb p /\
  finite_block C bb p (OK u) /\ Q h k (OK u) (OK v) /\ FnPair fn fn' ==>
  phase_run_entry A R FnPair k fn fn' u v
Proof
  rpt strip_tac >>
  `phase_entry A R X k u v` by
    (fs[indexed_ok_exit_def, indexed_entry_def] >> metis_tac[]) >>
  Cases_on `k`
  >- gvs[phase_entry_def, phase_run_entry_def] >>
  fs[phase_terminal_origins_def] >> metis_tac[]
QED

val _ = export_theory();
