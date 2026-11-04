Theory concretizeAnalysisFutureDemandProbe
Ancestors
  frameOriginHistory frameAllocationSizes ptrDisciplineEmptyTaint
  contextCodegenRel codegenRel venomExecSemantics ptrDiscipline venomState
  words finite_map list pred_set

(* Boundary diagnostics, not a whole-run demand theorem.
   A future demand at an observation must include that observation's reads
   BEFORE subtracting its successful writes.  A suitable backward edge is
       reads(inst,s) UNION (demand_after DIFF actual_writes(inst,s,post)).
   It must not subtract writes from reads at the same observation (MCOPY).

   Activation identity cannot be the current function name or stack depth:
   sequential invocations may reuse both.  The existing joint history gives
   a prefix witness (hs,h) at each reached observation; the prefix at entry,
   retained while the activation is suspended, is a candidate identity.
   Local ordinary edges use origin_edge and actual successful step_writes.
   Initial/callee observations contribute reads just like ordinary ones.
   A return must preserve demands on saved caller sites across the entire
   callee history, not merely the OriginResume edge.  The current logs do
   not retain that callee history after return; see the last probe below.
*)
Definition demand_mcopy_def:
  demand_mcopy = <| inst_id := 10; inst_opcode := MCOPY;
    inst_operands := [Lit 64w; Lit 64w; Lit 32w]; inst_outputs := [] |>
End

Theorem demand_mcopy_read_before_write:
  source_memory_read_ranges demand_mcopy s = [(64,32)] /\
  step_writes demand_mcopy s post = [(64,32)]
Proof
  simp[demand_mcopy_def, source_memory_read_ranges_def,
       step_writes_def, source_memory_write_ranges_def, eval_operand_def,
       sized_source_write_range_def, wordsTheory.w2n_n2w,
       wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem demand_mcopy_overwritten_read:
  64 IN range_bytes (source_memory_read_ranges demand_mcopy s) /\
  64 IN range_bytes (step_writes demand_mcopy s post)
Proof
  simp[demand_mcopy_read_before_write, range_bytes_def]
QED

(* A cache hit is NOT a fresh-byte event.  The stored size, rather than
   the allocation operand evaluated on this revisit, is authoritative. *)
Theorem demand_cached_alloca_no_fresh:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (baddr,sz) /\
  exec_alloca inst s n = OK post ==>
  new_site_bytes s post = {}
Proof
  simp[exec_alloca_def] >> rpt strip_tac >> gvs[] >>
  irule new_site_bytes_unchanged >> simp[update_var_def]
QED

(* Incoming pointer and local allocation accesses are separate obligations.
   setup_callee clears the local cache, but not shared memory. *)
Theorem demand_call_cache_boundary:
  setup_callee fn [n2w caller_base] s = SOME cs ==>
  cs.vs_params = [n2w caller_base] /\ cs.vs_allocas = FEMPTY /\
  cs.vs_memory = s.vs_memory /\ cs.vs_alloca_next = s.vs_alloca_next
Proof
  simp[setup_callee_def] >> strip_tac >> gvs[]
QED

Definition demand_load_def:
  demand_load v = <| inst_id := 11; inst_opcode := MLOAD;
    inst_operands := [Var v]; inst_outputs := ["loaded"] |>
End

Theorem demand_incoming_and_local_reads:
  caller_base < dimword (:256) /\ local_base < dimword (:256) ==>
  source_memory_read_ranges (demand_load "incoming")
    (update_var "incoming" (n2w caller_base)
      (update_var "local" (n2w local_base) cs)) = [(caller_base,32)] /\
  source_memory_read_ranges (demand_load "local")
    (update_var "incoming" (n2w caller_base)
      (update_var "local" (n2w local_base) cs)) = [(local_base,32)]
Proof
  simp[demand_load_def, source_memory_read_ranges_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* The resume event contains only the final callee instruction/states.
   It cannot expose an earlier incoming-pointer MLOAD.  This equation is
   an erasure diagnostic, not a counterexample to either stage theorem. *)
Theorem demand_resume_observations:
  origin_observations
    (caller_h ++ [OriginResume fuel callee rinst rs ret send post;
      OriginObserve snapshot]) =
  origin_observations caller_h ++ origin_observations [OriginObserve snapshot]
Proof
  simp[origin_observations_def]
QED

(* Proposed finite witness interface (not claimed proved here):

   demand(entry_prefix, site, byte, current_prefix) has a finite extension
   of joint_origin_history ending at an observation that reads byte, with
   no actual write of byte strictly before that observation.  Prefixes,
   including saved histories, identify activations; site is the cached
   (aid,base,size) of that activation, not just aid.  Existential intermediate
   prefixes retain nested callee observations even though the resumed local
   log erases them.  A read at current_prefix is the zero-edge witness.
   An ordinary edge is origin_edge plus byte NOTIN step_writes.  A call
   branches into a nested callee witness or a witness after return; the
   latter must protect byte throughout the callee, not just at its RET.
   Fresh ALLOCA creates a new site witness; cached ALLOCA is an ordinary
   nonwrite edge, as demand_cached_alloca_no_fresh requires.

   Missing bridges to the production analysis:
   1. Read endpoint: successful non-revert access_ok + byte in a cached site
      + source read range must yield allocation identity in production
      find_base_allocas_opt.  Incoming origins require the saved caller's
      site, not membership in the callee's empty local cache.
   2. Ordinary edge: the hypotheses of
      concretize_protected_cached_byte_no_kill (especially singleton
      writer allocation_exclusive, production sizes, successful execution,
      access_ok and non-revert) must be obtained, not assumed silently.
      Combine non-kill with production LiveAt predecessor closure.  A
      semantic CFG/control-flow path must be supplied to the static Used
      propagation interface; that static theorem alone says nothing about
      reads, activation prefixes, or byte protection.
   3. Callee-local identity: a reached callee ALLOCA must belong to
      static_alloca_items; successful layout completion gives a position;
      apply_context_concretize_layout records that identity.  Inclusion
      must survive unique_mems_used, then imported_mems_used along the
      actual decoded INVOKE.  Existing source_owns is the reverse direction.
   4. Incoming identity: PARAM/op_prov transfers the caller origin, but it
      is not an entry in the callee's local summary merely for being an
      incoming argument.  The caller's INVOKE operand use must retain this
      allocation in LiveAt/Used, including nested incoming uses.
   5. Return: merge_callee_state restores the saved cache, while keeping
      shared writes.  A nested-prefix extension/projection theorem must
      connect the protected caller site before/after the call and expose
      callee reads/writes. origin_edge's Resume case and origin_log alone
      cannot supply it (demand_resume_observations).

   No new convergence premise, dominance premise, or claim of whole-run
   coverage is made by these diagnostics.  In particular, these probes
   neither prove nor refute either frozen stage conclusion.
*)
