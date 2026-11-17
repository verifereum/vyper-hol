Theory concretizePtrDallocaBoundaryProbes
Ancestors
  ptrDiscipline venomState venomInst finite_map list

(* These are conditional ghost boundaries, not value-transport facts.
   The history induction must separately supply equality of parameter values. *)
Theorem ptr_dalloca_param_prov:
  inst.inst_opcode = PARAM /\ LENGTH PG = LENGTH PGt /\
  (!k site. k < LENGTH PGt /\ EL k PGt = SOME site ==>
     EL k PG = SOME site) /\
  out_prov PGt Gt inst t = SOME site ==>
  out_prov PG G inst s = SOME site
Proof
  strip_tac >> gvs[out_prov_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `op::ops` >> Cases_on `ops` >> gvs[] >>
  Cases_on `op` >> gvs[] >> metis_tac[]
QED

Theorem ptr_dalloca_phi_prov:
  prev = prevt /\
  (!lbl. prev = SOME lbl ==>
     resolve_phi lbl inst.inst_operands = resolve_phi lbl instt.inst_operands) /\
  (!v site. FLOOKUP Gt v = SOME site ==> FLOOKUP G v = SOME site) /\
  phi_prov prevt Gt instt = SOME site ==>
  phi_prov prev G inst = SOME site
Proof
  strip_tac >> Cases_on `prev` >> gvs[phi_prov_def] >>
  rename1 `resolve_phi lbl instt.inst_operands` >>
  Cases_on `resolve_phi lbl instt.inst_operands` >> gvs[] >>
  rename1 `op_prov Gt op = SOME site` >>
  Cases_on `op` >> gvs[op_prov_def]
QED

(* Interface audit for the stronger history invariant (not additional axioms).

   Reachable support:
   concretizePtrParamSupport.ptr_frame_current_static (Script:125) gives
   ptr_static_support P fn G from frame_reachable, EVERY (fn_ptr_ok P),
   and EVERY instruction wf. ptr_static_support_def (Script:11) is exactly
   target-independent support: G v = SOME site implies v IN fn_pv P fn.
   Thus FDOM G SUBSET fn_pv follows directly; it needs no ownership premise.

   Source static classification:
   concretizePtrSourceOwnership.ptr_source_ownership_prov_erases (Script:387)
   takes source ownership, ptr_discipline and instruction wf and gives
   ptr_ledger_erases (dyn_floor C vs) births TG G. PrefixLedger:56-77 says
   TG v = SOME owner implies G v = FLOOKUP births owner; TG v = NONE
   permits only numerical sites whose base is >= dyn_floor. This classifies
   the SOURCE ghost, not the target ghost. To conclude that erased source
   provenance was static, the new induction must additionally establish
   Gt v = NONE /\ G v = SOME site ==> FLOOKUP TG v <> NONE.
   This implication is a missing preservation field, NOT a consequence of
   ptr_ledger_erases alone (which permits dynamic sites with TG v = NONE).

   Scalar agreement:
   concretizePtrObservationInterface.ptr_mixed_scalar_eval (Script:117)
   needs nonopaque operand, equal labels, source provenance NONE AND empty
   source operand taint, besides mixed_vars and ledger erasure. It does
   not give unconditional equality for every v outside fn_pv. mixed_vars
   (OpaqueRetpc:255) gives only masked word agreement for untagged values.
   Therefore C1.2.1's unconditional nonpointer equality hypothesis must be
   discharged on demanded operands (with taint_ok) or strengthened into the
   history invariant; ghost inclusion/support alone do not discharge it.

   Parameter VALUES:
   PairedFields.ptr_paired_params_def (Script:41) provides either PT=[] and
   equal vs_params, or ptr_args_transport with empty masks. ValueTransport:5
   gives identity for tag NONE and relocation for SOME owner. PT is an
   ownership list, NOT the runtime a.po_params. SourceOwnership erasure
   relates PT to runtime source parameter ghosts; target runtime ghosts
   still require the new cross-run relation. PARAM incoming contract:
   equal runtime parameter-ghost lengths and pointwise surviving-site
   equality (the theorem above), PLUS equal EL k vs_params whenever the
   target runtime parameter ghost at k is SOME. Outgoing contract: same
   site and same produced value for that PARAM; taint inclusion separately.
   PHI incoming contract: equal prev, same resolved operand, ghost inclusion
   and equal values for each surviving target provenance. Outgoing: same
   selected site (proved above), and same selected value using that equality.

   Calls / saved caller restoration:
   PairedFields.ptr_paired_call_def and ptr_paired_frame_def (Script:50-65)
   retain actual pre-call observations; SourceOwnership.ptr_saved_erases_def
   (Script:191) relates saved ownership to SOURCE caller ghosts only.
   ReturnProduction.ptr_paired_ret_restored_vars (Script:196) restores mixed
   content; ReturnPrefix.ptr_paired_ret_prefix_immediate (Script:28) restores
   paired chronology. Neither asserts target runtime ghost inclusion.
   New call contract: save ghost_vars, parameter ghost inclusion and the
   conditional parameter value equality above for each paired caller;
   initialize callee ghosts from matched evaluated args. New RET contract:
   restore saved variable ghosts excluding call outputs, retain global
   memory/storage inclusion, discharge output values/taints via scalar RET
   operands (ReturnTransport.ptr_mixed_return_front, Script:21).

   Terminal Halt / ret_taint:
   ptrDiscipline.final_taint_def (Script:726) includes a non-INVOKE Halt
   step from a reachable observation. This is not a ptr_chrono_step OK
   successor. Required separate outgoing contract: a matched SOURCE Halt
   and final_taint witness; inclusion of post-step t_stor/t_trans/t_imm;
   equal call addresses, storage_agree_except source final masks and
   imms_agree_except; equal returndata lengths and byte agreement outside
   source ret_taint; target ret_taint SUBSET source ret_taint. The RETURN
   offsets may differ: ObservationInterface.ptr_terminal_read_range_transport
   (Script:134) gives relocated offsets and equal lengths, not terminal
   bytes or ret_taint inclusion. Those require live relocated memory
   comparison at every returned byte. ptr_taint_content (Script:14) covers
   persistent content only, not returndata. dead_wf then transfers D's
   masks at matched terminal contents, as taint_within_def (Script:933)
   requires. No full terminal simulation has been proved by this probe.
*)
