(* Protected-set interfaces for internal-call ghost confinement. *)
Theory bodyPtrIntCallConfinement
Ancestors bodyPtrDefs decoderGhostFramePtr ptrSafeRun ptrDiscipline
  venomExecSemantics finite_map pred_set list

Definition intcall_site_outside_def:
  intcall_site_outside P (b:num,n:num) <=>
    DISJOINT P {i | b <= i /\ i < b + n}
End

Definition intcall_prov_outside_def:
  intcall_prov_outside P PG G <=>
    (!site. MEM (SOME site) PG ==> intcall_site_outside P site) /\
    (!x site. FLOOKUP G x = SOME site ==> intcall_site_outside P site)
End

Definition intcall_mem_frame_def:
  intcall_mem_frame P (tn0:taint) (tn:taint) <=>
    tn.t_mem INTER P SUBSET tn0.t_mem
End

Definition intcall_protected_def:
  intcall_protected cenv (es:evaluation_state) sa (s0:venom_state) =
    {i | (?aid off sz.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                 off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz) \/
    (?n b sz. local_region cenv es.scopes s0 n b sz /\
      b <= i /\ i < b + sz /\
      (!k. dynarray_len_at cenv n k ==> i < b + k \/ b + k + 32 <= i))}
End

Theorem intcall_mem_frame_refl:
  intcall_mem_frame P tn tn
Proof
  simp[intcall_mem_frame_def, INTER_SUBSET]
QED

Theorem intcall_mem_frame_trans:
  intcall_mem_frame P tn0 tn1 /\ intcall_mem_frame P tn1 tn2 ==>
  intcall_mem_frame P tn0 tn2
Proof
  simp[intcall_mem_frame_def] >> SET_TAC[]
QED

Theorem intcall_ghost_kept_frame:
  ghost_kept cenv es sa G0 tn0 s0 G tn <=>
  (!x. not_fresh_at sa x ==>
       FLOOKUP G x = FLOOKUP G0 x /\
       op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  intcall_mem_frame (intcall_protected cenv es sa s0) tn0 tn
Proof
  simp[ghost_kept_def, intcall_mem_frame_def, intcall_protected_def,
       SUBSET_DEF, IN_INTER, GSPECIFICATION] >> metis_tac[]
QED

Theorem intcall_mem_frame_reset:
  intcall_mem_frame P tn0 (tn with t_var := FEMPTY) <=>
  intcall_mem_frame P tn0 tn
Proof
  simp[intcall_mem_frame_def]
QED

Theorem intcall_mem_frame_step:
  new_site_bytes s t SUBSET COMPL P /\
  written_taint tn inst s SUBSET COMPL P ==>
  intcall_mem_frame P tn (step_taint inst s t tn)
Proof
  strip_tac >> drule_all step_taint_memory_bound >>
  simp[intcall_mem_frame_def, SUBSET_DEF, IN_INTER, IN_UNION,
       IN_COMPL] >> metis_tac[]
QED

Theorem intcall_prov_outside_invoke:
  intcall_prov_outside P PG G ==>
  intcall_prov_outside P (MAP (op_prov G) ops) FEMPTY
Proof
  simp[intcall_prov_outside_def, MEM_MAP] >> rpt strip_tac >>
  rename1 `SOME site = op_prov G op` >>
  Cases_on `op` >> gvs[op_prov_def] >> metis_tac[]
QED

(* Consumer/producer audit (current base).
   ghost_kept_def asks only for non-increasing protected t_mem, exactly
   intcall_ghost_kept_frame, not equality. ghost_inv_def additionally asks
   for values in every memory agreeing off t_mem: the taint frame is not
   by itself a value-in-memory proof. The admitted S1 seam's
   intcall_callee_exit_def supplies mem_bytes_at equality below entry's
   frontier outside allocations with id >= sa.cs_next_id; it also supplies
   val_in_memory for the return buffer. Thus concrete memory equality on
   successful IntRet is already an authorized seam fact, not a new run
   theorem to duplicate here. Actual staging must separate its fresh
   sites from the fixed caller protected set and transport the local value
   robustness using that concrete frame and the one-sided ghost frame.

   Run-premise ledger: no DALLOCA is a pointer-judgment premise;
   lowering_context_ok follows compiler validation (needed to exclude
   SETFMP, whose fmp increase would add new_site_bytes below the frontier).
   Whole-site PG/G separation, reusable-allocation exclusion, and P below
   the frontier must be produced by staging. setup_callee resets allocas
   but preserves the frontier. Word-taint boundedness starts from clean
   callee t_var and is maintained opcode-locally. lo=0 is the body ghost
   boundary, so there are no unconstrained fixed-region writes.

   Ordinary store audit: written_taint for MSTORE/ISTORE tests address
   evaluation only, while source_memory_write_ranges also tests the value;
   step_inst = OK supplies the missing value evaluation. MCOPY tests all
   three operands in both definitions. Other opcodes add no written_taint.
   in_revert_forward exempts access_ok's write range clause, but its active
   instruction is RETURNDATACOPY or REVERT: neither adds written_taint.
   This suffices for the all-outcomes ghost frame; unconditional concrete
   memory equality on forwarding paths is neither claimed nor needed.
   Allocation transport must exclude DALLOCA/SETFMP, retain exclusion of
   reused ALLOCA sites, and use that fresh ALLOCA starts at the frontier.
   No missing admitted-seam premise was identified in this interface audit.
*)
