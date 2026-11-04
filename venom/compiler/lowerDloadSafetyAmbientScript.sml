(* Opcode-independent ambient projections of synchronization. *)
Theory lowerDloadSafetyAmbient
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadDefs words
  o1PassContract venomWf venomInst list

Theorem ld_sync_labels:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  s.vs_labels = t.vs_labels
Proof
  strip_tac >> drule ld_sync_memory >>
  simp[ld_nonghost_def]
QED

Theorem ld_sync_target_headroom:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  dload_headroom_ok C fn inst s ==>
  t.vs_alloca_next < dimword(:256)
Proof
  strip_tac >> drule ld_sync_frontier >>
  gvs[dload_headroom_ok_def]
QED

Theorem ld_sync_fn_shape:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  o1_ctx_shape C ==> o1_fn_shape C fn
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (qhdtm_x_assum `ld_sync` mp_tac >>
     simp[ld_sync_def, EVERY_MEM] >> strip_tac >>
     `MEM (HD frames) frames` by (Cases_on `frames` >> gvs[]) >>
     metis_tac[]) >>
  gvs[o1_ctx_shape_def, EVERY_MEM]
QED

Theorem o1_fn_shape_components:
  o1_fn_shape C fn ==>
  fn_shape_ok fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)
Proof
  simp[o1_fn_shape_def, wf_function_def, fn_labels_def]
QED

(* C1.11.5.48: source reachability interface audit (not a proved bridge).

   Checked interfaces:
   - ptrDiscipline.frame_reachable_rules, lines 447-500: five rules.
   - contextRawReachable.raw_reachable_rules, lines 26-57: four rules.
   - unitMemInv.mem_inv_raw_reachable, lines 104-117: given raw reachability,
     mem_inv M C vs0 yields M C fn inst s directly.
   - o1PassLift.frame_reach_raw_reachable, lines 653-666, is about the
     DIFFERENT three-rule frame_reach relation; it cannot erase our stack.

   Rule comparison:
   entry: identical executable premises to raw rule 1; ghosts disappear.
   next: raw rule 2 applies; the extra non-INVOKE premise is harmless.
   block: raw rule 3 applies with identical executable premises.
   call: raw rule 4 applies with the same decode, lookup, operands, setup,
         enters_block and active_inst facts. Also save those facts, the exact
         pre-INVOKE caller state and its raw reachability for later return.
   ret: NO direct raw rule. Raw rule 2 needs a successful atomic INVOKE at
        f.cf_state, not merely an IntRet at the current callee instruction.
        A plain raw-reachability IH loses the call path and is insufficient.

   Missing semantic obligation (proposed, not authorized/proved): retain for
   each activation an entry state cs and a backward continuation property:
     for every k, ret, e,
       step_inst k C rinst s = IntRet ret e ==>
       ?n. run_blocks n C fn cs = IntRet ret e.
   This displayed form is only the terminal specialization. Preservation
   needs the stronger arbitrary successful suffix from the current active
   instruction (exec_block at its exact index, followed by run_blocks if a
   terminator transfers control), plus a stack of saved call-entry witnesses.
   Entry composes enters_block/eval_phis with that suffix. Nonterminator next
   prepends step_inst; block prepends its terminator and re-enters the chosen
   block. Nested ret first reconstructs the inner run, then the atomic invoke,
   then prepends that invoke to the suspended caller continuation. Saved cs
   must be the SAME setup_callee result from the saved pre-INVOKE state;
   merging current state into an arbitrary raw-reachable caller is unsound.

   Fuel: venomExecProps.fuel_mono (406-418) aligns successful step_inst,
   exec_block and run_blocks results by taking a common upper bound; run_block
   has run_block_fuel_mono (420-426). run_blocks_step (556-564) and
   run_blocks_two_blocks (567-575) compose full blocks. run_defs (semantics
   1644-1704) supplies IntRet propagation and invocation reconstruction.
   Each crossed block needs SUC fuel; within-block instruction recursion
   retains fuel. Do not demand equal fuel for all observed prefix steps.
   No checked theorem in these inspected interfaces reconstructs a run from
   ptrDiscipline.frame_reachable with its saved stack. This is the next
   semantic proof obligation, not a solved arithmetic/projection leaf.

   Eventual consumer signatures (NOT theorems here):
     o1_ctx_shape C /\ frame_reachable vs0 C stk PG G tn fn inst s
       ==> raw_reachable vs0 C fn inst s
     o1_ctx_shape C /\ ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
     mem_inv M C vs0 ==> M C fn inst s
   Shape is conservatively retained pending proof of suffix reconstruction;
   the exact minimal requirements must be validated, not silently assumed.
   Specialize M=dload_headroom_ok, then use ld_sync_target_headroom.
*)
