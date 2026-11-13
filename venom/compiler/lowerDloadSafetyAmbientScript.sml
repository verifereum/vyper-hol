(* Opcode-independent ambient projections of synchronization. *)
Theory lowerDloadSafetyAmbient
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadDefs words lowerDloadFrontier
  o1PassContract venomWf venomInst list contextCodegenRel venomExecProps venomInstProps venomExecSemantics venomExecProofs contextRawReachable ptrDiscipline unitMemInv

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

(* C1.11.5.49.1 repaired interface audit.
   Existing venomExecProps.MEM_lookup_block (283-289) is exactly the missing
   uniqueness bridge. With active_inst_def it gives the proposed boundary:
     ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
     active_inst fn inst s ==>
     ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
          s.vs_inst_idx < LENGTH bb.bb_instructions /\
          EL s.vs_inst_idx bb.bb_instructions = inst.
   No new definition is needed for this boundary.

   Corrected semantic interfaces (proposed, not yet proved): write U fn for
   the ALL_DISTINCT expression above only in this comment, not a new predicate.
   Terminal: U fn /\ active_inst fn inst s /\
     step_inst k C inst s = IntRet ret e ==> ld_return_suffix C fn s ret e.
   Entry: U fn /\ enters_block fn cs s ==> ld_return_cont C fn cs s.
   Sequential: U fn /\ active_inst fn inst s /\
     ~is_terminator inst.inst_opcode /\ step_inst k C inst s = OK q /\
     ld_return_suffix C fn (q with vs_inst_idx := SUC s.vs_inst_idx) ret e
       ==> ld_return_suffix C fn s ret e.
   Block: U fn /\ active_inst fn inst s /\
     is_terminator inst.inst_opcode /\ step_inst k C inst s = OK q /\
     ~q.vs_halted /\ enters_block fn q s1 /\
     ld_return_suffix C fn s1 ret e ==> ld_return_suffix C fn s ret e.
   Cont corollaries have the same operational premises, replace the suffix
   premise by ld_return_cont C fn cs s and conclude cont at the successor.
   Sequential also needs a checked nonterminator current-bb preservation
   boundary INCLUDING INVOKE before same-block lookup can be reused.
   Entry must align eval_phis result current-bb with the input block;
   uniqueness alone is not a proof of that alignment. The run_defs/fuel
   composition obligations from the preceding audit remain unproved.

   Membership invariant required for the five-rule induction:
     MEM fn C.ctx_functions /\ EVERY (\f. MEM f.cf_fn C.ctx_functions) stk.
   entry: lookup_function_MEM gives current membership, stack is empty.
   next/block: neither fn nor stk changes, so retain both conjuncts.
   call: lookup_function_MEM gives callee membership; push the old current
         membership for the saved caller; retain the old tail invariant.
   ret: pop current membership from the head of the saved-stack invariant,
        retain tail. Do not attempt to obtain it from callee membership.
   The generic o1_fn_shape_components and o1_ctx_shape_def/EVERY_MEM convert
   this invariant to uniqueness for current and ALL saved callers.

   Saved_calls can retain its original recursive decode/setup/cont fields
   with an added MEM f.cf_fn C.ctx_functions conjunct at each cons; the
   strengthened induction also retains current membership. Return boundary
   needs o1_ctx_shape C, that certificate, current cont, active IntRet step,
   and the exact bind_outputs/merge equation. It returns atomic step OK q,
   saved raw caller, tail certificate, caller membership and successor cont.
   Current uniqueness is derived from current membership; restored caller
   uniqueness from the certificate. Push requires current membership and
   lookup callee; new callee cont uses the corrected entry boundary.

   Final proposed signature:
     o1_ctx_shape C /\ frame_reachable vs0 C stk PG G tn fn inst s
       ==> raw_reachable vs0 C fn inst s.
   Strengthened IH must quantify shape and retain membership, raw fact, and
   existential cs with cont/saved_calls, rather than assume final-only shape.
   Ambient consumer adds o1_ctx_shape C to the earlier proposed signature.
   The frozen theorem already supplies it; ld_sync supplies frame_reachable;
   o1_src_inv supplies the source memory rows. No frozen premise is added.
   REVIEW NEEDED: corrected suffix proofs are still missing from .49.2's
   dependency path after replacing the old .49.1 by this audit. They must be
   authorized and checked before saved-call construction, not skipped.
*)

Theorem ld_active_lookup:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn inst s ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       s.vs_inst_idx < LENGTH bb.bb_instructions /\
       EL s.vs_inst_idx bb.bb_instructions = inst
Proof
  simp[active_inst_def] >> rpt strip_tac >>
  drule_all MEM_lookup_block >> strip_tac >>
  qexists_tac `bb` >> simp[]
QED

Definition ld_return_suffix_def:
  ld_return_suffix C fn s ret e <=>
    ?bb n. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      (exec_block n C bb s = IntRet ret e \/
       ?q m. exec_block n C bb s = OK q /\ ~q.vs_halted /\
             run_blocks m C fn q = IntRet ret e)
End

Definition ld_return_cont_def:
  ld_return_cont C fn cs s <=>
    !ret e. ld_return_suffix C fn s ret e ==>
            ?n. run_blocks n C fn cs = IntRet ret e
End

Theorem ld_return_suffix_terminal:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\ step_inst k C inst s = IntRet ret e ==>
  ld_return_suffix C fn s ret e
Proof
  strip_tac >> drule_all ld_active_lookup >> strip_tac >>
  simp[ld_return_suffix_def] >> qexists_tac `k` >>
  simp[Once exec_block_def, get_instruction_def]
QED

Theorem ld_enters_block_alignment:
  enters_block fn cs s ==>
  ?bb sp. lookup_block cs.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis cs bb.bb_instructions = OK sp /\
    s = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
    s.vs_current_bb = cs.vs_current_bb
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  qexistsl_tac [`bb`, `s_phi`] >> simp[]
QED

Theorem ld_return_cont_entry:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  enters_block fn cs s ==> ld_return_cont C fn cs s
Proof
  strip_tac >> drule ld_enters_block_alignment >> strip_tac >>
  simp[ld_return_cont_def, ld_return_suffix_def] >> rpt strip_tac
  >- (qexists_tac `SUC n` >> simp[Once run_blocks_def]) >>
  `exec_block (n + m) C bb s = OK q` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  `run_blocks (n + m) C fn q = IntRet ret e` by
    (irule (cj 3 fuel_mono) >> simp[] >> qexists_tac `m` >> simp[]) >>
  qexists_tac `SUC (n + m)` >>
  gvs[] >> simp[Once run_blocks_def]
QED

Theorem ld_return_suffix_next:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  step_inst k C inst s = OK q /\
  ld_return_suffix C fn (q with vs_inst_idx := SUC s.vs_inst_idx) ret e ==>
  ld_return_suffix C fn s ret e
Proof
  strip_tac >> drule_all ld_active_lookup >> strip_tac >>
  drule_all step_preserves_control_flow >> strip_tac >>
  qpat_x_assum `ld_return_suffix _ _ _ _ _` mp_tac >>
  simp[ld_return_suffix_def] >> rpt strip_tac
  >- (`step_inst (k + n) C inst s = OK q` by
        (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
      `exec_block (k + n) C bb
         (q with vs_inst_idx := SUC s.vs_inst_idx) = IntRet ret e` by
        (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
      simp[ld_return_suffix_def] >> qexists_tac `k + n` >>
      simp[Once exec_block_def, get_instruction_def]) >>
  `step_inst (k + n) C inst s = OK q` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
  `exec_block (k + n) C bb
     (q with vs_inst_idx := SUC s.vs_inst_idx) = OK q'` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  simp[ld_return_suffix_def] >> qexists_tac `k + n` >>
  simp[Once exec_block_def, get_instruction_def] >>
  qexistsl_tac [`q'`, `m`] >>
  simp[Once exec_block_def, get_instruction_def]
QED

Theorem ld_return_suffix_block:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst k C inst s = OK q /\ ~q.vs_halted /\
  enters_block fn q s1 /\ ld_return_suffix C fn s1 ret e ==>
  ld_return_suffix C fn s ret e
Proof
  strip_tac >> drule_all ld_active_lookup >> strip_tac >>
  `ld_return_cont C fn q s1` by
    (irule ld_return_cont_entry >> simp[]) >>
  `?m. run_blocks m C fn q = IntRet ret e` by
    metis_tac[ld_return_cont_def] >>
  simp[ld_return_suffix_def] >> qexists_tac `k` >>
  simp[Once exec_block_def, get_instruction_def] >>
  qexistsl_tac [`q`, `m`] >>
  simp[Once exec_block_def, get_instruction_def]
QED

Theorem ld_return_cont_next:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  step_inst k C inst s = OK q /\ ld_return_cont C fn cs s ==>
  ld_return_cont C fn cs (q with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  metis_tac[ld_return_cont_def, ld_return_suffix_next]
QED

Theorem ld_return_cont_block:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst k C inst s = OK q /\ ~q.vs_halted /\
  enters_block fn q s1 /\ ld_return_cont C fn cs s ==>
  ld_return_cont C fn cs s1
Proof
  metis_tac[ld_return_cont_def, ld_return_suffix_block]
QED

Definition ld_saved_calls_def:
  (ld_saved_calls vs0 C [] fn cs <=> T) /\
  (ld_saved_calls vs0 C (f::stk) fn cs <=>
    ?caller_cs nm ops args.
      MEM f.cf_fn C.ctx_functions /\
      raw_reachable vs0 C f.cf_fn f.cf_inst f.cf_state /\
      active_inst f.cf_fn f.cf_inst f.cf_state /\
      f.cf_inst.inst_opcode = INVOKE /\
      decode_invoke f.cf_inst = SOME (nm, ops) /\
      lookup_function nm C.ctx_functions = SOME fn /\
      eval_operands ops f.cf_state = SOME args /\
      setup_callee fn args f.cf_state = SOME cs /\
      ld_return_cont C f.cf_fn caller_cs f.cf_state /\
      ld_saved_calls vs0 C stk f.cf_fn caller_cs)
End

Theorem ld_saved_calls_push:
  MEM caller C.ctx_functions /\ raw_reachable vs0 C caller callinst s /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm, ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  ld_return_cont C caller caller_cs s /\
  ld_saved_calls vs0 C stk caller caller_cs ==>
  ld_saved_calls vs0 C
    (<| cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk) callee cs
Proof
  simp[ld_saved_calls_def] >> metis_tac[]
QED

Theorem ld_saved_calls_return:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\
  ld_saved_calls vs0 C (f::stk) fn cs /\ ld_return_cont C fn cs s /\
  active_inst fn rinst s /\ step_inst k C rinst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME q ==>
  ?n caller_cs.
    step_inst n C f.cf_inst f.cf_state = OK q /\
    raw_reachable vs0 C f.cf_fn f.cf_inst f.cf_state /\
    active_inst f.cf_fn f.cf_inst f.cf_state /\
    MEM f.cf_fn C.ctx_functions /\
    ld_saved_calls vs0 C stk f.cf_fn caller_cs /\
    ld_return_cont C f.cf_fn caller_cs
      (q with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[o1_fn_shape_components]) >>
  `ld_return_suffix C fn s ret se` by
    (irule ld_return_suffix_terminal >> metis_tac[]) >>
  `?n. run_blocks n C fn cs = IntRet ret se` by
    metis_tac[ld_return_cont_def] >>
  qpat_x_assum `ld_saved_calls _ _ (_::_) _ _` mp_tac >>
  simp[ld_saved_calls_def] >> strip_tac >>
  `step_inst n C f.cf_inst f.cf_state = OK q` by
    simp[Once step_inst_def] >>
  qexistsl_tac [`n`, `caller_cs`] >> simp[] >>
  irule ld_return_cont_next >> simp[] >> conj_tac
  >- (gvs[o1_ctx_shape_def, EVERY_MEM] >>
      metis_tac[o1_fn_shape_components]) >>
  qexistsl_tac [`f.cf_inst`, `n`] >> simp[is_terminator_def]
QED

Theorem ld_frame_reachable_certificate:
  !vs0 C stk PG G tn fn inst s.
    frame_reachable vs0 C stk PG G tn fn inst s ==>
    o1_ctx_shape C ==>
    MEM fn C.ctx_functions /\ raw_reachable vs0 C fn inst s /\
    ?cs. ld_return_cont C fn cs s /\ ld_saved_calls vs0 C stk fn cs
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >> conj_tac
      >- metis_tac[lookup_function_MEM] >> conj_tac
      >- metis_tac[raw_reachable_entry] >>
      simp[ld_saved_calls_def] >>
      qexists_tac `vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                              vs_inst_idx := 0 |>` >>
      irule ld_return_cont_entry >>
      gvs[o1_ctx_shape_def, EVERY_MEM] >>
      metis_tac[lookup_function_MEM, o1_fn_shape_components])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >> simp[] >> conj_tac
      >- metis_tac[raw_reachable_next] >>
      qexists_tac `cs` >> simp[] >> irule ld_return_cont_next >>
      gvs[o1_ctx_shape_def, EVERY_MEM] >>
      metis_tac[o1_fn_shape_components])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >> simp[] >> conj_tac
      >- metis_tac[raw_reachable_block] >>
      qexists_tac `cs` >> simp[] >> irule ld_return_cont_block >>
      gvs[o1_ctx_shape_def, EVERY_MEM] >>
      metis_tac[o1_fn_shape_components])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >> conj_tac
      >- metis_tac[lookup_function_MEM] >> conj_tac
      >- metis_tac[raw_reachable_callee] >>
      qexists_tac `cs` >> conj_tac
      >- (irule ld_return_cont_entry >>
          gvs[o1_ctx_shape_def, EVERY_MEM] >>
          metis_tac[lookup_function_MEM, o1_fn_shape_components]) >>
      irule ld_saved_calls_push >> metis_tac[])
  >> rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `f.cf_inst.inst_opcode = INVOKE` by
    (gvs[ld_saved_calls_def]) >>
  drule_all ld_saved_calls_return >> strip_tac >> simp[] >> conj_tac
  >- (irule raw_reachable_next >> simp[] >>
      qexistsl_tac [`n`, `f.cf_inst`] >> simp[is_terminator_def]) >>
  metis_tac[]
QED

Theorem ld_frame_raw_reachable:
  o1_ctx_shape C /\ frame_reachable vs0 C stk PG G tn fn inst s ==>
  raw_reachable vs0 C fn inst s
Proof
  metis_tac[ld_frame_reachable_certificate]
QED

Theorem ld_sync_source_mem_inv:
  o1_ctx_shape C /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  mem_inv M C vs0 ==> M C fn inst s
Proof
  strip_tac >> drule ld_sync_source >> strip_tac >>
  drule_all ld_frame_raw_reachable >>
  gvs[mem_inv_raw_reachable]
QED

Theorem ld_sync_ambient_headroom:
  o1_ctx_shape C /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  mem_inv dload_headroom_ok C vs0 ==>
  t.vs_alloca_next < dimword(:256)
Proof
  strip_tac >> drule_all ld_sync_source_mem_inv >> strip_tac >>
  drule_all ld_sync_target_headroom >> simp[]
QED

Theorem ld_sync_frontier_lower_bound:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  lo <= t.vs_alloca_next
Proof
  strip_tac >> drule ld_sync_source >> strip_tac >>
  drule_all ld_frame_raw_reachable >>
  strip_tac >> drule ld_raw_reachable_frontier >> strip_tac >>
  drule ld_sync_frontier >> gvs[ptr_discipline_def]
QED
