(* Allocation/frontier probe. No correctness roots are imported. *)
Theory allocationSpillChecks
Ancestors
  contextCodegenRel contextCodegenRelProps spillSim stackPlanGenCompute
  stackPlanTypes list
  venomExecSemantics venomInst venomState
Libs wordsLib

(* The bytewise frame is independent of the number of live spill slots. *)
Theorem mstore_preserves_context_spill_bytes:
  (!r. MEM r cplan.cp_regions ==>
       off + 32 <= r.sr_spill_base \/ r.sr_spill_end <= off) ==>
  context_spill_step_safe cplan s (mstore off v s)
Proof
  rw[context_spill_step_safe_def, context_spill_byte_def] >>
  irule EQ_SYM >> irule read_byte_mstore_outside >>
  first_x_assum drule >> decide_tac
QED

Theorem nonspill_write_preserves_live_spills:
  plan_spill_rel lo vs spilled am /\
  (!op slot. FLOOKUP spilled op = SOME slot ==>
      slot + 32 <= off \/ off + 32 <= slot) ==>
  plan_spill_rel lo vs spilled (mem_write32 off v am)
Proof
  metis_tac[plan_spill_rel_write_disjoint]
QED

Definition frontier_alloc_def:
  frontier_alloc = instruction 0 INITIAL_FMP [] ["p"]
End
Definition frontier_bump_def:
  frontier_bump = instruction 3 BUMP [Var "p"; Lit 32w] ["buf"; "next"]
End
Definition frontier_store_def:
  frontier_store = instruction 1 MSTORE [Var "buf"; Lit 7w] []
End
Definition frontier_stop_def:
  frontier_stop = instruction 2 STOP [] []
End
Definition frontier_fn_def:
  frontier_fn = (mk_raw_function "main"
    [<| bb_label := "entry";
        bb_instructions := [frontier_alloc; frontier_bump; frontier_store; frontier_stop] |>])
    with fn_eom := SOME 64
End
Definition frontier_ctx_def:
  frontier_ctx = mk_venom_context [frontier_fn] (SOME "main")
End

Theorem frontier_plan_probe:
  ?cplan. generate_context_plan frontier_ctx = SOME cplan /\
       cplan.cp_max_static_eom = 64 /\ cplan.cp_initial_fmp = 64 /\
       context_plan_layout_wf cplan
Proof
  EVAL_TAC >> simp[stackModelTheory.stack_find_def] >> EVAL_TAC >>
  simp[listTheory.SET_TO_LIST_THM] >> EVAL_TAC >>
  simp[ordered_spill_regions_def]
QED

Definition frontier_start_def:
  frontier_start = (init_venom_state "entry") with vs_initial_fmp := 64w
End
Definition frontier_allocated_def:
  frontier_allocated =
    (update_var "next" 96w (update_var "buf" 64w
      (update_var "p" 64w frontier_start))) with vs_inst_idx := 2
End
Definition frontier_written_def:
  frontier_written = mstore 64 7w frontier_allocated
End

Theorem frontier_execution_probe:
  step_inst 0 frontier_ctx frontier_bump
    ((update_var "p" 64w frontier_start) with vs_inst_idx := 1) =
      OK (frontier_allocated with vs_inst_idx := 1) /\
  step_inst 0 frontier_ctx frontier_store frontier_allocated =
      OK frontier_written /\
  active_inst frontier_fn frontier_store frontier_allocated /\
  active_inst frontier_fn frontier_stop
    (frontier_written with vs_inst_idx := SUC frontier_allocated.vs_inst_idx) /\
  ~active_inst frontier_fn frontier_stop frontier_written
Proof
  simp[active_inst_def, frontier_fn_def, mk_raw_function_def] >> EVAL_TAC
QED

(* This implication uses the frontier from the generated plan, not a
   postulated global prohibition on source-memory accesses. *)
Theorem initial_fmp_write_frames_spills:
  context_plan_layout_wf cplan /\ cplan.cp_initial_fmp <= off ==>
  context_spill_step_safe cplan s (mstore off v s)
Proof
  rw[context_spill_step_safe_def, context_spill_byte_def] >>
  irule EQ_SYM >> irule read_byte_mstore_outside >>
  fs[context_plan_layout_wf_def, EVERY_MEM] >>
  `r.sr_spill_base < r.sr_spill_end` by decide_tac >>
  `r.sr_spill_end <= cplan.cp_peak_spill_end` by metis_tac[] >>
  decide_tac
QED

(* Candidate generalized Inv (not yet a definition): at the exposed active
   instruction, track a typed allocation provenance map, interval bounds
   below static EOM or above cp_initial_fmp, and non-wrapping dynamic frontier.
   Call boundaries additionally carry caller-live allocation regions and
   return-buffer ownership. This cannot be replaced by shape alone.

   Remaining preservation cases: ordinary scalar/pointer arithmetic;
   byte/word stores, copies and external-call output ranges; BUMP overflow
   checks; block-edge PHI provenance; INVOKE parameter transfer, callee-entry
   PHIs, RET/DRET aggregate-return copies and incremented caller continuation;
   RETURN/REVERT/SHA3/LOG read ranges. The closure index must be postincrement
   for ordinary returns and post-PHI for terminator entries. *)

Theorem generated_frontier_write_probe:
  ?cplan. generate_context_plan frontier_ctx = SOME cplan /\
    context_plan_layout_wf cplan /\
    frontier_start.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
    context_spill_step_safe cplan frontier_allocated frontier_written
Proof
  mp_tac frontier_plan_probe >> strip_tac >>
  qexists_tac `cplan` >> simp[frontier_start_def] >>
  simp[frontier_written_def] >>
  irule initial_fmp_write_frames_spills >> simp[]
QED

(* A real nonempty live slot: the preservation lemma is not merely relying
   on the zero-spill plan in the small BUMP computation above. *)
Theorem nonempty_spill_frame_probe:
  read_byte 64 (mstore 96 v s).vs_memory = read_byte 64 s.vs_memory /\
  read_byte 95 (mstore 96 v s).vs_memory = read_byte 95 s.vs_memory
Proof
  simp[read_byte_mstore_outside]
QED

val _ = List.app (fn (name,th) =>
  if null (List.filter (fn s => s <> "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("oracle dependency in " ^ name))
  (DB.thms "allocationSpillChecks");
