(*
 * Frame-aware relation between one Venom function frame and the assembly
 * state.
 *
 * venom_asm_rel and context_venom_asm_rel relate a planner state to the
 * whole assembly stack and value every stacked variable from vs_vars.
 * Across internal calls neither holds: the callee's assembly stack sits on
 * top of the caller's, and the return-address variable (the RETPC_PARAM
 * output and its ASSIGN/PHI copies) holds an assembly code offset, while
 * its Venom value is the opaque token vs_return_pc_token.
 *
 * fn_frame_inv is the running invariant of one frame: its own stack above
 * the caller's rest, the plan relations against a view of the Venom state
 * in which return-PC variables read as the assembly return address, the
 * context-wide memory relation, and every spill byte outside the frame's
 * call-graph closure unchanged since the frame was entered.
 *
 * TOP-LEVEL:
 *   frame_view          — Venom state with return-PC variables read as ra
 *   closure_spill_byte  — spill byte of a function reachable from name
 *   fn_frame_inv        — the running frame invariant
 *   fn_has_retpc, shared_state_rel, fn_entry_state_rel,
 *   fn_return_state_rel — function boundary relations, used by
 *                         venomToAsmProps's function simulation
 *)

Theory frameRel
Ancestors
  codegenRel contextCodegenRel unitShapeDefs fcgDefs venomState finite_map

(* Every defined return-PC variable reads as the return address ra.  Only
   vs_vars changes, so the memory and shared-state clauses of the plan
   relations are unaffected. *)
Definition frame_view_def:
  frame_view fn ra vs =
    vs with vs_vars :=
      FMAP_MAP2 (\(x,v). if retpc_var fn x then ra else v) vs.vs_vars
End

Theorem frame_view_vars_lookup:
  !fn ra vs x.
    FLOOKUP (frame_view fn ra vs).vs_vars x =
      OPTION_MAP (\v. if retpc_var fn x then ra else v) (FLOOKUP vs.vs_vars x)
Proof
  simp[frame_view_def, FLOOKUP_FMAP_MAP2]
QED

Theorem frame_view_non_retpc:
  !fn ra vs x.
    ~retpc_var fn x ==>
    FLOOKUP (frame_view fn ra vs).vs_vars x = FLOOKUP vs.vs_vars x
Proof
  simp[frame_view_vars_lookup] >> rpt strip_tac >>
  Cases_on `FLOOKUP vs.vs_vars x` >> simp[]
QED

(* A spill byte of some function reachable from name in the call graph,
   name itself included (fcg_path is reflexive). *)
Definition closure_spill_byte_def:
  closure_spill_byte ctx cp name b <=>
    ?r. MEM r cp.cp_regions /\ fcg_path ctx name r.sr_fn_name /\
        r.sr_spill_base <= b /\ b < r.sr_spill_end
End

(* The running invariant of fn's frame.
     ra:   the return address the caller's INVOKE pushed (unconstrained
           when fn has no RETPC_PARAM, since no variable then reads it);
     rest: the caller's assembly stack below the frame, never touched;
     mem0: the assembly memory when the frame was entered.
   The planner state's spill interval lies inside the frame's own context
   region; each step re-establishes this for its output state from the
   planner's allocator monotonicity along the function's plan. *)
Definition fn_frame_inv_def:
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as <=>
    ~vs.vs_halted /\
    n2w cp.cp_initial_fmp = vs.vs_initial_fmp /\
    (?top. as.as_stack = top ++ rest /\
           context_venom_asm_rel cp lo ps (frame_view fn ra vs)
             (as with as_stack := top)) /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
         read_byte b as.as_memory = read_byte b mem0) /\
    (?r. MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
         r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
         ps.ps_alloc.sa_next_offset <= r.sr_spill_end)
End

Theorem fn_frame_inv_gas_readings:
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast ==>
  ast.as_gas_readings = vs.vs_gas_readings
Proof
  rw[fn_frame_inv_def] >>
  fs[context_venom_asm_rel_def, frame_view_def]
QED

(* ===== Function boundary (PLAN 5.9) ===== *)

Definition fn_has_retpc_def:
  fn_has_retpc fn <=>
    EXISTS (\inst. inst.inst_opcode = RETPC_PARAM)
      (get_params (HD fn.fn_blocks).bb_instructions)
End

(* Leftover outcomes and GAS readings are a running/function-return contract
   ONLY.  terminal_rel still observes requests but not leftovers. *)
Definition shared_state_rel_def:
  shared_state_rel vs as <=>
    venom_asm_terminal_rel vs as /\ as.as_outcomes = vs.vs_outcomes /\
    as.as_gas_readings = vs.vs_gas_readings /\
    as.as_call_ctx = vs.vs_call_ctx /\ as.as_tx_ctx = vs.vs_tx_ctx /\
    as.as_block_ctx = vs.vs_block_ctx /\ as.as_code = vs.vs_code /\
    as.as_prev_hashes = vs.vs_prev_hashes
End

(* Fresh source variables need no stack-value relation at callee entry.
   ra is an opaque assembly address, not vs_return_pc_token; rest is caller-owned. *)
Definition fn_entry_state_rel_def:
  fn_entry_state_rel cp fn vs as ra rest <=>
    vs.vs_current_bb = (HD fn.fn_blocks).bb_label /\ ~vs.vs_halted /\
    vs.vs_vars = FEMPTY /\
    LENGTH vs.vs_params + (if fn_has_retpc fn then 1 else 0) =
      LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
    as.as_stack =
      (if fn_has_retpc fn then [ra] else []) ++ REVERSE vs.vs_params ++ rest /\
    n2w cp.cp_initial_fmp = vs.vs_initial_fmp /\
    context_memory_rel cp vs.vs_memory as.as_memory /\
    shared_state_rel vs as
End

Definition fn_return_state_rel_def:
  fn_return_state_rel ctx cp fn vs' as as' <=>
    context_memory_rel cp vs'.vs_memory as'.as_memory /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
         read_byte b as'.as_memory = read_byte b as.as_memory) /\
    venom_asm_terminal_rel vs' as' /\ as'.as_outcomes = vs'.vs_outcomes /\
    as'.as_gas_readings = vs'.vs_gas_readings /\
    as'.as_call_ctx = as.as_call_ctx /\ as'.as_tx_ctx = as.as_tx_ctx /\
    as'.as_block_ctx = as.as_block_ctx /\ as'.as_code = as.as_code /\
    as'.as_prev_hashes = as.as_prev_hashes
End
