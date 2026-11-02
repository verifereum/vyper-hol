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
 *   retpc_shape_ok      — RET jumps through a return-PC variable
 *   closure_spill_byte  — spill byte of a function reachable from name
 *   fn_frame_inv        — the running frame invariant
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

(* The generated code for RET jumps to its last operand, so the function
   theorem can land at the caller's return pc only if that operand is a
   return-PC variable; and a PHI that merges a return-PC variable with an
   ordinary one would read as ra on the ordinary path too.  opaque_use_ok
   restricts where return-PC variables may be used but requires neither. *)
Definition retpc_shape_ok_def:
  retpc_shape_ok fn <=>
    (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = RET ==>
       ?front x. inst.inst_operands = front ++ [Var x] /\ retpc_var fn x) /\
    (!inst x y. MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
       MEM (Var x) inst.inst_operands /\ MEM (Var y) inst.inst_operands /\
       retpc_var fn x ==> retpc_var fn y)
End

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
