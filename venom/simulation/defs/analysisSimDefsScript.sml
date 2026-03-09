(*
 * Analysis-Driven Simulation — Definitions
 *
 * Bridge between dataflow analysis results and the simulation framework.
 * Extends inst_simulates/block_simulates with per-instruction lattice values.
 *
 * TOP-LEVEL:
 *   analysis_inst_simulates      — per-instruction sim given sound lattice value
 *   analysis_block_transform     — transform block using per-instruction analysis
 *   analysis_function_transform  — transform function using analysis result
 *   analysis_block_transform_widen  — widen variant of block transform
 *   analysis_function_transform_widen — widen variant of function transform
 *
 * Helper:
 *   transfer_sound       — intra-block: transfer tracks concrete execution
 *   edge_transfer_sound  — inter-block: edge transfer sound for states on that edge
 *)

Theory analysisSimDefs
Ancestors
  dfAnalyzeDefs dfAnalyzeWidenDefs passSimulationDefs indexedLists

(* Per-instruction simulation parameterized by lattice soundness.
   f transforms an instruction given the lattice value at that point.
   sound connects abstract lattice values to concrete states.
   INVOKE instructions are preserved (transforms must not alter them).
   When sound = λv s. T, this reduces to ∀v. inst_simulates R_ok R_term (f v). *)
Definition analysis_inst_simulates_def:
  analysis_inst_simulates R_ok R_term
    (sound : 'a -> venom_state -> bool)
    (f : 'a -> instruction -> instruction) <=>
    (!v inst s.
       sound v s ==>
       lift_result R_ok R_term
         (step_inst_base inst s) (step_inst_base (f v inst) s)) /\
    (!v inst.
       is_terminator inst.inst_opcode =
       is_terminator (f v inst).inst_opcode) /\
    (!v inst. inst.inst_opcode = INVOKE ==> f v inst = inst)
End

(* Analysis soundness: abstract lattice values describe reachable concrete
   states. transfer_sound connects the abstract transfer to concrete
   execution: if the lattice value is sound before an instruction, the
   transferred value is sound after. *)
Definition transfer_sound_def:
  transfer_sound (sound : 'a -> venom_state -> bool)
                 (transfer : 'ctx -> instruction -> 'a -> 'a) ctx <=>
    !fuel run_ctx v inst s s'.
      sound v s /\ step_inst fuel run_ctx inst s = OK s' ==>
      sound (transfer ctx inst v) s'
End

(* Edge transfer soundness: edge_transfer preserves soundness for states
   that actually flow along edge (src → dst).
   vs_prev_bb = SOME src identifies the edge taken. This is set by
   goto_block when transitioning between basic blocks.
   For analyses without branch refinement (liveness PHI, identity),
   this holds universally. For range analysis branch narrowing,
   this restricts to states on the correct branch. *)
Definition edge_transfer_sound_def:
  edge_transfer_sound (sound : 'a -> venom_state -> bool)
                      (edge_transfer : 'ctx -> string -> string -> 'a -> 'a)
                      ctx <=>
    !src dst v s.
      sound v s /\ s.vs_prev_bb = SOME src /\ s.vs_current_bb = dst ==>
      sound (edge_transfer ctx src dst v) s
End

(* Transform a block using per-instruction analysis values.
   At each instruction index, query df_at for the lattice value and apply f. *)
Definition analysis_block_transform_def:
  analysis_block_transform (bottom : 'a) (result : 'a df_state) f bb =
    bb with bb_instructions :=
      MAPi (λidx inst. f (df_at bottom result bb.bb_label idx) inst)
           bb.bb_instructions
End

(* Transform an entire function using analysis results. *)
Definition analysis_function_transform_def:
  analysis_function_transform bottom result f fn =
    function_map_transform (analysis_block_transform bottom result f) fn
End

(* Widen variant: transform using df_widen_at instead of df_at. *)
Definition analysis_block_transform_widen_def:
  analysis_block_transform_widen (bottom : 'a) (result : 'a df_widen_state)
                                 f bb =
    bb with bb_instructions :=
      MAPi (λidx inst. f (df_widen_at bottom result bb.bb_label idx) inst)
           bb.bb_instructions
End

(* Widen variant: transform function using widening analysis results. *)
Definition analysis_function_transform_widen_def:
  analysis_function_transform_widen bottom result f fn =
    function_map_transform (analysis_block_transform_widen bottom result f) fn
End
