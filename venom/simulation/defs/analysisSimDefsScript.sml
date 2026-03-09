(*
 * Analysis-Driven Simulation — Definitions
 *
 * Bridge between dataflow analysis results and the simulation framework.
 * Extends inst_simulates/block_simulates with per-instruction lattice values.
 *
 * Two transform signatures:
 *   1:1  f : 'a → inst → inst         (replace)
 *   1:N  f : 'a → inst → inst list    (remove/replace/expand)
 *
 * TOP-LEVEL (1:1):
 *   analysis_inst_simulates      — per-instruction sim (1:1)
 *   analysis_block_transform     — block transform using MAPi
 *   analysis_function_transform  — function transform
 *   analysis_block_transform_widen  — widen variant
 *   analysis_function_transform_widen — widen variant
 *
 * TOP-LEVEL (1:N):
 *   run_insts                         — sequential step_inst over a list
 *   analysis_inst_simulates_1n        — per-instruction sim (1:N)
 *   analysis_block_transform_1n       — block transform using FLAT ∘ MAPi
 *   analysis_function_transform_1n    — function transform
 *   analysis_block_transform_1n_widen — widen variant
 *   analysis_function_transform_1n_widen — widen variant
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
   Uses step_inst (not step_inst_base) for consistency with inst_simulates.
   When sound = λv s. T, this reduces to ∀v. inst_simulates R_ok R_term (f v). *)
Definition analysis_inst_simulates_def:
  analysis_inst_simulates R_ok R_term
    (sound : 'a -> venom_state -> bool)
    (f : 'a -> instruction -> instruction) <=>
    (!v fuel ctx inst s.
       sound v s ==>
       lift_result R_ok R_term
         (step_inst fuel ctx inst s) (step_inst fuel ctx (f v inst) s)) /\
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

(* ===== 1:N Transform Framework ===== *)

(* Execute a list of instructions sequentially via step_inst.
   Does not handle INVOKE dispatch or inst_idx tracking — those are
   managed by run_block. Used only in the simulation predicate to
   state what the replacement instructions should compute. *)
Definition run_insts_def:
  run_insts fuel ctx [] s = OK s /\
  run_insts fuel ctx (inst :: rest) s =
    case step_inst fuel ctx inst s of
      OK s' => run_insts fuel ctx rest s'
    | other => other
End

(* Per-instruction simulation for 1:N transforms.
   f maps each instruction (given a lattice value) to a replacement list.

   Structural constraints ensure the transformed block is well-formed
   for run_block:
   - Terminators and INVOKE pass through unchanged (run_block handles
     these specially).
   - Expansion of other instructions produces only non-terminator
     non-INVOKE instructions (so run_block processes them via step_inst).

   The simulation clause relates one original step_inst to the sequential
   execution of the replacement list via run_insts. *)
Definition analysis_inst_simulates_1n_def:
  analysis_inst_simulates_1n R_ok R_term
    (sound : 'a -> venom_state -> bool)
    (f : 'a -> instruction -> instruction list) <=>
    (* Simulation: original step relates to sequential replacement *)
    (!fuel ctx v inst s.
       sound v s ==>
       lift_result R_ok R_term
         (step_inst fuel ctx inst s)
         (run_insts fuel ctx (f v inst) s)) /\
    (* Terminators preserved *)
    (!v inst. is_terminator inst.inst_opcode ==> f v inst = [inst]) /\
    (* INVOKE preserved *)
    (!v inst. inst.inst_opcode = INVOKE ==> f v inst = [inst]) /\
    (* Safe expansion: non-preserved produce only non-preserved *)
    (!v inst.
       ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
       EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
             (f v inst))
End

(* Transform a block using 1:N per-instruction analysis values.
   At each instruction index, query df_at, apply f, then FLAT. *)
Definition analysis_block_transform_1n_def:
  analysis_block_transform_1n (bottom : 'a) (result : 'a df_state) f bb =
    bb with bb_instructions :=
      FLAT (MAPi (\idx inst. f (df_at bottom result bb.bb_label idx) inst)
                  bb.bb_instructions)
End

(* Transform function using 1:N analysis results. *)
Definition analysis_function_transform_1n_def:
  analysis_function_transform_1n bottom result f fn =
    function_map_transform (analysis_block_transform_1n bottom result f) fn
End

(* 1:N widen variant: transform using df_widen_at. *)
Definition analysis_block_transform_1n_widen_def:
  analysis_block_transform_1n_widen (bottom : 'a) (result : 'a df_widen_state)
                                    f bb =
    bb with bb_instructions :=
      FLAT (MAPi (\idx inst.
              f (df_widen_at bottom result bb.bb_label idx) inst)
                  bb.bb_instructions)
End

(* 1:N widen variant: transform function using widening results. *)
Definition analysis_function_transform_1n_widen_def:
  analysis_function_transform_1n_widen bottom result f fn =
    function_map_transform
      (analysis_block_transform_1n_widen bottom result f) fn
End
