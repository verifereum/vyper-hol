(*
 * Analysis-Driven Simulation — Definitions
 *
 * Bridge between dataflow analysis results and the simulation framework.
 * f : 'a → inst → inst list (remove/replace/expand).
 * 1:1 (f : 'a → inst → inst) is a special case via analysis_inst_simulates_from_1.
 *
 * TOP-LEVEL:
 *   run_insts                       — sequential step_inst over a list
 *   analysis_inst_simulates         — per-instruction simulation
 *   analysis_block_transform        — block transform using FLAT ∘ MAPi
 *   analysis_function_transform     — function transform
 *   analysis_block_transform_widen  — widen variant
 *   analysis_function_transform_widen — widen variant
 *   transfer_sound       — intra-block: transfer tracks concrete execution
 *   edge_transfer_sound  — inter-block: edge transfer sound for states on that edge
 *
 * Helper:
 *   analysis_inst_simulates_1       — per-instruction sim (1:1, for corollary)
 *)

Theory analysisSimDefs
Ancestors
  dfAnalyzeDefs dfAnalyzeWidenDefs passSimulationDefs indexedLists

(* 1:1 simulation helper (used by analysis_inst_simulates_from_1 corollary).
   f : 'a → inst → inst maps each instruction to a single replacement.
   Passes satisfying this automatically satisfy analysis_inst_simulates
   via the corollary (\v inst. [g v inst]).
   Terminators may be transformed (e.g. JNZ→JMP) but must remain
   terminators. INVOKE may be transformed but must remain INVOKE. *)
Definition analysis_inst_simulates_1_def:
  analysis_inst_simulates_1 R_ok R_term
    (sound : 'a -> venom_state -> bool)
    (f : 'a -> instruction -> instruction) <=>
    (!v fuel ctx inst s.
       sound v s ==>
       lift_result R_ok R_term
         (step_inst fuel ctx inst s) (step_inst fuel ctx (f v inst) s)) /\
    (!v inst. is_terminator inst.inst_opcode ==>
       is_terminator (f v inst).inst_opcode) /\
    (!v inst. inst.inst_opcode = INVOKE ==>
       (f v inst).inst_opcode = INVOKE) /\
    (!v inst.
       ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
       ~is_terminator (f v inst).inst_opcode /\
       (f v inst).inst_opcode <> INVOKE)
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

(* ===== Transform Framework ===== *)

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

(* Per-instruction simulation: f maps each instruction (given a lattice
   value) to a replacement list. Structural constraints ensure the
   transformed block is well-formed for run_block:
   - Terminators map to a single terminator (may change opcode, e.g. JNZ→JMP)
   - INVOKE maps to a single INVOKE (may change operands)
   - Non-term non-INVOKE expand to only non-term non-INVOKE
   The simulation clause relates one original step_inst to sequential
   execution of the replacement list via run_insts. *)
Definition analysis_inst_simulates_def:
  analysis_inst_simulates R_ok R_term
    (sound : 'a -> venom_state -> bool)
    (f : 'a -> instruction -> instruction list) <=>
    (* Simulation: original step relates to sequential replacement *)
    (!fuel ctx v inst s.
       sound v s ==>
       lift_result R_ok R_term
         (step_inst fuel ctx inst s)
         (run_insts fuel ctx (f v inst) s)) /\
    (* Terminators map to a single terminator *)
    (!v inst. is_terminator inst.inst_opcode ==>
       ?inst'. f v inst = [inst'] /\ is_terminator inst'.inst_opcode) /\
    (* INVOKE preserved as INVOKE *)
    (!v inst. inst.inst_opcode = INVOKE ==>
       ?inst'. f v inst = [inst'] /\ inst'.inst_opcode = INVOKE) /\
    (* Safe expansion: non-preserved produce only non-preserved *)
    (!v inst.
       ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
       EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
             (f v inst))
End

(* Transform a block using per-instruction analysis values.
   At each instruction index, query df_at, apply f, then FLAT. *)
Definition analysis_block_transform_def:
  analysis_block_transform (bottom : 'a) (result : 'a df_state) f bb =
    bb with bb_instructions :=
      FLAT (MAPi (\idx inst. f (df_at bottom result bb.bb_label idx) inst)
                  bb.bb_instructions)
End

(* Transform function using analysis results. *)
Definition analysis_function_transform_def:
  analysis_function_transform bottom result f fn =
    function_map_transform (analysis_block_transform bottom result f) fn
End

(* Widen variant: transform using df_widen_at. *)
Definition analysis_block_transform_widen_def:
  analysis_block_transform_widen (bottom : 'a) (result : 'a df_widen_state)
                                    f bb =
    bb with bb_instructions :=
      FLAT (MAPi (\idx inst.
              f (df_widen_at bottom result bb.bb_label idx) inst)
                  bb.bb_instructions)
End

(* Widen variant: transform function using widening results. *)
Definition analysis_function_transform_widen_def:
  analysis_function_transform_widen bottom result f fn =
    function_map_transform
      (analysis_block_transform_widen bottom result f) fn
End

(* ===== Prepend-aware transform (0:N + 1:N) ===== *)

(* Some passes need to insert instructions at the START of a block
   that have no corresponding original instruction (e.g. PHI insertion
   from set-valued lattice analysis). These are 0:N insertions.

   Semantically, inserting a PHI that defines a fresh variable is a
   no-op: it just adds a binding to vs_vars that no existing instruction
   reads. The simulation proof reduces to a frame property.

   prepend : string → instruction list — maps block label to instructions
   to insert before the block's original instructions.
   f : 'a → instruction → instruction list — per-instruction 1:N transform. *)
Definition analysis_block_transform_prepend_def:
  analysis_block_transform_prepend (bottom : 'a) (result : 'a df_state)
                                   (prepend : string -> instruction list)
                                   f bb =
    bb with bb_instructions :=
      prepend bb.bb_label ++
      FLAT (MAPi (\idx inst. f (df_at bottom result bb.bb_label idx) inst)
                  bb.bb_instructions)
End

Definition analysis_function_transform_prepend_def:
  analysis_function_transform_prepend bottom result prepend f fn =
    function_map_transform
      (analysis_block_transform_prepend bottom result prepend f) fn
End

(* Prepend correctness: use state_equiv fresh / execution_equiv fresh
   where fresh = set of variables defined by the prepended instructions.
   The prepended PHIs define fresh vars that no original instruction reads,
   so excluding them from comparison preserves the simulation. *)
