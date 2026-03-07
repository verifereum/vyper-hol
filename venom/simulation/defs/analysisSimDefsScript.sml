(*
 * Analysis-Driven Simulation — Definitions
 *
 * Bridge between dataflow analysis results and the simulation framework.
 * Extends inst_simulates/block_simulates with per-instruction lattice values.
 *
 * TOP-LEVEL:
 *   analysis_inst_simulates   — per-instruction sim given sound lattice value
 *   analysis_block_transform  — transform block using per-instruction analysis
 *   analysis_function_transform — transform function using analysis result
 *)

Theory analysisSimDefs
Ancestors
  dfAnalyzeDefs passSimulationDefs indexedLists

(* Per-instruction simulation parameterized by lattice soundness.
   f transforms an instruction given the lattice value at that point.
   sound connects abstract lattice values to concrete states.
   When sound = λv s. T, this reduces to ∀v. inst_simulates R_ok R_term (f v). *)
Definition analysis_inst_simulates_def:
  analysis_inst_simulates R_ok R_term
    (sound : 'a -> venom_state -> bool)
    (f : 'a -> instruction -> instruction) <=>
    (!v inst s.
       sound v s ==>
       lift_result R_ok R_term
         (step_inst inst s) (step_inst (f v inst) s)) /\
    (!v inst.
       is_terminator inst.inst_opcode =
       is_terminator (f v inst).inst_opcode)
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
