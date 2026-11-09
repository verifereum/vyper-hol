(*
 * Pass transform combinators: lift an instruction-level rewrite to blocks
 * and functions, optionally driven by a dataflow analysis result.
 * The simulation theories (passSimulationDefs, analysisSimDefs) state
 * what each combinator must preserve.
 *)

Theory passTransform
Ancestors
  venomExecSemantics venomInst dfAnalyzeDefs dfAnalyzeWidenDefs indexedLists

(* ===== Transform definitions ===== *)

(* Level 1: 1:1 instruction mapping *)
Definition block_map_transform_def:
  block_map_transform f bb =
    bb with bb_instructions := MAP f bb.bb_instructions
End

(* Function transform: apply block transform to all blocks *)
Definition function_map_transform_def:
  function_map_transform bt fn =
    fn with fn_blocks := MAP bt fn.fn_blocks
End

Theorem function_map_transform_identity_metadata_eq:
  !bt fn. fn_identity_metadata_eq (function_map_transform bt fn) fn
Proof
  simp[function_map_transform_def, fn_identity_metadata_eq_def]
QED

Theorem function_map_transform_static_input_eq:
  !bt fn. fn_static_input_eq (function_map_transform bt fn) fn
Proof
  simp[function_map_transform_def, fn_static_input_eq_def]
QED

Theorem function_map_transform_static_layout_eq:
  !bt fn. fn_static_layout_eq (function_map_transform bt fn) fn
Proof
  simp[function_map_transform_def, fn_static_layout_eq_def]
QED

Theorem function_map_transform_fmp_convention_eq:
  !bt fn. fn_fmp_convention_eq (function_map_transform bt fn) fn
Proof
  simp[function_map_transform_def, fn_fmp_convention_eq_def]
QED

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
    let bt_insts = FLAT (MAPi (\idx inst. f (df_at bottom result bb.bb_label idx) inst)
                              bb.bb_instructions) in
    let pplen = phi_prefix_length bt_insts in
      bb with bb_instructions :=
        TAKE pplen bt_insts ++
        prepend bb.bb_label ++
        DROP pplen bt_insts
End

Definition analysis_function_transform_prepend_def:
  analysis_function_transform_prepend bottom result prepend f fn =
    function_map_transform
      (analysis_block_transform_prepend bottom result prepend f) fn
End
