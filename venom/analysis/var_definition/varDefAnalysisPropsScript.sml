(*
 * Variable Definition Analysis — Properties (Statements Only)
 *
 * Re-exports from proofs/varDefProofsScript.sml via ACCEPT_TAC.
 *
 * TOP-LEVEL:
 *   vardef_fixpoint    — analysis result is a fixpoint
 *   vardef_out_bounded — output sets contained in fn_all_assignments
 *   vardef_sound       — defined vars are assigned on every entry path
 *)

Theory varDefAnalysisProps
Ancestors
  varDefProofs

(* The analysis reaches a fixpoint: processing any block is a no-op. *)
Theorem vardef_fixpoint:
  !fn.
    wf_function fn ==>
    let cfg = cfg_analyze fn in
    let all_vars = fn_all_assignments fn in
    let entry_val =
      OPTION_MAP (λlbl. (lbl, [] : string list)) (fn_entry_label fn) in
    let process = df_process_block Forward all_vars list_intersect
                    vardef_transfer vardef_edge_transfer ()
                    entry_val cfg fn.fn_blocks in
    is_fixpoint process (fn_labels fn) (vardef_analyze fn)
Proof
  ACCEPT_TAC vardef_fixpoint_proof
QED

(* Every variable in any output set comes from fn_all_assignments. *)
Theorem vardef_out_bounded:
  !fn lbl v.
    wf_function fn /\
    MEM v (vardef_out_of fn lbl) ==>
    MEM v (fn_all_assignments fn)
Proof
  ACCEPT_TAC vardef_out_bounded_proof
QED

(* If v is in the defined set at block exit, then every block-level
   path from entry to that block passes through some block that assigns v. *)
Theorem vardef_sound:
  !fn lbl v path.
    wf_function fn /\
    fn.fn_blocks <> [] /\
    MEM v (vardef_out_of fn lbl) /\
    is_cfg_path (cfg_analyze fn) path /\
    path <> [] /\
    HD path = (HD fn.fn_blocks).bb_label /\
    LAST path = lbl ==>
    ?lbl'. MEM lbl' path /\ var_assigned_in_block fn lbl' v
Proof
  ACCEPT_TAC vardef_sound_proof
QED
