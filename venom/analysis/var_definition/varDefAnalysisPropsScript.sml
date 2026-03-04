(*
 * Variable Definition Analysis — Properties (Statements Only)
 *
 * Re-exports from proofs/varDefProofsScript.sml via ACCEPT_TAC.
 *
 * TOP-LEVEL:
 *   vardef_fixpoint       — analysis result is a fixpoint
 *   vardef_out_bounded    — output sets contained in fn_all_assignments
 *   vardef_at_bounded     — per-inst sets contained in fn_all_assignments
 *   vardef_sound          — defined vars are assigned on every entry path
 *   vardef_includes_local — local defs appear in block output
 *)

Theory varDefAnalysisProps
Ancestors
  varDefProofs

(* Processing any label is a no-op after analysis completes. *)
Theorem vardef_fixpoint:
  !fn.
    wf_function fn ==>
    let cfg = cfg_analyze fn in
    let vd = vardef_analyze fn in
    is_fixpoint (vardef_process cfg fn) (fn_labels fn) vd
Proof
  ACCEPT_TAC vardef_fixpoint_proof
QED

(* Every variable in any output set comes from fn_all_assignments. *)
Theorem vardef_out_bounded:
  !fn lbl v.
    wf_function fn /\
    MEM v (vardef_out_of (vardef_analyze fn) lbl) ==>
    MEM v (fn_all_assignments fn)
Proof
  ACCEPT_TAC vardef_out_bounded_proof
QED

(* Every variable in any per-instruction set comes from fn_all_assignments. *)
Theorem vardef_at_bounded:
  !fn inst_id v.
    wf_function fn /\
    MEM v (vardef_at (vardef_analyze fn) inst_id) ==>
    MEM v (fn_all_assignments fn)
Proof
  ACCEPT_TAC vardef_at_bounded_proof
QED

(* If v is in the defined set at block exit, then on every block-level
   path from entry to that block, some block on the path assigns v. *)
Theorem vardef_sound:
  !fn lbl v path.
    wf_function fn /\
    fn.fn_blocks <> [] /\
    MEM v (vardef_out_of (vardef_analyze fn) lbl) /\
    is_cfg_path (cfg_analyze fn) path /\
    path <> [] /\
    HD path = (HD fn.fn_blocks).bb_label /\
    LAST path = lbl ==>
    ?lbl'. MEM lbl' path /\ var_assigned_in_block fn lbl' v
Proof
  ACCEPT_TAC vardef_sound_proof
QED

(* If an instruction in block lbl defines variable v, then v is in
   the block's output defined set. *)
Theorem vardef_includes_local:
  !fn lbl bb inst v.
    wf_function fn /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM inst bb.bb_instructions /\
    MEM v (inst_defs inst) ==>
    MEM v (vardef_out_of (vardef_analyze fn) lbl)
Proof
  ACCEPT_TAC vardef_includes_local_proof
QED
