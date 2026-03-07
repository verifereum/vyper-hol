(*
 * Variable Definition Analysis — Internal Proofs
 *
 * Proofs re-exported via varDefAnalysisPropsScript.sml.
 *)

Theory varDefProofs
Ancestors
  varDefDefs cfgAnalysisProps dfAnalyzeProps dfHelperProps venomWf

(* ===== Fixpoint ===== *)

(* The analysis reaches a fixpoint: processing any block is a no-op.
   Instantiates df_analyze_fixpoint with var_def's lattice parameters. *)
Theorem vardef_fixpoint_proof:
  !fn.
    wf_function fn ==>
    let cfg = cfg_analyze fn in
    let all_vars = fn_all_assignments fn in
    let entry_lbl = case entry_block fn of
                      NONE => "" | SOME bb => bb.bb_label in
    let process = df_process_block Forward all_vars list_intersect
                    vardef_transfer vardef_edge_transfer ()
                    (SOME (entry_lbl, ([] : string list))) cfg
                    fn.fn_blocks in
    is_fixpoint process (fn_labels fn) (vardef_analyze fn)
Proof
  cheat
QED

(* ===== Boundedness ===== *)

(* Every variable in any output set comes from fn_all_assignments. *)
Theorem vardef_out_bounded_proof:
  !fn lbl v.
    wf_function fn /\
    MEM v (vardef_out_of fn lbl) ==>
    MEM v (fn_all_assignments fn)
Proof
  cheat
QED

(* ===== Soundness ===== *)

(* If v is in the defined set at block exit, then every block-level
   CFG path from entry to that block passes through some block
   that assigns v. *)
Theorem vardef_sound_proof:
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
  cheat
QED
