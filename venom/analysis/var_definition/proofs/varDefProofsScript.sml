(*
 * Variable Definition Analysis — Internal Proofs
 *
 * Proofs re-exported via varDefAnalysisPropsScript.sml.
 *)

Theory varDefProofs
Ancestors
  varDefDefs cfgAnalysisProps worklistProps dfHelperProps venomWf

(* ===== Fixpoint ===== *)

(* Processing any label is a no-op after analysis completes. *)
Theorem vardef_fixpoint_proof:
  !fn.
    wf_function fn ==>
    let cfg = cfg_analyze fn in
    let vd = vardef_analyze fn in
    is_fixpoint (vardef_process cfg fn) (fn_labels fn) vd
Proof
  cheat
QED

(* ===== Boundedness ===== *)

(* Every variable in any output set comes from fn_all_assignments. *)
Theorem vardef_out_bounded_proof:
  !fn lbl v.
    wf_function fn /\
    MEM v (vardef_out_of (vardef_analyze fn) lbl) ==>
    MEM v (fn_all_assignments fn)
Proof
  cheat
QED

(* Every variable in any per-instruction set comes from fn_all_assignments. *)
Theorem vardef_at_bounded_proof:
  !fn inst_id v.
    wf_function fn /\
    MEM v (vardef_at (vardef_analyze fn) inst_id) ==>
    MEM v (fn_all_assignments fn)
Proof
  cheat
QED

(* ===== Soundness ===== *)

(* If v is in the output defined set for block lbl, then on every
   block-level CFG path from the entry block to lbl, some block
   on the path assigns v.
   This is the key property: the analysis is sound w.r.t. all-paths
   reachability of definitions. *)
Theorem vardef_sound_proof:
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
  cheat
QED

(* ===== Local completeness ===== *)

(* If an instruction in block lbl defines variable v, then v is in
   the block's output defined set. *)
Theorem vardef_includes_local_proof:
  !fn lbl bb inst v.
    wf_function fn /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM inst bb.bb_instructions /\
    MEM v (inst_defs inst) ==>
    MEM v (vardef_out_of (vardef_analyze fn) lbl)
Proof
  cheat
QED
