(*
 * SSA Construction: CFG Utilities
 *
 * This theory defines basic control-flow graph helpers for SSA construction:
 * - Finding terminators and successors
 * - Computing predecessor sets
 *)

Theory mkSsaCfg
Ancestors
  venomInst list finite_map pred_set

(* ===== Terminators and Successors ===== *)

(* TOP-LEVEL: Get the terminator instruction of a block (if any). *)
Definition get_terminator_def:
  get_terminator bb =
    case bb.bb_instructions of
      [] => NONE
    | insts =>
        let last = LAST insts in
        if is_terminator last.inst_opcode then SOME last else NONE
End

(* TOP-LEVEL: Get successor labels of a basic block. *)
Definition get_block_successors_def:
  get_block_successors bb =
    case get_terminator bb of
      NONE => []
    | SOME term => get_successors term
End

(* ===== Predecessor Map ===== *)

(* TOP-LEVEL: Compute predecessor map from blocks. *)
Definition compute_preds_def:
  compute_preds blocks =
    FUN_FMAP (λlbl.
      {bb.bb_label | MEM bb blocks /\ MEM lbl (get_block_successors bb)}
    ) (set (MAP (λbb. bb.bb_label) blocks))
End

(* TOP-LEVEL: Lookup predecessors of a label. *)
Definition get_preds_def:
  get_preds pm lbl =
    case FLOOKUP pm lbl of
      SOME s => s
    | NONE => {}
End

Theorem get_preds_empty:
  !lbl. get_preds FEMPTY lbl = {}
Proof
  simp[get_preds_def]
QED

(* Helper: get_preds after a single update. *)
Theorem get_preds_update:
  !pm succ new lbl.
    get_preds (pm |+ (succ, new)) lbl =
      if lbl = succ then new else get_preds pm lbl
Proof
  rw[get_preds_def, FLOOKUP_UPDATE] >>
  Cases_on `lbl = succ` >> simp[]
QED

(* Helper: case FLOOKUP is get_preds. *)
Theorem get_preds_flookup:
  !pm lbl. (case FLOOKUP pm lbl of SOME s => s | NONE => {}) = get_preds pm lbl
Proof
  simp[get_preds_def]
QED

(* Helper: block labels are unique under ALL_DISTINCT. *)
Theorem block_label_unique:
  !blocks bb1 bb2.
    ALL_DISTINCT (MAP (λbb. bb.bb_label) blocks) /\
    MEM bb1 blocks /\ MEM bb2 blocks /\
    bb1.bb_label = bb2.bb_label ==>
    bb1 = bb2
Proof
  Induct_on `blocks` >> simp[] >>
  rpt strip_tac >>
  Cases_on `bb1 = h` >> Cases_on `bb2 = h` >> simp[] >>
  TRY (metis_tac[MEM_MAP, ALL_DISTINCT]) >>
  first_x_assum irule >> simp[]
QED

(* Predecessor/successor duality. *)
Theorem preds_succs_consistent:
  !blocks bb1 bb2 pm.
    pm = compute_preds blocks /\
    ALL_DISTINCT (MAP (λbb. bb.bb_label) blocks) /\
    MEM bb1 blocks /\ MEM bb2 blocks ==>
    (bb1.bb_label IN get_preds pm bb2.bb_label <=>
     MEM bb2.bb_label (get_block_successors bb1))
Proof
  rpt strip_tac >>
  simp[compute_preds_def, get_preds_def, FLOOKUP_FUN_FMAP] >>
  sg `MEM bb2.bb_label (MAP (λbb. bb.bb_label) blocks)` >-
    (simp[MEM_MAP] >> qexists_tac `bb2` >> simp[]) >>
  simp[] >>
  eq_tac
  >- (
    strip_tac >>
    sg `bb = bb1` >-
      (metis_tac[block_label_unique]) >-
      (simp[] >> gvs[])
  )
  >- (
    strip_tac >> qexists_tac `bb1` >> simp[]
  )
QED
