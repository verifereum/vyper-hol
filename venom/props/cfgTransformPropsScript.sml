(*
 * CFG Transform Properties (API)
 *
 * Re-exports non-trivial theorems from cfgTransformProofs via ACCEPT_TAC.
 * Consumers should use this theory, not cfgTransformProofs directly.
 *
 * TOP-LEVEL (block ops -- 8):
 *   lookup_block_remove_neq/eq — remove_block + lookup interaction
 *   fn_labels_remove_block     — labels after removal
 *   ALL_DISTINCT_remove_block  — distinctness after removal
 *   lookup_block_replace_neq/eq — replace_block + lookup interaction
 *   fn_labels_replace_block    — labels preserved by same-label replace
 *   lookup_block_subst_label_fn — lookup finds substituted block
 *
 * TOP-LEVEL (PHI correctness -- 4):
 *   resolve_phi_subst_label     — core: label subst + resolve
 *   resolve_phi_subst_label_Var — corollary for Var results (common case)
 *   resolve_phi_subst_other     — subst transparent for unrelated labels
 *   resolve_phi_remove_other    — removal preserves unrelated resolve
 *
 * TOP-LEVEL (label subst + wf -- 3):
 *   fn_labels_subst_label_fn    — block labels unchanged by subst
 *   bb_well_formed_subst_label  — well-formedness preserved by subst
 *   wf_function_remove_block    — wf preserved by non-entry removal
 *
 * TOP-LEVEL (entry + reachability -- 5):
 *   entry_block_remove_neq     — entry preserved by non-entry removal
 *   fn_entry_label_remove_neq  — entry label preserved
 *   reachable_entry            — entry label is reachable
 *   reachable_step             — closed under CFG edges
 *   reachable_trans            — transitivity
 *)

Theory cfgTransformProps
Ancestors
  cfgTransformProofs

(* ===== Block List Operations: remove_block ===== *)

(* Removing a different label preserves lookup (induction on block list). *)
Theorem lookup_block_remove_neq:
  !lbl other bbs.
    lbl <> other ==>
    lookup_block lbl (remove_block other bbs) = lookup_block lbl bbs
Proof
  ACCEPT_TAC cfgTransformProofsTheory.lookup_block_remove_neq
QED

(* Removing own label clears lookup (needs ALL_DISTINCT). *)
Theorem lookup_block_remove_eq:
  !lbl bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    lookup_block lbl (remove_block lbl bbs) = NONE
Proof
  ACCEPT_TAC cfgTransformProofsTheory.lookup_block_remove_eq
QED

(* Labels after removal = FILTER of original labels. *)
Theorem fn_labels_remove_block:
  !lbl bbs.
    MAP (\bb. bb.bb_label) (remove_block lbl bbs) =
    FILTER (\l. l <> lbl) (MAP (\bb. bb.bb_label) bbs)
Proof
  ACCEPT_TAC cfgTransformProofsTheory.fn_labels_remove_block
QED

(* Distinctness of labels preserved by removal. *)
Theorem ALL_DISTINCT_remove_block:
  !lbl bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (remove_block lbl bbs))
Proof
  ACCEPT_TAC cfgTransformProofsTheory.ALL_DISTINCT_remove_block
QED

(* ===== Block List Operations: replace_block ===== *)

(* Replacing a different label preserves lookup (requires same-label replacement).
   NOTE: original statement was missing new_bb.bb_label = other precondition.
   See lookup_block_replace_neq_counterexample in Proofs for why it's needed. *)
Theorem lookup_block_replace_neq:
  !lbl other new_bb bbs.
    lbl <> other /\ new_bb.bb_label = other ==>
    lookup_block lbl (replace_block other new_bb bbs) =
    lookup_block lbl bbs
Proof
  ACCEPT_TAC cfgTransformProofsTheory.lookup_block_replace_neq
QED

(* Replacing own label updates lookup (needs existing block). *)
Theorem lookup_block_replace_eq:
  !lbl new_bb bbs.
    (?bb. lookup_block lbl bbs = SOME bb) /\
    new_bb.bb_label = lbl ==>
    lookup_block lbl (replace_block lbl new_bb bbs) = SOME new_bb
Proof
  ACCEPT_TAC cfgTransformProofsTheory.lookup_block_replace_eq
QED

(* Labels unchanged by same-label replace (induction + conditional MAP). *)
Theorem fn_labels_replace_block:
  !lbl new_bb bbs.
    new_bb.bb_label = lbl ==>
    MAP (\bb. bb.bb_label) (replace_block lbl new_bb bbs) =
    MAP (\bb. bb.bb_label) bbs
Proof
  ACCEPT_TAC cfgTransformProofsTheory.fn_labels_replace_block
QED

(* ===== Label Substitution ===== *)

(* Block labels of subst_label_fn unchanged (MAP_MAP_o chain). *)
Theorem fn_labels_subst_label_fn:
  !old new fn.
    MAP (\bb. bb.bb_label)
        (subst_label_fn old new fn).fn_blocks =
    MAP (\bb. bb.bb_label) fn.fn_blocks
Proof
  ACCEPT_TAC cfgTransformProofsTheory.fn_labels_subst_label_fn
QED

(* Lookup on substituted blocks finds the substituted block (induction). *)
Theorem lookup_block_subst_label_fn:
  !old new bbs lbl bb.
    lookup_block lbl bbs = SOME bb ==>
    lookup_block lbl (MAP (subst_label_block old new) bbs) =
      SOME (subst_label_block old new bb)
Proof
  ACCEPT_TAC cfgTransformProofsTheory.lookup_block_subst_label_fn
QED

(* ===== PHI Label-Substitution Correctness ===== *)

(* Core PHI lemma: substituting old->new in operands and resolving with
   new gives the substituted version of what resolving with old gave.
   Precondition: Label new not in ops (fresh or non-predecessor label).
   Proof by induction on resolve_phi. *)
Theorem resolve_phi_subst_label:
  !old new ops.
    ~MEM (Label new) ops ==>
    resolve_phi new (MAP (subst_label_op old new) ops) =
      OPTION_MAP (subst_label_op old new) (resolve_phi old ops)
Proof
  ACCEPT_TAC cfgTransformProofsTheory.resolve_phi_subst_label
QED

(* When resolved operand is Var (common case), subst is identity on result.
   Enables direct drule without OPTION_MAP reasoning. *)
Theorem resolve_phi_subst_label_Var:
  !old new ops v.
    ~MEM (Label new) ops /\
    resolve_phi old ops = SOME (Var v) ==>
    resolve_phi new (MAP (subst_label_op old new) ops) = SOME (Var v)
Proof
  ACCEPT_TAC cfgTransformProofsTheory.resolve_phi_subst_label_Var
QED

(* Subst transparent for unrelated labels (prev <> old, prev <> new).
   Separate induction from core lemma (different case analysis). *)
Theorem resolve_phi_subst_other:
  !old new prev ops.
    prev <> old /\ prev <> new ==>
    resolve_phi prev (MAP (subst_label_op old new) ops) =
      OPTION_MAP (subst_label_op old new) (resolve_phi prev ops)
Proof
  ACCEPT_TAC cfgTransformProofsTheory.resolve_phi_subst_other
QED

(* Removing a label preserves resolve_phi for other labels.
   Induction on remove_phi_label structure. *)
Theorem resolve_phi_remove_other:
  !lbl prev ops.
    prev <> lbl ==>
    resolve_phi prev (remove_phi_label lbl ops) = resolve_phi prev ops
Proof
  ACCEPT_TAC cfgTransformProofsTheory.resolve_phi_remove_other
QED

(* ===== Well-formedness Preservation ===== *)

(* subst_label_block preserves bb_well_formed: terminator and PHI prefix
   preserved because opcode unchanged, only operand labels change. *)
Theorem bb_well_formed_subst_label:
  !old new bb.
    bb_well_formed bb ==>
    bb_well_formed (subst_label_block old new bb)
Proof
  ACCEPT_TAC cfgTransformProofsTheory.bb_well_formed_subst_label
QED

(* Removing a non-entry block with no remaining successors preserves wf.
   Composes ALL_DISTINCT, bb_well_formed, fn_succs_closed sub-conditions. *)
Theorem wf_function_remove_block:
  !fn lbl.
    wf_function fn /\
    fn_entry_label fn <> SOME lbl /\
    (!bb. MEM bb (remove_block lbl fn.fn_blocks) ==>
          ~MEM lbl (bb_succs bb)) ==>
    wf_function (fn with fn_blocks := remove_block lbl fn.fn_blocks)
Proof
  ACCEPT_TAC cfgTransformProofsTheory.wf_function_remove_block
QED

(* ===== Entry Preservation ===== *)

(* Entry block preserved when removing a non-entry label. *)
Theorem entry_block_remove_neq:
  !fn lbl.
    fn.fn_blocks <> [] /\
    (HD fn.fn_blocks).bb_label <> lbl ==>
    entry_block (fn with fn_blocks := remove_block lbl fn.fn_blocks) =
    entry_block fn
Proof
  ACCEPT_TAC cfgTransformProofsTheory.entry_block_remove_neq
QED

(* fn_entry_label preserved when removing a non-entry label. *)
Theorem fn_entry_label_remove_neq:
  !fn lbl.
    fn.fn_blocks <> [] /\
    (HD fn.fn_blocks).bb_label <> lbl ==>
    fn_entry_label (fn with fn_blocks := remove_block lbl fn.fn_blocks) =
    fn_entry_label fn
Proof
  ACCEPT_TAC cfgTransformProofsTheory.fn_entry_label_remove_neq
QED

(* ===== Reachability ===== *)

(* Entry label is reachable (RTC_REFL + existential witness). *)
Theorem reachable_entry:
  !fn lbl.
    fn_entry_label fn = SOME lbl ==>
    reachable fn lbl
Proof
  ACCEPT_TAC cfgTransformProofsTheory.reachable_entry
QED

(* Reachability closed under CFG edges (RTC step). *)
Theorem reachable_step:
  !fn a b.
    reachable fn a /\ fn_succ fn a b ==>
    reachable fn b
Proof
  ACCEPT_TAC cfgTransformProofsTheory.reachable_step
QED

(* Reachability transitive via RTC composition. *)
Theorem reachable_trans:
  !fn a b.
    reachable fn a /\ RTC (fn_succ fn) a b ==>
    reachable fn b
Proof
  ACCEPT_TAC cfgTransformProofsTheory.reachable_trans
QED


(* subst_block_labels: block label preservation *)
Theorem subst_block_labels_block_label:
  !m bb. (subst_block_labels_block m bb).bb_label = bb.bb_label
Proof
  ACCEPT_TAC cfgTransformProofsTheory.subst_block_labels_block_label
QED

Theorem fn_entry_label_subst_block_labels_fn:
  !m func.
    fn_entry_label (subst_block_labels_fn m func) = fn_entry_label func
Proof
  ACCEPT_TAC cfgTransformProofsTheory.fn_entry_label_subst_block_labels_fn
QED

Theorem fn_labels_subst_block_labels_fn:
  !m func.
    fn_labels (subst_block_labels_fn m func) = fn_labels func
Proof
  ACCEPT_TAC cfgTransformProofsTheory.fn_labels_subst_block_labels_fn
QED

Theorem fn_entry_label_MAP_bb_label:
  !f bbs.
    (!bb. (f bb).bb_label = bb.bb_label) ==>
    fn_entry_label (<| fn_blocks := MAP f bbs |>) =
    fn_entry_label (<| fn_blocks := bbs |>)
Proof
  ACCEPT_TAC cfgTransformProofsTheory.fn_entry_label_MAP_bb_label
QED

Theorem fn_entry_label_replace_block:
  !lbl bb' func.
    (bb'.bb_label = lbl) ==>
    fn_entry_label (func with fn_blocks := replace_block lbl bb' func.fn_blocks) =
    fn_entry_label func
Proof
  ACCEPT_TAC cfgTransformProofsTheory.fn_entry_label_replace_block
QED
