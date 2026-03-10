(*
 * CFG Transform Utilities -- Proofs
 *
 * Properties of block list operations, label substitution,
 * and their interaction with lookup_block and resolve_phi.
 *
 * Non-trivial theorems are re-exported via cfgTransformProps.
 * Trivial results not in props (consumers can unfold directly):
 *   subst_label_block_label: rw[subst_label_block_def]
 *   subst_label_inst_fields: rw[subst_label_inst_def]
 *   ALL_DISTINCT_replace_block: rw[fn_labels_replace_block]
 *   ALL_DISTINCT_subst_label_fn: rw[fn_labels_subst_label_fn]
 *   MEM_remove_block_iff: rw[remove_block_def, MEM_FILTER]
 *
 * TOP-LEVEL (block ops):
 *   lookup_block_remove_neq/eq  -- remove_block preserves/removes lookup
 *   lookup_block_replace_neq/eq -- replace_block preserves/updates lookup
 *   fn_labels_remove_block      -- labels after removing a block
 *   ALL_DISTINCT_remove_block   -- distinctness preserved by removal
 *
 * TOP-LEVEL (label substitution):
 *   subst_label_op_id           -- subst_label_op old old = identity
 *   subst_label_op_Var/Lit      -- subst on non-labels is identity
 *   subst_label_inst_fields     -- subst preserves id/opcode/outputs
 *   subst_label_block_label     -- subst preserves block label
 *   fn_labels_subst_label_fn    -- block labels unchanged by subst
 *   lookup_block_subst_label_fn -- lookup finds substituted block
 *
 * TOP-LEVEL (PHI correctness):
 *   resolve_phi_subst_label     -- core lemma: label subst + resolve
 *   resolve_phi_subst_label_Var -- corollary for Var results
 *   resolve_phi_subst_label_Lit -- corollary for Lit results
 *   resolve_phi_subst_other     -- subst transparent for unrelated labels
 *   resolve_phi_remove_label    -- removing a label pair from PHI ops
 *   resolve_phi_remove_other    -- removal preserves unrelated resolve
 *
 * TOP-LEVEL (reachability):
 *   reachable_entry             -- entry label is reachable
 *   reachable_step              -- closed under CFG edges
 *   reachable_trans             -- transitivity
 *)

Theory cfgTransformProofs
Ancestors
  cfgTransform venomExecSemantics venomInst venomWf
Libs
  listTheory

(* ===== Block List Operations: remove_block ===== *)

(* Removing a block does not affect lookup of other labels. *)
Theorem lookup_block_remove_neq:
  !lbl other bbs.
    lbl <> other ==>
    lookup_block lbl (remove_block other bbs) = lookup_block lbl bbs
Proof
  cheat
QED

(* Removing a block with distinct labels makes its own lookup fail. *)
Theorem lookup_block_remove_eq:
  !lbl bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    lookup_block lbl (remove_block lbl bbs) = NONE
Proof
  cheat
QED

(* Membership: if bb is in remove_block result, it was in original. *)
Theorem MEM_remove_block:
  !bb lbl bbs.
    MEM bb (remove_block lbl bbs) ==> MEM bb bbs
Proof
  cheat
QED

(* Converse direction: bb is in result iff it was in original and has different label. *)
Theorem MEM_remove_block_iff:
  !bb lbl bbs.
    MEM bb (remove_block lbl bbs) <=> MEM bb bbs /\ bb.bb_label <> lbl
Proof
  cheat
QED

(* Labels after removing a block. *)
Theorem fn_labels_remove_block:
  !lbl bbs.
    MAP (\bb. bb.bb_label) (remove_block lbl bbs) =
    FILTER (\l. l <> lbl) (MAP (\bb. bb.bb_label) bbs)
Proof
  cheat
QED

(* Distinctness preserved by block removal. *)
Theorem ALL_DISTINCT_remove_block:
  !lbl bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (remove_block lbl bbs))
Proof
  cheat
QED

(* LENGTH of remove_block is at most LENGTH of original. *)
Theorem LENGTH_remove_block:
  !lbl bbs.
    LENGTH (remove_block lbl bbs) <= LENGTH bbs
Proof
  cheat
QED

(* remove_block on empty list. *)
Theorem remove_block_nil:
  !lbl. remove_block lbl [] = []
Proof
  rw[remove_block_def]
QED

(* remove_block is idempotent. *)
Theorem remove_block_idem:
  !lbl bbs. remove_block lbl (remove_block lbl bbs) = remove_block lbl bbs
Proof
  cheat
QED

(* ===== Block List Operations: replace_block ===== *)

(* Replace preserves lookup at other labels. *)
Theorem lookup_block_replace_neq:
  !lbl other new_bb bbs.
    lbl <> other ==>
    lookup_block lbl (replace_block other new_bb bbs) =
    lookup_block lbl bbs
Proof
  cheat
QED

(* Replace updates lookup at target label (when label exists). *)
Theorem lookup_block_replace_eq:
  !lbl new_bb bbs.
    (?bb. lookup_block lbl bbs = SOME bb) /\
    new_bb.bb_label = lbl ==>
    lookup_block lbl (replace_block lbl new_bb bbs) = SOME new_bb
Proof
  cheat
QED

(* Labels unchanged by replace_block when replacement has same label. *)
Theorem fn_labels_replace_block:
  !lbl new_bb bbs.
    new_bb.bb_label = lbl ==>
    MAP (\bb. bb.bb_label) (replace_block lbl new_bb bbs) =
    MAP (\bb. bb.bb_label) bbs
Proof
  cheat
QED

(* Distinctness preserved by replace when replacement has same label. *)
Theorem ALL_DISTINCT_replace_block:
  !lbl new_bb bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    new_bb.bb_label = lbl ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (replace_block lbl new_bb bbs))
Proof
  cheat
QED

(* LENGTH unchanged by replace_block. *)
Theorem LENGTH_replace_block:
  !lbl new_bb bbs.
    LENGTH (replace_block lbl new_bb bbs) = LENGTH bbs
Proof
  rw[replace_block_def]
QED

(* ===== Label Substitution Properties ===== *)

(* Substituting a label for itself is identity. *)
Theorem subst_label_op_id:
  !l op. subst_label_op l l op = op
Proof
  Cases_on `op` >> rw[subst_label_op_def]
QED

(* Substitution on Var is identity. *)
Theorem subst_label_op_Var:
  !old new v. subst_label_op old new (Var v) = Var v
Proof
  rw[subst_label_op_def]
QED

(* Substitution on Lit is identity. *)
Theorem subst_label_op_Lit:
  !old new c. subst_label_op old new (Lit c) = Lit c
Proof
  rw[subst_label_op_def]
QED

(* Substitution on Label. *)
Theorem subst_label_op_Label:
  !old new l.
    subst_label_op old new (Label l) =
      if l = old then Label new else Label l
Proof
  rw[subst_label_op_def]
QED

(* MAP subst_label_op with same label is identity. *)
Theorem MAP_subst_label_op_id:
  !l ops. MAP (subst_label_op l l) ops = ops
Proof
  Induct_on `ops` >> rw[subst_label_op_id]
QED

(* subst_label_inst preserves inst_id, opcode, outputs. *)
Theorem subst_label_inst_fields:
  !old new inst.
    (subst_label_inst old new inst).inst_id = inst.inst_id /\
    (subst_label_inst old new inst).inst_opcode = inst.inst_opcode /\
    (subst_label_inst old new inst).inst_outputs = inst.inst_outputs
Proof
  rw[subst_label_inst_def]
QED

(* subst_label_inst with same label is identity. *)
Theorem subst_label_inst_id:
  !l inst. subst_label_inst l l inst = inst
Proof
  rw[subst_label_inst_def, MAP_subst_label_op_id] >>
  rw[instruction_component_equality]
QED

(* subst_label_block preserves block label. *)
Theorem subst_label_block_label:
  !old new bb.
    (subst_label_block old new bb).bb_label = bb.bb_label
Proof
  rw[subst_label_block_def]
QED

(* subst_label_fn preserves function name. *)
Theorem subst_label_fn_name:
  !old new fn.
    (subst_label_fn old new fn).fn_name = fn.fn_name
Proof
  rw[subst_label_fn_def]
QED

(* Block labels of subst_label_fn are unchanged. *)
Theorem fn_labels_subst_label_fn:
  !old new fn.
    MAP (\bb. bb.bb_label)
        (subst_label_fn old new fn).fn_blocks =
    MAP (\bb. bb.bb_label) fn.fn_blocks
Proof
  rw[subst_label_fn_def, MAP_MAP_o, combinTheory.o_DEF,
     subst_label_block_label]
QED

(* Distinctness of block labels preserved by label substitution. *)
Theorem ALL_DISTINCT_subst_label_fn:
  !old new fn.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label)
                      (subst_label_fn old new fn).fn_blocks)
Proof
  rw[fn_labels_subst_label_fn]
QED

(* lookup_block on substituted blocks: finds the substituted block. *)
Theorem lookup_block_subst_label_fn:
  !old new bbs lbl bb.
    lookup_block lbl bbs = SOME bb ==>
    lookup_block lbl (MAP (subst_label_block old new) bbs) =
      SOME (subst_label_block old new bb)
Proof
  cheat
QED

(* ===== PHI Label-Substitution Correctness ===== *)

(*
 * Core PHI lemma: substituting old->new in operands and resolving with
 * new gives the substituted version of what resolving with old gave.
 *
 * Precondition: Label new does not appear in ops. This holds because
 * new is either a fresh block label (cfg_normalization) or the kept
 * block label that was not already a predecessor (simplify_cfg).
 *
 * The OPTION_MAP accounts for the possibility that the resolved operand
 * is itself a Label (unusual in practice -- PHI values are Var or Lit).
 *)
Theorem resolve_phi_subst_label:
  !old new ops.
    ~MEM (Label new) ops ==>
    resolve_phi new (MAP (subst_label_op old new) ops) =
      OPTION_MAP (subst_label_op old new) (resolve_phi old ops)
Proof
  cheat
QED

(*
 * Corollary: when the resolved operand is a Var, substitution is identity
 * on the result, so we get exact equality.
 *)
Theorem resolve_phi_subst_label_Var:
  !old new ops v.
    ~MEM (Label new) ops /\
    resolve_phi old ops = SOME (Var v) ==>
    resolve_phi new (MAP (subst_label_op old new) ops) = SOME (Var v)
Proof
  cheat
QED

(*
 * Corollary: when the resolved operand is a Lit, substitution is identity.
 *)
Theorem resolve_phi_subst_label_Lit:
  !old new ops c.
    ~MEM (Label new) ops /\
    resolve_phi old ops = SOME (Lit c) ==>
    resolve_phi new (MAP (subst_label_op old new) ops) = SOME (Lit c)
Proof
  cheat
QED

(*
 * Substitution does not affect resolve_phi for labels other than old/new.
 * If prev <> old and prev <> new, substitution is transparent.
 *)
Theorem resolve_phi_subst_other:
  !old new prev ops.
    prev <> old /\ prev <> new ==>
    resolve_phi prev (MAP (subst_label_op old new) ops) =
      OPTION_MAP (subst_label_op old new) (resolve_phi prev ops)
Proof
  cheat
QED

(*
 * When resolving for a label that is not old and not new, and the
 * resolve does not find a match, substitution preserves NONE.
 *)
Theorem resolve_phi_subst_not_found:
  !old new prev ops.
    prev <> old /\ prev <> new /\
    resolve_phi prev ops = NONE ==>
    resolve_phi prev (MAP (subst_label_op old new) ops) = NONE
Proof
  cheat
QED

(* ===== PHI Operand Removal ===== *)

(* Removing a label preserves resolve_phi for other labels. *)
Theorem resolve_phi_remove_other:
  !lbl prev ops.
    prev <> lbl ==>
    resolve_phi prev (remove_phi_label lbl ops) = resolve_phi prev ops
Proof
  cheat
QED

(* Removing a label makes resolve_phi return NONE for that label. *)
Theorem resolve_phi_remove_eq:
  !lbl ops.
    resolve_phi lbl (remove_phi_label lbl ops) = NONE
Proof
  cheat
QED

(* ===== Well-formedness Preservation ===== *)

(* subst_label_block preserves bb_well_formed: block structure unchanged,
   only operand labels change, so terminator and PHI prefix are preserved. *)
Theorem bb_well_formed_subst_label:
  !old new bb.
    bb_well_formed bb ==>
    bb_well_formed (subst_label_block old new bb)
Proof
  cheat
QED

(* Removing a non-entry block from a wf function preserves wf_function,
   provided the removed block is not a successor of any remaining block. *)
Theorem wf_function_remove_block:
  !fn lbl.
    wf_function fn /\
    fn_entry_label fn <> SOME lbl /\
    (* no remaining block has lbl as successor *)
    (!bb. MEM bb (remove_block lbl fn.fn_blocks) ==>
          ~MEM lbl (bb_succs bb)) ==>
    wf_function (fn with fn_blocks := remove_block lbl fn.fn_blocks)
Proof
  cheat
QED

(* Entry block is preserved when removing a different label. *)
Theorem entry_block_remove_neq:
  !fn lbl.
    fn.fn_blocks <> [] /\
    (HD fn.fn_blocks).bb_label <> lbl ==>
    entry_block (fn with fn_blocks := remove_block lbl fn.fn_blocks) =
    entry_block fn
Proof
  cheat
QED

(* fn_entry_label preserved when removing a non-entry label. *)
Theorem fn_entry_label_remove_neq:
  !fn lbl.
    fn.fn_blocks <> [] /\
    (HD fn.fn_blocks).bb_label <> lbl ==>
    fn_entry_label (fn with fn_blocks := remove_block lbl fn.fn_blocks) =
    fn_entry_label fn
Proof
  cheat
QED

(* ===== Reachability ===== *)

(* The entry label is reachable. *)
Theorem reachable_entry:
  !fn lbl.
    fn_entry_label fn = SOME lbl ==>
    reachable fn lbl
Proof
  cheat
QED

(* If a is reachable and a->b is a CFG edge, then b is reachable. *)
Theorem reachable_step:
  !fn a b.
    reachable fn a /\ fn_succ fn a b ==>
    reachable fn b
Proof
  cheat
QED

(* Reachability is transitive via RTC. *)
Theorem reachable_trans:
  !fn a b.
    reachable fn a /\ RTC (fn_succ fn) a b ==>
    reachable fn b
Proof
  cheat
QED
