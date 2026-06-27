(*
 * CFG Transform Utilities -- Proofs
 *
 * Properties of block list operations, label substitution,
 * and their interaction with lookup_block and resolve_phi.
 *
 * This is the workhorse/technical proof theory.  Stable public theorem names
 * are owned by cfgTransformProps; this theory remains available for technical
 * lemmas and for downstream proofs that still depend on the older proof-layer
 * names during the transition.
 *
 * TOP-LEVEL (block ops, technical extras):
 *   MEM_remove_block/_iff       -- membership in remove_block
 *   LENGTH/remove idempotence   -- small remove_block facts
 *   ALL_DISTINCT_replace_block  -- distinctness preserved by replace
 *   LENGTH_replace_block        -- replace_block preserves length
 *
 * TOP-LEVEL (label substitution, technical extras):
 *   subst_label_op_id           -- subst_label_op old old = identity
 *   subst_label_op_Var/Lit      -- subst on non-labels is identity
 *   subst_label_inst_fields     -- subst preserves id/opcode/outputs
 *   subst_label_block_label     -- subst preserves block label
 *   ALL_DISTINCT_subst_label_fn -- label subst preserves distinct labels
 *
 * TOP-LEVEL (PHI correctness, technical extras):
 *   resolve_phi_subst_label_Lit -- corollary for Lit results
 *   resolve_phi_subst_not_found -- NONE corollary for unrelated labels
 *   resolve_phi_remove_eq       -- removed label no longer resolves
 *)

Theory cfgTransformProofs
Ancestors
  cfgTransformProps cfgTransform venomExecSemantics venomInst venomWf
Libs
  listTheory

(* ===== Block List Operations: remove_block ===== *)

Theorem MEM_remove_block:
  !bb lbl bbs.
    MEM bb (remove_block lbl bbs) ==> MEM bb bbs
Proof
  rw[remove_block_def, MEM_FILTER]
QED

Theorem MEM_remove_block_iff:
  !bb lbl bbs.
    MEM bb (remove_block lbl bbs) <=> MEM bb bbs /\ bb.bb_label <> lbl
Proof
  rw[remove_block_def, MEM_FILTER] >> metis_tac[]
QED

Theorem LENGTH_remove_block:
  !lbl bbs.
    LENGTH (remove_block lbl bbs) <= LENGTH bbs
Proof
  rw[remove_block_def, rich_listTheory.LENGTH_FILTER_LEQ]
QED

Theorem remove_block_nil:
  !lbl. remove_block lbl [] = []
Proof
  rw[remove_block_def]
QED

Theorem remove_block_idem:
  !lbl bbs. remove_block lbl (remove_block lbl bbs) = remove_block lbl bbs
Proof
  rw[remove_block_def, rich_listTheory.FILTER_IDEM]
QED

(* ===== Block List Operations: replace_block ===== *)

Theorem lookup_block_replace_neq_counterexample[local]:
  let bb1 = <| bb_label := "A"; bb_instructions := [] |> in
  let new_bb = <| bb_label := "B"; bb_instructions := [] |> in
  lookup_block "B" (replace_block "A" new_bb [bb1]) <>
  lookup_block "B" [bb1]
Proof
  EVAL_TAC
QED

Theorem ALL_DISTINCT_replace_block:
  !lbl new_bb bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    new_bb.bb_label = lbl ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (replace_block lbl new_bb bbs))
Proof
  rw[fn_labels_replace_block]
QED

Theorem LENGTH_replace_block:
  !lbl new_bb bbs.
    LENGTH (replace_block lbl new_bb bbs) = LENGTH bbs
Proof
  rw[replace_block_def]
QED

(* ===== Label Substitution Properties ===== *)

Theorem subst_label_op_id:
  !l op. subst_label_op l l op = op
Proof
  Cases_on `op` >> rw[subst_label_op_def]
QED

Theorem subst_label_op_Var:
  !old new v. subst_label_op old new (Var v) = Var v
Proof
  rw[subst_label_op_def]
QED

Theorem subst_label_op_Lit:
  !old new c. subst_label_op old new (Lit c) = Lit c
Proof
  rw[subst_label_op_def]
QED

Theorem subst_label_op_Label:
  !old new l.
    subst_label_op old new (Label l) =
      if l = old then Label new else Label l
Proof
  rw[subst_label_op_def]
QED

Theorem MAP_subst_label_op_id:
  !l ops. MAP (subst_label_op l l) ops = ops
Proof
  Induct_on `ops` >> rw[subst_label_op_id]
QED

Theorem subst_label_inst_fields:
  !old new inst.
    (subst_label_inst old new inst).inst_id = inst.inst_id /\
    (subst_label_inst old new inst).inst_opcode = inst.inst_opcode /\
    (subst_label_inst old new inst).inst_outputs = inst.inst_outputs
Proof
  rw[subst_label_inst_def]
QED

Theorem subst_label_inst_id:
  !l inst. subst_label_inst l l inst = inst
Proof
  rw[subst_label_inst_def, MAP_subst_label_op_id] >>
  rw[instruction_component_equality]
QED

Theorem subst_label_block_label:
  !old new bb.
    (subst_label_block old new bb).bb_label = bb.bb_label
Proof
  rw[subst_label_block_def]
QED

Theorem subst_label_fn_name:
  !old new fn.
    (subst_label_fn old new fn).fn_name = fn.fn_name
Proof
  rw[subst_label_fn_def]
QED

Theorem ALL_DISTINCT_subst_label_fn:
  !old new fn.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label)
                      (subst_label_fn old new fn).fn_blocks)
Proof
  rw[fn_labels_subst_label_fn]
QED

(* ===== PHI Label-Substitution Correctness ===== *)

Theorem resolve_phi_subst_label_Lit:
  !old new ops c.
    ~MEM (Label new) ops /\
    resolve_phi old ops = SOME (Lit c) ==>
    resolve_phi new (MAP (subst_label_op old new) ops) = SOME (Lit c)
Proof
  rw[resolve_phi_subst_label, subst_label_op_def,
     optionTheory.OPTION_MAP_DEF]
QED

Theorem resolve_phi_subst_not_found:
  !old new prev ops.
    prev <> old /\ prev <> new /\
    resolve_phi prev ops = NONE ==>
    resolve_phi prev (MAP (subst_label_op old new) ops) = NONE
Proof
  rw[resolve_phi_subst_other, optionTheory.OPTION_MAP_DEF]
QED

(* ===== PHI Operand Removal ===== *)

Theorem resolve_phi_remove_eq:
  !lbl ops.
    resolve_phi lbl (remove_phi_label lbl ops) = NONE
Proof
  recInduct remove_phi_label_ind >>
  rw[remove_phi_label_def, resolve_phi_def]
QED

(* ===== Well-formedness Preservation ===== *)

