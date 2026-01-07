(* 
 * Simplify-CFG PHI Lemmas
 *
 * Shared PHI and well-formedness lemmas for simplify-cfg proofs.
 *)

Theory scfgPhiLemmas
Ancestors
  scfgEquiv scfgTransform scfgDefs venomSemProps venomSem venomState venomInst
  stateEquiv list relation

Theorem simplify_phi_inst_no_phi:
  !preds inst.
    inst.inst_opcode <> PHI ==> simplify_phi_inst preds inst = inst
Proof
  rw[simplify_phi_inst_def]
QED

Theorem simplify_phi_inst_is_terminator:
  !preds inst.
    is_terminator (simplify_phi_inst preds inst).inst_opcode =
    is_terminator inst.inst_opcode
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (
    simp[simplify_phi_inst_def, is_terminator_def] >>
    qabbrev_tac `ops = phi_remove_non_preds preds inst.inst_operands` >>
    Cases_on `NULL ops` >> simp[is_terminator_def] >>
    Cases_on `LENGTH ops = 2` >> simp[is_terminator_def]
  )
  >- (
    `simplify_phi_inst preds inst = inst` by simp[simplify_phi_inst_no_phi] >>
    simp[]
  )
QED

(* ===== resolve_phi under Label Rewriting ===== *)

Theorem resolve_phi_vals_not_label:
  !ops prev val_op.
    phi_vals_not_label ops /\
    resolve_phi prev ops = SOME val_op ==> (!lbl. val_op <> Label lbl)
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >> simp[resolve_phi_def, phi_vals_not_label_def] >>
  Cases_on `t` >> simp[resolve_phi_def, phi_vals_not_label_def] >>
  Cases_on `h` >> gvs[resolve_phi_def, phi_vals_not_label_def]
  >- (first_x_assum (qspec_then `t'` mp_tac) >> simp[])
  >- (first_x_assum (qspec_then `t'` mp_tac) >> simp[])
  >- (
    Cases_on `h'` >> gvs[phi_vals_not_label_def]
    >- (
      Cases_on `s = prev` >| [
        gvs[resolve_phi_def] >> simp[],
        gvs[resolve_phi_def] >>
        first_x_assum (qspec_then `t'` mp_tac) >> simp[]
      ] >>
      metis_tac[])
    >- (
      Cases_on `s = prev` >| [
        gvs[resolve_phi_def] >> simp[],
        gvs[resolve_phi_def] >>
        first_x_assum (qspec_then `t'` mp_tac) >> simp[]
      ] >>
      metis_tac[])
  )
QED

Theorem resolve_phi_replace_label:
  !old new ops val_op.
    old <> new /\
    ~MEM (Label new) ops /\
    phi_vals_not_label ops /\
    resolve_phi old ops = SOME val_op ==>
    resolve_phi new (MAP (replace_label_operand old new) ops) =
    SOME (replace_label_operand old new val_op)
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >> simp[resolve_phi_def, phi_vals_not_label_def] >>
  Cases_on `t` >> simp[resolve_phi_def, phi_vals_not_label_def] >>
  Cases_on `h`
  >- (
    rpt strip_tac >>
    fs[resolve_phi_def, replace_label_operand_def, phi_vals_not_label_def] >>
    first_x_assum (qspec_then `t'` mp_tac) >> simp[])
  >- (
    rpt strip_tac >>
    fs[resolve_phi_def, replace_label_operand_def, phi_vals_not_label_def] >>
    first_x_assum (qspec_then `t'` mp_tac) >> simp[])
  >- (
    rpt strip_tac >>
    Cases_on `s = old`
    >- (
      fs[resolve_phi_def, replace_label_operand_def] >>
      Cases_on `h'` >>
      fs[phi_vals_not_label_def, resolve_phi_def, replace_label_operand_def])
    >- (
      fs[resolve_phi_def, replace_label_operand_def, phi_vals_not_label_def] >>
      first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
      strip_tac >>
      Cases_on `h'` >> fs[phi_vals_not_label_def] >>
      first_x_assum (qspecl_then [`old`, `new`, `val_op`] mp_tac) >> simp[]))
QED

(* When prev differs from BOTH old and new, label replacement doesn't affect resolve_phi *)
Theorem resolve_phi_replace_label_other:
  !old new prev ops.
    prev <> old /\
    prev <> new /\
    phi_vals_not_label ops ==>
    resolve_phi prev (MAP (replace_label_operand old new) ops) = resolve_phi prev ops
Proof
  measureInduct_on `LENGTH ops` >> rpt strip_tac >> Cases_on `ops` >>
  simp[resolve_phi_def] >> Cases_on `t` >> simp[resolve_phi_def] >>
  Cases_on `h`
  >- (
    simp[resolve_phi_def, replace_label_operand_def, phi_vals_not_label_def] >>
    first_x_assum (qspec_then `t'` mp_tac) >> simp[] >> strip_tac >>
    first_x_assum irule >> gvs[phi_vals_not_label_def])
  >- (
    simp[resolve_phi_def, replace_label_operand_def, phi_vals_not_label_def] >>
    first_x_assum (qspec_then `t'` mp_tac) >> simp[] >> strip_tac >>
    first_x_assum irule >> gvs[phi_vals_not_label_def])
  >- (
    simp[replace_label_operand_def] >>
    Cases_on `s = old` >> simp[resolve_phi_def]
    >- (
      first_x_assum (qspec_then `t'` mp_tac) >> simp[] >> strip_tac >>
      first_x_assum irule >> gvs[phi_vals_not_label_def] >>
      Cases_on `h'` >> gvs[])
    >- (
      Cases_on `s = prev`
      >- (
        gvs[phi_vals_not_label_def] >> Cases_on `h'` >>
        gvs[replace_label_operand_def, phi_vals_not_label_def])
      >- (
        gvs[] >> first_x_assum (qspec_then `t'` mp_tac) >> simp[] >> strip_tac >>
        first_x_assum irule >> gvs[phi_vals_not_label_def] >> Cases_on `h'` >>
        gvs[phi_vals_not_label_def])))
QED

(* ===== PHI Well-Formedness Helpers ===== *)

Theorem phi_ops_all_preds_MEM_label:
  !preds ops lbl.
    phi_ops_all_preds preds ops /\
    MEM (Label lbl) ops ==> MEM lbl preds
Proof
  rw[phi_ops_all_preds_def]
QED

Theorem phi_ops_all_preds_no_label:
  !preds ops lbl.
    phi_ops_all_preds preds ops /\
    ~MEM lbl preds ==> ~MEM (Label lbl) ops
Proof
  rw[phi_ops_all_preds_def] >> metis_tac[]
QED

Theorem phi_ops_complete_MEM:
  !preds ops lbl.
    phi_ops_complete preds ops /\
    MEM lbl preds ==> ?val_op. resolve_phi lbl ops = SOME val_op
Proof
  rw[phi_ops_complete_def] >> metis_tac[]
QED

Theorem phi_inst_wf_props:
  !preds inst.
    phi_inst_wf preds inst /\
    inst.inst_opcode = PHI ==>
    (?out. inst.inst_outputs = [out]) /\
    phi_ops_all_preds preds inst.inst_operands /\
    phi_ops_complete preds inst.inst_operands /\
    phi_vals_not_label inst.inst_operands
Proof
  rw[phi_inst_wf_def] >> gvs[]
QED

Theorem phi_block_wf_inst:
  !preds bb inst.
    phi_block_wf preds bb /\
    MEM inst bb.bb_instructions ==> phi_inst_wf preds inst
Proof
  rw[phi_block_wf_def]
QED

Theorem phi_fn_wf_block:
  !fn bb.
    phi_fn_wf fn /\
    MEM bb fn.fn_blocks ==>
    phi_block_wf (pred_labels fn bb.bb_label) bb
Proof
  rw[phi_fn_wf_def]
QED

Theorem phi_fn_wf_entry_no_phi:
  !fn. phi_fn_wf fn ==> block_has_no_phi (HD fn.fn_blocks)
Proof
  rw[phi_fn_wf_def]
QED

Definition phi_resolve_ok_def:
  phi_resolve_ok preds prev ops val <=>
    MEM prev preds /\ resolve_phi prev ops = SOME val
End

Theorem resolve_phi_remove_non_preds:
  !preds prev ops val.
    MEM prev preds /\
    resolve_phi prev ops = SOME val ==>
    resolve_phi prev (phi_remove_non_preds preds ops) = SOME val
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops`
  >- simp[venomSemTheory.resolve_phi_def, scfgDefsTheory.phi_remove_non_preds_def]
  >- (
    Cases_on `t`
    >- simp[venomSemTheory.resolve_phi_def, scfgDefsTheory.phi_remove_non_preds_def]
    >- (
      Cases_on `h`
      >- (
        rpt strip_tac >>
        fs[venomSemTheory.resolve_phi_def, scfgDefsTheory.phi_remove_non_preds_def] >>
        first_x_assum irule >> simp[]
      )
      >- (
        rpt strip_tac >>
        fs[venomSemTheory.resolve_phi_def, scfgDefsTheory.phi_remove_non_preds_def] >>
        first_x_assum irule >> simp[]
      )
      >- (
        rpt strip_tac >>
        fs[venomSemTheory.resolve_phi_def, scfgDefsTheory.phi_remove_non_preds_def] >>
        Cases_on `s = prev`
        >- (
          fs[venomSemTheory.resolve_phi_def, scfgDefsTheory.phi_remove_non_preds_def] >>
          simp[]
        )
        >- (
          fs[venomSemTheory.resolve_phi_def, scfgDefsTheory.phi_remove_non_preds_def] >>
          Cases_on `MEM s preds` >>
          fs[venomSemTheory.resolve_phi_def, scfgDefsTheory.phi_remove_non_preds_def] >>
          first_x_assum irule >> simp[]
        )
      )
    )
  )
QED

Theorem resolve_phi_remove_non_preds_ok:
  !preds prev ops val.
    phi_resolve_ok preds prev ops val ==>
    resolve_phi prev (phi_remove_non_preds preds ops) = SOME val
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops`
  >- (
    rpt strip_tac >>
    fs[phi_resolve_ok_def, resolve_phi_def, phi_remove_non_preds_def]
  )
  >- (
    Cases_on `t`
    >- (
      rpt strip_tac >>
      fs[phi_resolve_ok_def, resolve_phi_def, phi_remove_non_preds_def]
    )
    >- (
      Cases_on `h`
      >- (
        rpt strip_tac >>
        fs[phi_resolve_ok_def, resolve_phi_def, phi_remove_non_preds_def] >>
        first_x_assum irule >> simp[phi_resolve_ok_def]
      )
      >- (
        rpt strip_tac >>
        fs[phi_resolve_ok_def, resolve_phi_def, phi_remove_non_preds_def] >>
        first_x_assum irule >> simp[phi_resolve_ok_def]
      )
      >- (
        rpt strip_tac >>
        fs[phi_resolve_ok_def, resolve_phi_def, phi_remove_non_preds_def] >>
        Cases_on `s = prev`
        >- (
          fs[resolve_phi_def, phi_remove_non_preds_def] >>
          simp[]
        )
        >- (
          fs[resolve_phi_def, phi_remove_non_preds_def] >>
          Cases_on `MEM s preds` >>
          fs[resolve_phi_def, phi_remove_non_preds_def] >>
          first_x_assum irule >> simp[phi_resolve_ok_def]
        )
      )
    )
  )
QED

(* phi_remove_non_preds preserves phi_vals_not_label *)
Theorem phi_vals_not_label_remove_non_preds:
  !preds ops.
    phi_vals_not_label ops ==>
    phi_vals_not_label (phi_remove_non_preds preds ops)
Proof
  gen_tac >> Induct_on `ops` using phi_vals_not_label_ind >>
  simp[phi_vals_not_label_def, phi_remove_non_preds_def] >>
  Cases_on `op` >> gvs[] >> Cases_on `MEM lbl preds` >>
  gvs[phi_vals_not_label_def]
QED

(* phi_remove_non_preds produces output where all labels are in preds *)
Theorem phi_ops_all_preds_remove_non_preds:
  !preds ops.
    phi_vals_not_label ops ==>
    phi_ops_all_preds preds (phi_remove_non_preds preds ops)
Proof
  gen_tac >> Induct_on `ops` using phi_vals_not_label_ind >>
  simp[phi_vals_not_label_def, phi_remove_non_preds_def, phi_ops_all_preds_def]
  >- (
    rpt strip_tac >> Cases_on `op` >> gvs[]
    >- (Cases_on `MEM lbl preds` >> gvs[phi_ops_all_preds_def])
    >- (Cases_on `MEM lbl preds` >> gvs[phi_ops_all_preds_def]))
  >- (
    simp[phi_ops_all_preds_def] >>
    rpt strip_tac >> first_x_assum drule >> simp[phi_ops_all_preds_def])
  >- (
    rpt strip_tac >> first_x_assum drule >> simp[phi_ops_all_preds_def])
QED

(* Simplifying a PHI instruction preserves well-formedness when new_preds ⊆ old_preds *)
Theorem simplify_phi_inst_wf:
  !old_preds new_preds inst.
    phi_inst_wf old_preds inst /\
    (!lbl. MEM lbl new_preds ==> MEM lbl old_preds) ==>
    phi_inst_wf new_preds (simplify_phi_inst new_preds inst)
Proof
  rpt strip_tac >>
  simp[simplify_phi_inst_def, phi_inst_wf_def] >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  Cases_on `NULL (phi_remove_non_preds new_preds inst.inst_operands)` >> gvs[] >>
  Cases_on `LENGTH (phi_remove_non_preds new_preds inst.inst_operands) = 2` >>
  gvs[phi_inst_wf_def] >>
  rpt conj_tac
  >- (irule phi_ops_all_preds_remove_non_preds >> simp[])
  >- (
    simp[phi_ops_complete_def] >> rpt strip_tac >>
    `MEM lbl old_preds` by metis_tac[] >>
    `?val. resolve_phi lbl inst.inst_operands = SOME val`
      by fs[phi_ops_complete_def] >>
    fs[] >> irule_at Any resolve_phi_remove_non_preds >> simp[]
  )
  >- (irule phi_vals_not_label_remove_non_preds >> simp[])
QED

(* Simplifying a block preserves phi_block_wf when new_preds ⊆ old_preds *)
Theorem simplify_phi_block_wf:
  !old_preds new_preds bb.
    phi_block_wf old_preds bb /\
    (!lbl. MEM lbl new_preds ==> MEM lbl old_preds) ==>
    phi_block_wf new_preds (simplify_phi_block new_preds bb)
Proof
  rpt strip_tac >>
  simp[phi_block_wf_def, simplify_phi_block_def, MEM_MAP] >>
  rpt strip_tac >>
  `phi_inst_wf old_preds y` by fs[phi_block_wf_def] >>
  drule_all simplify_phi_inst_wf >> simp[]
QED

(* pred_labels is a subset when filtering blocks *)
Theorem pred_labels_filter_subset:
  !fn P lbl x.
    MEM x (pred_labels (fn with fn_blocks := FILTER P fn.fn_blocks) lbl) ==>
    MEM x (pred_labels fn lbl)
Proof
  simp[pred_labels_def, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

(* Simplifying a block preserves block_has_no_phi *)
Theorem simplify_phi_block_no_phi:
  !preds bb. block_has_no_phi bb ==> block_has_no_phi (simplify_phi_block preds bb)
Proof
  rpt strip_tac >>
  simp[block_has_no_phi_def, block_has_phi_def, simplify_phi_block_def,
       EXISTS_MEM, MEM_MAP] >>
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  `y.inst_opcode <> PHI` by metis_tac[scfgEquivTheory.block_has_no_phi_inst] >>
  `simplify_phi_inst preds y = y` by metis_tac[simplify_phi_inst_no_phi] >>
  gvs[]
QED

(* Simplifying a block preserves block_successors *)
Theorem simplify_phi_block_successors:
  !preds bb. block_successors (simplify_phi_block preds bb) = block_successors bb
Proof
  rpt gen_tac >>
  simp[block_successors_def, block_last_inst_def, simplify_phi_block_def] >>
  Cases_on `NULL bb.bb_instructions` >> simp[] >>
  `bb.bb_instructions <> []` by gvs[NULL_EQ] >>
  simp[LAST_MAP] >>
  Cases_on `is_terminator (LAST bb.bb_instructions).inst_opcode`
  >- (
    sg `(LAST bb.bb_instructions).inst_opcode <> PHI`
    >- (spose_not_then strip_assume_tac >> gvs[is_terminator_def])
    >- simp[simplify_phi_inst_no_phi]
  )
  >- simp[get_successors_def, simplify_phi_inst_is_terminator]
QED

val _ = export_theory();
