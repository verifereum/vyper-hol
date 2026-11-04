Theory cfgTransformInstWf
Ancestors
  cfgTransform venomWf venomInst venomState dretShapeDefs list

(* Substituting a label preserves whether an operand carries a label. *)
Theorem get_label_subst_label_op_is_some[local]:
  !old_lbl new_lbl op.
    IS_SOME (get_label op) ==>
    IS_SOME (get_label (subst_label_op old_lbl new_lbl op))
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[cfgTransformTheory.subst_label_op_def,
      venomStateTheory.get_label_def] >>
  Cases_on `s = old_lbl` >>
  gvs[venomStateTheory.get_label_def]
QED

(* Label substitution does not change DRET's literal/count envelope. *)
Theorem parse_dret_shape_subst_label_inst[local]:
  !old_lbl new_lbl inst.
    parse_dret_shape (subst_label_inst old_lbl new_lbl inst) =
    parse_dret_shape inst
Proof
  rw[cfgTransformTheory.subst_label_inst_def,
     dretShapeDefsTheory.parse_dret_shape_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >>
  gvs[cfgTransformTheory.subst_label_op_def] >>
  Cases_on `s = old_lbl` >> gvs[]
QED

(* inst_wf preserved by subst_label_inst for terminators *)
Theorem inst_wf_subst_label_inst:
  !old_lbl new_lbl inst.
    inst_wf inst /\ is_terminator inst.inst_opcode ==>
    inst_wf (subst_label_inst old_lbl new_lbl inst)
Proof
  rw[cfgTransformTheory.subst_label_inst_def, inst_wf_def] >>
  Cases_on `inst.inst_opcode` >>
  fs[venomInstTheory.is_terminator_def, listTheory.LENGTH_MAP,
     listTheory.MAP_MAP_o, cfgTransformTheory.subst_label_op_def] >>
  rw[] >> fs[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rw[] >> res_tac >>
  FIRST
    [(rename1 `IS_SOME (get_label (subst_label_op old_lbl new_lbl x))` >>
      qspecl_then [`old_lbl`, `new_lbl`, `x`] mp_tac
        get_label_subst_label_op_is_some >> simp[]),
     (qspecl_then [`old_lbl`, `new_lbl`, `inst`] mp_tac
        parse_dret_shape_subst_label_inst >>
      simp[cfgTransformTheory.subst_label_inst_def])]
QED
