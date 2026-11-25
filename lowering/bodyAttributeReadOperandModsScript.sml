(* Read a linked value/place without depending on field selection. *)
Theory bodyAttributeReadOperandMods
Ancestors
  bodyFullPostsMods bodyPtrAttributeSource context exprSimAttribute

Theorem attribute_read_operand_mods:
  vv_holds_mods cenv cx ty tv vv ee t ==>
  ?v w. read_result cx tv ee = (INL v,ee) /\
        eval_operand (vv_operand vv) t = SOME w
Proof
  Cases_on `vv` >> simp[vv_holds_mods_def,vv_operand_def]
  >- (strip_tac >> drule attribute_vv_holds_read_operand >> simp[vv_operand_def]) >>
  rename1 `p.ptr_location = LocCode` >> Cases_on `p.ptr_location = LocCode`
  >- (simp[immutable_holds_mods_def] >> rpt strip_tac >>
      drule immutable_holds_read >> simp[]) >>
  simp[] >> strip_tac >> drule attribute_vv_holds_read_operand >> simp[vv_operand_def]
QED
