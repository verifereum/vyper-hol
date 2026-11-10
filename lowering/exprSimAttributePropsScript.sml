(* Pointer location and offset properties for struct attributes. *)
Theory exprSimAttributeProps
Ancestors
  exprSimProps exprSimDefs compileEnv loweringPosts
  valueEncoding vyperAST vyperValue venomState words list



Definition vv_loc_def:
  vv_loc vv = case vv_location vv of SOME l => l | NONE => LocMemory
End

Definition attr_offset_def:
  attr_offset cenv bty loc fld =
    let fields = get_struct_fields cenv.ce_struct_fields
                   (case bty of StructT sn => nsid_to_string sn | _ => "") in
    if (case loc of LocStorage => T | LocTransient => T | _ => F)
    then struct_field_offset_slots fields fld
    else struct_field_offset fields fld
End

Theorem field_ptr_w2n:
  !(w:bytes32) off fsz tsz.
    off + fsz <= tsz /\ (tsz = 0 \/ w2n w + tsz < dimword (:256)) ==>
    w2n (w + n2w off) = w2n w + off
Proof
  rpt strip_tac >- gvs[] >> irule buffer_offset_no_wrap >>
  qexists_tac `tsz` >> DECIDE_TAC
QED
