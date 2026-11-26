(* Common source and operand facts at a reached runtime-code array selector. *)
Theory bodyArrayFramedCodeSelectInputsDefsMods
Ancestors
  exprSimArrayIndex compileEnv context venomState
  vyperInterpreter vyperState vyperAST vyperTypeSystem
  vyperTypeInvariants vyperArray integer_word words

Definition framed_code_select_inputs_mods_def[nocompute]:
  framed_code_select_inputs_mods cenv cx env ty obj idx ann et bd
      (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
      (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni)
      p etv av i iw w <=>
    bvv = LocatedValue (ArrayT et bd) p /\
    p.ptr_location = LocCode /\ loc = LocCode /\ ann = et /\
    eval_operand p.ptr_operand s = SOME w /\
    eval_operand p.ptr_operand it = SOME w /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\
    read_result cx raw mid = (INL (ArrayV av),mid) /\
    read_result cx raw fin = (INL (ArrayV av),fin) /\
    (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
    key = IntV i /\ eval_operand iop it = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
    array_length (ArrayTV etv bd) av < dimword (:256) /\
    (valid_index (ArrayTV etv bd) av i <=>
      idx_in_range (is_signed_type (expr_type idx)) iw
        (n2w (array_length (ArrayTV etv bd) av)))
End
