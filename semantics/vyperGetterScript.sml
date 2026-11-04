Theory vyperGetter
Ancestors
  vyperAST vyperContext cv cv_std
Libs
  cv_transLib

(* Shared construction of implicit public-variable getters. *)

Definition getter_vtype_annotation_def:
  getter_vtype_annotation (Type ty) = ty /\
  getter_vtype_annotation (HashMapT _ _) = NoneT
End

val () = cv_auto_trans getter_vtype_annotation_def;

Definition build_getter_def:
  build_getter e kt (Type vt) n =
    (let vn = num_to_dec_string n in
      if is_ArrayT vt then
        (let (args, ret, exp) =
           build_getter
             (Subscript vt e (Name kt vn))
             (BaseT (UintT 256)) (Type (ArrayT_type vt)) (SUC n) in
           ((vn, kt)::args, ret, exp))
      else ([(vn, kt)], vt, Subscript vt e (Name kt vn))) /\
  build_getter e kt (HashMapT typ vtyp) n =
    (let vn = num_to_dec_string n in
     let (args, ret, exp) =
       build_getter
         (Subscript (getter_vtype_annotation (HashMapT typ vtyp)) e (Name kt vn))
         typ vtyp (SUC n) in
     ((vn, kt)::args, ret, exp))
Termination
  WF_REL_TAC `measure (value_type_size o FST o SND o SND)`
  \\ Cases \\ rw[type_size_def]
End

val () = cv_auto_trans_rec build_getter_def (
  WF_REL_TAC `measure (cv_size o FST o SND o SND)`
  \\ conj_tac \\ Cases \\ rw[]
  >- (
    qmatch_goalsub_rename_tac`cv_snd p`
    \\ Cases_on`p` \\ rw[] )
  \\ qmatch_asmsub_rename_tac`cv_is_ArrayT a`
  \\ Cases_on `a` \\ gvs[cv_is_ArrayT_def, cv_ArrayT_type_def]
  \\ rw[] \\ gvs[]
  \\ qmatch_goalsub_rename_tac`cv_fst p`
  \\ Cases_on `p` \\ gvs[]
);

Definition getter_def:
  getter nr ne kt vt =
  let (args, ret, exp) =
    build_getter ne kt vt 0
  in
    (View, nr, args, [], ret, [Return $ SOME exp])
End

val () = cv_auto_trans getter_def;
