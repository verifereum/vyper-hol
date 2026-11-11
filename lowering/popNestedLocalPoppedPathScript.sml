Theory popNestedLocalPoppedPath
Ancestors
  vyperState list alist integer

(* Only traversed containers must have fixed shape.  In particular, an
   empty path may end at a dynamically sized value. *)
Definition fixed_shape_path_def:
  fixed_shape_path tv [] = T /\
  fixed_shape_path tv (sb::path) =
    (case (tv,sb) of
       (ArrayTV et (Fixed n), ValueSubscript (IntV i)) =>
         0 <= i /\ Num i < n /\ fixed_shape_path et path
     | (StructTV fields, AttrSubscript name) =>
         (case ALOOKUP fields name of
            SOME ft => fixed_shape_path ft path
          | NONE => F)
     | _ => F)
End

Theorem fixed_shape_path_nil[simp]:
  fixed_shape_path tv []
Proof
  simp[fixed_shape_path_def]
QED

Theorem fixed_shape_path_static[simp]:
  fixed_shape_path (ArrayTV et (Fixed n))
    (ValueSubscript (IntV i)::path) <=>
  0 <= i /\ Num i < n /\ fixed_shape_path et path
Proof
  simp[fixed_shape_path_def]
QED

Theorem fixed_shape_path_dynamic[simp]:
  ~fixed_shape_path (ArrayTV et (Dynamic n)) (sb::path)
Proof
  Cases_on `sb` >> simp[fixed_shape_path_def]
QED

Theorem fixed_shape_path_struct[simp]:
  fixed_shape_path (StructTV fields) (AttrSubscript name::path) <=>
  ?ft. ALOOKUP fields name = SOME ft /\ fixed_shape_path ft path
Proof
  simp[fixed_shape_path_def] >>
  Cases_on `ALOOKUP fields name` >> simp[]
QED

Theorem fixed_shape_path_static_bounds:
  ~fixed_shape_path (ArrayTV et (Fixed n))
      (ValueSubscript (IntV (-1))::path) /\
  ~fixed_shape_path (ArrayTV et (Fixed n))
      (ValueSubscript (IntV (&n))::path)
Proof
  simp[fixed_shape_path_def]
QED
