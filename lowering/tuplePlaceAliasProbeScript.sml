(* Concrete checks for the proposed positive-size aliasing witness. *)
Theory tuplePlaceAliasProbe
Ancestors
  stmtLowering exprLowering vyperCompiler vyperInterpreter vyperTypeSystem
  finite_map

Definition alias_member_ty_def:
  alias_member_ty = ArrayT (BaseT (UintT 256)) (Fixed 1)
End

Definition alias_pair_ty_def:
  alias_pair_ty = TupleT [alias_member_ty; alias_member_ty]
End

Definition alias_rhs_def:
  alias_rhs = IfExp alias_pair_ty (Literal (BaseT BoolT) (BoolL T))
                (Name alias_pair_ty "x") (Name alias_pair_ty "x")
End

Theorem alias_rhs_not_view:
  ~is_memory_view alias_rhs
Proof
  EVAL_TAC
QED

Theorem alias_rhs_lowered_type:
  !cenv. lowered_value_type cenv alias_rhs = alias_pair_ty
Proof
  gen_tac >> EVAL_TAC
QED

(* Tuple reads accept a literal index, but tuple place subscripts do not:
   subscript_vtype deliberately rejects every tuple. *)
Theorem alias_tuple_target_rejected:
  !env i. type_place_target env (NameTarget "x") = SOME (Type alias_pair_ty) ==>
    type_place_target env (SubscriptTarget (NameTarget "x") i) = NONE
Proof
  rpt strip_tac >>
  simp[Once well_typed_expr_def, subscript_vtype_def, alias_pair_ty_def]
QED

Theorem alias_tuple_atarget_rejected:
  !env i ty.
    type_place_target env (NameTarget "x") = SOME (Type alias_pair_ty) ==>
    ~well_typed_atarget env (BaseTarget (SubscriptTarget (NameTarget "x") i)) ty
Proof
  rpt strip_tac >>
  drule alias_tuple_target_rejected >>
  disch_then (qspec_then `i` assume_tac) >>
  gvs[well_typed_atarget_def, well_typed_target_def]
QED
