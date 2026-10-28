Theory sourceTypeResolve
Ancestors
  sourceTypeDefs sourceConstAnnotation sourceConstAST sourceConstEval
  vyperTypeSystem vyperAST list

(* TOP-LEVEL: source_type_resolve, source_type_check_claim.
   This opt-in API has no dependency on inferred annotation metadata.
   tenv contains independently elaborated nominal declarations; names maps
   resolved paths to identities. Neither environment is constructed here. *)

Definition source_type_sized_def:
  source_type_sized tenv env is_string e =
    source_type_bind (source_type_bound env e) (\n.
      source_type_checked tenv
        (Type (BaseT (if is_string then StringT n else BytesT (Dynamic n))))
        [] [(e,n)])
End

Definition source_type_array_def:
  source_type_array tenv env dynamic e child =
    source_type_bind (source_type_as_type child) (\ty.
      source_type_bind (source_type_bound env e) (\n.
        source_type_checked tenv
          (Type (ArrayT ty (if dynamic then Dynamic n else Fixed n))) []
          (source_type_bounds child ++ [(e,n)])))
End

Definition source_type_hashmap_def:
  source_type_hashmap tenv key value =
    source_type_bind (source_type_as_type key) (\kt.
      source_type_bind (source_type_unqualified value) (\vt.
        if hashmap_key_type kt then
          source_type_checked tenv (HashMapT kt vt) []
            (source_type_bounds key ++ source_type_bounds value)
        else ST_Error STE_HashMapKey))
End

Definition source_type_tuple_types_def:
  source_type_tuple_types [] = ST_Ok [] /\
  source_type_tuple_types (r::rs) =
    source_type_bind (source_type_as_type r) (\ty.
      source_type_bind (source_type_tuple_types rs) (\tys. ST_Ok (ty::tys)))
End

Definition source_type_tuple_def:
  source_type_tuple tenv children =
    if children = [] then ST_Error STE_EmptyTuple else
      source_type_bind (source_type_tuple_types children) (\tys.
        source_type_checked tenv (Type (TupleT tys)) []
          (FLAT (MAP source_type_bounds children)))
End

Definition source_type_resolve_def:
  source_type_resolve tenv names env (SCA_Name path) =
    source_type_bind (source_type_name names path) (\ty.
      source_type_checked tenv (Type ty) [] []) /\
  source_type_resolve tenv names env (SCA_String e) =
    source_type_require_constructor names STC_String
      (source_type_sized tenv env T e) /\
  source_type_resolve tenv names env (SCA_Bytes e) =
    source_type_require_constructor names STC_Bytes
      (source_type_sized tenv env F e) /\
  source_type_resolve tenv names env (SCA_StaticArray a e) =
    source_type_bind (source_type_resolve tenv names env a)
      (source_type_array tenv env F e) /\
  source_type_resolve tenv names env (SCA_DynArray a e) =
    source_type_require_constructor names STC_DynArray
      (source_type_bind (source_type_resolve tenv names env a)
        (source_type_array tenv env T e)) /\
  source_type_resolve tenv names env (SCA_HashMap key value) =
    source_type_require_constructor names STC_HashMap
      (source_type_bind (source_type_resolve tenv names env key) (\kr.
        source_type_bind (source_type_resolve tenv names env value)
          (source_type_hashmap tenv kr))) /\
  source_type_resolve tenv names env (SCA_Tuple annotations) =
    source_type_bind (source_type_resolve_list tenv names env annotations)
      (source_type_tuple tenv) /\
  source_type_resolve tenv names env (SCA_Qualified q a) =
    source_type_require_constructor names (STC_Qualifier q)
      (source_type_bind (source_type_resolve tenv names env a)
        (source_type_add_qualifier q)) /\
  source_type_resolve_list tenv names env [] = ST_Ok [] /\
  source_type_resolve_list tenv names env (a::annotations) =
    source_type_bind (source_type_resolve tenv names env a) (\r.
      source_type_bind (source_type_resolve_list tenv names env annotations)
        (\rs. ST_Ok (r::rs)))
End

(* Inferred claims are checked ONLY AFTER independently resolving source.
   A false claim rejects; it never selects a type, bound or name identity. *)
Definition source_type_check_claim_def:
  source_type_check_claim tenv names env annotation claim =
    source_type_bind (source_type_resolve tenv names env annotation) (\r.
      if source_type_vtype r = claim then ST_Ok r
      else ST_Error STE_InferredClaim)
End
