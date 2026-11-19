Theory bodyFullSubscriptLayoutByte
Ancestors
  valueEncodingDefs

(* Addresses read by the tests in val_in_memory, not the allocation
   bounds. Keep the list recursions at the same typed strides as the
   representation equations, including sparse fixed-array defaults. *)
Definition subscript_layout_byte_cases:
  (subscript_layout_byte tv (BoolV b) a i = (a <= i /\ i < a + 32)) /\
  (subscript_layout_byte tv (IntV n) a i = (a <= i /\ i < a + 32)) /\
  (subscript_layout_byte tv (FlagV n) a i = (a <= i /\ i < a + 32)) /\
  (subscript_layout_byte tv (DecimalV n) a i = (a <= i /\ i < a + 32)) /\
  (subscript_layout_byte tv (BytesV bs) a i =
    ((a <= i /\ i < a + 32) \/
     case tv of
       BaseTV (BytesT (Fixed _)) => F
     | BaseTV AddressT => F
     | _ => a + 32 <= i /\ i < a + 32 + LENGTH bs)) /\
  (subscript_layout_byte tv (StringV s) a i =
    ((a <= i /\ i < a + 32) \/
     (a + 32 <= i /\ i < a + 32 + LENGTH s))) /\
  (subscript_layout_byte tv NoneV a i = F) /\
  (subscript_layout_byte tv (StructV fields) a i =
    case tv of
      StructTV ftvs => subscript_layout_fields_byte fields ftvs a i
    | _ => F) /\
  (subscript_layout_byte tv (ArrayV (DynArrayV vs)) a i =
    ((a <= i /\ i < a + 32) \/
     case tv of
       ArrayTV etv _ => subscript_layout_elems_byte vs (a + 32) etv i
     | _ => F)) /\
  (subscript_layout_byte tv (ArrayV (SArrayV kvs)) a i =
    case tv of
      ArrayTV etv bd =>
        subscript_layout_kvs_byte kvs a etv i \/
        (?n k. bd = Fixed n /\ k < n /\ ALOOKUP kvs k = NONE /\
               subscript_layout_byte etv (default_value etv)
                 (a + k * type_memory_size etv) i)
    | _ => F) /\
  (subscript_layout_byte tv (ArrayV (TupleV vs)) a i =
    case tv of
      TupleTV tvs => subscript_layout_tuple_byte vs tvs a i
    | _ => F) /\
  (subscript_layout_fields_byte [] ftvs a i = F) /\
  (subscript_layout_fields_byte ((name,v)::rest) ftvs a i =
    let (ftv, rest_tvs) =
      case ftvs of
        (_,ty)::tvs => (ty,tvs)
      | [] => (BaseTV BoolT,[])
    in
      subscript_layout_byte ftv v a i \/
      subscript_layout_fields_byte rest rest_tvs (a + type_memory_size ftv) i) /\
  (subscript_layout_elems_byte [] a tv i = F) /\
  (subscript_layout_elems_byte (v::vs) a tv i =
    (subscript_layout_byte tv v a i \/
     subscript_layout_elems_byte vs (a + type_memory_size tv) tv i)) /\
  (subscript_layout_kvs_byte [] a tv i = F) /\
  (subscript_layout_kvs_byte ((k,v)::rest) a tv i =
    (subscript_layout_byte tv v (a + k * type_memory_size tv) i \/
     subscript_layout_kvs_byte rest a tv i)) /\
  (subscript_layout_tuple_byte [] tvs a i = F) /\
  (subscript_layout_tuple_byte (v::vs) tvs a i =
    let (etv, rest_tvs) =
      case tvs of
        ty::ts => (ty,ts)
      | [] => (BaseTV BoolT,[])
    in
      subscript_layout_byte etv v a i \/
      subscript_layout_tuple_byte vs rest_tvs (a + type_memory_size etv) i)
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (\x.
    case x of
      INL (ty, v, _, _) => (type_value_size ty, value_size v)
    | INR (INL (fields, field_tvs, _, _)) =>
        (1 + list_size (pair_size (list_size char_size) type_value_size)
               field_tvs,
         list_size (pair_size (list_size char_size) value_size) fields)
    | INR (INR (INL (vs, _, tv, _))) =>
        (type_value_size tv, list_size value_size vs)
    | INR (INR (INR (INL (kvs, _, tv, _)))) =>
        (type_value_size tv, list_size (pair_size (K 0) value_size) kvs)
    | INR (INR (INR (INR (vs, tvs, _, _)))) =>
        (1 + list_size type_value_size tvs, list_size value_size vs))`
  >> rw[] >> gvs[AllCaseEqs(), vyperValueTheory.value_size_def,
                 vyperValueTheory.type_value_size_def,
                 vyperASTTheory.base_type_size_def, listTheory.list_size_def,
                 basicSizeTheory.pair_size_def]
End
