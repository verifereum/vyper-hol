(*
 * Layout of struct, tuple and array literals (#636)
 *
 * Under expr_body_pre, StructLit and MakeArray compile to an ALLOCA of the
 * literal's size followed by compile_struct_lit, compile_make_tuple or
 * compile_make_array, and the evaluated types and field sizes add up to
 * that size (expr_sim_inv's struct fields clause gives the sizes).  For
 * empty(T): the buffer size, and when a zeroed buffer holds the default.
 *
 * TOP-LEVEL:
 *   struct_literal_decl_types, struct_literal_layout_types — a well-typed
 *     struct literal matches the declared fields and ce_struct_fields
 *   compile_struct_literal_inv, compile_tuple_literal_inv,
 *   compile_array_literal_inv — the compiled literal's shape
 *   struct_literal_evaluated_layout, make_tuple_evaluated_layout,
 *   make_array_evaluated_layout — evaluated types and buffer size
 *   compile_struct_lit_as_tuple — compile_struct_lit is compile_make_tuple
 *     on the field values
 *   empty_type_buffer_size, empty_type_default_memory — empty(T)
 *
 * Helpers: struct_layout_lookup, type_memory_size_aligned, and the per-case
 *   compile_* lemmas behind the _inv ones.  expr_sim_inv_memory_size
 *   (type_memory_bytes = type_memory_size under expr_sim_inv) is in
 *   exprSimHyps.
 *)
Theory exprSimAggregateLayout
Ancestors
  exprSimSource
  exprSimHypsDefs
  structFieldsProps vyperTypeSystem valueEncoding valueEncodingProps compileEnv
  exprSimHyps exprSimBufferEmpty vyperValue list pair finite_map vfmConstants
  exprCallbackContracts exprLowering exprSimWordBuiltins

(* A variable's type takes memory: it takes a storage slot
   (assignable_type_slot_size_pos), so it takes memory. *)
Theorem expr_sim_inv_memory_bytes_pos:
  !cenv ty cx env es.
    expr_sim_inv cenv cx env es /\
    assignable_type (get_tenv cx) ty ==>
    0 < type_memory_bytes cenv ty
Proof
  cheat
QED


Theorem type_memory_size_aligned:
  (!tv. type_memory_size tv MOD 32 = 0) /\
  (!tvs. type_memory_size_list tvs MOD 32 = 0) /\
  (!fields. type_memory_size_fields fields MOD 32 = 0)
Proof
  cheat
QED

Theorem struct_layout_lookup:
  !fields kes i tenv tv.
    MAP FST fields = MAP FST kes /\
    MAP (FST o SND) fields = MAP (expr_type o SND) kes /\
    ALL_DISTINCT (MAP FST fields) /\ i < LENGTH kes /\
    EVERY (\(name,ty,sz). !tv. evaluate_type tenv ty = SOME tv ==>
                              sz = type_memory_size tv) fields /\
    evaluate_type tenv (expr_type (SND (EL i kes))) = SOME tv ==>
    ?sz. ALOOKUP fields (FST (EL i kes)) =
           SOME (expr_type (SND (EL i kes)),sz) /\
         sz = type_memory_size tv
Proof
  cheat
QED

Theorem compile_struct_lit_as_tuple:
  !fields off.
    EVERY (\(name,e).
      ALOOKUP (get_struct_fields ce.ce_struct_fields
        (case ty of StructT nsid => nsid_to_string nsid | _ => "")) name =
      SOME (expr_type e,type_memory_bytes ce (expr_type e))) fields ==>
    compile_struct_lit cfn ce ty fields buf off =
    compile_make_tuple cfn ce (MAP SND fields) buf off
Proof
  cheat
QED

Theorem struct_literal_lookup_types:
  expr_body_pre ce cx env (StructLit ann nsid kes) es ==>
  EVERY (\(name,e).
    ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) name =
      SOME (expr_type e,type_memory_bytes ce (expr_type e))) kes
Proof
  cheat
QED

Theorem empty_type_buffer_size:
  !cenv cx env es ty tv.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    (if is_bytestring_type ty \/
        (case ty of ArrayT _ (Dynamic _) => T | _ => F)
     then 32 <= type_memory_bytes cenv ty
     else type_memory_bytes cenv ty MOD 32 = 0)
Proof
  cheat
QED

Theorem empty_type_default_memory:
  !cenv cx env es ty tv off mem.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    (if is_bytestring_type ty \/
        (case ty of ArrayT _ (Dynamic _) => T | _ => F)
     then mem_word_at off mem = 0w
     else mem_bytes_at off (type_memory_bytes cenv ty) mem =
            REPLICATE (type_memory_bytes cenv ty) 0w) ==>
    val_in_memory tv (default_value tv) off mem
Proof
  cheat
QED

Theorem struct_child_compile:
  !ann nsid fields ce buf sa.
    compile_struct_lit
      (expr_child_callback (expr_size (StructLit ann nsid fields)) compile_expr)
      ce (StructT nsid) fields buf 0 sa =
    compile_struct_lit compile_expr ce (StructT nsid) fields buf 0 sa
Proof
  cheat
QED

Theorem compile_struct_literal:
  !ce ty ann nsid fields sa.
    compile_expr ce ty (StructLit ann nsid fields) sa =
    let (ba,sm) = compile_alloc_buffer
      (SUM (MAP (SND o SND)
        (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa in
    let (u,sb) = compile_struct_lit compile_expr ce (StructT nsid)
                  fields ba.buf_operand 0 sm in
    (LocatedValue (expr_type (StructLit ann nsid fields)) (base_ptr ba),sb)
Proof
  cheat
QED

Theorem compile_struct_literal_inv:
  !ce ty ann nsid fields sa vv sb.
    compile_expr ce ty (StructLit ann nsid fields) sa = (vv,sb) ==>
    ?ba sm u.
      compile_alloc_buffer
        (SUM (MAP (SND o SND)
          (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa = (ba,sm) /\
      compile_struct_lit compile_expr ce (StructT nsid) fields ba.buf_operand 0 sm = (u,sb) /\
      vv = LocatedValue (expr_type (StructLit ann nsid fields)) (base_ptr ba)
Proof
  cheat
QED

Theorem evaluated_struct_layout:
  evaluate_type tenv (StructT nsid) = SOME tv ==>
  ?args tvs. FLOOKUP tenv nsid = SOME (StructArgs args) /\
    OPT_MMAP (evaluate_type tenv) (MAP SND args) = SOME tvs /\
    tv = StructTV (ZIP (MAP FST args,tvs))
Proof
  cheat
QED

Theorem struct_literal_evaluated_layout:
  expr_body_pre ce cx env (StructLit ann nsid fields) es ==>
  ?tvs.
    OPT_MMAP (evaluate_type (get_tenv cx))
      (MAP expr_type (MAP SND fields)) = SOME tvs /\
    type_memory_size_list tvs =
      SUM (MAP (SND o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))) /\
    evaluate_type (get_tenv cx) (StructT nsid) =
      SOME (StructTV (ZIP (MAP FST fields,tvs)))
Proof
  cheat
QED

Theorem make_tuple_evaluated_layout:
  expr_body_pre ce cx env (Builtin ann (MakeArray NONE bnd) args) es ==>
  ?tvs. ann = TupleT (MAP expr_type args) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
    evaluate_type (get_tenv cx) ann = SOME (TupleTV tvs) /\
    SUM (MAP (type_memory_bytes ce o expr_type) args) = type_memory_size_list tvs
Proof
  cheat
QED

Theorem make_array_evaluated_layout:
  expr_body_pre ce cx env (Builtin ann (MakeArray (SOME et) bnd) args) es ==>
  ?tv. ann = ArrayT et bnd /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    evaluate_type (get_tenv cx) ann = SOME (ArrayTV tv bnd) /\
    EVERY (\e. expr_type e = et) args /\
    type_memory_bytes ce et = type_memory_size tv /\
    (if (case bnd of Dynamic _ => T | _ => F) then 32 else 0) +
      LENGTH args * type_memory_size tv <= type_memory_bytes ce ann
Proof
  cheat
QED

Theorem tuple_child_compile:
  compile_make_tuple (expr_child_callback (list_size expr_size args) compile_expr)
    ce args buf off sa = compile_make_tuple compile_expr ce args buf off sa
Proof
  cheat
QED

Theorem array_child_compile:
  compile_make_array (expr_child_callback (list_size expr_size args) compile_expr)
    ce args et sz lw buf sa = compile_make_array compile_expr ce args et sz lw buf sa
Proof
  cheat
QED

Theorem make_array_not_names[local]:
  !args topt bnd. ~names_builtin (MakeArray topt bnd) args
Proof
  cheat
QED

Theorem compile_tuple_literal:
  compile_expr ce ty (Builtin ann (MakeArray NONE bnd) args) sa =
  let (ba,sm) = compile_alloc_buffer
    (SUM (MAP (type_memory_bytes ce o expr_type) args)) sa in
  as_ptr_val ann LocMemory (compile_make_tuple compile_expr ce args ba.buf_operand 0 sm)
Proof
  cheat
QED

Theorem compile_array_literal:
  compile_expr ce ty (Builtin ann (MakeArray (SOME et) bnd) args) sa =
  let (ba,sm) = compile_alloc_buffer (type_memory_bytes ce ann) sa in
  as_ptr_val ann LocMemory (compile_make_array compile_expr ce args et
    (type_memory_bytes ce et) (case bnd of Dynamic _ => T | _ => F) ba.buf_operand sm)
Proof
  cheat
QED

Theorem compile_tuple_literal_inv:
  compile_expr ce ty (Builtin ann (MakeArray NONE bnd) args) sa = (vv,sb) ==>
  ?ba sm u.
    compile_alloc_buffer (SUM (MAP (type_memory_bytes ce o expr_type) args)) sa = (ba,sm) /\
    compile_make_tuple compile_expr ce args ba.buf_operand 0 sm = (u,sb) /\
    vv = LocatedValue ann (mk_ptr u LocMemory)
Proof
  cheat
QED

Theorem compile_array_literal_inv:
  compile_expr ce ty (Builtin ann (MakeArray (SOME et) bnd) args) sa = (vv,sb) ==>
  ?ba sm u.
    compile_alloc_buffer (type_memory_bytes ce ann) sa = (ba,sm) /\
    compile_make_array compile_expr ce args et (type_memory_bytes ce et)
      (case bnd of Dynamic _ => T | _ => F) ba.buf_operand sm = (u,sb) /\
    vv = LocatedValue ann (mk_ptr u LocMemory)
Proof
  cheat
QED
