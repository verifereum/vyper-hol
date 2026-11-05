Theory bodyPtrSubscriptTemporalProbe
Ancestors
  vyperState vyperTypeSystem exprLowering context compileEnv vyperAST

(* Retaining a memory aggregate does not inspect its annotation. *)
Theorem conditional_dynamic_memory_view:
  place_type_value cx (MemoryPlace id path) es =
    (INL (ArrayTV tv (Dynamic n)), es) ==>
  conditional_result cx (PlaceR (MemoryPlace id path)) es =
    (INL (PlaceR (MemoryPlace id path)), es)
Proof
  simp[conditional_result_def, bind_def, return_def]
QED

Theorem unequal_dynamic_array_layout:
  ~same_memory_layout cenv
    (ArrayT (BaseT (UintT 256)) (Dynamic 1))
    (ArrayT (BaseT (UintT 256)) (Dynamic 2))
Proof
  simp[same_memory_layout_def, type_memory_bytes_def]
QED

(* IfExp annotations do not permit arm widening: both annotated arm
   types must be exactly the conditional type, even in an unused arm. *)
Theorem conditional_arm_annotations:
  well_typed_expr env (IfExp ty cond a b) ==>
  expr_type a = ty /\ expr_type b = ty
Proof
  simp[well_typed_expr_def]
QED

Theorem narrow_array_name_cannot_widen:
  ~well_typed_expr env
    (IfExp (ArrayT (BaseT (UintT 256)) (Dynamic 2)) cond
      (Name (ArrayT (BaseT (UintT 256)) (Dynamic 1)) id) other)
Proof
  simp[well_typed_expr_def, expr_type_def]
QED

Theorem dynamic_array_arm_materializes:
  compile_ifexp_arm cenv
    (ArrayT (BaseT (UintT 256)) (Dynamic 2))
    (ArrayT (BaseT (UintT 256)) (Dynamic 1)) vv =
  do tmp <- compile_alloc_buffer
       (type_memory_bytes cenv (ArrayT (BaseT (UintT 256)) (Dynamic 2)));
     src <- unwrap_value cenv vv;
     compile_store_memory cenv src tmp.buf_operand
       (ArrayT (BaseT (UintT 256)) (Dynamic 2))
       (ArrayT (BaseT (UintT 256)) (Dynamic 1));
     comp_return tmp.buf_operand
  od
Proof
  simp[compile_ifexp_arm_def, unequal_dynamic_array_layout, is_word_type_def]
QED

Theorem dynamic_array_name_arm_aliases:
  compile_ifexp_arm cenv (ArrayT (BaseT (UintT 256)) (Dynamic n))
    (lowered_value_type cenv
      (Name (ArrayT (BaseT (UintT 256)) (Dynamic n)) id)) vv =
  unwrap_value cenv vv
Proof
  simp[compile_ifexp_arm_def, lowered_value_type_def, expr_type_def,
       same_memory_layout_def, punnable_def]
QED

Theorem narrow_variable_cannot_annotate_wide:
  FLOOKUP env.var_types id =
    SOME (ArrayT (BaseT (UintT 256)) (Dynamic 1)) ==>
  ~well_typed_expr env (Name (ArrayT (BaseT (UintT 256)) (Dynamic 2)) id)
Proof
  simp[well_typed_expr_def]
QED

(* Diagnostic conclusion (not a universal temporal transport theorem):

   The proposed named dynamic-array widening is EXCLUDED.  The IfExp rule
   requires BOTH arm annotations to equal its result annotation, regardless
   of the condition's value.  Annotating the narrow variable as wide also
   fails the exact env.var_types lookup required by Name typing.  The actual
   compiler passes ret_ty = expr_type (IfExp ...) and each arm's
   lowered_value_type (exprLowering:2942-2959); Name's lowered type is its
   annotation, so the permitted equal-bound named array case aliases.

   Remaining aggregate audit: punnable_def recurses through arrays and
   tuples (equal element/member byte sizes), and defaults to true for other
   destinations, including structs and bytelike types. same_memory_layout
   additionally requires equal total byte size. Thus a wider top-level
   array/string/bytes capacity can require materialization, but Name,
   Subscript, Attribute, Pop and IfExp retain their annotated lowered types.
   The only lowered_value_type exceptions (exprLowering:161-175) are string
   and dynamic-bytes literals, AbiEncode, and internal calls. Their result
   forms/typing/representation must be checked before claiming a general
   retained-view/copy exclusion. In particular calls' declared return type
   may differ from the expression annotation; this diagnostic does not
   establish their temporal representation contract.

   No typed retained-view/copy mismatch has been established here. The
   narrow-array candidate therefore does not authorize a post-pop divergence
   claim or a counterexample to the frozen theorem. General retained-place
   identity, Pop transport, and counted selector execution remain open.
*)
