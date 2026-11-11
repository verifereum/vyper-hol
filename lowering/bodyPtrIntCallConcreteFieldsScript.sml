(* Consumer-facing publication of concrete counted field copying.
 *
 * Reuse intcall_tuple_fields_conditional and
 * intcall_struct_fields_conditional directly: wrappers would duplicate
 * their contracts.  Both expose the recursive child-store effect as the
 * only operational correctness premise; byte-offset execution is proved
 * internally via intcall_field_offset_counted.
 *
 * Tuple annotations and physical semantic types remain separate lists.
 * Whole tuple source footprint is its physical size sum.  Struct layout
 * is identical on both sides, with full-table lookup/size agreement.
 * Both interfaces retain strict containing source/destination endpoints,
 * capacity coverage and disjointness.  Child source numeric bounds use
 * val_footprint, not type capacity (in particular for bytes/string).
 *
 * Conclusions include counted execution, exact terminal cursor, robust
 * destination representation, ambient state, old-variable value/provenance/
 * operand-taint preservation, and exterior byte and memory-taint equality.
 * Array execution and discharge of the child callback are not claimed here.
 *)
Theory bodyPtrIntCallConcreteFields
Ancestors bodyPtrIntCallTupleFields bodyPtrIntCallStructFields
