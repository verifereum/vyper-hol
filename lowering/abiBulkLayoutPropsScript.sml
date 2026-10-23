(* Canonical bytes after a bulk copy, not execution of the copy instruction.
   The no-clamp/static tests select the lowering branch; the structural
   compatibility contract supplies the semantic layout and size agreement. *)
Theory abiBulkLayoutProps
Ancestors
  abiStaticReverseProps abiStaticAggregateProps abiStaticLayoutProps
  exprLowering abiEncoder valueEncoding vyperTyping vyperABI compileEnv

Theorem abi_bulk_layout_sizes:
  static_layout_compatible cenv tenv ty tv ==>
  evaluate_type tenv ty = SOME tv /\
  ~is_dynamic (vyper_to_abi_type tenv ty) /\
  ~is_abi_dynamic cenv.ce_struct_fields ty /\
  static_length (vyper_to_abi_type tenv ty) = type_memory_bytes cenv ty /\
  type_memory_size tv = type_memory_bytes cenv ty
Proof
  metis_tac[static_layout_compatible_properties]
QED

Theorem abi_bulk_encoding_length:
  static_layout_compatible cenv tenv ty tv /\
  value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av ==>
  LENGTH (enc (vyper_to_abi_type tenv ty) av) = type_memory_bytes cenv ty
Proof
  metis_tac[static_typed_encoding_length, static_layout_compatible_properties]
QED

(* di is the actual translated descriptor, not arbitrary DecComplex metadata.
   This is the post-copy representation boundary for each static element.
   Recursive execution must additionally establish source preservation, the
   copied slice, output bounds and compatibility of the actual reachable type. *)
Theorem abi_bulk_copy_canonical_layout:
  di = type_to_abi_dec_info cenv.ce_struct_fields cenv ty /\
  ~dec_info_needs_clamp di /\
  ~is_abi_dynamic cenv.ce_struct_fields ty /\
  static_layout_compatible cenv tenv ty tv /\
  value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av /\
  dst + type_memory_bytes cenv ty <= LENGTH mem /\
  mem_bytes_at dst (type_memory_bytes cenv ty) mem =
    enc (vyper_to_abi_type tenv ty) av ==>
  val_in_memory tv v dst mem
Proof
  rpt strip_tac >>
  drule static_layout_compatible_properties >> strip_tac >>
  irule static_canonical_memory_layout >>
  metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BULK_LAYOUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI bulk layout not kernel closed: " ^ n)
  end) (DB.thms "abiBulkLayoutProps");
