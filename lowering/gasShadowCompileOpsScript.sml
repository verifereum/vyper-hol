(* Checked callback-free boundary interface for the three open compiler bodies.
   Callback-bearing helpers remain the responsibility of the helper proofs.

   Expression body: Literal/Name and Env use Literal; modular Name fast paths
   use Names; Pop uses CallSupport after the callback-bearing target traversal.
   Subscript/target traversal use Membership with the Context ptr_load boundary;
   attribute traversal only emits ADD. Struct/tuple/array construction use
   Context store_memory and Convert unwrap_value. Concat only emits/copies.

   Builtin body: arithmetic and empty/len use Arith; invert uses Names;
   negation uses Convert; hashing/method-id use BuiltinHash; modular, block,
   decimal, EC and wei operations use BuiltinScalar; slice/extract32 use
   BuiltinBytes; uint2str uses BuiltinStrings. Env is the sole directed
   GAS-to-GASPRICE boundary (Literal). Acc only uses lower_value and emissions.
   Type builtin body: conversion uses Convert, empty uses Arith,
   ABI staging/encode/decode use BuiltinAbi, extract32 uses BuiltinBytes.

   Call transitive edges: internal staging and store_multi_results are in
   CallSupport, emit_multi_op in Emit. External-call finalization is in
   External; keyword materialization in Convert. Creation snapshots are in
   CallSupport, constructor tuple stores use its extcall_store_values, ABI
   encoding uses Abi. All reachable raw-call stages are in BuiltinSystem;
   all reachable creation stages and their result checks are in BuiltinCreate.
   Dynamic allocation/copy and select are existing Context/Arith boundaries.
   No legacy raw-create or convenience creation wrapper is called here.
*)
Theory gasShadowCompileOps
Ancestors
  gasShadowCompileBase gasShadowCompilePure
  gasShadowCompileContext gasShadowCompileArith gasShadowCompileAbi
  gasShadowCompileMembership gasShadowCompileLiteral gasShadowCompileConvert
  gasShadowCompileCallSupport gasShadowCompileExternal gasShadowCompileNames
  gasShadowCompileBuiltinHash gasShadowCompileBuiltinScalar
  gasShadowCompileBuiltinBytes gasShadowCompileBuiltinStrings
  gasShadowCompileBuiltinAbi gasShadowCompileEmit
  gasShadowCompileBuiltinSystem gasShadowCompileBuiltinCreate
