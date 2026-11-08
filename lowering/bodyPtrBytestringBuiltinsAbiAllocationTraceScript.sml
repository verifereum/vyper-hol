Theory bodyPtrBytestringBuiltinsAbiAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsStoreAllocationTrace
          bodyPtrBytestringBuiltinsChildAllocationTrace
          bodyPtrBytestringBuiltinsAbiEncodeAllocationTrace
          bodyPtrBytestringBuiltinsAbiDecodeAllocationTrace builtinAbi exprLowering

Theorem lower_abi_encode_allocation_trace[simp]:
  !ensure mid src info maxlen s.
    allocation_trace s (SND (lower_abi_encode ensure mid src info maxlen s))
Proof
  rpt gen_tac >> Cases_on `mid` >> simp[lower_abi_encode_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem lower_abi_decode_allocation_trace[simp]:
  !data info minsz maxsz outsz s.
    allocation_trace s (SND (lower_abi_decode data info minsz maxsz outsz s))
Proof
  rpt gen_tac >> simp[lower_abi_decode_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_store_abi_tuple_allocation_trace[simp]:
  !cenv buf off vs s.
    allocation_trace s (SND (compile_store_abi_tuple cenv buf off vs s))
Proof
  gen_tac >> Induct_on `vs` >>
  simp[compile_store_abi_tuple_def] >>
  gen_tac >> PairCases_on `h` >> simp[compile_store_abi_tuple_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED
