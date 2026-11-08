(* This source consumer deliberately retains the three child contracts.
   They have not been established for the full recursive expression compiler. *)
Theory bodyPtrBytestringBuiltinsTupleAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsImageTupleHistory exprLowering context
          compileEnv emitHelper list

Theorem compile_make_tuple_allocation_trace:
  !cfn cenv.
  (!ty e s. allocation_trace s (SND (cfn cenv ty e s))) /\
  (!vv s. allocation_trace s (SND (unwrap_value cenv vv s))) /\
  (!v dst ty src_ty s.
    allocation_trace s (SND (compile_store_memory cenv v dst ty src_ty s))) ==>
  !es buf off s. allocation_trace s (SND (compile_make_tuple cfn cenv es buf off s))
Proof
  rpt gen_tac >> strip_tac >> Induct >>
  simp[compile_make_tuple_def, allocation_trace_return] >>
  rpt gen_tac >> irule allocation_trace_bind >> simp[] >>
  rpt gen_tac >> irule allocation_trace_bind >>
  reverse conj_tac >- metis_tac[allocation_trace_emit_op, pairTheory.PAIR] >>
  rpt gen_tac >> simp[] >> irule allocation_trace_bind >> simp[] >>
  rpt gen_tac >> simp[] >> irule allocation_trace_ignore_bind >> simp[]
QED

Theorem compile_make_tuple_protected_tail:
  !cfn cenv.
  (!ty e s. allocation_trace s (SND (cfn cenv ty e s))) /\
  (!vv s. allocation_trace s (SND (unwrap_value cenv vv s))) /\
  (!v dst ty src_ty s.
    allocation_trace s (SND (compile_store_memory cenv v dst ty src_ty s))) ==>
  !es buf off sa result sb k.
  compile_make_tuple cfn cenv es buf off sa = (result,sb) /\
  k < sa.cs_next_var ==>
  (tail_alloc (Var (STRING #"%" (toString k))) sb.cs_current_insts ==>
   tail_alloc (Var (STRING #"%" (toString k))) sa.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_make_tuple_allocation_trace >>
  rpt strip_tac >>
  `allocation_trace sa sb` by metis_tac[pairTheory.SND] >>
  metis_tac[allocation_trace_protected_tail]
QED

Theorem compile_make_tuple_no_protected_tail:
  !cfn cenv.
  (!ty e s. allocation_trace s (SND (cfn cenv ty e s))) /\
  (!vv s. allocation_trace s (SND (unwrap_value cenv vv s))) /\
  (!v dst ty src_ty s.
    allocation_trace s (SND (compile_store_memory cenv v dst ty src_ty s))) ==>
  !es buf off sa result sb k.
  compile_make_tuple cfn cenv es buf off sa = (result,sb) /\
  k < sa.cs_next_var /\
  ~tail_alloc (Var (STRING #"%" (toString k))) sa.cs_current_insts ==>
  ~tail_alloc (Var (STRING #"%" (toString k))) sb.cs_current_insts
Proof
  metis_tac[compile_make_tuple_protected_tail]
QED
