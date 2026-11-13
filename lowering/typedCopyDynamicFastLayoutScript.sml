(* Compiler-only elimination of the flat dynamic payload tail. *)
Theory typedCopyDynamicFastLayout
Ancestors typedCopyDynamicLayout immutableCopyExecution placeMemoryCodeLayout

Theorem compile_copy_dynarray_fast_tail_layout:
 !len stride dst src sa sb.
 (do data_sz <- emit_op MUL [Var len; Lit (n2w stride)];
     compile_copy_memory_dynamic (Var dst) (Var src) data_sz od) sa = ((),sb) ==>
 ?kreg sm.
 emit_op MUL [Var len; Lit (n2w stride)] sa = (Var kreg,sm) /\
 compile_copy_memory_dynamic (Var dst) (Var src) (Var kreg) sm = ((),sb)
Proof
 rpt gen_tac >> simp[Once immutable_comp_bind_cases] >> strip_tac >>
 imp_res_tac placeMemoryCodeLayoutTheory.emit_op_next_var >> gvs[] >>
 metis_tac[]
QED
