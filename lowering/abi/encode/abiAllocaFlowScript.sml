(* TOP-LEVEL: every recursive ABI encoding branch preserves predicates on
   allocations whenever those predicates accept newly generated output names.
   This covers nested arrays, dynamic tuples and structs, independently of
   the concrete source values. Helpers cover the nonrecursive compiler pieces. *)
Theory abiAllocaFlow
Ancestors
  compileAllocaFlow abiEncoder context compileEnv
Libs pairLib

val abi_alloca_rules =
  [compiler_alloca_pred_return, compiler_alloca_pred_prims,
   compiler_alloca_pred_emit_op, compiler_alloca_pred_emit_void, compiler_alloca_pred_emit_inst];

fun abi_alloca_tac rules =
  rpt (FIRST [CHANGED_TAC (asm_simp_tac (srw_ss()) rules),
    ho_match_mp_tac compiler_alloca_pred_bind >> conj_tac >> rpt gen_tac,
    ho_match_mp_tac compiler_alloca_pred_ignore_bind >> conj_tac,
    IF_CASES_TAC, gen_tac, strip_tac]);

Theorem compiler_alloca_pred_abi_alloc:
  !P byte_count. compiler_alloca_pred P (compile_alloc_buffer byte_count)
Proof
  rpt gen_tac >> rewrite_tac[compile_alloc_buffer_def] >> abi_alloca_tac abi_alloca_rules
QED

Theorem compiler_alloca_pred_abi_word:
  !P dst src. compiler_alloca_pred P (compile_abi_encode_static dst src)
Proof
  rpt gen_tac >> rewrite_tac[compile_abi_encode_static_def] >> abi_alloca_tac abi_alloca_rules
QED

Theorem compiler_alloca_pred_abi_static_info:
  !P dst src info. compiler_alloca_pred P (compile_abi_encode_static_info dst src info)
Proof
  rpt gen_tac >> Cases_on `info` >> simp_tac (srw_ss()) [compile_abi_encode_static_info_def] >>
  abi_alloca_tac (compiler_alloca_pred_abi_word :: abi_alloca_rules)
QED

Theorem compiler_alloca_pred_abi_static_loop:
  !P dst src info abi_size mem_size len_op.
    compiler_alloca_pred P (compile_abi_encode_dyn_static_loop dst src info abi_size mem_size len_op)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_abi_encode_dyn_static_loop_def, LET_THM] >>
  abi_alloca_tac (compiler_alloca_pred_abi_alloc :: compiler_alloca_pred_abi_static_info :: abi_alloca_rules)
QED

Theorem compiler_alloca_pred_abi_encode:
  !P.
    (!dst src info is_dyn head_offset dyn_ptr.
      compiler_alloca_pred P (compile_abi_encode_child dst src info is_dyn head_offset dyn_ptr)) /\
    (!dst src info. compiler_alloca_pred P (compile_abi_encode_to_buf dst src info)) /\
    (!dst src elems src_offset head_offset dyn_ptr.
      compiler_alloca_pred P (compile_abi_encode_complex_elems dst src elems src_offset head_offset dyn_ptr)) /\
    (!dst src info abi_size mem_size len_op.
      compiler_alloca_pred P (compile_abi_encode_dyn_loop dst src info abi_size mem_size len_op))
Proof
  gen_tac >> ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  simp_tac (srw_ss()) [Once compile_abi_encode_child_def, LET_THM] >>
  abi_alloca_tac (compiler_alloca_pred_abi_alloc :: compiler_alloca_pred_abi_static_loop ::
    compiler_alloca_pred_abi_word :: abi_alloca_rules) >>
  first_x_assum irule >> fs[] >>
  rename1 `?other. actual_alloc.buf_operand = other.buf_operand` >>
  qexists_tac `actual_alloc` >> simp[]
QED

Theorem compile_abi_encode_alloca_code:
  !P dst src info cs op cs'.
    compile_abi_encode_to_buf dst src info cs = (op,cs') /\ compiler_alloca_code P cs /\
    (!id ops n. cs.cs_next_var <= n ==> P (mk_inst id ALLOCA ops ["%" ++ toString n])) ==>
    compiler_alloca_code P cs'
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`dst`, `src`, `info`] (cj 2 (Q.SPEC `P` compiler_alloca_pred_abi_encode))) >>
  simp_tac bool_ss [compiler_alloca_pred_def] >> strip_tac >>
  qpat_x_assum `!cs. _` (qspec_then `cs` mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive ABI allocation-output flow: " ^ name)
  end) (DB.thms "abiAllocaFlow")
