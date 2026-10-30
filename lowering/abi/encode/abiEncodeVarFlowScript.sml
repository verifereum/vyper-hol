(* TOP-LEVEL: recursive ABI encoding monotonically allocates SSA names.
   This permits child summaries to protect operands across generated loops. *)
Theory abiEncodeVarFlow
Ancestors
  compileVarFlow abiEncoder context compileEnv
Libs pairLib

val abi_var_rules =
  [compiler_vars_mono_return, compiler_vars_mono_prims, compiler_vars_mono_emit_helpers];

fun abi_var_tac rules =
  rpt (FIRST [CHANGED_TAC (asm_simp_tac (srw_ss()) rules),
    ho_match_mp_tac compiler_vars_mono_bind >> conj_tac >> rpt gen_tac,
    ho_match_mp_tac compiler_vars_mono_ignore_bind >> conj_tac,
    IF_CASES_TAC, gen_tac, strip_tac]);

Theorem compiler_vars_mono_abi_alloc:
  !byte_count. compiler_vars_mono (compile_alloc_buffer byte_count)
Proof
  gen_tac >> rewrite_tac[compile_alloc_buffer_def] >> abi_var_tac abi_var_rules
QED

Theorem compiler_vars_mono_abi_word:
  !dst src. compiler_vars_mono (compile_abi_encode_static dst src)
Proof
  rpt gen_tac >> rewrite_tac[compile_abi_encode_static_def] >> abi_var_tac abi_var_rules
QED

Theorem compiler_vars_mono_abi_static_info:
  !dst src info. compiler_vars_mono (compile_abi_encode_static_info dst src info)
Proof
  rpt gen_tac >> Cases_on `info` >> simp_tac (srw_ss()) [compile_abi_encode_static_info_def] >>
  abi_var_tac (compiler_vars_mono_abi_word :: abi_var_rules)
QED

Theorem compiler_vars_mono_abi_static =
  CONJ compiler_vars_mono_abi_word compiler_vars_mono_abi_static_info;

Theorem compiler_vars_mono_abi_static_loop:
  !dst src info abi_size mem_size len_op.
    compiler_vars_mono (compile_abi_encode_dyn_static_loop dst src info abi_size mem_size len_op)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_abi_encode_dyn_static_loop_def, LET_THM] >>
  abi_var_tac (compiler_vars_mono_abi_alloc :: CONJUNCTS compiler_vars_mono_abi_static @ abi_var_rules)
QED

Theorem compiler_vars_mono_abi_encode:
  (!dst src info is_dyn head_offset dyn_ptr.
    compiler_vars_mono (compile_abi_encode_child dst src info is_dyn head_offset dyn_ptr)) /\
  (!dst src info. compiler_vars_mono (compile_abi_encode_to_buf dst src info)) /\
  (!dst src elems src_offset head_offset dyn_ptr.
    compiler_vars_mono (compile_abi_encode_complex_elems dst src elems src_offset head_offset dyn_ptr)) /\
  (!dst src info abi_size mem_size len_op.
    compiler_vars_mono (compile_abi_encode_dyn_loop dst src info abi_size mem_size len_op))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  simp_tac (srw_ss()) [Once compile_abi_encode_child_def, LET_THM] >>
  abi_var_tac (compiler_vars_mono_abi_alloc :: compiler_vars_mono_abi_static_loop ::
    CONJUNCTS compiler_vars_mono_abi_static @ abi_var_rules) >>
  first_x_assum irule >> fs[] >>
  rename1 `?other. actual_alloc.buf_operand = other.buf_operand` >>
  qexists_tac `actual_alloc` >> simp[]
QED

Theorem compile_abi_encode_next_var:
  !dst src info cs op cs'.
    compile_abi_encode_to_buf dst src info cs = (op,cs') ==>
    cs.cs_next_var <= cs'.cs_next_var
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`dst`, `src`, `info`] (cj 2 compiler_vars_mono_abi_encode)) >>
  DISCH_TAC >> drule_all compiler_vars_mono_result >> simp[]
QED
