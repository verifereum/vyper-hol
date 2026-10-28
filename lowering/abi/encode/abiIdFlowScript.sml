(* TOP-LEVEL: every native recursive ABI compiler action preserves fresh
   instruction-ID history and grows its ID counter. No runtime allocation
   cache ordering is assumed. Helpers cover the nonrecursive compiler pieces. *)
Theory abiIdFlow
Ancestors
  compileIdFlow abiEncoder context compileEnv
Libs pairLib

val abi_id_rules =
  [compiler_id_flow_return, compiler_id_flow_prims, compiler_id_flow_emit_helpers];

fun abi_id_tac rules =
  rpt (FIRST [CHANGED_TAC (asm_simp_tac (srw_ss()) rules),
    ho_match_mp_tac compiler_id_flow_bind >> conj_tac >> rpt gen_tac,
    ho_match_mp_tac compiler_id_flow_ignore_bind >> conj_tac,
    IF_CASES_TAC, gen_tac, strip_tac]);

Theorem compiler_id_flow_abi_alloc:
  !byte_count. compiler_id_flow (compile_alloc_buffer byte_count)
Proof
  gen_tac >> rewrite_tac[compile_alloc_buffer_def] >> abi_id_tac abi_id_rules
QED

Theorem compiler_id_flow_abi_word:
  !dst src. compiler_id_flow (compile_abi_encode_static dst src)
Proof
  rpt gen_tac >> rewrite_tac[compile_abi_encode_static_def] >> abi_id_tac abi_id_rules
QED

Theorem compiler_id_flow_abi_static_info:
  !dst src info. compiler_id_flow (compile_abi_encode_static_info dst src info)
Proof
  rpt gen_tac >> Cases_on `info` >> simp_tac (srw_ss()) [compile_abi_encode_static_info_def] >>
  abi_id_tac (compiler_id_flow_abi_word :: abi_id_rules)
QED

Theorem compiler_id_flow_abi_static_loop:
  !dst src info abi_size mem_size len_op.
    compiler_id_flow (compile_abi_encode_dyn_static_loop dst src info abi_size mem_size len_op)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_abi_encode_dyn_static_loop_def, LET_THM] >>
  abi_id_tac (compiler_id_flow_abi_alloc :: compiler_id_flow_abi_static_info :: abi_id_rules)
QED

Theorem compiler_id_flow_abi_encode:
  (!dst src info is_dyn head_offset dyn_ptr.
    compiler_id_flow (compile_abi_encode_child dst src info is_dyn head_offset dyn_ptr)) /\
  (!dst src info. compiler_id_flow (compile_abi_encode_to_buf dst src info)) /\
  (!dst src elems src_offset head_offset dyn_ptr.
    compiler_id_flow (compile_abi_encode_complex_elems dst src elems src_offset head_offset dyn_ptr)) /\
  (!dst src info abi_size mem_size len_op.
    compiler_id_flow (compile_abi_encode_dyn_loop dst src info abi_size mem_size len_op))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  simp_tac (srw_ss()) [Once compile_abi_encode_child_def, LET_THM] >>
  abi_id_tac (compiler_id_flow_abi_alloc :: compiler_id_flow_abi_static_loop ::
    compiler_id_flow_abi_word :: abi_id_rules) >>
  first_x_assum irule >> fs[] >>
  rename1 `?other. actual_alloc.buf_operand = other.buf_operand` >>
  qexists_tac `actual_alloc` >> simp[]
QED

Theorem compile_abi_encode_id_flow:
  !dst src info cs ret cs'.
    compile_abi_encode_to_buf dst src info cs = (ret,cs') ==>
    cs.cs_next_id <= cs'.cs_next_id /\ (compiler_id_history cs ==> compiler_id_history cs')
Proof
  rpt gen_tac >> DISCH_TAC >>
  qspecl_then [`compile_abi_encode_to_buf dst src info`, `cs`, `ret`, `cs'`]
    mp_tac compiler_id_flow_result >> simp[compiler_id_flow_abi_encode]
QED

Theorem compile_abi_child_id_flow:
  !dst src info is_dyn head_offset dyn_ptr cs ret cs'.
    compile_abi_encode_child dst src info is_dyn head_offset dyn_ptr cs = (ret,cs') ==>
    cs.cs_next_id <= cs'.cs_next_id /\ (compiler_id_history cs ==> compiler_id_history cs')
Proof
  rpt gen_tac >> DISCH_TAC >>
  qspecl_then [`compile_abi_encode_child dst src info is_dyn head_offset dyn_ptr`, `cs`, `ret`, `cs'`]
    mp_tac compiler_id_flow_result >> simp[compiler_id_flow_abi_encode]
QED

Theorem compile_abi_fields_id_flow:
  !dst src entries src_offset head_offset dyn_ptr cs ret cs'.
    compile_abi_encode_complex_elems dst src entries src_offset head_offset dyn_ptr cs = (ret,cs') ==>
    cs.cs_next_id <= cs'.cs_next_id /\ (compiler_id_history cs ==> compiler_id_history cs')
Proof
  rpt gen_tac >> DISCH_TAC >>
  qspecl_then [`compile_abi_encode_complex_elems dst src entries src_offset head_offset dyn_ptr`, `cs`, `ret`, `cs'`]
    mp_tac compiler_id_flow_result >> simp[compiler_id_flow_abi_encode]
QED

Theorem compile_abi_loop_id_flow:
  !dst src info abi_size mem_size len_op cs ret cs'.
    compile_abi_encode_dyn_loop dst src info abi_size mem_size len_op cs = (ret,cs') ==>
    cs.cs_next_id <= cs'.cs_next_id /\ (compiler_id_history cs ==> compiler_id_history cs')
Proof
  rpt gen_tac >> DISCH_TAC >>
  qspecl_then [`compile_abi_encode_dyn_loop dst src info abi_size mem_size len_op`, `cs`, `ret`, `cs'`]
    mp_tac compiler_id_flow_result >> simp[compiler_id_flow_abi_encode]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive ABI instruction ID flow: " ^ name)
  end) (DB.thms "abiIdFlow")
