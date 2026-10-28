(* TOP-LEVEL: every recursive ABI encoder extends its compile state.
   This supplies the actual block-containment premises needed to compose
   encoding fragments in the final containing function, including loops. *)
Theory abiEncoderStructure
Ancestors
  fragExec abiEncoder context compileEnv emitHelper
Libs pairLib

val append_rules =
  [cs_appends_prims, cs_appends_emit_helpers, cs_appends_return];

fun append_tac rules =
  rpt (FIRST
    [CHANGED_TAC (asm_simp_tac (srw_ss()) rules),
     ho_match_mp_tac cs_appends_bind >> conj_tac >> rpt gen_tac,
     ho_match_mp_tac cs_appends_ignore_bind >> conj_tac,
     IF_CASES_TAC,
     gen_tac,
     strip_tac]);

Theorem cs_appends_compile_alloc_buffer:
  !region_size. cs_appends (compile_alloc_buffer region_size)
Proof
  gen_tac >> rewrite_tac[compile_alloc_buffer_def] >> append_tac append_rules
QED

Theorem cs_appends_compile_abi_encode_static:
  !dst src. cs_appends (compile_abi_encode_static dst src)
Proof
  rpt gen_tac >> rewrite_tac[compile_abi_encode_static_def] >> append_tac append_rules
QED

Theorem cs_appends_compile_abi_encode_static_info:
  !dst src info. cs_appends (compile_abi_encode_static_info dst src info)
Proof
  rpt gen_tac >> Cases_on `info` >>
  simp_tac (srw_ss()) [compile_abi_encode_static_info_def] >>
  append_tac (cs_appends_compile_abi_encode_static :: append_rules)
QED

Theorem cs_appends_compile_abi_encode_dyn_static_loop:
  !dst src elem_info elem_abi_sz elem_mem_sz len_op.
    cs_appends
      (compile_abi_encode_dyn_static_loop dst src elem_info elem_abi_sz elem_mem_sz len_op)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_abi_encode_dyn_static_loop_def, LET_THM] >>
  append_tac (cs_appends_compile_alloc_buffer ::
    cs_appends_compile_abi_encode_static_info :: append_rules)
QED

Theorem cs_appends_compile_abi_encode:
  (!dst child_ptr info is_dyn static_ofst dyn_ptr.
    cs_appends (compile_abi_encode_child dst child_ptr info is_dyn static_ofst dyn_ptr)) /\
  (!dst src info. cs_appends (compile_abi_encode_to_buf dst src info)) /\
  (!dst src elems src_ofst head_ofst dyn_ptr.
    cs_appends (compile_abi_encode_complex_elems dst src elems src_ofst head_ofst dyn_ptr)) /\
  (!dst src elem_info elem_abi_sz elem_mem_sz len_op.
    cs_appends (compile_abi_encode_dyn_loop dst src elem_info elem_abi_sz elem_mem_sz len_op))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  simp_tac (srw_ss()) [Once compile_abi_encode_child_def, LET_THM] >>
  append_tac (cs_appends_compile_alloc_buffer :: cs_appends_compile_abi_encode_static ::
    cs_appends_compile_abi_encode_dyn_static_loop :: append_rules) >>
  first_x_assum irule >> fs[] >>
  rename1 `?other. actual_alloc.buf_operand = other.buf_operand` >>
  qexists_tac `actual_alloc` >> simp[]
QED

Theorem compile_abi_encode_extends:
  !dst src info cs op cs'.
    compile_abi_encode_to_buf dst src info cs = (op,cs') ==> cs_extends cs cs'
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`dst`, `src`, `info`] (cj 2 cs_appends_compile_abi_encode)) >>
  simp[cs_appends_def] >> disch_then drule >> simp[]
QED

Theorem compile_abi_encode_code_split:
  !dst src info cs op mid cs' func.
    compile_abi_encode_to_buf dst src info cs = (op,mid) /\
    cs_extends mid cs' /\ fn_has_code cs cs' func ==>
    fn_has_code cs mid func /\ fn_has_code mid cs' func
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends cs mid` by (drule_all compile_abi_encode_extends >> simp[]) >>
  irule fn_has_code_split >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI compiler structure theorem: " ^ name)
  end)
  (DB.thms "abiEncoderStructure")
