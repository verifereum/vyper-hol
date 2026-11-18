(* The ABI encoder and decoder preserve block-local DALLOCA windows. *)
Theory runtimePeakMemoryAbi
Ancestors
  runtimePeakMemoryCode abiEncoder builtinAbi context compileEnv emitHelper
  venomInst list arithmetic

fun windows_tac thms =
  rpt (FIRST [
    CHANGED_TAC (simp(thms @ [LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
      dalloca_windows_emit_helpers, dalloca_windows_new_block,
      dalloca_windows_fresh, dalloca_windows_return, dalloca_windows_alloc_buffer])),
    gen_tac, irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac,
    COND_CASES_TAC, BasicProvers.TOP_CASE_TAC]);

Theorem dalloca_windows_abi_encode_static[local]:
  preserves_dalloca_windows window (compile_abi_encode_static dst src) /\
  preserves_dalloca_windows window (compile_abi_encode_static_info dst src info) /\
  preserves_dalloca_windows window (compile_abi_zero_pad dst len mask)
Proof
  Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, compile_abi_encode_static_def,
       compile_abi_zero_pad_def] >> rpt conj_tac >> windows_tac []
QED

Theorem dalloca_windows_abi_encode_static_loop[local]:
  preserves_dalloca_windows window
    (compile_abi_encode_dyn_static_loop dst src info abi_sz mem_sz len)
Proof
  simp[compile_abi_encode_dyn_static_loop_def] >>
  windows_tac [dalloca_windows_abi_encode_static]
QED

Theorem dalloca_windows_abi_encode:
  (!dst p info dyn off dp.
     preserves_dalloca_windows window (compile_abi_encode_child dst p info dyn off dp)) /\
  (!dst src info.
     preserves_dalloca_windows window (compile_abi_encode_to_buf dst src info)) /\
  (!dst src elems so ho dp.
     preserves_dalloca_windows window (compile_abi_encode_complex_elems dst src elems so ho dp)) /\
  (!dst src info abi_sz mem_sz len.
     preserves_dalloca_windows window
       (compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  simp[Once compile_abi_encode_child_def] >>
  windows_tac [dalloca_windows_abi_encode_static, dalloca_windows_abi_encode_static_loop] >>
  gvs[] >>
  TRY (first_assum irule >> simp[] >> NO_TAC) >>
  TRY (qexists_tac `x` >> simp[] >> NO_TAC) >>
  TRY (rename1 `SUM (MAP (λ(_3,abi_sz,_4,_5). abi_sz) (item::items))` >>
       qpat_x_assum `!a b dp buf. _`
    (qspecl_then [`SUM (MAP (λ(_3,abi_sz,_4,_5). abi_sz) (item::items))`,
                  `T`, `x.buf_operand`, `x`] mp_tac) >> simp[] >> NO_TAC) >>
  metis_tac[ADD_COMM]
QED

Theorem dalloca_windows_abi_decode_helpers:
  (preserves_dalloca_windows window (compile_abi_clamp_basetype v clamp)) /\
  (preserves_dalloca_windows window (compile_abi_decode_range_check lo hi limit)) /\
  (preserves_dalloca_windows window (compile_abi_dec_addr base_op pos)) /\
  (opc <> DALLOCA ==>
   preserves_dalloca_windows window (compile_getelemptr_abi src dyn off opc base_op hi)) /\
  (opc <> DALLOCA ==>
   preserves_dalloca_windows window (compile_abi_decode_dyn_elem_ptr opc base_op src dp hi sz))
Proof
  `!base_op pos. preserves_dalloca_windows window (compile_abi_dec_addr base_op pos)` by
    (simp[compile_abi_dec_addr_def] >> windows_tac []) >>
  `!lo hi limit. preserves_dalloca_windows window (compile_abi_decode_range_check lo hi limit)` by
    (simp[compile_abi_decode_range_check_def] >> windows_tac []) >>
  Cases_on `clamp` >> rpt conj_tac >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, compile_getelemptr_abi_def,
       compile_abi_decode_dyn_elem_ptr_def] >>
  rpt strip_tac >> windows_tac []
QED

Theorem dalloca_windows_abi_decode:
  (!dst src opc base_op hi info. opc <> DALLOCA ==>
     preserves_dalloca_windows window (compile_abi_decode_to_buf dst src opc base_op hi info)) /\
  (!dst src opc base_op hi elems off vo. opc <> DALLOCA ==>
     preserves_dalloca_windows window
       (compile_abi_decode_complex_elems dst src opc base_op hi elems off vo)) /\
  (!dst src opc base_op hi info abi_sz mem_sz ip cnt. opc <> DALLOCA ==>
     preserves_dalloca_windows window
       (compile_abi_decode_dyn_loop dst src opc base_op hi info abi_sz mem_sz ip cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  simp[Once compile_abi_decode_to_buf_def, compile_abi_decode_static_def] >>
  windows_tac [dalloca_windows_abi_decode_helpers] >>
  metis_tac[ADD_COMM]
QED

Theorem dalloca_windows_lower_abi:
  preserves_dalloca_windows window (lower_abi_encode ensure mid src enc_info sz) /\
  preserves_dalloca_windows window (lower_abi_decode src dec_info lo hi sz)
Proof
  Cases_on `mid` >> simp[lower_abi_encode_def, lower_abi_decode_def] >> conj_tac >>
  windows_tac [dalloca_windows_abi_encode, dalloca_windows_abi_decode]
QED
