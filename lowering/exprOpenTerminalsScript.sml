(*
 * compile_expr keeps its block open: ABI coding, copies and calls
 *
 * TOP-LEVEL:
 *   compile_abi_decode_open_mutual, lower_abi_decode_open,
 *   lower_abi_encode_open — ABI decoding and encoding
 *   compile_word_copy_loop_open, compile_imm_copy_to_memory_open,
 *   compile_ensure_in_memory_open — copies (loops end with new_block)
 *   compile_intcall_open, compile_extcall_open, compile_send_open
 *                         — calls, their default-return and failure paths
 *)

Theory exprOpenTerminals
Ancestors
  exprOpenPrimitives builtinAbi abiEncoder compileEnv venomInst context exprLowering emitHelper

Theorem lower_abi_encode_open:
  !tuple mid src info maxlen sa v sb.
    lower_abi_encode tuple mid src info maxlen sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `mid`
  >- (simp[lower_abi_encode_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def] >>
      ntac 4 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      drule emit_void_terminated >> simp[is_terminator_def]) >>
  simp[lower_abi_encode_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  ntac 7 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_word_copy_loop_open:
  !src dst count load store ctor sa u sb.
    compile_word_copy_loop src dst count load store ctor sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_word_copy_loop_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule new_block_open >> simp[]
QED

Theorem compile_imm_copy_to_memory_open:
  !n ctor imm src dst off sa u sb.
    ~block_is_terminated sa /\
    compile_imm_copy_to_memory ctor imm src dst n off sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  Induct >>
  simp[compile_imm_copy_to_memory_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> simp[]) >> strip_tac >>
  last_x_assum (drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)) >>
  disch_then irule >>
  drule_at (Pat `emit_void _ _ _ = _`) emit_void_terminated >>
  simp[is_terminator_def]
QED

Theorem compile_ensure_in_memory_open:
  !ptr loc bytes words ctor imm sa v sb.
    ~block_is_terminated sa /\
    compile_ensure_in_memory ptr loc bytes words ctor imm sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `loc`
  >- (simp[compile_ensure_in_memory_def, comp_return_def] >> metis_tac[])
  >- suspend "storage"
  >- suspend "transient"
  >- suspend "code"
  >> suspend "calldata"
QED

Resume compile_ensure_in_memory_open[storage]:
  Cases_on `words = 1`
  >- (simp[compile_ensure_in_memory_def, comp_bind_def,
           comp_ignore_bind_def, comp_return_def] >>
      ntac 3 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      drule emit_void_terminated >> simp[is_terminator_def]) >>
  simp[compile_ensure_in_memory_def, compile_storage_to_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 3 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule compile_word_copy_loop_open >> simp[]
QED

Resume compile_ensure_in_memory_open[transient]:
  Cases_on `words = 1`
  >- (simp[compile_ensure_in_memory_def, comp_bind_def,
           comp_ignore_bind_def, comp_return_def] >>
      ntac 3 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      drule emit_void_terminated >> simp[is_terminator_def]) >>
  simp[compile_ensure_in_memory_def, compile_transient_to_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 3 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule compile_word_copy_loop_open >> simp[]
QED

Resume compile_ensure_in_memory_open[code]:
  simp[compile_ensure_in_memory_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  metis_tac[compile_alloc_buffer_open, compile_imm_copy_to_memory_open]
QED

Resume compile_ensure_in_memory_open[calldata]:
  simp[compile_ensure_in_memory_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  ntac 6 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Finalise compile_ensure_in_memory_open

Theorem unwrap_value_open:
  !cenv vv sa v sb.
    ~block_is_terminated sa /\ unwrap_value cenv vv sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `vv`
  >- (simp[unwrap_value_def, comp_return_def] >> metis_tac[]) >>
  rename1 `LocatedValue aty aptr` >>
  simp[unwrap_value_def] >> Cases_on `is_word_type aty`
  >- (simp[] >> metis_tac[compile_ptr_load_open]) >>
  simp[] >> Cases_on `aptr.ptr_location` >>
  simp[comp_return_def] >>
  metis_tac[compile_ensure_in_memory_open]
QED

Theorem compile_abi_decode_static_open:
  !src dst load clamp sa u sb.
    compile_abi_decode_static src dst load clamp sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_abi_decode_static_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_abi_decode_dyn_loop_open:
  !dst src load base_op hi info asz msz ip cnt sa u sb.
    compile_abi_decode_dyn_loop dst src load base_op hi info asz msz ip cnt sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[NoAsms, Once compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule new_block_open >> simp[]
QED

Theorem compile_abi_decode_open_mutual:
  (!dst src load base_op hi info sa u sb.
     ~block_is_terminated sa /\
     compile_abi_decode_to_buf dst src load base_op hi info sa = (u,sb) ==>
     ~block_is_terminated sb) /\
  (!dst src load base_op hi elems ao vo sa u sb.
     ~block_is_terminated sa /\
     compile_abi_decode_complex_elems dst src load base_op hi elems ao vo sa = (u,sb) ==>
     ~block_is_terminated sb) /\
  (!dst src load base_op hi info asz msz ip cnt sa u sb.
     ~block_is_terminated sa /\
     compile_abi_decode_dyn_loop dst src load base_op hi info asz msz ip cnt sa = (u,sb) ==>
     ~block_is_terminated sb)
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- (rpt gen_tac >>
      simp[NoAsms, Once compile_abi_decode_to_buf_def, comp_bind_def] >>
      pairarg_tac >> simp[] >> strip_tac >>
      drule compile_abi_decode_static_open >> simp[])
  >- suspend "bytes"
  >- suspend "dynarray"
  >- suspend "complex"
  >- (simp[NoAsms, Once compile_abi_decode_to_buf_def, comp_return_def] >> metis_tac[])
  >- suspend "elements"
  >> metis_tac[compile_abi_decode_dyn_loop_open]
QED

Resume compile_abi_decode_open_mutual[bytes]:
  rpt gen_tac >>
  simp[NoAsms, Once compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `base_op = Lit 0w`
  >- (Cases_on `load = CALLDATALOAD`
      >- (simp[] >> rpt (pairarg_tac >> simp[]) >> strip_tac >>
          drule emit_void_terminated >> simp[is_terminator_def]) >>
      Cases_on `load = DLOAD`
      >- (simp[] >> rpt (pairarg_tac >> simp[]) >> strip_tac >>
          drule emit_void_terminated >> simp[is_terminator_def]) >>
      Cases_on `load` >> gvs[] >> rpt (pairarg_tac >> simp[]) >> strip_tac >>
      drule emit_void_terminated >> simp[is_terminator_def]) >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Resume compile_abi_decode_open_mutual[dynarray]:
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  simp[NoAsms, Once compile_abi_decode_to_buf_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  ntac 9 (pairarg_tac >> simp[]) >>
  qpat_x_assum `!can_bulk_copy ip i_ptr_alloc cnt. _` kall_tac >>
  IF_CASES_TAC
  >- (simp[comp_bind_def] >> ntac 4 (pairarg_tac >> simp[]) >>
      Cases_on `load = CALLDATALOAD`
      >- (gvs[] >> strip_tac >> drule emit_void_terminated >> simp[is_terminator_def]) >>
      Cases_on `load = DLOAD`
      >- (gvs[] >> strip_tac >> drule emit_void_terminated >> simp[is_terminator_def]) >>
      Cases_on `load` >> gvs[] >> strip_tac >>
      drule emit_void_terminated >> simp[is_terminator_def]) >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> strip_tac >>
  drule compile_abi_decode_dyn_loop_open >> simp[]
QED

Resume compile_abi_decode_open_mutual[complex]:
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  simp[NoAsms, Once compile_abi_decode_to_buf_def] >>
  Cases_on `hi = Lit 0w`
  >- (gvs[] >> metis_tac[]) >>
  gvs[] >>
  simp[compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule emit_void_terminated >> simp[is_terminator_def] >>
  metis_tac[]
QED

Resume compile_abi_decode_open_mutual[elements]:
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  simp[NoAsms, Once compile_abi_decode_to_buf_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  ntac 3 (pairarg_tac >> simp[]) >> strip_tac >>
  gvs[arithmeticTheory.ADD_COMM] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def] >>
  metis_tac[]
QED

Finalise compile_abi_decode_open_mutual

Theorem compile_abi_decode_to_buf_open:
  !dst src load base_op hi info sa u sb.
    ~block_is_terminated sa /\
    compile_abi_decode_to_buf dst src load base_op hi info sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  metis_tac[compile_abi_decode_open_mutual]
QED

Theorem lower_abi_decode_open:
  !data info min_size max_size size sa v sb.
    lower_abi_decode data info min_size max_size size sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[lower_abi_decode_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  ntac 5 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule compile_alloc_buffer_open >> strip_tac >>
  drule_all compile_abi_decode_to_buf_open >> simp[]
QED

Theorem compile_return_value_decode_open:
  !min_size max_size sa v sb.
    compile_return_value_decode min_size max_size sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_return_value_decode_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 5 (pairarg_tac >> simp[]) >> strip_tac >>
  drule compile_select_open >> simp[]
QED

Theorem compile_default_return_path_open:
  !cenv rty dty buf result default_op addr skip min_size max_size info sa v sb.
    compile_default_return_path cenv rty dty buf result default_op addr skip
      min_size max_size info sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_default_return_path_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule new_block_open >> simp[]
QED

Theorem compile_external_call_kwargs_open:
  !cenv addr vals tys memsz abisz mid retsz minsz retmem static value gas skip
   has_default default_op rty dty enc dec sa v sb.
    compile_external_call_kwargs cenv addr vals tys memsz abisz mid retsz minsz
      retmem static value gas skip has_default default_op rty dty enc dec sa =
      (v,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_external_call_kwargs_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  ntac 5 (pairarg_tac >> simp[]) >>
  ntac 5 (pairarg_tac >> simp[]) >>
  ntac 5 (pairarg_tac >> simp[]) >>
  Cases_on `rty = NoneT`
  >- (simp[comp_return_def] >> strip_tac >> gvs[] >>
      drule new_block_open >> simp[]) >>
  simp[] >> Cases_on `has_default`
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
      drule compile_default_return_path_open >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 3 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule compile_return_value_decode_open >>
  metis_tac[compile_abi_decode_to_buf_open]
QED

Theorem emit_inst_nonterminator_open:
  !opc args outs sa u sb.
    emit_inst opc args outs sa = (u,sb) /\ ~is_terminator opc ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[emit_inst_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule emit_nonterminator_open >> simp[mk_inst_def]
QED

Theorem emit_multi_op_nonterminator_open:
  !opc args count sa v sb.
    emit_multi_op opc args count sa = (v,sb) /\ ~is_terminator opc ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[emit_multi_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_inst_nonterminator_open >> simp[]
QED

Theorem store_multi_results_open:
  !buf ops offset sa u sb.
    ~block_is_terminated sa /\ store_multi_results buf ops offset sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  Induct_on `ops`
  >- (simp[store_multi_results_def, comp_return_def] >> metis_tac[]) >>
  rpt gen_tac >>
  simp[store_multi_results_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_void_terminated >> simp[is_terminator_def] >> metis_tac[]
QED

Theorem compile_intcall_open:
  !cfn cenv ret_ty ty fid args default_ret sa vv sb.
    compile_call cfn cenv ret_ty ty (IntCall fid) args default_ret sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_call_def] >>
  ntac 4 (pairarg_tac >> simp[]) >>
  IF_CASES_TAC
  >- (BasicProvers.TOP_CASE_TAC
      >- (simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
          drule emit_op_nonterminator_open >> simp[is_terminator_def]) >>
      simp[] >> ntac 2 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      drule emit_multi_op_nonterminator_open >> simp[is_terminator_def] >>
      metis_tac[store_multi_results_open]) >>
  pairarg_tac >> simp[] >> BasicProvers.TOP_CASE_TAC >>
  simp[] >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_send_open:
  !cfn cenv rty ty gas addr amount gas_es default_ret sa vv sb.
    LENGTH gas_es = (if gas then 1 else 0) /\
    compile_call cfn cenv rty ty (Send gas) (addr::amount::gas_es)
      default_ret sa = (vv,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_call_def] >> strip_tac >>
  ntac 5 (pairarg_tac >> gvs[]) >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_extcall_open:
  !cfn cenv rty ty static skip name tys ret opts addr args default_ret sa vv sb.
    compile_call cfn cenv rty ty (ExtCall static skip (name,tys,ret) opts)
      (addr::args) default_ret sa = (vv,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_call_def] >>
  ntac 5 (pairarg_tac >> simp[]) >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> strip_tac >> gvs[] >>
  drule compile_external_call_kwargs_open >> simp[]
QED
