(*
 * Fuel bounds (fuel_ok) for the ABI encoder/decoder, abi builtin, create
 * builtin and misc builtin helpers.  The three loops (the static-element
 * and dynamic-element encode loops and the decode loop) are in the
 * fragFuelLoopAbi* theories; everything else is proved here.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_abi_int_clamp, fuel_ok_compile_abi_bytes_clamp,
 *   fuel_ok_compile_abi_clamp_basetype, fuel_ok_abi_straight,
 *   fuel_ok_compile_abi_decode_static, fuel_ok_abi_decode_helpers,
 *   fuel_ok_abi_encode_family, fuel_ok_compile_abi_encode_to_buf,
 *   fuel_ok_compile_abi_encode_child,
 *   fuel_ok_compile_abi_encode_complex_elems,
 *   fuel_ok_abi_decode_family, fuel_ok_compile_abi_decode_to_buf,
 *   fuel_ok_compile_abi_decode_complex_elems,
 *   fuel_ok_compile_lower_abi_encode, fuel_ok_compile_lower_abi_decode,
 *   fuel_ok_compile_check_create_result, fuel_ok_compile_create_dispatch,
 *   fuel_ok_compile_raw_create_legacy, fuel_ok_compile_create_proxy_buf,
 *   fuel_ok_compile_create_proxy, fuel_ok_compile_create_copy,
 *   fuel_ok_compile_create_blueprint_check,
 *   fuel_ok_compile_create_blueprint_append,
 *   fuel_ok_compile_create_blueprint,
 *   fuel_ok_builtin_precompiles, fuel_ok_builtin_misc_ops
 *
 * The decode helpers take the source load opcode as a parameter, so each
 * needs ~is_terminator load_opc /\ load_opc <> PHI.
 *)

Theory fragFuelAbi
Ancestors
  fragFuel fragFuelContextBase fragFuelContext fragFuelExprHelpers
  fragFuelBuiltins fragFuelLoopAbiEncStatic
  fragFuelLoopAbiEncDyn fragFuelLoopAbiDecDyn compileEnv emitHelper context
  venomInst abiEncoder builtinAbi builtinCreate builtinSimple builtinMisc
Libs
  fragFuelLib

(* ===== Generic helpers ===== *)

Theorem next_stable_opvar[local]:
  !c. next_stable (\st. !x. c = Var x ==> var_below st.cs_next_var x)
Proof
  rw[next_stable_def, var_below_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compile_alloc_buffer_var[local]:
  !n st a st'. compile_alloc_buffer n st = (a, st') ==>
    !y. a.buf_operand = Var y ==> var_below st'.cs_next_var y
Proof
  rpt gen_tac >> simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  Cases_on `emit_op ALLOCA [Lit (n2w n)] st` >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[emit_op_var]
QED

(* A bind whose result operand the continuation's loop depends on. *)
Theorem fuel_ok_bind_var[local]:
  !m f Wv E.
    fuel_ok Wv {} E m /\
    (!st x st'. m st = (x, st') ==>
       !y. x = Var y ==> var_below st'.cs_next_var y) /\
    (!a. fuel_okS (\st. !y. a = Var y ==> var_below st.cs_next_var y) Wv {} E
           (f a)) ==>
    fuel_ok Wv {} E (comp_bind m f)
Proof
  rpt strip_tac >> irule fuel_ok_of_okS >> qexists_tac `\st. T` >> simp[] >>
  `fuel_okS (\st. T) Wv ({} UNION {}) E (comp_bind m f)` suffices_by simp[] >>
  match_mp_tac fuel_okS_bind >>
  qexistsl_tac [`\a st. !y. a = Var y ==> var_below st.cs_next_var y`,
                `E`, `E`] >>
  simp[pred_setTheory.SUBSET_DEF] >> rpt conj_tac
  >- (irule fuel_okS_of_ok >> first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Theorem fuel_ok_bind_alloc[local]:
  !n f Wv E.
    (!a. fuel_okS (\st. !y. a.buf_operand = Var y ==>
                           var_below st.cs_next_var y) Wv {} E (f a)) ==>
    fuel_ok Wv {} E (comp_bind (compile_alloc_buffer n) f)
Proof
  rpt strip_tac >> irule fuel_ok_of_okS >> qexists_tac `\st. T` >> simp[] >>
  `fuel_okS (\st. T) Wv ({} UNION {}) E (comp_bind (compile_alloc_buffer n) f)`
    suffices_by simp[] >>
  match_mp_tac fuel_okS_bind >>
  qexistsl_tac [`\a st. !y. a.buf_operand = Var y ==>
                          var_below st.cs_next_var y`, `E`, `E`] >>
  simp[pred_setTheory.SUBSET_DEF] >> rpt conj_tac
  >- (irule fuel_okS_of_ok >> simp[fuel_ok_compile_alloc_buffer]) >>
  metis_tac[compile_alloc_buffer_var]
QED

Theorem opcode_case3[local]:
  (case lo of CALLDATALOAD => (a:'a) | DLOAD => b | _ => c) =
  if lo = CALLDATALOAD then a else if lo = DLOAD then b else c
Proof
  Cases_on `lo` >> simp[]
QED

(* ===== Clamps and straight-line helpers ===== *)

Theorem fuel_ok_compile_abi_int_clamp:
  !val_op bits is_signed Wv E.
    fuel_ok Wv {} E (compile_abi_int_clamp val_op bits is_signed)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_abi_int_clamp_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_abi_bytes_clamp:
  !val_op m Wv E. fuel_ok Wv {} E (compile_abi_bytes_clamp val_op m)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_abi_bytes_clamp_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_abi_clamp_basetype:
  !val_op c Wv E. fuel_ok Wv {} E (compile_abi_clamp_basetype val_op c)
Proof
  Cases_on `c` >> simp_tac std_ss [compile_abi_clamp_basetype_def] >>
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_abi_int_clamp, fuel_ok_compile_abi_bytes_clamp] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_abi_encode_static:
  !dst src Wv E. fuel_ok Wv {} E (compile_abi_encode_static dst src)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_abi_encode_static_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_abi_encode_static_info:
  !dst src info Wv E.
    fuel_ok Wv {} E (compile_abi_encode_static_info dst src info)
Proof
  Cases_on `info` >> simp_tac (srw_ss()) [compile_abi_encode_static_info_def] >>
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_void_any, fuel_ok_compile_abi_encode_static] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_abi_straight:
  (!bytez_ptr length count Wv E.
     fuel_ok Wv {} E (compile_abi_zero_pad bytez_ptr length count)) /\
  (!parent_ptr offset Wv E.
     fuel_ok Wv {} E (compile_get_element_ptr parent_ptr offset)) /\
  (!parent_ptr idx_op elem_size Wv E.
     fuel_ok Wv {} E (compile_get_dynarray_elem_ptr parent_ptr idx_op elem_size)) /\
  (!base_op pos_op Wv E. fuel_ok Wv {} E (compile_abi_dec_addr base_op pos_op)) /\
  (!start_op end_op hi_op Wv E.
     fuel_ok Wv {} E (compile_abi_decode_range_check start_op end_op hi_op))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp_tac std_ss [compile_abi_zero_pad_def, compile_get_element_ptr_def,
    compile_get_dynarray_elem_ptr_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_abi_decode_static:
  !src_op dst_op load_opc clamp_fn.
    ~is_terminator load_opc /\ load_opc <> PHI /\
    (!v Wv E. fuel_ok Wv {} E (clamp_fn v)) ==>
    !Wv E. fuel_ok Wv {} E
             (compile_abi_decode_static src_op dst_op load_opc clamp_fn)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_abi_decode_static_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
  simp[is_terminator_def] >> metis_tac[]
QED

Theorem fuel_ok_abi_decode_helpers:
  (!src_op is_dyn abi_offset load_opc base_op hi_op Wv E.
     ~is_terminator load_opc /\ load_opc <> PHI ==>
     fuel_ok Wv {} E
       (compile_getelemptr_abi src_op is_dyn abi_offset load_opc base_op hi_op)) /\
  (!load_opc base_op elem_src src_data hi_op elem_abi_sz Wv E.
     ~is_terminator load_opc /\ load_opc <> PHI ==>
     fuel_ok Wv {} E
       (compile_abi_decode_dyn_elem_ptr load_opc base_op elem_src src_data
          hi_op elem_abi_sz))
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp_tac std_ss [compile_getelemptr_abi_def,
    compile_abi_decode_dyn_elem_ptr_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_abi_straight] >>
  simp[is_terminator_def] >>
  metis_tac[fuel_ok_abi_straight]
QED

(* ===== The encoder family ===== *)

val [enc_child, enc_prim, enc_bytes, enc_copy, enc_dyn, enc_cnil, enc_ccons,
     enc_enil, enc_econs, enc_loop] =
  CONJUNCTS compile_abi_encode_child_def;

Theorem fuel_ok_abi_encode_family:
  (!dst child_ptr child_info is_dyn static_ofst dyn_ofst_ptr Wv E.
     fuel_ok Wv {} E
       (compile_abi_encode_child dst child_ptr child_info is_dyn static_ofst
          dyn_ofst_ptr)) /\
  (!dst src info Wv E.
     fuel_ok Wv {} E (compile_abi_encode_to_buf dst src info)) /\
  (!dst src elems src_offset head_offset dyn_ptr Wv E.
     fuel_ok Wv {} E
       (compile_abi_encode_complex_elems dst src elems src_offset head_offset
          dyn_ptr)) /\
  (!dst src elem_info elem_abi_sz elem_mem_sz len_op Wv E.
     fuel_okS (\st. !x. len_op = Var x ==> var_below st.cs_next_var x) Wv {} E
       (compile_abi_encode_dyn_loop dst src elem_info elem_abi_sz elem_mem_sz
          len_op))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac
  (* child *)
  >- (rpt strip_tac >> simp_tac std_ss [enc_child] >>
      fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
      simp[is_terminator_def] >> metis_tac[])
  (* word *)
  >- (rpt strip_tac >> simp[enc_prim, fuel_ok_compile_abi_encode_static])
  (* bytestring *)
  >- (rpt strip_tac >> simp_tac std_ss [enc_bytes] >>
      fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
      simp[is_terminator_def])
  (* copy *)
  >- (rpt strip_tac >> simp_tac std_ss [enc_copy] >>
      fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
      simp[is_terminator_def])
  (* dynamic array: the loop's length operand is the fresh MLOAD result *)
  >- (rpt strip_tac >> simp_tac std_ss [enc_dyn, LET_THM] >>
      match_mp_tac fuel_ok_bind0 >> conj_tac
      >- simp[fuel_ok_compile_alloc_buffer] >>
      gen_tac >> BETA_TAC >>
      match_mp_tac fuel_ok_ignore_bind0 >> conj_tac
      >- (fuel_auto [fuel_ok_emit_void_any] >> simp[is_terminator_def]) >>
      match_mp_tac fuel_ok_bind_var >> rpt conj_tac
      >- (fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def])
      >- metis_tac[emit_op_var] >>
      gen_tac >> BETA_TAC >>
      match_mp_tac fuel_okS_ignore_bind_keep >> rpt conj_tac
      >- MATCH_ACCEPT_TAC next_stable_opvar
      >- (irule fuel_okS_of_ok >> fuel_auto [fuel_ok_emit_void_any] >>
          simp[is_terminator_def])
      >- (match_mp_tac fuel_okS_bind_keep >> rpt conj_tac
          >- MATCH_ACCEPT_TAC next_stable_opvar
          >- (match_mp_tac fuel_okS_if >> conj_tac >> strip_tac
              >- MATCH_ACCEPT_TAC fuel_okS_compile_abi_encode_dyn_static_loop >>
              first_x_assum irule >> metis_tac[])
          >- (gen_tac >> BETA_TAC >> irule fuel_okS_of_ok >>
              fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
              simp[is_terminator_def])))
  (* empty tuple *)
  >- (rpt strip_tac >> simp[enc_cnil, fuel_ok_return])
  (* tuple *)
  >- (rpt strip_tac >> gvs[] >> simp_tac std_ss [enc_ccons, LET_THM] >>
      fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
                 fuel_ok_compile_alloc_buffer] >>
      simp[is_terminator_def] >>
      metis_tac[listTheory.EXISTS_DEF, listTheory.NOT_EXISTS,
                listTheory.EVERY_DEF, combinTheory.o_THM])
  (* elements: nil, cons *)
  >- (rpt strip_tac >> simp[enc_enil, fuel_ok_return])
  >- (rpt strip_tac >> simp_tac std_ss [enc_econs] >>
      fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def] >> metis_tac[])
  (* the loop *)
  >> rpt strip_tac >> irule fuel_okS_compile_abi_encode_dyn_loop >> metis_tac[]
QED

Theorem fuel_ok_compile_abi_encode_child =
  fuel_ok_abi_encode_family |> CONJUNCT1

Theorem fuel_ok_compile_abi_encode_to_buf =
  fuel_ok_abi_encode_family |> CONJUNCT2 |> CONJUNCT1

Theorem fuel_ok_compile_abi_encode_complex_elems =
  fuel_ok_abi_encode_family |> CONJUNCT2 |> CONJUNCT2 |> CONJUNCT1

(* ===== The decoder family ===== *)

val [dec_prim, dec_bytes, dec_dyn, dec_complex, dec_enil, dec_econs, dec_loop] =
  CONJUNCTS compile_abi_decode_to_buf_def;

(* The loop call after allocating its counter pointer. *)
Theorem fuel_ok_dec_alloc_loop[local]:
  !dst src_op load_opc base_op hi_op elem_info elem_abi_sz elem_mem_sz cnt Wv E.
    (!a. fuel_okS (\st. !x. a.buf_operand = Var x ==>
                           var_below st.cs_next_var x) Wv {} E
           (compile_abi_decode_dyn_loop dst src_op load_opc base_op hi_op
              elem_info elem_abi_sz elem_mem_sz a.buf_operand cnt)) ==>
    fuel_ok Wv {} E
      (comp_bind (compile_alloc_buffer 32)
         (\a. comp_ignore_bind (emit_void MSTORE [a.buf_operand; Lit 0w])
                (compile_abi_decode_dyn_loop dst src_op load_opc base_op hi_op
                   elem_info elem_abi_sz elem_mem_sz a.buf_operand cnt)))
Proof
  rpt strip_tac >> match_mp_tac fuel_ok_bind_alloc >> gen_tac >> BETA_TAC >>
  match_mp_tac fuel_okS_ignore_bind_keep >> rpt conj_tac
  >- MATCH_ACCEPT_TAC next_stable_opvar
  >- (irule fuel_okS_of_ok >> fuel_auto [fuel_ok_emit_void_any] >>
      simp[is_terminator_def])
  >- (first_x_assum (qspec_then `a` ACCEPT_TAC))
QED

fun dec_auto firsts ths =
  rpt (FIRST (map leaf_tac (leaf_thms firsts) @
              (fuel_step :: map leaf_tac (leaf_thms ths) @
               [first_assum MATCH_ACCEPT_TAC])));

Theorem fuel_ok_abi_decode_family:
  (!dst src_op load_opc base_op hi_op info Wv E.
     ~is_terminator load_opc /\ load_opc <> PHI /\ load_opc <> INVOKE ==>
     fuel_ok Wv {} E
       (compile_abi_decode_to_buf dst src_op load_opc base_op hi_op info)) /\
  (!dst src_op load_opc base_op hi_op elems abi_offset vyper_offset Wv E.
     ~is_terminator load_opc /\ load_opc <> PHI /\ load_opc <> INVOKE ==>
     fuel_ok Wv {} E
       (compile_abi_decode_complex_elems dst src_op load_opc base_op hi_op
          elems abi_offset vyper_offset)) /\
  (!dst src_op load_opc base_op hi_op elem_info elem_abi_sz elem_mem_sz i_ptr
    cnt Wv E.
     ~is_terminator load_opc /\ load_opc <> PHI /\ load_opc <> INVOKE ==>
     fuel_okS (\st. !x. i_ptr = Var x ==> var_below st.cs_next_var x) Wv {} E
       (compile_abi_decode_dyn_loop dst src_op load_opc base_op hi_op
          elem_info elem_abi_sz elem_mem_sz i_ptr cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  (* word *)
  >- (rpt strip_tac >>
      simp_tac std_ss [dec_prim, compile_abi_decode_static_def] >>
      fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
                 fuel_ok_abi_straight,
                 fuel_ok_compile_abi_clamp_basetype] >>
      simp[is_terminator_def] >> metis_tac[fuel_ok_abi_straight])
  (* bytestring *)
  >- (rpt strip_tac >>
      simp_tac std_ss [dec_bytes, opcode_case3, LET_THM] >>
      fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
      simp[is_terminator_def] >> metis_tac[fuel_ok_abi_straight])
  (* dynamic array *)
  >- (rpt strip_tac >> gvs[] >>
      simp_tac std_ss [dec_dyn, opcode_case3, LET_THM] >>
      dec_auto [fuel_ok_dec_alloc_loop] [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
      simp[is_terminator_def] >> metis_tac[fuel_ok_abi_straight])
  (* complex *)
  >- (rpt strip_tac >> gvs[] >> simp_tac std_ss [dec_complex, LET_THM] >>
      fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def] >>
      metis_tac[fuel_ok_abi_straight])
  (* elements *)
  >- (rpt strip_tac >> simp[dec_enil, fuel_ok_return])
  >- (rpt strip_tac >> gvs[] >> simp_tac std_ss [dec_econs, LET_THM] >>
      fuel_auto [fuel_ok_emit_op, CONJUNCT1 fuel_ok_abi_decode_helpers] >>
      simp[is_terminator_def] >> metis_tac[fuel_ok_abi_decode_helpers])
  (* the loop *)
  >> rpt strip_tac >> gvs[] >> irule fuel_okS_compile_abi_decode_dyn_loop >>
     metis_tac[]
QED

Theorem fuel_ok_compile_abi_decode_to_buf =
  fuel_ok_abi_decode_family |> CONJUNCT1

Theorem fuel_ok_compile_abi_decode_complex_elems =
  fuel_ok_abi_decode_family |> CONJUNCT2 |> CONJUNCT1

(* ===== Builtins: abi_encode, abi_decode ===== *)

Theorem fuel_ok_compile_lower_abi_encode:
  !ensure_tuple method_id_opt src_op enc_info maxlen Wv E.
    fuel_ok Wv {} E
      (lower_abi_encode ensure_tuple method_id_opt src_op enc_info maxlen)
Proof
  Cases_on `method_id_opt` >> simp_tac (srw_ss()) [lower_abi_encode_def] >>
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_buffer, fuel_ok_compile_abi_encode_to_buf] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_lower_abi_decode:
  !data_op dec_info abi_min_size abi_max_size output_size Wv E.
    fuel_ok Wv {} E
      (lower_abi_decode data_op dec_info abi_min_size abi_max_size output_size)
Proof
  rpt gen_tac >> simp_tac std_ss [lower_abi_decode_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_buffer, fuel_ok_compile_abi_decode_to_buf] >>
  simp[is_terminator_def]
QED

(* ===== Builtins: create ===== *)

Theorem fuel_ok_compile_check_create_result:
  !result revert_on_failure Wv E.
    fuel_ok Wv {} E (compile_check_create_result result revert_on_failure)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_check_create_result_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any, fuel_ok_emit_inst_jnz,
             fuel_ok_emit_inst_any, fuel_ok_compile_alloc_buffer] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_create_dispatch:
  !code_ptr code_len value_op salt_opt revert_on_failure Wv E.
    fuel_ok Wv {} E
      (compile_create_dispatch code_ptr code_len value_op salt_opt
         revert_on_failure)
Proof
  Cases_on `salt_opt` >> simp_tac (srw_ss()) [compile_create_dispatch_def] >>
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_check_create_result] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_raw_create_legacy:
  !bytecode_op value_op salt_opt revert_on_failure ctor_args_info Wv E.
    fuel_ok Wv {} E
      (compile_raw_create_legacy bytecode_op value_op salt_opt
         revert_on_failure ctor_args_info)
Proof
  Cases_on `ctor_args_info`
  >- (simp_tac (srw_ss()) [compile_raw_create_legacy_def] >> rpt gen_tac >>
      fuel_auto [fuel_ok_emit_op, fuel_ok_compile_create_dispatch] >>
      simp[is_terminator_def]) >>
  rename1 `SOME p` >> PairCases_on `p` >>
  simp_tac (srw_ss()) [compile_raw_create_legacy_def] >> rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_create_dispatch,
             fuel_ok_compile_alloc_buffer, fuel_ok_compile_abi_encode_to_buf,
             fuel_ok_context_storage] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_create_proxy_buf:
  !target_op Wv E. fuel_ok Wv {} E (compile_create_proxy_buf target_op)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_create_proxy_buf_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_buffer] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_create_proxy:
  !target_op value_op salt_opt revert_on_failure Wv E.
    fuel_ok Wv {} E
      (compile_create_proxy target_op value_op salt_opt revert_on_failure)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_create_proxy_def] >>
  fuel_auto [fuel_ok_compile_create_proxy_buf, fuel_ok_compile_create_dispatch]
QED

Theorem fuel_ok_compile_create_copy:
  !target_op value_op salt_opt revert_on_failure Wv E.
    fuel_ok Wv {} E
      (compile_create_copy target_op value_op salt_opt revert_on_failure)
Proof
  Cases_on `salt_opt` >> simp_tac (srw_ss()) [compile_create_copy_def] >>
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_dynamic,
             fuel_ok_compile_check_create_result] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_create_blueprint_check:
  !target_op code_offset_op Wv E.
    fuel_ok Wv {} E (compile_create_blueprint_check target_op code_offset_op)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_create_blueprint_check_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_create_blueprint_append:
  !target_op value_op salt_opt code_offset_op code_size args_ptr args_len
   revert_on_failure Wv E.
    fuel_ok Wv {} E
      (compile_create_blueprint_append target_op value_op salt_opt
         code_offset_op code_size args_ptr args_len revert_on_failure)
Proof
  Cases_on `salt_opt` >>
  simp_tac (srw_ss()) [compile_create_blueprint_append_def] >>
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_dynamic,
             fuel_ok_compile_check_create_result,
             fuel_ok_context_storage] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_create_blueprint:
  !target_op value_op salt_opt code_offset_op args_info revert_on_failure Wv E.
    fuel_ok Wv {} E
      (compile_create_blueprint target_op value_op salt_opt code_offset_op
         args_info revert_on_failure)
Proof
  Cases_on `args_info`
  >- (simp_tac (srw_ss()) [compile_create_blueprint_def] >> rpt gen_tac >>
      fuel_auto [fuel_ok_compile_create_blueprint_check,
                 fuel_ok_compile_create_blueprint_append] >> simp[] >>
      fuel_auto [fuel_ok_compile_create_blueprint_check,
                 fuel_ok_compile_create_blueprint_append]) >>
  rename1 `SOME p` >> PairCases_on `p` >>
  simp_tac (srw_ss()) [compile_create_blueprint_def] >> rpt gen_tac >>
  fuel_auto [fuel_ok_compile_create_blueprint_check,
             fuel_ok_compile_create_blueprint_append] >> simp[] >>
  fuel_auto [fuel_ok_compile_create_blueprint_check,
             fuel_ok_compile_create_blueprint_append]
QED

(* ===== Builtins: precompiles and misc ===== *)

Theorem fuel_ok_builtin_precompiles:
  (!hash_op v_op r_op s_op Wv E.
     fuel_ok Wv {} E (compile_ecrecover hash_op v_op r_op s_op)) /\
  (!x1 y1 x2 y2 Wv E. fuel_ok Wv {} E (compile_ecadd x1 y1 x2 y2)) /\
  (!x y scalar Wv E. fuel_ok Wv {} E (compile_ecmul x y scalar)) /\
  (!p1 p2 Wv E. fuel_ok Wv {} E (compile_ecadd_points p1 p2)) /\
  (!p scalar Wv E. fuel_ok Wv {} E (compile_ecmul_point p scalar))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp_tac std_ss [compile_ecrecover_def, compile_ecadd_def, compile_ecmul_def,
    compile_ecadd_points_def, compile_ecmul_point_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_buffer] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_builtin_misc_ops:
  (!n_op Wv E. fuel_ok Wv {} E (compile_blockhash n_op)) /\
  (!n_op Wv E. fuel_ok Wv {} E (compile_blobhash n_op)) /\
  (!val_op divisor Wv E. fuel_ok Wv {} E (compile_floor val_op divisor)) /\
  (!val_op divisor Wv E. fuel_ok Wv {} E (compile_ceil val_op divisor)) /\
  (!val_op scale is_signed Wv E.
     fuel_ok Wv {} E (compile_as_wei_value_int val_op scale is_signed)) /\
  (!val_op scale decimal_divisor Wv E.
     fuel_ok Wv {} E (compile_as_wei_value_decimal val_op scale decimal_divisor))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp_tac std_ss [compile_blockhash_def, compile_blobhash_def,
    compile_floor_def, compile_ceil_def, compile_as_wei_value_int_def,
    compile_as_wei_value_decimal_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any, fuel_ok_compile_select] >>
  simp[is_terminator_def]
QED
