(*
 * Fuel bounds (fuel_ok) for the expression-lowering helpers.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_clamp, fuel_ok_clamp_and_return,
 *   fuel_ok_compile_clamp_basetype, fuel_ok_arith_basic (safe_add/sub/mul/
 *   div/mod/decimal_div, mul_overflow_check, wrap_truncate),
 *   fuel_ok_compile_compare, fuel_ok_compile_safe_pow,
 *   fuel_ok_membership, fuel_ok_compile_list_membership, fuel_ok_misc_emit,
 *   fuel_ok_load_bytestring_as_word (opcode must be a non-terminator),
 *   fuel_ok_store_multi_results, fuel_ok_compile_name_vv,
 *   fuel_ok_compile_type_convert, fuel_ok_compile_store_byte_chunks,
 *   fuel_ok_compile_bytelike_literal, fuel_ok_compile_literal_vv,
 *   fuel_ok_unwrap_value, fuel_ok_compile_multi_vvs (callback hypothesis),
 *   fuel_ok_compile_extcall_store_values, fuel_ok_compile_stage_intcall_args,
 *   fuel_ok_compile_array_subscript (loader hypothesis),
 *   fuel_ok_compile_dynarray_pop, fuel_ok_compile_dynarray_append
 *   (opcodes must be non-terminators), fuel_ok_compile_var_array_membership
 *
 * Skipped: compile_binop, compile_return_value_decode (compile_select, in
 * builtinSimple); compile_default_return_path and
 * compile_external_call_kwargs (compile_abi_* from abiEncoder).
 *)

Theory fragFuelExprHelpers
Ancestors
  fragFuel fragFuelContextBase fragFuelContext compileEnv emitHelper context
  venomInst exprLowering fragFuelLoopArrayMembership
Libs
  fragFuelLib

val uncurry_const = prim_mk_const {Thy = "pair", Name = "UNCURRY"};

(* A bound pair variable under UNCURRY: split it. *)
fun pair_tac (g as (_, w)) =
  case find_terms (fn t => is_comb t andalso is_comb (rator t) andalso
                           same_const (rator (rator t)) uncurry_const andalso
                           is_var (rand t)) w of
    (t :: _) => (Cases_on [ANTIQUOTE (rand t)] >>
                 simp_tac std_ss [pairTheory.UNCURRY_DEF]) g
  | [] => NO_TAC g;

fun fuel_auto2 ths =
  rpt (FIRST (pair_tac :: fuel_step :: map leaf_tac (leaf_thms ths) @
              [first_assum MATCH_ACCEPT_TAC]));

val ft = fn ths =>
  fuel_auto2 (fuel_ok_emit_op :: fuel_ok_emit_void_any :: fuel_ok_emit_inst_any ::
              ths) >> rpt IF_CASES_TAC >> asm_simp_tac (srw_ss()) [is_terminator_def];

Theorem fuel_ok_compile_clamp:
  !v ty Wv E. fuel_ok Wv {} E (compile_clamp v ty)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_clamp_def] >>
  Cases_on `type_bounds ty` >> simp_tac std_ss [LET_THM, pairTheory.UNCURRY_DEF] >>
  match_mp_tac fuel_ok_if >> conj_tac >> strip_tac >> ft []
QED

Theorem fuel_ok_clamp_and_return:
  !v ty Wv E. fuel_ok Wv {} E (clamp_and_return v ty)
Proof
  rpt gen_tac >> simp_tac std_ss [clamp_and_return_def] >>
  ft [fuel_ok_compile_clamp]
QED

Theorem fuel_ok_compile_clamp_basetype:
  !v ty Wv E. fuel_ok Wv {} E (compile_clamp_basetype v ty)
Proof
  ho_match_mp_tac compile_clamp_basetype_ind >> rpt strip_tac >>
  simp_tac std_ss [compile_clamp_basetype_def] >>
  ft [fuel_ok_clamp_and_return]
QED

Theorem fuel_ok_arith_basic:
  (!x y ty Wv E. fuel_ok Wv {} E (compile_safe_add x y ty)) /\
  (!x y ty Wv E. fuel_ok Wv {} E (compile_safe_sub x y ty)) /\
  (!x y res s bits Wv E.
     fuel_ok Wv {} E (compile_mul_overflow_check x y res s bits)) /\
  (!x y ty Wv E. fuel_ok Wv {} E (compile_safe_mul x y ty)) /\
  (!x y ty Wv E. fuel_ok Wv {} E (compile_safe_div x y ty)) /\
  (!x y d ty Wv E. fuel_ok Wv {} E (compile_safe_decimal_div x y d ty)) /\
  (!x y ty Wv E. fuel_ok Wv {} E (compile_safe_mod x y ty)) /\
  (!r ty Wv E. fuel_ok Wv {} E (wrap_truncate r ty))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp_tac std_ss [compile_safe_add_def, compile_safe_sub_def,
    compile_mul_overflow_check_def, compile_safe_mul_def, compile_safe_div_def,
    compile_safe_decimal_div_def, compile_safe_mod_def, wrap_truncate_def,
    pairTheory.UNCURRY_DEF] >>
  ft [fuel_ok_clamp_and_return, fuel_ok_compile_clamp]
QED

Theorem fuel_ok_compile_compare:
  !op x y ty Wv E. fuel_ok Wv {} E (compile_compare op x y ty)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_compare_def, LET_THM] >>
  Cases_on `op` >> simp_tac (srw_ss()) [] >> ft []
QED

Theorem fuel_ok_compile_safe_pow:
  !x y ty bl el Wv E. fuel_ok Wv {} E (compile_safe_pow x y ty bl el)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_safe_pow_def] >>
  Cases_on `bl` >> Cases_on `el` >> simp_tac std_ss [optionTheory.option_case_def] >>
  ft [fuel_ok_compile_clamp]
QED

(* ===== Memory-address helpers and list membership ===== *)

Theorem emit_op_var:
  !opc ops st x st'.
    emit_op opc ops st = (x, st') ==>
    !y. x = Var y ==> var_below st'.cs_next_var y
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >> simp[var_below_def] >> rpt strip_tac >>
  fs[ASCIInumbersTheory.toString_inj]
QED

Theorem compile_ptr_load_var:
  !c i loc op st x st'.
    compile_ptr_load c i loc op st = (x, st') ==>
    !y. x = Var y ==> var_below st'.cs_next_var y
Proof
  Cases_on `loc` >>
  simp_tac (srw_ss()) [compile_ptr_load_def, compile_imm_load_word_def] >>
  rpt gen_tac >> TRY (Cases_on `c`) >> TRY (Cases_on `i`) >>
  simp_tac (srw_ss()) [] >> rpt strip_tac >>
  TRY (gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[])) >> metis_tac[emit_op_var]
QED

Theorem emit_op_not_label:
  !opc ops st x st'. emit_op opc ops st = (x, st') ==> !l. x <> Label l
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem compile_ptr_load_not_label:
  !c i loc op st x st'.
    compile_ptr_load c i loc op st = (x, st') ==> !l. x <> Label l
Proof
  Cases_on `loc` >>
  simp_tac (srw_ss()) [compile_ptr_load_def, compile_imm_load_word_def] >>
  rpt gen_tac >> TRY (Cases_on `c`) >> TRY (Cases_on `i`) >>
  simp_tac (srw_ss()) [] >> rpt strip_tac >>
  TRY (gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[])) >>
  metis_tac[emit_op_not_label]
QED

Theorem fuel_ok_membership:
  (!needle elems Wv E. fuel_ok Wv {} E (emit_membership_eqs needle elems)) /\
  (!acc cs Wv E. fuel_ok Wv {} E (fold_membership_or acc cs)) /\
  (!acc cs Wv E. fuel_ok Wv {} E (fold_membership_and acc cs))
Proof
  rpt conj_tac
  >- (Induct_on `elems` >> simp_tac std_ss [emit_membership_eqs_def] >>
      rpt gen_tac >> ft [])
  >- (Induct_on `cs` >> rpt gen_tac >>
      simp_tac std_ss [Once fold_membership_or_def] >> ft [])
  >- (Induct_on `cs` >> rpt gen_tac >>
      simp_tac std_ss [Once fold_membership_and_def] >> ft [])
QED

Theorem fuel_ok_compile_list_membership:
  (!needle elems Wv E. fuel_ok Wv {} E (compile_list_membership_in needle elems)) /\
  (!needle elems Wv E. fuel_ok Wv {} E (compile_list_membership_notin needle elems))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp_tac std_ss [compile_list_membership_in_def,
                   compile_list_membership_notin_def] >>
  match_mp_tac fuel_ok_bind0 >> (conj_tac >- simp[fuel_ok_membership]) >>
  gen_tac >> BETA_TAC >> Cases_on `a` >> simp_tac (srw_ss()) [] >>
  ft [fuel_ok_membership]
QED

Theorem fuel_ok_misc_emit:
  (!p Wv E. fuel_ok Wv {} E (compile_bytestring_hash p)) /\
  (!b k Wv E. fuel_ok Wv {} E (compile_mapping_subscript b k)) /\
  (!k b Wv E. fuel_ok Wv {} E (compile_keccak256_key k b)) /\
  (!a Wv E. fuel_ok Wv {} E (compile_extcodesize_check a)) /\
  (!b n Wv E. fuel_ok Wv {} E (compile_tuple_subscript b n)) /\
  (!v ty Wv E. fuel_ok Wv {} E (compile_neg v ty)) /\
  (!i Wv E. fuel_ok Wv {} E (compile_env_var i)) /\
  (!s n v Wv E. fuel_ok Wv {} E (compile_int_clamp s n v)) /\
  (!n v sz Wv E. fuel_ok Wv {} E (compile_bytestring_widen_copy n v sz))
Proof
  rpt conj_tac >> rpt gen_tac
  >- (simp_tac std_ss [compile_bytestring_hash_def] >> ft [])
  >- (simp_tac std_ss [compile_mapping_subscript_def, LET_THM] >>
      ft [fuel_ok_compile_alloc_buffer])
  >- (simp_tac std_ss [compile_keccak256_key_def, LET_THM] >>
      ft [fuel_ok_compile_alloc_buffer])
  >- (simp_tac std_ss [compile_extcodesize_check_def] >> ft [])
  >- (simp_tac std_ss [compile_tuple_subscript_def] >> ft [])
  >- (simp_tac std_ss [compile_neg_def] >>
      Cases_on `type_bounds ty` >> simp_tac std_ss [LET_THM, pairTheory.UNCURRY_DEF] >>
      ft [])
  >- (Cases_on `i` >> simp_tac (srw_ss()) [compile_env_var_def] >> ft [])
  >- (simp_tac std_ss [compile_int_clamp_def, LET_THM] >> ft [])
  >- (simp_tac std_ss [compile_bytestring_widen_copy_def] >>
      ft [fuel_ok_compile_alloc_buffer, fuel_ok_compile_copy_memory])
QED

Theorem fuel_ok_load_bytestring_as_word:
  !v c Wv E.
    ~is_terminator c /\ c <> PHI ==>
    fuel_ok Wv {} E (load_bytestring_as_word v c)
Proof
  rpt strip_tac >> simp_tac std_ss [load_bytestring_as_word_def] >> ft []
QED

Theorem fuel_ok_store_multi_results:
  !ops buf off Wv E. fuel_ok Wv {} E (store_multi_results buf ops off)
Proof
  Induct >> simp_tac std_ss [store_multi_results_def] >> rpt gen_tac >> ft []
QED

Theorem fuel_ok_compile_name_vv:
  !cenv ty id Wv E. fuel_ok Wv {} E (compile_name_vv cenv ty id)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_name_vv_def] >>
  Cases_on `FLOOKUP cenv.ce_vars id` >> simp_tac (srw_ss()) []
  >- ft [] >>
  rename1 `SOME v` >> Cases_on `v` >> simp_tac (srw_ss()) [] >> ft []
QED

Theorem fuel_ok_compile_type_convert:
  !v op Wv E. fuel_ok Wv {} E (compile_type_convert v op)
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp_tac (srw_ss()) [compile_type_convert_def, LET_THM] >>
  ft [fuel_ok_misc_emit, fuel_ok_load_bytestring_as_word]
QED

Theorem fuel_ok_compile_store_byte_chunks:
  !p bs off Wv E. fuel_ok Wv {} E (compile_store_byte_chunks p bs off)
Proof
  ho_match_mp_tac compile_store_byte_chunks_ind >> rpt strip_tac >>
  simp_tac (srw_ss()) [Once compile_store_byte_chunks_def, LET_THM,
                       fuel_ok_return] >>
  ft [] >> gvs[]
QED

Theorem fuel_ok_compile_bytelike_literal:
  !bs n Wv E. fuel_ok Wv {} E (compile_bytelike_literal bs n)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_bytelike_literal_def, LET_THM] >>
  ft [fuel_ok_compile_alloc_buffer, fuel_ok_compile_store_byte_chunks]
QED

Theorem fuel_ok_compile_literal_vv:
  !ty l Wv E. fuel_ok Wv {} E (compile_literal_vv ty l)
Proof
  rpt gen_tac >> Cases_on `l` >> TRY (Cases_on `b`) >>
  simp_tac (srw_ss()) [compile_literal_vv_def, fuel_ok_return] >>
  TRY (Cases_on `ty` >> simp_tac (srw_ss()) [fuel_ok_return] >>
       TRY (rename1 `BaseT bt` >> Cases_on `bt` >>
            simp_tac (srw_ss()) [fuel_ok_return] >>
            TRY (rename1 `BytesT bb` >> Cases_on `bb` >>
                 simp_tac (srw_ss()) [fuel_ok_return]))) >>
  ft [fuel_ok_compile_bytelike_literal]
QED

(* ===== Value unwrapping and staged arguments ===== *)

Theorem fuel_ok_unwrap_value:
  !cenv vv Wv E. fuel_ok Wv {} E (unwrap_value cenv vv)
Proof
  rpt gen_tac >> Cases_on `vv` >> simp_tac (srw_ss()) [unwrap_value_def]
  >- simp[fuel_ok_return] >>
  IF_CASES_TAC >- simp[fuel_ok_compile_ptr_load] >>
  Cases_on `p.ptr_location` >> simp_tac (srw_ss()) [LET_THM] >>
  simp[fuel_ok_return, fuel_ok_compile_ensure_in_memory]
QED

Theorem fuel_ok_compile_multi_vvs:
  !cfn.
    (!ce t e Wv E. fuel_ok Wv {} E (cfn ce t e)) ==>
    !cenv es Wv E. fuel_ok Wv {} E (compile_multi_vvs cfn cenv es)
Proof
  gen_tac >> strip_tac >> Induct_on `es` >>
  simp_tac std_ss [compile_multi_vvs_def] >> rpt gen_tac >> ft []
QED

Theorem fuel_ok_compile_extcall_store_values:
  !cenv l buf off Wv E.
    fuel_ok Wv {} E (compile_extcall_store_values cenv l buf off)
Proof
  ho_match_mp_tac compile_extcall_store_values_ind >> rpt strip_tac >>
  simp_tac std_ss [compile_extcall_store_values_def, LET_THM] >>
  ft [fuel_ok_unwrap_value, fuel_ok_context_storage]
QED

Theorem fuel_ok_compile_stage_intcall_args:
  !cenv vals flags tys Wv E.
    fuel_ok Wv {} E (compile_stage_intcall_args cenv vals flags tys)
Proof
  ho_match_mp_tac compile_stage_intcall_args_ind >> rpt strip_tac >>
  simp_tac (srw_ss()) [Once compile_stage_intcall_args_def, LET_THM] >>
  ft [fuel_ok_unwrap_value, fuel_ok_compile_alloc_buffer,
      fuel_ok_context_storage, fuel_ok_compile_store_memory]
QED

(* ===== Array and dynarray helpers ===== *)

Theorem fuel_ok_compile_array_subscript:
  !loader.
    (!a Wv E. fuel_ok Wv {} E (loader a)) ==>
    !base idx dyn cnt ws es sgn Wv E.
      fuel_ok Wv {} E
        (compile_array_subscript base idx dyn cnt ws es sgn loader)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_array_subscript_def, LET_THM] >>
  ft []
QED

Theorem fuel_ok_compile_dynarray_pop:
  !base ws es c i loc Wv E.
    fuel_ok Wv {} E (compile_dynarray_pop base ws es c i loc)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_dynarray_pop_def, LET_THM] >>
  ft [fuel_ok_compile_ptr_load, fuel_ok_compile_ptr_store]
QED

(* The opcodes are arbitrary, so they must be ordinary non-terminators. *)
Theorem fuel_ok_compile_dynarray_append:
  !cenv base v ws es dt st cap prim lo so Wv E.
    ~is_terminator lo /\ lo <> PHI /\ ~is_terminator so /\ so <> PHI ==>
    fuel_ok Wv {} E
      (compile_dynarray_append cenv base v ws es dt st cap prim lo so)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_dynarray_append_def, LET_THM] >>
  ft [fuel_ok_compile_store_memory, CONJUNCT2 fuel_ok_compile_word_copy_loop]
QED

(* The loop leaf needs the length operand allocated before it. *)
Theorem fuel_ok_bind_array_membership_loop:
  !loader.
    (!a Wv E. fuel_ok Wv {} E (loader a)) ==>
    !m needle arr_op sz ob bo ii Wv E.
      fuel_ok Wv {} E m /\
      (!st x st'. m st = (x, st') ==>
                  (!y. x = Var y ==> var_below st'.cs_next_var y) /\
                  !l. x <> Label l) ==>
      fuel_ok Wv {} E
        (comp_bind m (\len_op.
           compile_array_membership_loop needle arr_op len_op sz ob loader
             bo ii))
Proof
  rpt strip_tac >> irule fuel_ok_of_okS >> qexists_tac `\st. T` >> simp[] >>
  `fuel_okS (\st. T) Wv ({} UNION {}) E
     (comp_bind m (\len_op.
        compile_array_membership_loop needle arr_op len_op sz ob loader bo ii))`
    suffices_by simp[] >>
  match_mp_tac fuel_okS_bind >>
  qexistsl_tac [`\c st. (!x. c = Var x ==> var_below st.cs_next_var x) /\
                         !l. c <> Label l`,
                `E`, `E`] >>
  simp[pred_setTheory.SUBSET_DEF] >> rpt conj_tac
  >- simp[fuel_okS_of_ok]
  >- metis_tac[] >>
  gen_tac >> BETA_TAC >>
  irule fuel_okS_compile_array_membership_loop >> first_assum ACCEPT_TAC
QED

Theorem fuel_ok_compile_var_array_membership:
  !cenv needle arr_vv rhs_ty is_in Wv E.
    fuel_ok Wv {} E
      (compile_var_array_membership cenv needle arr_vv rhs_ty is_in)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_var_array_membership_def, LET_THM] >>
  Cases_on `rhs_ty` >> TRY (rename1 `ArrayT _ b` >> Cases_on `b`) >>
  simp_tac (srw_ss()) [] >>
  match_mp_tac (MP_CANON fuel_ok_bind_array_membership_loop) >>
  simp[fuel_ok_compile_ptr_load, fuel_ok_return, comp_return_def,
       compile_ptr_load_var] >>
  metis_tac[compile_ptr_load_var, compile_ptr_load_not_label]
QED
