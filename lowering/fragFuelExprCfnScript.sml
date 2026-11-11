(*
 * Fuel bounds (fuel_ok) for the expression-lowering helpers that take the
 * expression compiler as a callback `cfn`, from lower_value on, and for
 * compile_call.  Each takes the hypothesis that cfn is itself bounded:
 *   (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)).
 *
 * TOP-LEVEL:
 *   fuel_ok_as_stack_val, fuel_ok_as_ptr_val,
 *   fuel_ok_lower_value, fuel_ok_compile_get_target_ptr,
 *   fuel_ok_lower_value_with_loc, fuel_ok_compile_concat,
 *   fuel_ok_compile_make_tuple, fuel_ok_compile_make_array_elems,
 *   fuel_ok_compile_make_array, fuel_ok_compile_multi_exprs,
 *   fuel_ok_compile_store_abi_tuple, fuel_ok_compile_subscript,
 *   fuel_ok_compile_attribute, fuel_ok_compile_struct_lit,
 *   fuel_ok_compile_extcall_store_args, fuel_ok_compile_materialize_vv,
 *   fuel_ok_compile_ifexp_arm, fuel_ok_compile_snapshot_vv,
 *   fuel_ok_compile_abi_encode_args, fuel_ok_compile_ext_call_kwarg,
 *   fuel_ok_compile_ext_call_kwargs, fuel_ok_compile_create_salt,
 *   fuel_ok_compile_create_ctor_tuple, fuel_ok_compile_create_blueprint_args,
 *   fuel_ok_compile_create_snapshot, fuel_ok_compile_raw_create,
 *   fuel_ok_compile_create_call, fuel_ok_compile_store_words,
 *   fuel_ok_compile_invert, fuel_ok_compile_acc,
 *   fuel_ok_compile_addmod_names, fuel_ok_compile_mulmod_names,
 *   fuel_ok_compile_powmod256_names, fuel_ok_compile_call
 *
 * Also (framework additions, local to this theory but exported):
 *   fuel_ok_emit_multi_op
 *)

Theory fragFuelExprCfn
Ancestors
  fragFuel fragFuelContextBase fragFuelContext compileEnv emitHelper context
  venomInst fragFuelExprHelpers fragFuelBuiltins fragFuelAbi exprLowering
Libs
  fragFuelLib

(* ===== Tactic support ===== *)

(* UNCURRY k (UNCURRY (\x s. (f x, s)) p): a state-passing map, flattened so
   that fuel_auto sees one bind. *)
Theorem uncurry_map[local]:
  !k f p. UNCURRY k (UNCURRY (\x s. (f x, s)) p) = UNCURRY (\x s. k (f x) s) p
Proof
  Cases_on `p` >> simp[]
QED

(* Lemmas of the form `h ==> !xs. fuel_ok ...` as `!xs. h ==> fuel_ok ...`,
   which fuel_auto applies as a rule. *)
fun pn th =
  GEN_ALL (CONV_RULE (REDEPTH_CONV RIGHT_IMP_FORALL_CONV) (SPEC_ALL th));

val uncurry_tm = prim_mk_const {Thy = "pair", Name = "UNCURRY"};

(* Split a variable of product type that a UNCURRY consumes. *)
fun prod_tac (g as (_, w)) =
  let
    val fvs = free_vars w
    val ts = find_terms (fn t => is_comb t andalso is_comb (rator t) andalso
                                 same_const (rator (rator t)) uncurry_tm andalso
                                 is_var (rand t) andalso tmem (rand t) fvs) w
  in
    case ts of
      [] => NO_TAC g
    | t :: _ =>
        let val p = rand t in
          (Cases_on `^p` >> simp_tac std_ss []) g
        end
  end;

val tidy_tac = CHANGED_TAC (simp_tac std_ss [uncurry_map, SF ETA_ss]);

(* fuel_auto, then a case, a pair or an eta step it can't take, repeated. *)
fun fa ths =
  rpt (fuel_auto (map pn ths) >> FIRST [tidy_tac, prod_tac, TOP_CASE_TAC]);

(* ===== Generic lemmas ===== *)

Theorem fuel_ok_as_stack_val:
  !ty m Wv L E.
    fuel_ok Wv L E m ==> fuel_ok Wv L E (\st. as_stack_val ty (m st))
Proof
  rw[fuel_ok_def] >> Cases_on `m st` >> gvs[as_stack_val_def] >> metis_tac[]
QED

Theorem fuel_ok_as_ptr_val:
  !ty loc m Wv L E.
    fuel_ok Wv L E m ==> fuel_ok Wv L E (\st. as_ptr_val ty loc (m st))
Proof
  rw[fuel_ok_def] >> Cases_on `m st` >> gvs[as_ptr_val_def] >> metis_tac[]
QED

Theorem fuel_ok_fresh_vars_bind[local]:
  !n k Wv L E.
    (!vs. fuel_ok (set vs UNION Wv) L E (k vs)) ==>
    fuel_ok Wv L E (comp_bind (fresh_vars n) k)
Proof
  Induct >> rpt strip_tac
  >- (simp[fresh_vars_def, comp_bind_return] >>
      first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  simp[fresh_vars_def, comp_bind_assoc, comp_bind_return] >>
  match_mp_tac fuel_ok_fresh_var >> gen_tac >> simp_tac std_ss [] >>
  first_x_assum match_mp_tac >> gen_tac >> simp_tac std_ss [] >>
  first_x_assum (qspec_then `x::vs` mp_tac) >>
  `set (x::vs) UNION Wv = set vs UNION (x INSERT Wv)` by
    (simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  simp[]
QED

(* Framework addition: the multi-output emit (INVOKE with several results). *)
Theorem fuel_ok_emit_multi_op:
  !opc ops n Wv E.
    ~is_terminator opc /\ opc <> PHI ==>
    fuel_ok Wv {} E (emit_multi_op opc ops n)
Proof
  rpt strip_tac >> simp_tac std_ss [emit_multi_op_def] >>
  match_mp_tac fuel_ok_fresh_vars_bind >> gen_tac >> simp_tac std_ss [] >>
  match_mp_tac fuel_ok_ignore_bind0 >> conj_tac
  >- (match_mp_tac fuel_ok_emit_inst >> simp[]) >>
  simp[fuel_ok_return]
QED

(* The lemmas every proof below uses. *)
val base = [fuel_ok_emit_op, fuel_ok_emit_void_any, fuel_ok_emit_inst_any,
            fuel_ok_emit_multi_op, fuel_ok_as_stack_val, fuel_ok_as_ptr_val,
            fuel_ok_compile_alloc_buffer, fuel_ok_compile_copy_memory,
            fuel_ok_compile_ptr_load, fuel_ok_compile_store_memory,
            fuel_ok_compile_imm_copy_to_memory, fuel_ok_context_copies,
            fuel_ok_context_storage, fuel_ok_compile_ensure_in_memory];

val helpers = [fuel_ok_unwrap_value, fuel_ok_compile_multi_vvs,
               fuel_ok_compile_keccak256_key, fuel_ok_compile_mapping_subscript,
               fuel_ok_compile_array_subscript, fuel_ok_compile_tuple_subscript,
               fuel_ok_compile_name_vv, fuel_ok_compile_stage_intcall_args,
               fuel_ok_store_multi_results, fuel_ok_compile_external_call_kwargs,
               fuel_ok_compile_extcall_store_values];

(* ===== lower_value and friends ===== *)

Theorem fuel_ok_lower_value:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ty e Wv E. fuel_ok Wv {} E (lower_value cfn cenv ty e)
Proof
  rpt strip_tac >> simp_tac std_ss [lower_value_def] >>
  fa (base @ helpers) >> simp[is_terminator_def]
QED

val lv = fuel_ok_lower_value;

Theorem fuel_ok_lower_value_with_loc:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ty e Wv E. fuel_ok Wv {} E (lower_value_with_loc cfn cenv ty e)
Proof
  rpt strip_tac >> simp_tac std_ss [lower_value_with_loc_def] >>
  fa (base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_get_target_ptr:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv tgt Wv E. fuel_ok Wv {} E (compile_get_target_ptr cfn cenv tgt)
Proof
  gen_tac >> strip_tac >> gen_tac >> Induct >> rpt gen_tac >>
  simp_tac std_ss [compile_get_target_ptr_def] >>
  fa (lv :: base @ helpers) >> simp[is_terminator_def]
QED

(* ===== Materialising ===== *)

Theorem fuel_ok_compile_materialize_vv:
  !cenv ty vv Wv E. fuel_ok Wv {} E (compile_materialize_vv cenv ty vv)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_materialize_vv_def] >>
  fa (base @ helpers) >> simp[is_terminator_def]
QED

(* ===== Expression lists ===== *)

Theorem fuel_ok_compile_concat:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !es cenv data_ptr infos off_ptr Wv E.
      fuel_ok Wv {} E (compile_concat cfn cenv es data_ptr infos off_ptr)
Proof
  gen_tac >> strip_tac >> Induct >> rpt gen_tac
  >- simp[compile_concat_def, fuel_ok_return] >>
  Cases_on `infos` >> simp[compile_concat_def, fuel_ok_return] >>
  rename1 `p::infos` >> PairCases_on `p` >>
  simp_tac std_ss [compile_concat_def] >>
  fa (lv :: base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_make_tuple:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !es cenv buf cur Wv E.
      fuel_ok Wv {} E (compile_make_tuple cfn cenv es buf cur)
Proof
  gen_tac >> strip_tac >> Induct >> rpt gen_tac >>
  simp_tac std_ss [compile_make_tuple_def] >>
  fa (base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_make_array_elems:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !es cenv elem_ty elem_size hlw buf idx Wv E.
      fuel_ok Wv {} E
        (compile_make_array_elems cfn cenv es elem_ty elem_size hlw buf idx)
Proof
  gen_tac >> strip_tac >> Induct >> rpt gen_tac >>
  simp_tac std_ss [compile_make_array_elems_def] >>
  fa (base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_make_array:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv es elem_ty elem_size hlw buf Wv E.
      fuel_ok Wv {} E
        (compile_make_array cfn cenv es elem_ty elem_size hlw buf)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_make_array_def] >>
  fa (fuel_ok_compile_make_array_elems :: base @ helpers) >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_multi_exprs:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !es cenv Wv E. fuel_ok Wv {} E (compile_multi_exprs cfn cenv es)
Proof
  gen_tac >> strip_tac >> Induct >> rpt gen_tac >>
  simp_tac std_ss [compile_multi_exprs_def] >>
  fa (lv :: base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_store_abi_tuple:
  !l cenv buf off Wv E.
    fuel_ok Wv {} E (compile_store_abi_tuple cenv buf off l)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_store_abi_tuple_def, fuel_ok_return] >>
  PairCases_on `h` >> simp_tac std_ss [compile_store_abi_tuple_def] >>
  fa (base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_extcall_store_args:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !es tys cenv buf off Wv E.
      fuel_ok Wv {} E (compile_extcall_store_args cfn cenv es tys buf off)
Proof
  gen_tac >> strip_tac >> Induct >> rpt gen_tac
  >- simp[compile_extcall_store_args_def, fuel_ok_return] >>
  Cases_on `tys` >> simp_tac std_ss [compile_extcall_store_args_def] >>
  fa (lv :: base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_abi_encode_args:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !es cenv Wv E. fuel_ok Wv {} E (compile_abi_encode_args cfn cenv es)
Proof
  gen_tac >> strip_tac >> Induct >> rpt gen_tac >>
  simp_tac std_ss [compile_abi_encode_args_def] >>
  fa (fuel_ok_compile_materialize_vv :: base @ helpers) >>
  simp[is_terminator_def]
QED

(* ===== Subscript, attribute, struct literals ===== *)

Theorem fuel_ok_compile_subscript:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ret_ty ty base_e idx_e Wv E.
      fuel_ok Wv {} E (compile_subscript cfn cenv ret_ty ty base_e idx_e)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_subscript_def] >>
  fa (lv :: base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_attribute:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ret_ty ty base_e field Wv E.
      fuel_ok Wv {} E (compile_attribute cfn cenv ret_ty ty base_e field)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_attribute_def] >>
  fa (base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_struct_lit:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !flds cenv ty buf off Wv E.
      fuel_ok Wv {} E (compile_struct_lit cfn cenv ty flds buf off)
Proof
  gen_tac >> strip_tac >> Induct >> rpt gen_tac
  >- simp[compile_struct_lit_def, fuel_ok_return] >>
  PairCases_on `h` >> simp_tac std_ss [compile_struct_lit_def] >>
  fa (base @ helpers) >> simp[is_terminator_def]
QED

(* ===== Materialising values ===== *)

Theorem fuel_ok_compile_ifexp_arm:
  !cenv res_ty arm_ty vv Wv E.
    fuel_ok Wv {} E (compile_ifexp_arm cenv res_ty arm_ty vv)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_ifexp_arm_def] >>
  fa (fuel_ok_compile_materialize_vv :: base @ helpers) >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_snapshot_vv:
  !cenv copy vv Wv E. fuel_ok Wv {} E (compile_snapshot_vv cenv copy vv)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_snapshot_vv_def] >>
  fa (fuel_ok_compile_materialize_vv :: base @ helpers) >>
  simp[is_terminator_def]
QED

(* ===== External-call keyword operands ===== *)

Theorem fuel_ok_compile_ext_call_kwarg:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv rt k e Wv E.
      fuel_ok Wv {} E (compile_ext_call_kwarg cfn cenv rt k e)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_ext_call_kwarg_def] >>
  fa (lv :: fuel_ok_compile_materialize_vv :: base @ helpers) >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_ext_call_kwargs:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !ks es cenv rt Wv E.
      fuel_ok Wv {} E (compile_ext_call_kwargs cfn cenv rt ks es)
Proof
  gen_tac >> strip_tac >> Induct >> rpt gen_tac
  >- simp[compile_ext_call_kwargs_def, fuel_ok_return] >>
  Cases_on `es` >> simp_tac std_ss [compile_ext_call_kwargs_def]
  >- simp[fuel_ok_return] >>
  fa (fuel_ok_compile_ext_call_kwarg :: base @ helpers) >>
  simp[is_terminator_def]
QED

(* ===== Creation operands ===== *)

Theorem fuel_ok_compile_create_salt:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv opt Wv E. fuel_ok Wv {} E (compile_create_salt cfn cenv opt)
Proof
  rpt strip_tac >> Cases_on `opt` >> simp_tac std_ss [compile_create_salt_def] >>
  fa (lv :: base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_create_ctor_tuple:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv args Wv E.
      fuel_ok Wv {} E (compile_create_ctor_tuple cfn cenv args)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_create_ctor_tuple_def] >>
  fa (base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_create_blueprint_args:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv raw args Wv E.
      fuel_ok Wv {} E (compile_create_blueprint_args cfn cenv raw args)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_create_blueprint_args_def] >>
  fa (lv :: fuel_ok_compile_create_ctor_tuple :: fuel_ok_compile_abi_encode_to_buf ::
      base @ helpers) >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_create_snapshot:
  !cenv vv ty Wv E. fuel_ok Wv {} E (compile_create_snapshot cenv vv ty)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_create_snapshot_def] >>
  fa (base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_raw_create:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv bytecode_e value_e ctor_args salt_e rof Wv E.
      fuel_ok Wv {} E
        (compile_raw_create cfn cenv bytecode_e value_e ctor_args salt_e rof)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_raw_create_def] >>
  fa (lv :: fuel_ok_compile_create_ctor_tuple :: fuel_ok_compile_create_salt ::
      fuel_ok_compile_create_snapshot :: fuel_ok_compile_abi_encode_to_buf ::
      fuel_ok_compile_create_dispatch :: base @ helpers) >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_create_call:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ck has_salt rof args Wv E.
      fuel_ok Wv {} E (compile_create_call cfn cenv ck has_salt rof args)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_create_call_def] >>
  fa (lv :: fuel_ok_compile_raw_create :: fuel_ok_compile_create_salt ::
      fuel_ok_compile_create_blueprint_args :: fuel_ok_compile_create_dispatch ::
      fuel_ok_compile_create_proxy_buf :: fuel_ok_compile_create_copy ::
      fuel_ok_compile_create_blueprint_check ::
      fuel_ok_compile_create_blueprint_append :: base @ helpers) >>
  simp[is_terminator_def]
QED

(* ===== Small dispatch helpers ===== *)

Theorem fuel_ok_compile_store_words:
  !vs buf off Wv E. fuel_ok Wv {} E (compile_store_words buf vs off)
Proof
  Induct >> rpt gen_tac >> simp_tac std_ss [compile_store_words_def] >>
  fa (base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_invert:
  !v ty cenv Wv E. fuel_ok Wv {} E (compile_invert v ty cenv)
Proof
  rpt gen_tac >> Cases_on `ty` >> simp_tac std_ss [compile_invert_def] >>
  fa (base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_acc:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv addr_e item Wv E.
      fuel_ok Wv {} E (compile_acc cfn cenv addr_e item)
Proof
  rpt strip_tac >> Cases_on `item` >>
  simp_tac std_ss [eta_def compile_acc_def] >>
  fa (lv :: base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_addmod_names:
  !cenv ret_ty aty a bty b mty m Wv E.
    fuel_ok Wv {} E (compile_addmod_names cenv ret_ty aty a bty b mty m)
Proof
  rpt gen_tac >> simp_tac std_ss [eta_def compile_addmod_names_def] >>
  fa (fuel_ok_compile_addmod :: base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_mulmod_names:
  !cenv ret_ty aty a bty b mty m Wv E.
    fuel_ok Wv {} E (compile_mulmod_names cenv ret_ty aty a bty b mty m)
Proof
  rpt gen_tac >> simp_tac std_ss [eta_def compile_mulmod_names_def] >>
  fa (fuel_ok_compile_mulmod :: base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_powmod256_names:
  !cenv ret_ty aty a bty b Wv E.
    fuel_ok Wv {} E (compile_powmod256_names cenv ret_ty aty a bty b)
Proof
  rpt gen_tac >> simp_tac std_ss [eta_def compile_powmod256_names_def] >>
  fa (fuel_ok_compile_pow_mod256 :: base @ helpers) >> simp[is_terminator_def]
QED

(* ===== compile_call, one theorem per call target ===== *)

Theorem fuel_ok_compile_call_int[local]:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ret_ty ty fid args dflt Wv E.
      fuel_ok Wv {} E (compile_call cfn cenv ret_ty ty (IntCall fid) args dflt)
Proof
  rpt strip_tac >>
  `?a b c. cenv.ce_func_info (nsid_to_string fid) = (a,b,c)` by
    (Cases_on `cenv.ce_func_info (nsid_to_string fid)` >> Cases_on `r` >> gvs[]) >>
  pop_assum (qx_choosel_then [`a`,`b`,`c`] (fn th =>
    simp_tac std_ss [eta_def compile_call_def, LET_THM, uncurry_map, th])) >>
  fa (lv :: base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_call_ext[local]:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ret_ty ty is_static skip fname atys rty opts args dflt Wv E.
      fuel_ok Wv {} E
        (compile_call cfn cenv ret_ty ty
           (ExtCall is_static skip (fname,atys,rty) opts) args dflt)
Proof
  rpt strip_tac >> Cases_on `args` >>
  simp_tac std_ss [eta_def compile_call_def, LET_THM, uncurry_map] >>
  fa (lv :: fuel_ok_compile_ext_call_kwargs :: base @ helpers) >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_call_send[local]:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ret_ty ty has_gas args dflt Wv E.
      fuel_ok Wv {} E (compile_call cfn cenv ret_ty ty (Send has_gas) args dflt)
Proof
  rpt strip_tac >> simp_tac std_ss [eta_def compile_call_def, LET_THM, uncurry_map] >>
  fa (lv :: base @ helpers) >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_call_rawcall[local]:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ret_ty ty rcf args dflt Wv E.
      fuel_ok Wv {} E
        (compile_call cfn cenv ret_ty ty (RawCallTarget rcf) args dflt)
Proof
  rpt strip_tac >> simp_tac std_ss [eta_def compile_call_def, LET_THM, uncurry_map] >>
  fa (lv :: fuel_ok_compile_ext_call_kwargs :: fuel_ok_compile_raw_call_outbuf ::
      fuel_ok_compile_raw_call_finish :: base @ helpers) >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_call_rawcalldata[local]:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ret_ty ty rcf args dflt Wv E.
      fuel_ok Wv {} E
        (compile_call cfn cenv ret_ty ty (RawCallCalldataTarget rcf) args dflt)
Proof
  rpt strip_tac >> simp_tac std_ss [eta_def compile_call_def, LET_THM, uncurry_map] >>
  fa (lv :: fuel_ok_compile_ext_call_kwargs :: fuel_ok_compile_raw_call_outbuf ::
      fuel_ok_compile_raw_call_finish :: fuel_ok_compile_msg_data_to_memory ::
      base @ helpers) >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_call_rawlog[local]:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ret_ty ty args dflt Wv E.
      fuel_ok Wv {} E (compile_call cfn cenv ret_ty ty RawLog args dflt)
Proof
  rpt strip_tac >> simp_tac std_ss [eta_def compile_call_def, LET_THM, uncurry_map] >>
  fa (lv :: fuel_ok_compile_multi_exprs :: base @ helpers) >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_call_rawrevert[local]:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ret_ty ty args dflt Wv E.
      fuel_ok Wv {} E (compile_call cfn cenv ret_ty ty RawRevert args dflt)
Proof
  rpt strip_tac >> simp_tac std_ss [eta_def compile_call_def, LET_THM, uncurry_map] >>
  fa (lv :: fuel_ok_compile_raw_revert :: base @ helpers) >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_call_selfdestruct[local]:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ret_ty ty args dflt Wv E.
      fuel_ok Wv {} E
        (compile_call cfn cenv ret_ty ty SelfDestructTarget args dflt)
Proof
  rpt strip_tac >> simp_tac std_ss [eta_def compile_call_def, LET_THM, uncurry_map] >>
  fa (lv :: fuel_ok_compile_selfdestruct :: base @ helpers) >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_call:
  !cfn. (!c t e Wv E. fuel_ok Wv {} E (cfn c t e)) ==>
    !cenv ret_ty ty target args dflt Wv E.
      fuel_ok Wv {} E (compile_call cfn cenv ret_ty ty target args dflt)
Proof
  rpt strip_tac >> Cases_on `target`
  >- (irule (pn fuel_ok_compile_call_int) >> first_assum ACCEPT_TAC)
  >- (rename1 `ExtCall _ _ sg _` >> PairCases_on `sg` >>
      irule (pn fuel_ok_compile_call_ext) >> first_assum ACCEPT_TAC)
  >- (irule (pn fuel_ok_compile_call_send) >> first_assum ACCEPT_TAC)
  >- (irule (pn fuel_ok_compile_call_rawcall) >> first_assum ACCEPT_TAC)
  >- (irule (pn fuel_ok_compile_call_rawcalldata) >> first_assum ACCEPT_TAC)
  >- (irule (pn fuel_ok_compile_call_rawlog) >> first_assum ACCEPT_TAC)
  >- (irule (pn fuel_ok_compile_call_rawrevert) >> first_assum ACCEPT_TAC)
  >- (irule (pn fuel_ok_compile_call_selfdestruct) >> first_assum ACCEPT_TAC) >>
  simp_tac std_ss [eta_def compile_call_def] >>
  match_mp_tac fuel_ok_as_stack_val >>
  irule (pn fuel_ok_compile_create_call) >> first_assum ACCEPT_TAC
QED
