(*
 * External Return ABI Plan Properties
 *
 * The encoding plan and buffer size update_cenv_ret_abi puts in the compile
 * env are right for the source's ABI encoding of the return value: the plan
 * meets abi_enc_plan and the size is vyper_abi_size_bound, of the return
 * type wrapped in a singleton tuple when the ABI wraps it and it is dynamic.
 * The compiler reads struct fields from make_struct_fields_map, which agrees
 * with type_env (structFieldsProps), so its ABI sizes and flags agree with
 * the source's: is_abi_dynamic, abi_static_size and abi_size_bound with
 * vyper_is_dynamic and vyper_abi_size_bound (as in Python's abi_types.py,
 * ABIType.is_dynamic/static_size/size_bound).
 *
 * TOP-LEVEL:
 *   update_cenv_ret_abi_plan -- the plan and size of a return type
 *   build_compile_env_ret_abi_plan -- the same at build_compile_env
 * Helpers:
 *   vyper_to_abi_type_submap -- evaluation and ABI type in a larger env
 *   abi_props_vyper -- compile-side ABI sizes and flags are the source's
 *   type_to_abi_enc_info_plan -- type_to_abi_enc_info builds a plan
 *)

Theory retAbiPlanProps
Ancestors
  compileVyper compileEnv exprLowering abiEncoderProps structFieldsProps
  vyperTypeSystem vyperContext vyperValue vyperABI contractABI
  valueEncoding finite_map list rich_list pair combin

(* ===== Source side ===== *)

(* Evaluation and the ABI type are stable under a larger type env: a type
   that evaluates names only structs its env has. *)
Theorem vyper_to_abi_type_submap:
  (!env ty tv.
     evaluate_type env ty = SOME tv ==>
     !tenv. env SUBMAP tenv ==>
            evaluate_type tenv ty = SOME tv /\
            vyper_to_abi_type env ty = vyper_to_abi_type tenv ty) /\
  (!env ts acc tvs.
     evaluate_types env ts acc = SOME tvs ==>
     !tenv. env SUBMAP tenv ==>
            evaluate_types tenv ts acc = SOME tvs /\
            vyper_to_abi_types env ts = vyper_to_abi_types tenv ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt strip_tac >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      `FLOOKUP tenv nsid = SOME (StructArgs args)`
        by fs[SUBMAP_FLOOKUP_EQN] >>
      `env \\ nsid SUBMAP tenv \\ nsid`
        by fs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
      first_x_assum drule >> simp[])
  >~ [`FlagT nsid`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      fs[SUBMAP_FLOOKUP_EQN])
  >~ [`ArrayT t bd`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      first_x_assum drule >> Cases_on `bd` >> simp[])
  >> rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

Theorem vyper_to_abi_type_dynamic:
  (!tenv ty tv.
     evaluate_type tenv ty = SOME tv ==>
     is_dynamic (vyper_to_abi_type tenv ty) = vyper_is_dynamic tenv ty) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs ==>
     any_dynamic (vyper_to_abi_types tenv ts) = vyper_any_dynamic tenv ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[evaluate_type_def, vyper_is_dynamic_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> TRY (Cases_on `bd`) >> gvs[vyper_is_dynamic_def]
QED

Theorem vyper_to_abi_static_length:
  (!tenv ty tv.
     evaluate_type tenv ty = SOME tv /\ ~vyper_is_dynamic tenv ty ==>
     static_length (vyper_to_abi_type tenv ty) = vyper_abi_size_bound tenv ty) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs /\ ~vyper_any_dynamic tenv ts ==>
     static_length (Tuple (vyper_to_abi_types tenv ts)) =
     vyper_abi_size_bound_list tenv ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[evaluate_type_def, vyper_is_dynamic_def, vyper_abi_size_bound_def,
       AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> TRY (Cases_on `bd`) >>
  gvs[vyper_is_dynamic_def, vyper_abi_size_bound_def, static_length_Tuple_SUM]
QED

(* ===== Compile side against the source ===== *)

(* The struct map stays consistent with the type env when both drop the same
   struct, as long as every struct key of the env is a main-module one (so
   nsid_to_string tells the env's structs apart). *)
Theorem sfields_tenv_consistent_domsub:
  sfields_tenv_consistent sf tenv /\
  (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
  FLOOKUP tenv nsid = SOME (StructArgs args) ==>
  sfields_tenv_consistent (sf \\ nsid_to_string nsid) (tenv \\ nsid) /\
  (!k a. FLOOKUP (tenv \\ nsid) k = SOME (StructArgs a) ==> FST k = NONE)
Proof
  strip_tac >>
  `!k a. FLOOKUP tenv k = SOME (StructArgs a) /\ k <> nsid ==>
         nsid_to_string k <> nsid_to_string nsid`
    by (rpt strip_tac >> res_tac >>
        Cases_on `k` >> Cases_on `nsid` >> gvs[nsid_to_string_def]) >>
  fs[sfields_tenv_consistent_def, DOMSUB_FLOOKUP_THM] >> rpt strip_tac
  >~ [`nsid_to_string _ <> name`]
  >- (res_tac >> qexistsl [`nsid'`, `args'`] >> simp[] >>
      strip_tac >> gvs[])
QED

Theorem abi_props_vyper:
  (!tenv ty tv.
     evaluate_type tenv ty = SOME tv ==>
     !sf. sfields_tenv_consistent sf tenv /\
          (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) ==>
          is_abi_dynamic sf ty = vyper_is_dynamic tenv ty /\
          abi_size_bound sf ty = vyper_abi_size_bound tenv ty /\
          (~vyper_is_dynamic tenv ty ==>
           abi_static_size sf ty = vyper_abi_size_bound tenv ty)) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs ==>
     !sf. sfields_tenv_consistent sf tenv /\
          (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) ==>
          EXISTS (is_abi_dynamic sf) ts = vyper_any_dynamic tenv ts /\
          SUM (MAP (\t. (if is_abi_dynamic sf t then 32
                         else abi_static_size sf t) +
                        (if is_abi_dynamic sf t then abi_size_bound sf t
                         else 0)) ts) =
            vyper_abi_size_bound_list tenv ts /\
          (~vyper_any_dynamic tenv ts ==>
           SUM (MAP (\t. if is_abi_dynamic sf t then 32
                         else abi_static_size sf t) ts) =
             vyper_abi_size_bound_list tenv ts))
Proof
  cheat
QED

(* ===== Encoding plans ===== *)

(* What a plan element needs of a component type evaluating in a smaller
   env than the compiler's struct map stands for. *)
Theorem abi_elem_props:
  tenv SUBMAP tenv0 /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
  (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type tenv0 t = SOME tv ==>
          type_memory_bytes cenv t = type_memory_size tv) /\
  evaluate_type tenv t = SOME tv ==>
  is_abi_dynamic cenv.ce_struct_fields t =
    is_dynamic (vyper_to_abi_type tenv t) /\
  abi_embedded_static_size cenv.ce_struct_fields t =
    (if is_dynamic (vyper_to_abi_type tenv t) then 32
     else static_length (vyper_to_abi_type tenv t)) /\
  abi_size_bound cenv.ce_struct_fields t = vyper_abi_size_bound tenv0 t /\
  type_memory_bytes cenv t = type_memory_size tv
Proof
  cheat
QED

Theorem abi_enc_plans_map:
  !ts.
    tenv SUBMAP tenv0 /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
    (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
    (!t tv. evaluate_type tenv0 t = SOME tv ==>
            type_memory_bytes cenv t = type_memory_size tv) /\
    (!t. MEM t ts ==>
         IS_SOME (evaluate_type tenv t) /\ abi_enc_plan tenv t (f t)) ==>
    abi_enc_plans tenv ts
      (MAP (\t. (f t, abi_embedded_static_size cenv.ce_struct_fields t,
                 type_memory_bytes cenv t,
                 is_abi_dynamic cenv.ce_struct_fields t)) ts)
Proof
  cheat
QED

(* type_to_abi_enc_info builds a plan for an assignable type (which has no
   NoneT inside: the compiler gives NoneT AbiComplex [], for which there is
   no plan). sf is the struct map the recursion has narrowed to tenv's
   structs; the sizes and flags come from the whole map. *)
Theorem type_to_abi_enc_info_plan:
  !tenv ty.
    assignable_type tenv ty ==>
    !sf cenv tenv0.
      tenv SUBMAP tenv0 /\
      sfields_tenv_consistent sf tenv /\
      (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
      sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
      (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
      (!t tv. evaluate_type tenv0 t = SOME tv ==>
              type_memory_bytes cenv t = type_memory_size tv) ==>
      abi_enc_plan tenv ty (type_to_abi_enc_info sf cenv ty)
Proof
  cheat
QED

(* ===== The return plan ===== *)

Theorem external_return_needs_wrap_eq:
  external_return_needs_wrap ty = needs_external_call_wrap ty
Proof
  Cases_on `ty` >> simp[external_return_needs_wrap_def,
                        needs_external_call_wrap_def] >>
  rename1 `TupleT ts` >> Cases_on `ts` >>
  simp[external_return_needs_wrap_def] >>
  rename1 `TupleT (_ :: ts)` >> Cases_on `ts` >>
  simp[external_return_needs_wrap_def]
QED

(* The return's encoding plan and buffer size: for an assignable return type
   (not NoneT, and none inside it), the plan update_cenv_ret_abi builds is a
   plan for the type the ABI encodes, and the buffer is exactly its ABI size
   bound. *)
Theorem update_cenv_ret_abi_plan:
  !tops cenv ret.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    assignable_type (type_env tops) ret ==>
    abi_enc_plan (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret)
      (update_cenv_ret_abi cenv ret).ce_ret_enc_info /\
    vyper_abi_size_bound (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret) =
      (update_cenv_ret_abi cenv ret).ce_max_return_size
Proof
  cheat
QED

Theorem build_compile_env_ret_abi_plan:
  !tops vis mut func_name args ret_type fn_body use_trans ret.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    assignable_type (type_env tops) ret ==>
    abi_enc_plan (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret)
      (update_cenv_ret_abi
         (build_compile_env tops vis mut func_name args ret_type fn_body
            use_trans) ret).ce_ret_enc_info /\
    vyper_abi_size_bound (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret) =
      (update_cenv_ret_abi
         (build_compile_env tops vis mut func_name args ret_type fn_body
            use_trans) ret).ce_max_return_size
Proof
  rpt gen_tac >> strip_tac >> irule update_cenv_ret_abi_plan >>
  simp[build_compile_env_ce_struct_fields]
QED
