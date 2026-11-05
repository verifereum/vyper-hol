(*
 * Entry argument decoding: the compiler's decode plans and head offsets
 * (#639)
 *
 * The decode info build_positional_arg puts in a positional argument
 * (type_to_abi_dec_info) is an abi_dec_plan for every static assignable
 * type, and the decoder's head offsets (the running sum of
 * abi_embedded_static_size that compile_register_positional_args steps by)
 * are the ABI's (abi_head_size), whatever the earlier arguments' types.
 * Both need the compile env to agree with the type environment
 * (dec_cenv_agrees), as the encoder's plans do (retAbiPlanProps).
 *
 * TOP-LEVEL:
 *   int_byte_widths — every signed integer type in a type value is a whole
 *     number of bytes wide
 *   dec_cenv_agrees — the compile env's struct fields, memory sizes and
 *     flag member counts are the type environment's
 *   type_to_abi_dec_info_plan — type_to_abi_dec_info builds a plan for a
 *     static assignable type
 *   decode_head_offset — the decoder's head offset is the ABI's
 *   compile_decode_static_arg_calldata — a static non-word argument of
 *     calldata that encodes the call decodes to the source value at its
 *     ALLOCA
 *   compile_decode_word_arg_calldata — the same for a word argument
 *   make_struct_fields_map_dec_cenv_agrees — dec_cenv_agrees holds of an
 *     env with the compiler's struct map, given the flag counts
 *   package_external_fn_dec_cenv_agrees — package_external_fn's positional
 *     arguments are build_positional_args at an env where dec_cenv_agrees
 *     holds
 *
 * Helpers: static_length_memory_size, vyper_to_abi_static_enc_length,
 *   abi_dec_plans_map, abi_head_size_embedded, build_flag_info_n_members.
 *)
Theory entryDecodePlanProps
Ancestors
  arithmetic list rich_list finite_map
  entryDecodeStaticProps entryDecodeProps retAbiPlanProps structFieldsProps
  valueEncodingProofs valueEncoding
  vyperABI vyperABIRoundtrip vyperTyping vyperValue vyperTypeSystem
  vyperMisc vyperTypeABI contractABI
  compileEnv compileVyper exprLowering moduleLowering selectorDispatch
  fragExec

(* ===== Hypotheses ===== *)

(* Every signed integer type inside a type value is a whole number of bytes
   wide, as Vyper's int8 ... int256 are.  The decoder's clamp for intN
   sign-extends from byte N DIV 8 - 1, so it accepts every intN value only
   for those widths.  evaluate_type admits only such widths
   (evaluate_type_int_byte_widths in entryStateRel). *)
Definition int_byte_widths_def:
  int_byte_widths (BaseTV (IntT m)) = (m MOD 8 = 0) /\
  int_byte_widths (TupleTV tvs) = EVERY int_byte_widths tvs /\
  int_byte_widths (ArrayTV tv _) = int_byte_widths tv /\
  int_byte_widths (StructTV fields) = EVERY (int_byte_widths o SND) fields /\
  int_byte_widths _ = T
End

(* The compile env agrees with the type environment tenv: its struct map
   has tenv's structs with their field types (make_struct_fields_map, see
   structFieldsProps), every struct is the main module's (so
   nsid_to_string tells them apart), type_memory_bytes is the memory size
   of the evaluated type, and a flag's member count is tenv's. *)
Definition dec_cenv_agrees_def:
  dec_cenv_agrees cenv tenv <=>
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
    (!t tv. evaluate_type tenv t = SOME tv ==>
            type_memory_bytes cenv t = type_memory_size tv) /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m)
End

(* ===== Sizes of static types ===== *)

Theorem static_length_memory_size:
  (!tenv ty tv.
     evaluate_type tenv ty = SOME tv /\
     ~is_dynamic (vyper_to_abi_type tenv ty) ==>
     static_length (vyper_to_abi_type tenv ty) = type_memory_size tv) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs /\
     ~any_dynamic (vyper_to_abi_types tenv ts) ==>
     static_length (Tuple (vyper_to_abi_types tenv ts)) +
       SUM (MAP type_memory_size acc) = SUM (MAP type_memory_size tvs))
Proof
  cheat
QED

Theorem length_flat_map2_replicate[local]:
  !xs t k.
    (!i. i < LENGTH xs ==> LENGTH (enc t (EL i xs)) = k) ==>
    LENGTH (FLAT (MAP2 enc (REPLICATE (LENGTH xs) t) xs)) = LENGTH xs * k
Proof
  cheat
QED

Theorem length_word_to_bytes_256[local,simp]:
  LENGTH (word_to_bytes (w:bytes32) T) = 32
Proof
  cheat
QED

(* A static value's ABI encoding takes its memory size. *)
Theorem vyper_to_abi_static_enc_length:
  (!env ty. !tv v av.
     evaluate_type env ty = SOME tv /\
     ~is_dynamic (vyper_to_abi_type env ty) /\
     value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
     LENGTH (enc (vyper_to_abi_type env ty) av) = type_memory_size tv) /\
  (!env ts. !tvs vs avs.
     OPT_MMAP (evaluate_type env) ts = SOME tvs /\
     EVERY is_static (vyper_to_abi_types env ts) /\
     values_have_types tvs vs /\ vyper_to_abi_list env ts vs = SOME avs ==>
     LENGTH avs = LENGTH ts /\
     LENGTH (FLAT (MAP2 enc (vyper_to_abi_types env ts) avs)) =
       SUM (MAP type_memory_size tvs))
Proof
  cheat
QED







(* ===== Plans ===== *)

Theorem vyper_to_abi_types_MAP[local]:
  !env ts. vyper_to_abi_types env ts = MAP (vyper_to_abi_type env) ts
Proof
  cheat
QED

Theorem OPT_MMAP_MEM[local]:
  !ts tvs t. OPT_MMAP f ts = SOME tvs /\ MEM t ts ==>
             ?tv. f t = SOME tv /\ MEM tv tvs
Proof
  cheat
QED

Theorem EVERY_SND_ZIP[local]:
  !l1 l2. LENGTH l1 = LENGTH l2 ==>
          (EVERY (P o SND) (ZIP (l1, l2)) <=> EVERY P l2)
Proof
  cheat
QED

Theorem map_field_types[local]:
  !fields. MAP (\(fn, fty, sz). g fty) fields = MAP g (MAP (FST o SND) fields)
Proof
  cheat
QED

Theorem dec_cenv_agrees_struct_keys[local]:
  tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 ==>
  (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE)
Proof
  cheat
QED

Theorem dec_cenv_agrees_flags[local]:
  tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 ==>
  (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
            cenv.ce_flag_n_members (nsid_to_string nsid) = m)
Proof
  cheat
QED

(* What a plan element needs of a static component type. *)
Theorem dec_cenv_agrees_elem[local]:
  tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 /\
  evaluate_type tenv t = SOME tv /\ ~is_dynamic (vyper_to_abi_type tenv t) ==>
  ~is_abi_dynamic cenv.ce_struct_fields t /\
  abi_embedded_static_size cenv.ce_struct_fields t = type_memory_size tv /\
  type_memory_bytes cenv t = type_memory_size tv
Proof
  cheat
QED

Theorem abi_dec_plans_map:
  !tenv tenv0 cenv f ts.
    tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 /\
    (!t. MEM t ts ==>
         IS_SOME (evaluate_type tenv t) /\
         ~is_dynamic (vyper_to_abi_type tenv t) /\
         abi_dec_plan tenv t (f t)) ==>
    ~EXISTS (is_abi_dynamic cenv.ce_struct_fields) ts /\
    abi_dec_plans tenv ts
      (MAP (\t. (f t, abi_embedded_static_size cenv.ce_struct_fields t,
                 type_memory_bytes cenv t)) ts)
Proof
  cheat
QED

(* The StructT case of type_to_abi_dec_info_plan, given each field's plan
   (the induction hypothesis). *)
Theorem type_to_abi_dec_info_plan_struct[local]:
  FLOOKUP tenv nsid = SOME (StructArgs args) /\
  EVERY (assignable_type (tenv \\ nsid) o SND) args /\
  (!x. MEM x args ==>
     assignable_type (tenv \\ nsid) (SND x) ==>
     !(sf' : (string, (string # type # num) list) fmap) cenv tenv1 tv.
       tenv \\ nsid SUBMAP tenv1 /\ dec_cenv_agrees cenv tenv1 /\
       sfields_tenv_consistent sf' (tenv \\ nsid) /\
       evaluate_type (tenv \\ nsid) (SND x) = SOME tv /\ int_byte_widths tv /\
       ~is_dynamic (vyper_to_abi_type (tenv \\ nsid) (SND x)) ==>
       abi_dec_plan (tenv \\ nsid) (SND x)
         (type_to_abi_dec_info sf' cenv (SND x))) /\
  tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 /\
  sfields_tenv_consistent (sf : (string, (string # type # num) list) fmap)
    tenv /\
  evaluate_type tenv (StructT nsid) = SOME tv /\ int_byte_widths tv /\
  ~is_dynamic (vyper_to_abi_type tenv (StructT nsid)) ==>
  abi_dec_plan tenv (StructT nsid) (type_to_abi_dec_info sf cenv (StructT nsid))
Proof
  cheat
QED

(* The TupleT case of type_to_abi_dec_info_plan, given each component's
   plan (the induction hypothesis). *)
Theorem type_to_abi_dec_info_plan_tuple[local]:
  (!ty. MEM ty tys ==>
     assignable_type tenv ty ==>
     !(sf : (string, (string # type # num) list) fmap) cenv tenv0 tv.
       tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 /\
       sfields_tenv_consistent sf tenv /\
       evaluate_type tenv ty = SOME tv /\ int_byte_widths tv /\
       ~is_dynamic (vyper_to_abi_type tenv ty) ==>
       abi_dec_plan tenv ty (type_to_abi_dec_info sf cenv ty)) /\
  assignable_type tenv (TupleT tys) /\
  tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 /\
  sfields_tenv_consistent (sf : (string, (string # type # num) list) fmap)
    tenv /\
  evaluate_type tenv (TupleT tys) = SOME tv /\ int_byte_widths tv /\
  ~is_dynamic (vyper_to_abi_type tenv (TupleT tys)) ==>
  abi_dec_plan tenv (TupleT tys) (type_to_abi_dec_info sf cenv (TupleT tys))
Proof
  cheat
QED

(* type_to_abi_dec_info builds a plan for a static assignable type.  sf is
   the struct map the recursion has narrowed to tenv's structs; sizes and
   flags come from the whole compile env, which agrees with tenv0. *)
Theorem type_to_abi_dec_info_plan:
  !tenv ty.
    assignable_type tenv ty ==>
    !(sf : (string, (string # type # num) list) fmap) cenv tenv0 tv.
      tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 /\
      sfields_tenv_consistent sf tenv /\
      evaluate_type tenv ty = SOME tv /\ int_byte_widths tv /\
      ~is_dynamic (vyper_to_abi_type tenv ty) ==>
      abi_dec_plan tenv ty (type_to_abi_dec_info sf cenv ty)
Proof
  cheat
QED

(* ===== Head offsets ===== *)

(* An argument takes as many bytes in the ABI head as the decoder steps
   over for it. *)
Theorem abi_head_size_embedded:
  !cenv tenv t tv v av.
    dec_cenv_agrees cenv tenv /\ evaluate_type tenv t = SOME tv /\
    value_has_type tv v /\ vyper_to_abi tenv t v = SOME av ==>
    abi_head_size (vyper_to_abi_type tenv t) av =
    abi_embedded_static_size cenv.ce_struct_fields t
Proof
  cheat
QED

(* The decoder's head offset for argument i (abi_embedded_static_size
   summed over the earlier arguments, as compile_register_positional_args
   steps) is the ABI's, whatever the earlier arguments' types. *)
Theorem decode_head_offset:
  !cenv tenv tys vals avs i.
    dec_cenv_agrees cenv tenv /\
    vyper_to_abi_list tenv tys vals = SOME avs /\ i <= LENGTH tys /\
    (!j. j < i ==> ?tv. evaluate_type tenv (EL j tys) = SOME tv /\
                        value_has_type tv (EL j vals)) ==>
    SUM (MAP2 abi_head_size (TAKE i (vyper_to_abi_types tenv tys))
                            (TAKE i avs)) =
    SUM (MAP (abi_embedded_static_size cenv.ce_struct_fields) (TAKE i tys))
Proof
  cheat
QED

(* ===== Arguments of calldata that encodes the call ===== *)

Theorem map_embedded_take[local]:
  MAP (abi_embedded_static_size sf o SND) (TAKE i args) =
  MAP (abi_embedded_static_size sf) (TAKE i (MAP SND args))
Proof
  cheat
QED

(* The ABI head offset of argument i is the decoder's off. *)
Theorem calldata_head_offset[local]:
  dec_cenv_agrees cenv0 tenv /\
  vyper_to_abi_list tenv (MAP SND args) vals = SOME avs /\
  i < LENGTH args /\
  (!j. j < i ==> ?tv. evaluate_type tenv (SND (EL j args)) = SOME tv /\
                      value_has_type tv (EL j vals)) ==>
  4 + SUM (MAP2 abi_head_size (TAKE i (vyper_to_abi_types tenv (MAP SND args)))
                              (TAKE i avs)) =
  4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
               (TAKE i args))
Proof
  cheat
QED

(* A static argument other than a word, of calldata that encodes the call,
   decodes without reverting to the source value in memory at its ALLOCA.
   off is where compile_register_positional_args decodes argument i from:
   4 plus the abi sizes build_positional_arg gives the earlier arguments.
   The earlier arguments may be of any (well-typed) type. *)
Theorem compile_decode_static_arg_calldata:
  !cenv cenv0 tenv fname args vals i off hi st st' ctx loc dst s0 p tv.
    dec_cenv_agrees cenv0 tenv /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                       (TAKE i args)) /\
    compile_decode_args cenv [build_positional_arg cenv0 (EL i args)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    calldata_encodes tenv fname (MAP SND args) vals
      s0.vs_call_ctx.cc_calldata /\
    LENGTH vals = LENGTH args /\ i < LENGTH args /\
    (!j. j < i ==> ?tv. evaluate_type tenv (SND (EL j args)) = SOME tv /\
                        value_has_type tv (EL j vals)) /\
    assignable_type tenv (SND (EL i args)) /\
    ~is_word_type (SND (EL i args)) /\
    ~is_dynamic (vyper_to_abi_type tenv (SND (EL i args))) /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\ int_byte_widths tv /\
    value_has_type tv (EL i vals) /\
    off + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv < dimword (:256) ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. dec_frame st (w2n p) (type_memory_size tv) s0 t /\
           fresh_vars_wrt st' t /\
           val_in_memory tv (EL i vals) (w2n p) t.vs_memory)
      (\r. F)
Proof
  cheat
QED

(* The same for a word argument (#739's compile_decode_word_arg_correct,
   at the head offset of calldata that encodes the call). *)
Theorem compile_decode_word_arg_calldata:
  !cenv cenv0 tenv fname args vals i off hi st st' ctx loc dst s0 p tv.
    dec_cenv_agrees cenv0 tenv /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                       (TAKE i args)) /\
    compile_decode_args cenv [build_positional_arg cenv0 (EL i args)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    calldata_encodes tenv fname (MAP SND args) vals
      s0.vs_call_ctx.cc_calldata /\
    LENGTH vals = LENGTH args /\ i < LENGTH args /\
    (!j. j < i ==> ?tv. evaluate_type tenv (SND (EL j args)) = SOME tv /\
                        value_has_type tv (EL j vals)) /\
    is_word_type (SND (EL i args)) /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\ int_byte_widths tv /\
    value_has_type tv (EL i vals) /\
    off < dimword (:256) ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. vars_pc_only (mstore (w2n p) (typed_val_to_w256 tv (EL i vals)) s0)
             t /\
           fresh_vars_wrt st' t /\
           (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0) /\
           val_in_memory tv (EL i vals) (w2n p) t.vs_memory)
      (\r. F)
Proof
  cheat
QED

(* ===== The compiler's env ===== *)

(* dec_cenv_agrees holds of an env whose struct map is the compiler's
   (build_compile_env's), for a contract whose type keys are distinct,
   given the flag member counts (see exprSimHyps on why
   build_compile_env's counts need not be the source's). *)
Theorem make_struct_fields_map_dec_cenv_agrees:
  !tops cenv.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    (!nsid m. FLOOKUP (type_env tops) nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    dec_cenv_agrees cenv (type_env tops)
Proof
  cheat
QED

(* build_flag_info's member counts are type_env's, for distinct keys. *)
Theorem build_flag_info_other[local]:
  !tops fmid fnm id.
    ~MEM (NONE, id)
       (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) ==>
    SND (build_flag_info tops fmid fnm) id = fnm id
Proof
  cheat
QED

Theorem build_flag_info_n_members[local]:
  !tops fmid fnm nsid m.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    FLOOKUP (type_env_for_module NONE tops) nsid = SOME (FlagArgs m) ==>
    SND (build_flag_info tops fmid fnm) (nsid_to_string nsid) = m
Proof
  cheat
QED

Theorem build_compile_env_ce_flag_n_members[local]:
  !tops vis mut func_name args ret_type (body : stmt list) use_trans.
    (build_compile_env tops vis mut func_name args ret_type body use_trans).
      ce_flag_n_members = SND (build_flag_info tops (K (K 0)) (K 0))
Proof
  cheat
QED

(* package_external_fn decodes its positional arguments with the decode
   infos of build_positional_args, at an env that agrees with the
   contract's type environment. *)
Theorem package_external_fn_dec_cenv_agrees:
  !tops use_trans nkey_map mut nr rr fname fargs dflts ret body
   lbl cenv pos_args rest.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    package_external_fn tops use_trans nkey_map
      (mut, nr, rr, fname, fargs, dflts, ret, body) =
      (lbl, cenv, pos_args, rest) ==>
    pos_args = build_positional_args cenv fargs /\
    dec_cenv_agrees cenv (type_env tops)
Proof
  cheat
QED
