(*
 * Entry argument decoding: static complex arguments (#639)
 *
 * TOP-LEVEL:
 *   abi_dec_plan — what a decode info must be for a static type, as
 *     abi_enc_plan is for encoding
 *   abi_dec_plan_value — for a value of the type, a plan is static, its
 *     clamps accept the value's encoding wherever it sits, and memory
 *     holding the encoding holds the value (the converse of
 *     val_in_memory_static_abi)
 *   compile_abi_decode_static_buf_correct — compile_abi_decode_to_buf from
 *     calldata holding a static value's encoding leaves the value in
 *     memory at the destination, without reverting
 *   calldata_encodes_static_arg — calldata that encodes a call holds a
 *     static argument's encoding at the argument's head offset
 *   compile_decode_static_arg_correct — the static, non-word path of
 *     compile_decode_args (tuples, structs, static arrays): the argument
 *     ends in memory at its ALLOCA (val_in_memory)
 *   type_to_abi_dec_info_word_plan — a word type's decode info is a plan
 *   type_to_abi_dec_info_word_tuple_plan,
 *   type_to_abi_dec_info_word_sarray_plan — so is that of a tuple of word
 *     types and of a static array of a word type (abi_dec_plan is not
 *     vacuous for the infos the compiler builds)
 *
 * Helpers: dec_value, decs_value, sparse_val and their lemmas.
 *
 * Not here: that type_to_abi_dec_info builds plans for every static
 * complex type (structs, nested aggregates), and that the decoder's head
 * offsets (abi_embedded_static_size) match the ABI's for them.  Both
 * need the compile env's struct metadata and sizes (ce_struct_fields,
 * type_memory_bytes, abi_embedded_static_size) to agree with the type
 * environment, as the encoder's plans do (abi_enc_plan).  For a word
 * type the plan follows from word_arg_clamp_ok
 * (type_to_abi_dec_info_word_plan).
 *)
Theory entryDecodeStaticProps
Ancestors
  exprSimProps arithmetic list rich_list words sorting alist
  abiDecodeStaticProps entryDecodeProps entryDispatchProps moduleLoweringProps
  valueEncodingProofs valueEncodingProps valueEncoding
  vyperABI vyperABIRoundtrip vyperTyping vyperTypeDefaults vyperTypeABI
  vyperValue vfmTypes
  compileEnv exprLowering moduleLowering selectorDispatch
  emitHelperProps fragExec venomState
Libs
  wordsLib

(* ===== Decode plans ===== *)

(* abi_dec_plan env ty info: info decodes a static value of type ty in type
   environment env.  A word's clamp accepts every value of its type; an
   aggregate's elements are its components in order (a struct's typed in
   env \\ nsid, as vyper_to_abi_type does), each taking its memory size in
   the ABI head; a static array repeats its element's plan.  Dynamic types
   have no plan here. *)
Inductive abi_dec_plan:
[~prim:]
  is_word_type ty /\
  (!tv v. evaluate_type env ty = SOME tv /\ value_has_type tv v ==>
          abi_clamp_ok c (typed_val_to_w256 tv v)) ==>
  abi_dec_plan env ty (DecPrimWord c)
[~tuple:]
  abi_dec_plans env ts elems ==>
  abi_dec_plan env (TupleT ts) (DecComplex F elems)
[~sarray:]
  evaluate_type env t = SOME tv /\ abi_dec_plan env t ei ==>
  abi_dec_plan env (ArrayT t (Fixed n))
    (DecComplex F
       (REPLICATE n (ei, type_memory_size tv, type_memory_size tv)))
[~struct:]
  FLOOKUP env nsid = SOME (StructArgs args) /\
  abi_dec_plans (env \\ nsid) (MAP SND args) elems ==>
  abi_dec_plan env (StructT nsid) (DecComplex F elems)
[~nil:]
  abi_dec_plans env [] []
[~cons:]
  evaluate_type env t = SOME tv /\ abi_dec_plan env t ei /\
  abi_dec_plans env ts elems ==>
  abi_dec_plans env (t::ts)
    ((ei, type_memory_size tv, type_memory_size tv) :: elems)
End

(* A word type's decode info is a plan, under word_arg_clamp_ok's
   premises. *)
Theorem type_to_abi_dec_info_word_plan:
  !tenv sfields cenv ty.
    is_word_type ty /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    abi_dec_plan tenv ty (type_to_abi_dec_info sfields cenv ty)
Proof
  cheat
QED

(* ===== What a plan decodes ===== *)

(* The facts abi_dec_plan_value gives for a value v of type tv with ABI
   value av, decoded by info. *)
Definition dec_value_def:
  dec_value env ty tv v av info <=>
    ~is_dynamic (vyper_to_abi_type env ty) /\
    LENGTH (enc (vyper_to_abi_type env ty) av) = type_memory_size tv /\
    static_dec info (type_memory_size tv) /\
    (!cd off. mem_bytes_at off (type_memory_size tv) cd =
              enc (vyper_to_abi_type env ty) av ==> dec_ok info cd off) /\
    (!off mem. mem_bytes_at off (type_memory_size tv) mem =
               enc (vyper_to_abi_type env ty) av ==>
               val_in_memory tv v off mem)
End

Definition decs_value_def:
  decs_value env ts tvs vs avs elems <=>
    LENGTH avs = LENGTH ts /\
    EVERY is_static (vyper_to_abi_types env ts) /\
    LENGTH (FLAT (MAP2 enc (vyper_to_abi_types env ts) avs)) =
      SUM (MAP type_memory_size tvs) /\
    static_decs elems (SUM (MAP type_memory_size tvs)) /\
    (!cd off. mem_bytes_at off (SUM (MAP type_memory_size tvs)) cd =
              FLAT (MAP2 enc (vyper_to_abi_types env ts) avs) ==>
              decs_ok elems cd off) /\
    (!off mem. mem_bytes_at off (SUM (MAP type_memory_size tvs)) mem =
               FLAT (MAP2 enc (vyper_to_abi_types env ts) avs) ==>
               tuple_in_memory vs tvs off mem)
End

Theorem word_type_memory_size:
  !env ty tv.
    is_word_type ty /\ evaluate_type env ty = SOME tv ==>
    type_memory_size tv = 32
Proof
  cheat
QED

Theorem mem_bytes_at_word_eq:
  !off mem (w : bytes32).
    mem_bytes_at off 32 mem = word_to_bytes w T <=> mem_word_at off mem = w
Proof
  cheat
QED

Theorem mem_bytes_at_split_eq:
  !off m n mem x y.
    LENGTH x = m /\ mem_bytes_at off (m + n) mem = x ++ y ==>
    mem_bytes_at off m mem = x /\ mem_bytes_at (off + m) n mem = y
Proof
  cheat
QED

Theorem word_dec_value:
  !env ty tv v av c.
    is_word_type ty /\ evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    abi_clamp_ok c (typed_val_to_w256 tv v) ==>
    dec_value env ty tv v av (DecPrimWord c)
Proof
  cheat
QED

(* ===== Plans of word aggregates ===== *)

Theorem word_type_dec_sizes:
  !sfields cenv ty.
    is_word_type ty ==>
    ~is_abi_dynamic sfields ty /\ abi_embedded_static_size sfields ty = 32 /\
    type_memory_bytes cenv ty = 32
Proof
  cheat
QED

Theorem type_to_abi_dec_info_word_plans:
  !tenv sfields cenv ts.
    EVERY (\t. is_word_type t /\ IS_SOME (evaluate_type tenv t)) ts /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    abi_dec_plans tenv ts
      (MAP (\t. (type_to_abi_dec_info sfields cenv t,
                 abi_embedded_static_size cenv.ce_struct_fields t,
                 type_memory_bytes cenv t)) ts)
Proof
  cheat
QED

(* Non-vacuity: the decode info type_to_abi_dec_info builds for a tuple of
   word types is a plan. *)
Theorem type_to_abi_dec_info_word_tuple_plan:
  !tenv sfields cenv ts.
    EVERY (\t. is_word_type t /\ IS_SOME (evaluate_type tenv t)) ts /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    abi_dec_plan tenv (TupleT ts)
      (type_to_abi_dec_info sfields cenv (TupleT ts))
Proof
  cheat
QED

(* Non-vacuity: so is the decode info of a static array of a word type. *)
Theorem type_to_abi_dec_info_word_sarray_plan:
  !tenv sfields cenv t n.
    is_word_type t /\ IS_SOME (evaluate_type tenv t) /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    abi_dec_plan tenv (ArrayT t (Fixed n))
      (type_to_abi_dec_info sfields cenv (ArrayT t (Fixed n)))
Proof
  cheat
QED

(* ===== Tuples, structs and static arrays ===== *)

Theorem decs_value_nil:
  !env. decs_value env [] [] [] [] []
Proof
  cheat
QED

Theorem decs_value_cons:
  !env t tv v av ei ts tvs vs avs elems.
    dec_value env t tv v av ei /\ decs_value env ts tvs vs avs elems ==>
    decs_value env (t::ts) (tv::tvs) (v::vs) (av::avs)
      ((ei, type_memory_size tv, type_memory_size tv)::elems)
Proof
  cheat
QED

Theorem decs_value_tuple:
  !env ts tvs vs avs elems.
    decs_value env ts tvs vs avs elems ==>
    dec_value env (TupleT ts) (TupleTV tvs) (ArrayV (TupleV vs)) (ListV avs)
      (DecComplex F elems)
Proof
  cheat
QED

Theorem decs_value_struct:
  !env nsid args tvs fields avs elems.
    FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH tvs = LENGTH args /\
    decs_value (env \\ nsid) (MAP SND args) tvs (MAP SND fields) avs elems ==>
    dec_value env (StructT nsid) (StructTV (ZIP (MAP FST args, tvs)))
      (StructV fields) (ListV avs) (DecComplex F elems)
Proof
  cheat
QED

(* The element at index i of a sparse static array. *)
Definition sparse_val_def:
  sparse_val tv kvs (i : num) =
    case ALOOKUP kvs i of SOME v => v | NONE => default_value tv
End

Theorem vyper_to_abi_sparse_EL:
  !m env t tv sparse xs.
    vyper_to_abi_sparse env t tv m sparse = SOME xs /\
    evaluate_type env t = SOME tv ==>
    LENGTH xs = m /\
    !i. i < m ==>
        vyper_to_abi env t (sparse_val tv sparse i) = SOME (EL i xs)
Proof
  cheat
QED

Theorem sparse_val_has_type:
  !env t tv n sparse i.
    sparse_has_type tv n sparse /\ evaluate_type env t = SOME tv ==>
    value_has_type tv (sparse_val tv sparse i)
Proof
  cheat
QED

Theorem sorted_alookup_mem:
  !kvs k (v : value).
    SORTED $< (MAP FST kvs) /\ MEM (k, v) kvs ==> ALOOKUP kvs k = SOME v
Proof
  cheat
QED

Theorem kvs_in_memory_intro:
  !kvs off tv mem.
    (!k v. MEM (k, v) kvs ==>
           val_in_memory tv v (off + k * type_memory_size tv) mem) ==>
    kvs_in_memory kvs off tv mem
Proof
  cheat
QED

Theorem tuple_in_memory_replicate:
  !vs tv off mem i.
    tuple_in_memory vs (REPLICATE (LENGTH vs) tv) off mem /\ i < LENGTH vs ==>
    val_in_memory tv (EL i vs) (off + i * type_memory_size tv) mem
Proof
  cheat
QED

Theorem vyper_to_abi_types_REPLICATE:
  !n env t.
    vyper_to_abi_types env (REPLICATE n t) =
    REPLICATE n (vyper_to_abi_type env t)
Proof
  cheat
QED

Theorem decs_value_replicate:
  !avs env t tv ei vs.
    LENGTH vs = LENGTH avs /\
    (!i. i < LENGTH avs ==> dec_value env t tv (EL i vs) (EL i avs) ei) ==>
    decs_value env (REPLICATE (LENGTH avs) t) (REPLICATE (LENGTH avs) tv)
      vs avs
      (REPLICATE (LENGTH avs) (ei, type_memory_size tv, type_memory_size tv))
Proof
  cheat
QED

Theorem decs_value_sarray:
  !env t tv n sparse avs ei.
    (!i. i < n ==> dec_value env t tv (sparse_val tv sparse i) (EL i avs) ei) /\
    dec_value env t tv (default_value tv) (default_to_abi tv) ei /\
    LENGTH avs = n /\ SORTED $< (MAP FST sparse) /\
    sparse_has_type tv n sparse ==>
    dec_value env (ArrayT t (Fixed n)) (ArrayTV tv (Fixed n))
      (ArrayV (SArrayV sparse)) (ListV avs)
      (DecComplex F
         (REPLICATE n (ei, type_memory_size tv, type_memory_size tv)))
Proof
  cheat
QED

(* ===== Plans decode values ===== *)

val inv_plan_tac =
  qpat_x_assum `abi_dec_plan _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [abi_dec_plan_cases]);

val inv_plans_tac =
  qpat_x_assum `abi_dec_plans _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [abi_dec_plan_cases]);

Theorem abi_dec_plan_value:
  (!env ty. !tv v av info.
     abi_dec_plan env ty info /\ evaluate_type env ty = SOME tv /\
     value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
     dec_value env ty tv v av info) /\
  (!env ts. !tvs vs avs elems.
     abi_dec_plans env ts elems /\ OPT_MMAP (evaluate_type env) ts = SOME tvs /\
     values_have_types tvs vs /\ vyper_to_abi_list env ts vs = SOME avs ==>
     decs_value env ts tvs vs avs elems)
Proof
  cheat
QED






(* ===== Decoding a static value ===== *)

(* Calldata holding a static value's encoding at a decodes to the value in
   memory at p, without reverting. *)
Theorem compile_abi_decode_static_buf_correct:
  !env ty tv v av info dst src st st' ctx s0 p a.
    abi_dec_plan env ty info /\ evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info st =
      ((), st') /\
    eval_operand dst s0 = SOME p /\ eval_operand src s0 = SOME a /\
    fresh_vars_wrt st s0 /\
    w2n p + type_memory_size tv < dimword (:256) /\
    w2n a + type_memory_size tv < dimword (:256) /\
    mem_bytes_at (w2n a) (type_memory_size tv) s0.vs_call_ctx.cc_calldata =
      enc (vyper_to_abi_type env ty) av ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. dec_frame st (w2n p) (type_memory_size tv) s0 t /\
           fresh_vars_wrt st' t /\ val_in_memory tv v (w2n p) t.vs_memory)
      (\r. F)
Proof
  cheat
QED

(* ===== Static arguments ===== *)

(* Calldata that encodes a call holds a static argument's encoding at the
   argument's head offset, after the 4-byte selector. *)
Theorem calldata_encodes_static_arg:
  !tenv fname tys vals cd i.
    calldata_encodes tenv fname tys vals cd /\ LENGTH vals = LENGTH tys /\
    i < LENGTH tys /\ ~is_dynamic (vyper_to_abi_type tenv (EL i tys)) ==>
    ?avs. vyper_to_abi_list tenv tys vals = SOME avs /\
          vyper_to_abi tenv (EL i tys) (EL i vals) = SOME (EL i avs) /\
          mem_bytes_at
            (4 + SUM (MAP2 abi_head_size
                        (TAKE i (vyper_to_abi_types tenv tys)) (TAKE i avs)))
            (LENGTH (enc (vyper_to_abi_type tenv (EL i tys)) (EL i avs))) cd =
          enc (vyper_to_abi_type tenv (EL i tys)) (EL i avs)
Proof
  cheat
QED

(* The static, non-word path of compile_decode_args for one calldata
   argument: the head pointer, then compile_abi_decode_to_buf. *)
Theorem compile_decode_static_arg_phases:
  !cenv name abi_size info off hi st st' loc dst.
    compile_decode_args cenv [(name, F, F, abi_size, info)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_decode_operand loc = SOME dst ==>
    ?src st1.
      emit_op ADD [Lit 4w; Lit (n2w (off - 4))] st = (src, st1) /\
      compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info st1 =
        ((), st')
Proof
  cheat
QED

Theorem decode_head_ptr_run:
  !off st src st1 s.
    emit_op ADD [Lit 4w; Lit (n2w (off - 4))] st = (src, st1) /\
    4 <= off /\ fresh_vars_wrt st s ==>
    ?t. run_inst_seq (emitted_insts st st1) s = OK t /\
        eval_operand src t = SOME (n2w off) /\
        fresh_vars_wrt st1 t /\ vars_pc_only s t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

(* A static argument whose encoding sits at off in the calldata decodes
   without reverting, leaving the value in memory at the destination.
   For calldata that encodes the call, calldata_encodes_static_arg gives
   the encoding at the ABI head offset; that it is the decoder's off is
   the head-offset agreement this file leaves out (see the header). *)
Theorem compile_decode_static_arg_correct:
  !cenv name abi_size info off hi st st' ctx loc dst s0 p tenv ty tv v av.
    compile_decode_args cenv [(name, F, F, abi_size, info)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    4 <= off /\ off + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv < dimword (:256) /\
    abi_dec_plan tenv ty info /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av /\
    mem_bytes_at off (type_memory_size tv) s0.vs_call_ctx.cc_calldata =
      enc (vyper_to_abi_type tenv ty) av ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. dec_frame st (w2n p) (type_memory_size tv) s0 t /\
           fresh_vars_wrt st' t /\ val_in_memory tv v (w2n p) t.vs_memory)
      (\r. F)
Proof
  cheat
QED
