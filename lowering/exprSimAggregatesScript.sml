(*
 * Expression simulation: aggregates and type builtins (#636, Aggregates
 * and type builtins)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for struct and array
 * literals and the type builtins but extract32.  Proved: struct and array
 * literals, empty(T), max_value, min_value, epsilon, and the conversions
 * exprSimConvert proves (which rest on the cheated lower_value_word_shape).
 * Struct and array literals store each child with unwrap_value_sim, so
 * they carry exprSimUnwrap's cheated constructor immutable cases.
 * The other conversions, abi_encode and abi_decode are re-exported from
 * their leaf theories (exprSimConvertOther, exprSimAbiEncode,
 * exprSimAbiDecode).
 *
 * TOP-LEVEL:
 *   compile_struct_lit_case, compile_make_array_case — StructLit, MakeArray
 *                           (lists and tuples), row 1, for compile_expr_sim
 *                           and the body simulation; compile_struct_lit_sim
 *                           and compile_make_array_sim follow
 *   compile_empty_case    — empty(T), row 2: compile_empty_word_sim, the
 *                           literal 0, for a word type;
 *                           compile_empty_memory_sim, a zeroed buffer, for
 *                           the rest
 *   compile_bound_builtin_case_sim, compile_bound_builtin_case — max_value,
 *                           min_value and epsilon of a numeric type
 *                           (row 2): a Lit of the bound.
 *                           compile_max_value_sim, compile_min_value_sim
 *                           and compile_epsilon_sim follow from it
 *   compile_convert_case  — convert, row 3: compile_convert_word_case
 *                           (exprSimConvert) between integer types, from
 *                           bool to an integer and from an integer to
 *                           bool; compile_convert_other_case for the rest
 *                           (#548)
 *   compile_abi_encode_case, compile_abi_decode_case — abi_encode (#551),
 *                           abi_decode with its validation aborts, row 4
 *
 * StructLit, MakeArray and empty(T) of a type that is not a word build
 * their value in a buffer of their own, an ALLOCA of type_memory_bytes
 * bytes, as exprSimLiteralBuffer's bytes literals do:
 *   - expr_sim_pre's alloc_limits_expr bounds the buffer below 2 ** 64, so
 *     the ALLOCA's literal size does not wrap, and stmt_state_rel's
 *     alloca_room keeps the buffer's end below 2 ** 256, so the stores at
 *     ADD buf off do not wrap either;
 *   - the buffer is a fresh allocation, disjoint from the live locals and
 *     every other allocation, so the stores keep stmt_state_rel and the
 *     memory expr_post's frame asks for;
 *   - expr_sim_inv's struct fields clauses make the lowering's layout the
 *     source's: type_memory_bytes is type_memory_size, and a struct's
 *     fields, from ce_struct_fields, are the declaration's in its order,
 *     which well_typed_expr makes the literal's (the StructLit case takes
 *     its layout from the literal's own struct, whatever the caller's ty:
 *     compile_expr_struct_lit_ty).
 *
 * The elements of a struct or array literal are lowered as
 * cfn ...; ADD ...; unwrap_value, then stored into the buffer before the
 * next element runs, so an element's value need not outlive the next
 * element's fragment; the buffer's stored elements do, by the next
 * element's expr_post frame (the buffer's allocation id is below the
 * element's start counter and its region misses the live locals).  An
 * element that is a storage or transient array evaluates to a captured storage place:
 * these lemmas use exprs_case's expr_vv_case of each element, not its
 * expr_sim_case.
 *)

Theory exprSimAggregates
Ancestors
  exprSimAggregatesAllocCounted
  exprSimAbiDecode
  exprSimAbiEncode
  exprSimConvertOther
  exprWordOperand
  exprSimSource
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  exprSimAlloc
  allocLimits
  list  exprSimHyps exprSimConvert exprLowering compileEnv
  exprSimValues gasNormalPrefix gasSummary gasOutcome gasContext
  fragGasMode fragGasPath fragGasSeq
  valueEncoding vyperAST vyperInterpreter vyperState vyperContext
  vyperValueOperation vyperTypeSystem fragExec venomState
  exprSimBuffer exprSimBufferEmptyExec exprSimAggregateLayout
  exprSimAggregateSource exprSimAggregateLoops exprSimAggregateChildren
  exprLoweringProps

(* The allocation must be a generated ALLOCA, not merely a tracked map entry. *)
Theorem aggregate_alloca_immutable_sep[local]:
  stmt_state_rel ctx func cenv cx es t /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = venomInst$ALLOCA /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
  cenv.ce_is_ctor ==>
  !name itv iv io.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
      SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b sz
Proof
  cheat
QED

Theorem aggregate_outcome_map[local]:
  gas_outcome memory tops (ctx,func) source (es,s) Q R /\
  (!res ee t. Q res ee t ==> Q' (SUM_MAP f I res) ee t) /\
  (!res ee r. R res ee r ==> R' (SUM_MAP f I res) ee r) ==>
  gas_outcome memory tops (ctx,func) (bind source (return o f)) (es,s) Q' R'
Proof
  cheat
QED

Theorem aggregate_struct_action[local]:
  eval_expr cx (StructLit ann nsid fields) =
  bind (eval_exprs cx (MAP SND fields))
    (return o (\vs. Value (StructV (ZIP (MAP FST fields,vs)))))
Proof
  cheat
QED

Theorem aggregate_tuple_action[local]:
  compatible_bound bnd (LENGTH args) ==>
  eval_expr cx (Builtin ann (MakeArray NONE bnd) args) =
  bind (eval_exprs cx args) (return o (\vs. Value (ArrayV (TupleV vs))))
Proof
  cheat
QED

Theorem aggregate_array_action[local]:
  compatible_bound bnd (LENGTH args) /\
  evaluate_type (get_tenv cx) et = SOME tv ==>
  eval_expr cx (Builtin ann (MakeArray (SOME et) bnd) args) =
  bind (eval_exprs cx args)
    (return o (\vs. Value (ArrayV (make_array_value tv bnd vs))))
Proof
  cheat
QED

Theorem aggregate_outcome_source_run[local]:
  gas_outcome memory tops (ctx,func) source (es,s) Q R ==>
  gas_outcome memory tops (ctx,func) source (es,s)
    (\res ee t. Q res ee t /\
       ?gs. source (es with gas_obs := gs) = (res,ee)) R
Proof
  cheat
QED

Theorem compile_struct_lit_vv_case:
  !nocalls ctx func cenv cx ann nsid fields.
    exprs_case nocalls ctx func cenv cx (MAP SND fields) /\
    (~nocalls ==> !e. MEM e (MAP SND fields) ==>
       int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e) ==>
    expr_vv_case nocalls ctx func cenv cx (StructLit ann nsid fields)
Proof
  cheat
QED

Theorem compile_make_array_vv_case:
  !nocalls ctx func cenv cx ann topt bnd args.
    exprs_case nocalls ctx func cenv cx args /\
    (~nocalls ==> !e. MEM e args ==>
       int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e) ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (MakeArray topt bnd) args)
Proof
  cheat
QED




Theorem compile_struct_lit_case:
  !nocalls ctx func cenv cx ann nsid fields.
    exprs_case nocalls ctx func cenv cx (MAP SND fields) /\
    (~nocalls ==> !e. MEM e (MAP SND fields) ==>
       int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e) ==>
    expr_sim_case nocalls ctx func cenv cx (StructLit ann nsid fields) /\
    expr_vv_case nocalls ctx func cenv cx (StructLit ann nsid fields)
Proof
  cheat
QED

Theorem compile_make_array_case:
  !nocalls ctx func cenv cx ann topt bnd args.
    exprs_case nocalls ctx func cenv cx args /\
    (~nocalls ==> !e. MEM e args ==>
       int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e) ==>
    expr_sim_case nocalls ctx func cenv cx
      (Builtin ann (MakeArray topt bnd) args) /\
    expr_vv_case nocalls ctx func cenv cx
      (Builtin ann (MakeArray topt bnd) args)
Proof
  cheat
QED

Theorem compile_struct_lit_sim:
  !cenv ann nsid fields.
    expr_sim_below cenv (expr_size (StructLit ann nsid fields)) ==>
    expr_vv_ok cenv (StructLit ann nsid fields)
Proof
  cheat
QED

Theorem compile_make_array_sim:
  !cenv ann topt bnd args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (MakeArray topt bnd) args)
Proof
  cheat
QED


(* ===== empty(T) ===== *)

Theorem eval_expr_empty:
  !cx ann t args es res es'.
    (do r <- eval_expr cx (TypeBuiltin ann Empty t args); read_result cx r od) es = (res, es') /\
    expr_res_ok res ==>
    es' = es /\ args = [] /\
    ?tv. evaluate_type (get_tenv cx) t = SOME tv /\
         res = INL (default_value tv)
Proof
  cheat
QED

Theorem typed_val_to_w256_address_zero[local]:
  typed_val_to_w256 (BaseTV AddressT) (BytesV (word_to_bytes (0w:address) T)) =
  0w
Proof
  cheat
QED

(* The default value of a word type is the word 0 in its typed encoding. *)
Theorem typed_val_to_w256_default_word:
  !tenv t tv.
    is_word_type t /\ evaluate_type tenv t = SOME tv ==>
    typed_val_to_w256 tv (default_value tv) = 0w
Proof
  cheat
QED

(* empty(T) reads no gas observation: once admissible, it has the same
   value whatever the observations. *)
Theorem empty_read_all_tails[local]:
  !cx ann t args es.
    gas_admissible (bind (eval_expr cx (TypeBuiltin ann Empty t args))
      (read_result cx)) expr_res_ok es ==>
    args = [] /\
    ?tv. evaluate_type (get_tenv cx) t = SOME tv /\
      !gs. bind (eval_expr cx (TypeBuiltin ann Empty t args)) (read_result cx)
             (es with gas_obs := gs) =
           (INL (default_value tv), es with gas_obs := gs)
Proof
  cheat
QED

(* empty(T) of a word type: the literal 0, no code. *)
Theorem compile_empty_word_sim:
  !cenv ann t args.
    is_word_type t ==> expr_sim_ok cenv (TypeBuiltin ann Empty t args)
Proof
  cheat
QED

Theorem compile_empty_word_case_sim:
  !cenv ann t args.
    is_word_type t ==> expr_ok cenv (TypeBuiltin ann Empty t args)
Proof
  cheat
QED

(* empty(T) of any other type: a buffer of its own, of type_memory_bytes
   bytes (a multiple of 32), with its length word zeroed for a bytestring
   or dynamic array, whose default is empty, and every word zeroed for the
   rest.  The default value of any type lies in zeroed memory: a word's
   typed encoding is 0 (typed_val_to_w256_default_word), and a nested
   bytestring or dynamic array is empty, its length word 0. *)
(* The value form of empty_read_all_tails, for the vv judgment. *)
Theorem empty_eval_all_tails[local]:
  !cx ann t args es.
    gas_admissible (eval_expr cx (TypeBuiltin ann Empty t args))
      expr_vv_res_ok es ==>
    args = [] /\
    ?tv. evaluate_type (get_tenv cx) t = SOME tv /\
      !gs. eval_expr cx (TypeBuiltin ann Empty t args)
             (es with gas_obs := gs) =
           (INL (Value (default_value tv)), es with gas_obs := gs)
Proof
  cheat
QED

Theorem zero_words_no_gas[local]:
  !n pop sa sb.
    compile_zero_words pop n sa = ((),sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  cheat
QED

(* empty(T)'s buffer code reads no gas: its run is a gas path of no
   readings. *)
Theorem empty_complex_gas_path[local]:
  !sz header sa buf sb ctx func s t.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    gas_path ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    t.vs_current_bb = sb.cs_current_bb
Proof
  cheat
QED

Theorem compile_empty_memory_sim:
  !cenv ann t args.
    ~is_word_type t ==> expr_vv_ok cenv (TypeBuiltin ann Empty t args)
Proof
  cheat
QED

Theorem compile_empty_case:
  !nocalls ctx func cenv cx ann t args.
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Empty t args)
Proof
  cheat
QED

(* ===== max_value, min_value, epsilon ===== *)

Theorem eval_expr_bound_builtin:
  !cx ann tb t args es res es'.
    (do result <- eval_expr cx (TypeBuiltin ann tb t args); read_result cx result od) es = (res, es') /\
    expr_res_ok res /\ MEM tb [MaxValue; MinValue; Epsilon] ==>
    es' = es /\ args = [] /\
    ?v. res = INL v /\ evaluate_type_builtin cx tb t [] [] = INL v
Proof
  cheat
QED

(* max_value, min_value and epsilon read no gas observation either. *)
Theorem bound_read_all_tails[local]:
  !cx ann tb t args es.
    gas_admissible (bind (eval_expr cx (TypeBuiltin ann tb t args))
      (read_result cx)) expr_res_ok es /\
    MEM tb [MaxValue; MinValue; Epsilon] ==>
    args = [] /\
    ?v. evaluate_type_builtin cx tb t [] [] = INL v /\
      !gs. bind (eval_expr cx (TypeBuiltin ann tb t args)) (read_result cx)
             (es with gas_obs := gs) = (INL v, es with gas_obs := gs)
Proof
  cheat
QED

(* max_value, min_value and epsilon of a numeric type: a Lit of the bound,
   no code. *)
Theorem compile_bound_builtin_word_sim:
  !cenv ann tb t args.
    MEM tb [MaxValue; MinValue; Epsilon] ==>
    expr_sim_ok cenv (TypeBuiltin ann tb t args)
Proof
  cheat
QED

Theorem compile_bound_builtin_case_sim:
  !cenv ann tb t args.
    MEM tb [MaxValue; MinValue; Epsilon] ==>
    expr_ok cenv (TypeBuiltin ann tb t args)
Proof
  cheat
QED

Theorem compile_bound_builtin_case:
  !nocalls ctx func cenv cx ann tb t args.
    MEM tb [MaxValue; MinValue; Epsilon] ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann tb t args)
Proof
  cheat
QED

Theorem compile_max_value_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann MaxValue t args)
Proof
  cheat
QED

Theorem compile_min_value_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann MinValue t args)
Proof
  cheat
QED

Theorem compile_epsilon_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann Epsilon t args)
Proof
  cheat
QED

(* The conversions exprSimConvert does not cover: those to or from
   decimal, address, bytesM, bytestrings and flags, in exprSimConvertOther
   (#548). *)
Theorem compile_convert_other_case = exprSimConvertOtherTheory.compile_convert_other_case

Theorem compile_convert_case:
  !nocalls ctx func cenv cx ann t args.
    exprs_case nocalls ctx func cenv cx args /\
    (~nocalls ==> !e1 a f cargs d. args = [e1] /\ e1 = Call a (IntCall f) cargs d ==>
       lowered_value_type cenv e1 = expr_type e1) ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t args)
Proof
  cheat
QED

Theorem compile_abi_encode_case = exprSimAbiEncodeTheory.compile_abi_encode_case

Theorem compile_abi_decode_case = exprSimAbiDecodeTheory.compile_abi_decode_case
