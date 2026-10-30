(*
 * The hypotheses of the expression simulation theorem (#636)
 *
 * The main theorems (exprSimMain's compile_expr_sim and
 * compile_expr_vv_sim) say expr_ok of every expression: expr_sim and
 * expr_vv_sim (exprSim) hold at every source state where expr_sim_pre
 * holds.  expr_sim speaks of lower_value's code, expr_vv_sim of
 * compile_expr's alone and the value_vv it hands out, for a case that
 * unwraps an operand later or never.  The case lemmas each prove expr_ok,
 * or expr_vv_ok, from which expr_ok follows (expr_ok_of_vv), of one form of
 * expression from expr_sim_below, expr_ok of every smaller expression,
 * which is the induction hypothesis compile_expr_ind gives.
 *
 * TOP-LEVEL:
 *   expr_sim_inv      — the facts about the source state and the context
 *                       that every subexpression keeps: type soundness's
 *                       invariants, the locals of the type environment
 *                       held through pointer variables, and the flag
 *                       member ids, flag member counts and struct fields
 *                       of the compile environment
 *   expr_sim_pre      — expr_sim_inv, the expression well typed, its
 *                       integer types of whole bytes, its buffers below
 *                       the allocation limit, and no internal call in it
 *   byte_widths_expr  — every node's type has a width of whole bytes
 *   alloc_limits_expr, literal_alloc_ok — every static buffer the lowering
 *                       allocates for a node is below 2 ** 64 bytes
 *   expr_body_pre     — expr_sim_pre less int_calls_expr e = []: the
 *                       body simulation's (bodySim)
 *   expr_sim_ok       — expr_sim wherever expr_sim_pre holds
 *   expr_vv_ok        — expr_vv_sim wherever expr_sim_pre holds
 *   expr_ok           — both: the induction predicate
 *   expr_sim_below    — expr_ok of every expression below a size
 *   builtin_sim_ok, type_builtin_sim_ok — expr_ok of a builtin and a type
 *                       builtin, the dispatchers' induction predicates
 *   names_builtin     — the three builtins on names that compile_expr does
 *                       not hand to compile_builtin_dispatch
 *   compile_expr_type_builtin_dispatch — compile_expr of a type builtin is
 *                       its dispatcher's
 *   word_value_type   — the types whose values are word_values
 *   popped_keys_indexed — every key of a local's popped history ends in
 *                       an array index
 *   eval_expr_popped_keys_indexed — evaluation keeps popped_keys_indexed
 *   expr_sim_pre_eval — type soundness: evaluation keeps expr_sim_inv and
 *                       raises no type error
 *   expr_sim_pre_res_ok, expr_sim_pre_word_result — the results of an
 *                       expression are those expr_sim speaks of; a
 *                       word_value_type one's values are word_values
 *   expr_sim_pre_builtin_arg — an argument of a builtin meets expr_sim_pre
 *                       wherever expr_sim_inv holds
 *   byte_widths_expr_type — the expression's own type has whole bytes
 *   expr_sim_pre_var_types_well_formed — the local types are well formed
 *   well_typed_expr_type_evaluates — a well-typed expression's type
 *                       evaluates
 *   expr_ok_of_vv, expr_ok_stack — expr_ok from expr_vv_ok (by
 *                       exprSimUnwrap's expr_sim_of_vv_sim), and from
 *                       expr_sim_ok for a form lowered to a StackValue
 *   expr_sim_case, expr_vv_case — the judgments of a shared case lemma,
 *                       which compile_expr_sim and the body simulation
 *                       both use: expr_sim and expr_vv_sim wherever
 *                       expr_body_pre holds, and with no internal call if
 *                       its nocalls flag is set (expr_sim_ok_case,
 *                       expr_vv_ok_case, expr_ok_case)
 *   expr_sim_case_of_vv, expr_vv_case_stack — expr_ok_of_vv and
 *                       expr_ok_stack for them
 *   exprs_case        — the operands' judgments, each one's only if the
 *                       operands before it evaluate, as body_exprs_ok
 *                       gives them (exprs_case_below from expr_sim_below,
 *                       body_exprs_ok_case in bodySimExprCases)
 *   expr_case_of_ok, expr_vv_case_nil — the judgments of a form with no
 *                       internal call from its expr_ok or expr_vv_ok
 *
 * The type-soundness lemmas above hold of expr_body_pre too
 * (expr_body_pre_eval_result, expr_body_pre_eval, ...): they use
 * call_evaluation_safe, not int_calls_expr e = [].
 *
 * Why these hypotheses:
 *   - well_typed_expr, env_consistent, state_well_typed,
 *     accounts_well_typed, context_well_typed, functions_well_typed and
 *     call_evaluation_safe are exactly the premises of type soundness
 *     (vyperTypeEvalSoundness's eval_scc_type_sound_mutual, the expression
 *     conjunct).  The lowering trusts the annotations: an operator picks its
 *     bounds from the operand's annotated type, a literal is emitted at its
 *     annotated type.  So an expression whose values do not have their
 *     annotated types is lowered to code that does not simulate it.  Type
 *     soundness gives what the case lemmas need of the source values (a word
 *     operand evaluates to a word, a result has its type) and carries
 *     env_consistent, state_well_typed and accounts_well_typed to the next
 *     operand; the others are about the context and do not change.  With no
 *     internal call, call_evaluation_safe is call_evaluation_safe cx [], a
 *     fact about the call stack.
 *   - The locals clause: every local of the type environment is held
 *     through a pointer variable (PtrVar (Var p)).  This is how every
 *     entry's prologue registers the parameters (external functions, with
 *     or without default arguments, and the constructor: entryLocals;
 *     internal functions: package_internal_fn_prologue_ptrs in
 *     intCallCallee) and how the statement lowering declares
 *     locals; state_rel only relates the locals that are held so
 *     (local_ptrs_rel), and compile_name_vv emits INVALID for a name it
 *     does not find.
 *   - The local types clause: the compile environment's type of a local
 *     is its type in the type environment.  pop reads the element type of
 *     the array it pops from ce_var_type (elem_size_in_location), as
 *     Python's _lower_dynarray_pop reads the target's typ.value_type.  The
 *     statement lowering records each declared local's type there
 *     (ce_var_type updated_by (id =+ SOME ty)), and build_compile_env the
 *     parameters' (local_var_type).
 *   - The flag members clause: the compile environment's id of a flag
 *     member is its index in its flag's declaration, the bit
 *     lookup_flag_mem sets.  Vyper's compiler guarantees this:
 *     FlagT.from_FlagDef (vyper/semantics/types/user.py) numbers the
 *     members in declaration order and rejects a repeated one, and the
 *     Venom lowering of a flag member is the literal 2 ** id
 *     (codegen_venom/expr.py).  build_compile_env fills
 *     ce_flag_member_id from the main module's declarations only, so for
 *     a flag of an imported module with two members or more the clause
 *     does not hold of the environment it builds.  expr_sim_inv is about
 *     the whole target, so the theorem then says nothing about any
 *     expression of the contract, not only those that use the flag.
 *   - The flag counts clause: the compile environment's member count of a
 *     flag type is the one the type environment gives it (FlagArgs, the
 *     length of its declaration's member list), which bounds its values.
 *     Vyper's lowering of ~ on a flag XORs with the mask of that many
 *     bits, (1 << len(typ._flag_members)) - 1 (codegen_venom/expr.py
 *     lower_UnaryOp).  build_compile_env fills ce_flag_n_members from the
 *     main module's declarations only, and gives a flag of an imported
 *     module 0 members, so the clause does not hold of the environment
 *     it builds for any contract that imports a module declaring a flag;
 *     the theorem then says nothing about that contract.  Restricting the
 *     clause to the main module would not help: ~ on an imported flag
 *     would then lower to an XOR with 0, not Vyper's mask.
 *   - byte_widths_expr e: every integer type in the expression is
 *     int8..int256 or uint8..uint256 in steps of 8, as Vyper's are
 *     (IntegerT.signeds and IntegerT.unsigneds, bits = 8 * i for i in
 *     1..32, vyper/semantics/types/primitives.py).  evaluate_type admits
 *     any width up to 256; the unsafe operators' lowering wraps by whole
 *     bytes, as Python's does, so it does not compute the source's result
 *     at other widths.
 *   - alloc_limits_expr cenv e: every static buffer the lowering allocates
 *     for the expression's nodes is below 2 ** 64 bytes: a bytes or string
 *     literal's, and the type_memory_bytes of a struct literal, a list or
 *     tuple literal and empty(T) of a type that is not a word, and a
 *     calldata slice's output buffer.  Python's Context.allocate_buffer
 *     (vyper/codegen_venom/context.py) raises MemoryAllocationException
 *     for a buffer of 2 ** 64 bytes or more; _lower_bytelike allocates its
 *     buffer through it, and _lower_struct_constructor, lower_List,
 *     lower_Tuple, lower_empty and _lower_adhoc_slice through
 *     new_temporary_value, which allocates
 *     typ.memory_bytes_required.  The lowering's ALLOCA takes the size as a
 *     word literal and cannot fail, so a buffer of 2 ** 256 bytes or more
 *     would wrap; evaluate_type admits Bytes[n] and String[n] for any
 *     n < 2 ** 256.  return_buffer_ok is the same limit for an external
 *     function's return buffer.
 *   - The outcomes clause (outcomes_accounts_typed): every successful call
 *     outcome still to consume adopts runtime well-typed accounts.
 *     take_call_outcome raises "call outcome accounts" on a successful
 *     nonstatic outcome whose accounts are not, while Venom's CALL adopts
 *     it and goes on, so without the clause send and extcall do not
 *     simulate.  The outcomes are the environment's answers, not the
 *     contract's: e2eDefs's call_outcomes_ok asks this of the initial ones,
 *     and the evaluator only drops outcomes from the front
 *     (eval_outcome_suffix_mutual), so expr_sim_pre_eval carries it on.
 *   - int_calls_expr e = []: no internal call.  An internal call lowers to
 *     INVOKE, whose simulation is #638's call step; until that is stated
 *     this theorem excludes them, and #638 replaces this conjunct with its
 *     hypothesis on the callees.
 *   - The popped keys clause (popped_keys_indexed): every key of a local's
 *     popped history ends in an array index.  Reading a field of a popped
 *     element reads the history, and a snapshot recorded at the field
 *     itself would be read instead of the field of the element's snapshot,
 *     which memory at the field's pointer holds.  This is a fact about the
 *     source semantics, not the compiler: pop records the element it
 *     removes at path ++ [ValueSubscript (IntV i)] (record_pop), a new
 *     local starts with no history, and evaluation changes the scopes only
 *     by pops (eval_expr_popped_keys_indexed).
 *
 *   - The struct fields clauses: the compile environment's struct field
 *     map agrees with the type environment's struct declarations, field
 *     names and types in declaration order (sfields_tenv_consistent), its
 *     field names are distinct, and each field's size is the source's
 *     memory size of its type (type_memory_size), so type_memory_bytes is
 *     type_memory_size for every type.  Vyper's compiler guarantees these:
 *     a struct's members are distinct and laid out in declaration order,
 *     memory_bytes_required each (StructT.tuple_keys,
 *     _lower_struct_constructor).  build_compile_env's map
 *     (make_struct_fields_map, structFieldsProps, #727) sizes each field by
 *     field_mem_bytes, its type_memory_size, and the checker rejects
 *     repeated members (check_contract_struct_fields_distinct).  As for
 *     flags, the map holds the main module's structs only, so the theorem
 *     says nothing about a contract whose type environment holds an
 *     imported struct.
 *
 * Not here yet:
 *   - The rest of the compile environment's metadata (dynamic array
 *     capacities, method ids) is not related to the source context.  The
 *     cases that read it (Attribute, ...) will need a clause each in
 *     expr_sim_inv, as pop has the local types clause, and
 *     TopLevelName needs every immutable to be in ce_vars (#563); storage
 *     and transient variables are there by storage_vars_rel and
 *     transient_vars_rel.  Each is to match what Vyper's compiler
 *     guarantees.
 *   - Keeping an operand's value_vv through the code between compile_expr
 *     and unwrap_value (a later operand's fragment) needs the operand
 *     composition of #636's Infrastructure: vv_post's memory frame for a
 *     pointer into memory, unchanged storage for a storage pointer.
 *)

Theory exprSimHyps
Ancestors
  list finite_map
  exprSim exprCallBounds exprBopLowering exprLowering compileEnv
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallStackSoundness
  vyperTypeExprResult vyperTypeEvalSoundness vyperTypeBuiltins
  vyperExprNoControl loweringSlice exprSimUnwrap exprSafeOperand
  vyperEvalOutcomeSuffix vyperRuntimeAccounts vyperLookup
  vyperPlaceResultTyping
Libs
  pairLib

(* ===== The hypotheses ===== *)

(* Every successful outcome still to consume adopts accounts that are
   runtime well typed, as e2eDefs's call_outcomes_ok asks of the initial
   ones.  The evaluator only drops outcomes from the front
   (vyperEvalOutcomeSuffix), so this carries from one operand to the next. *)
Definition outcomes_accounts_typed_def:
  outcomes_accounts_typed (oos : call_outcome list option) <=>
    !os. oos = SOME os ==>
         EVERY (\oc. oc.co_success ==>
                     accounts_runtime_well_typed oc.co_accounts) os
End

(* Every key of a local's popped history ends in an array index: pop records
   the element it removes at path ++ [ValueSubscript (IntV i)] (record_pop),
   and replace_popped keeps the keys. *)
Definition popped_keys_indexed_def:
  popped_keys_indexed (scs : scope list) <=>
    EVERY (\sc. !id entry. FLOOKUP sc id = SOME entry ==>
                 EVERY (\k. ?p i. k = p ++ [ValueSubscript i])
                       (MAP FST entry.popped)) scs
End

Definition expr_sim_inv_def:
  expr_sim_inv cenv cx env (es:evaluation_state) <=>
    env_consistent env cx es /\ state_well_typed es /\
    accounts_well_typed es.accounts /\
    context_well_typed cx /\ functions_well_typed cx /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
             ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
             cenv.ce_var_type id = SOME ty) /\
    (!src fid ts ls mid i.
       get_module_code cx src = SOME ts /\ lookup_flag fid ts = SOME ls /\
       INDEX_OF mid ls = SOME i ==>
       cenv.ce_flag_member_id (nsid_to_string (src, fid)) mid = i) /\
    (!nsid m. FLOOKUP (get_tenv cx) nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
                                     sz = type_memory_size tv) fields) /\
    outcomes_accounts_typed es.outcomes /\
    popped_keys_indexed es.scopes
End

(* The types whose values are word_values (loweringSlice): integers,
   decimals, booleans and flags.  address and bytesN values are BytesV. *)
Definition word_value_type_def:
  word_value_type t <=> is_numeric_type t \/ is_bool_type t \/ is_flag_type t
End

(* Every node of an expression has a type whose width, type_bits, is a
   whole number of bytes: of the integer types, those Vyper has.  The same
   recursion as int_calls_expr. *)
Definition byte_widths_expr_def:
  byte_widths_expr (Name t _) = (type_bits t MOD 8 = 0) /\
  byte_widths_expr (TopLevelName t _) = (type_bits t MOD 8 = 0) /\
  byte_widths_expr (FlagMember t _ _) = (type_bits t MOD 8 = 0) /\
  byte_widths_expr (IfExp t c x y) =
    (type_bits t MOD 8 = 0 /\ byte_widths_expr c /\ byte_widths_expr x /\
     byte_widths_expr y) /\
  byte_widths_expr (Literal t _) = (type_bits t MOD 8 = 0) /\
  byte_widths_expr (StructLit t _ kes) =
    (type_bits t MOD 8 = 0 /\ byte_widths_named_exprs kes) /\
  byte_widths_expr (Subscript t x y) =
    (type_bits t MOD 8 = 0 /\ byte_widths_expr x /\ byte_widths_expr y) /\
  byte_widths_expr (Attribute t x _) =
    (type_bits t MOD 8 = 0 /\ byte_widths_expr x) /\
  byte_widths_expr (Builtin t _ es) =
    (type_bits t MOD 8 = 0 /\ byte_widths_exprs es) /\
  byte_widths_expr (TypeBuiltin t _ _ es) =
    (type_bits t MOD 8 = 0 /\ byte_widths_exprs es) /\
  byte_widths_expr (Pop t tgt) =
    (type_bits t MOD 8 = 0 /\ byte_widths_target tgt) /\
  byte_widths_expr (Call t _ es dflt) =
    (type_bits t MOD 8 = 0 /\ byte_widths_exprs es /\ byte_widths_opt dflt) /\

  byte_widths_target (NameTarget _) = T /\
  byte_widths_target (TopLevelNameTarget _) = T /\
  byte_widths_target (SubscriptTarget tgt e) =
    (byte_widths_target tgt /\ byte_widths_expr e) /\
  byte_widths_target (AttributeTarget tgt _) = byte_widths_target tgt /\

  byte_widths_exprs [] = T /\
  byte_widths_exprs (e::es) = (byte_widths_expr e /\ byte_widths_exprs es) /\

  byte_widths_opt NONE = T /\
  byte_widths_opt (SOME e) = byte_widths_expr e /\

  byte_widths_named_exprs [] = T /\
  byte_widths_named_exprs ((_,e)::kes) =
    (byte_widths_expr e /\ byte_widths_named_exprs kes)
Termination
  (* the measure names the container sizes with `list_size`/`option_size` over
     `expr_size`, as in `vyperTypeCallGraph`, so that the obligations are
     arithmetic over one set of size functions. *)
  qexists_tac `measure (\(x : expr + base_assignment_target + expr list +
                                      expr option + (identifier # expr) list).
    case x of
    | INL e => expr_size e
    | INR (INL tgt) => base_assignment_target_size tgt
    | INR (INR (INL es)) => list_size expr_size es
    | INR (INR (INR (INL opt))) => option_size expr_size opt
    | INR (INR (INR (INR kes))) =>
        list_size (pair_size (list_size char_size) expr_size) kes)` >>
  conj_tac >- MATCH_ACCEPT_TAC prim_recTheory.WF_measure >>
  PURE_REWRITE_TAC [prim_recTheory.measure_thm, sumTheory.sum_case_def] >>
  simp[expr_size_def, listTheory.list_size_def,
       basicSizeTheory.pair_size_def, basicSizeTheory.option_size_def,
       bnfPrelimsTheory.option_size_map, bnfPrelimsTheory.pair_size_map,
       listTheory.list_size_map, SF ETA_ss]
End

(* The buffer the lowering allocates for a bytes or string literal, its
   length word and its data rounded up to whole words, is below 2 ** 64
   bytes.  A bytesN or address literal has at most 32 bytes and no buffer,
   and the bound holds of it all the same. *)
Definition literal_alloc_ok_def:
  literal_alloc_ok (BytesL bs) = (32 + 32 * word_size (LENGTH bs) < 2 ** 64) /\
  literal_alloc_ok (StringL str) =
    (32 + 32 * word_size (LENGTH str) < 2 ** 64) /\
  literal_alloc_ok _ = T
End

(* Every static buffer the lowering allocates for a node of the expression
   is below Python's allocation limit, 2 ** 64 bytes: the buffers of bytes
   and string literals, struct and array literals, empty(T) of a type that
   is not a word, and the output of a calldata slice.  The same recursion
   as byte_widths_expr. *)
Definition alloc_limits_expr_def:
  alloc_limits_expr cenv (Name t _) = T /\
  alloc_limits_expr cenv (TopLevelName t _) = T /\
  alloc_limits_expr cenv (FlagMember t _ _) = T /\
  alloc_limits_expr cenv (IfExp t c x y) =
    (alloc_limits_expr cenv c /\ alloc_limits_expr cenv x /\
     alloc_limits_expr cenv y) /\
  alloc_limits_expr cenv (Literal t l) = literal_alloc_ok l /\
  alloc_limits_expr cenv (StructLit t nsid kes) =
    (type_memory_bytes cenv (StructT nsid) < 2 ** 64 /\
     alloc_limits_named_exprs cenv kes) /\
  alloc_limits_expr cenv (Subscript t x y) =
    (alloc_limits_expr cenv x /\ alloc_limits_expr cenv y) /\
  alloc_limits_expr cenv (Attribute t x _) = alloc_limits_expr cenv x /\
  alloc_limits_expr cenv (Builtin t bi es) =
    ((case bi of
        MakeArray NONE _ =>
          SUM (MAP (type_memory_bytes cenv o expr_type) es) < 2 ** 64
      | MakeArray (SOME _) _ => type_memory_bytes cenv t < 2 ** 64
      | CalldataSlice n => 32 + 32 * word_size n < 2 ** 64
      | _ => T) /\
     alloc_limits_exprs cenv es) /\
  alloc_limits_expr cenv (TypeBuiltin t tb ty es) =
    ((tb = Empty /\ ~is_word_type ty ==> type_memory_bytes cenv ty < 2 ** 64) /\
     alloc_limits_exprs cenv es) /\
  alloc_limits_expr cenv (Pop t tgt) = alloc_limits_target cenv tgt /\
  alloc_limits_expr cenv (Call t _ es dflt) =
    (alloc_limits_exprs cenv es /\ alloc_limits_opt cenv dflt) /\

  alloc_limits_target cenv (NameTarget _) = T /\
  alloc_limits_target cenv (TopLevelNameTarget _) = T /\
  alloc_limits_target cenv (SubscriptTarget tgt e) =
    (alloc_limits_target cenv tgt /\ alloc_limits_expr cenv e) /\
  alloc_limits_target cenv (AttributeTarget tgt _) =
    alloc_limits_target cenv tgt /\

  alloc_limits_exprs cenv [] = T /\
  alloc_limits_exprs cenv (e::es) =
    (alloc_limits_expr cenv e /\ alloc_limits_exprs cenv es) /\

  alloc_limits_opt cenv NONE = T /\
  alloc_limits_opt cenv (SOME e) = alloc_limits_expr cenv e /\

  alloc_limits_named_exprs cenv [] = T /\
  alloc_limits_named_exprs cenv ((_,e)::kes) =
    (alloc_limits_expr cenv e /\ alloc_limits_named_exprs cenv kes)
Termination
  (* as above: container sizes, not the package's per-instance size functions. *)
  qexists_tac `measure (\(x : compile_env # expr + compile_env #
                              base_assignment_target + compile_env # expr list +
                              compile_env # expr option +
                              compile_env # (identifier # expr) list).
    case x of
    | INL (_, e) => expr_size e
    | INR (INL (_, tgt)) => base_assignment_target_size tgt
    | INR (INR (INL (_, es))) => list_size expr_size es
    | INR (INR (INR (INL (_, opt)))) => option_size expr_size opt
    | INR (INR (INR (INR (_, kes)))) =>
        list_size (pair_size (list_size char_size) expr_size) kes)` >>
  conj_tac >- MATCH_ACCEPT_TAC prim_recTheory.WF_measure >>
  PURE_REWRITE_TAC [prim_recTheory.measure_thm, sumTheory.sum_case_def,
                    pairTheory.pair_case_def] >>
  simp[expr_size_def, listTheory.list_size_def,
       basicSizeTheory.pair_size_def, basicSizeTheory.option_size_def,
       bnfPrelimsTheory.option_size_map, bnfPrelimsTheory.pair_size_map,
       listTheory.list_size_map, SF ETA_ss]
End

Definition expr_sim_pre_def:
  expr_sim_pre cenv cx env e es <=>
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    byte_widths_expr e /\ alloc_limits_expr cenv e /\
    int_calls_expr e = [] /\ call_evaluation_safe cx (int_calls_expr e)
End

(* expr_sim_pre without int_calls_expr e = []: the body simulation's
   (bodySim), where an operand may call an internal function. *)
Definition expr_body_pre_def:
  expr_body_pre cenv cx env e es <=>
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    byte_widths_expr e /\ alloc_limits_expr cenv e /\
    call_evaluation_safe cx (int_calls_expr e)
End

Theorem expr_sim_pre_body:
  !cenv cx env e es.
    expr_sim_pre cenv cx env e es <=>
    expr_body_pre cenv cx env e es /\ int_calls_expr e = []
Proof
  rw[expr_sim_pre_def, expr_body_pre_def] >> metis_tac[]
QED

Theorem expr_sim_pre_body_pre:
  !cenv cx env e es.
    expr_sim_pre cenv cx env e es ==> expr_body_pre cenv cx env e es
Proof
  simp[expr_sim_pre_body]
QED

Definition expr_sim_ok_def:
  expr_sim_ok cenv e <=>
    !ctx func cx env ty es.
      expr_sim_pre cenv cx env e es ==> expr_sim ctx func cenv cx ty e es
End

Definition expr_vv_ok_def:
  expr_vv_ok cenv e <=>
    !ctx func cx env ty es.
      expr_sim_pre cenv cx env e es ==> expr_vv_sim ctx func cenv cx ty e es
End

(* The induction predicate: both judgments, so a case can use whichever an
   operand's lowering needs. *)
Definition expr_ok_def:
  expr_ok cenv e <=> expr_sim_ok cenv e /\ expr_vv_ok cenv e
End

Definition expr_sim_below_def:
  expr_sim_below cenv n <=> !e. expr_size e < n ==> expr_ok cenv e
End

(* The judgments a shared case lemma takes of its operands and concludes of
   its expression: expr_sim and expr_vv_sim at one ctx, func and cx, at
   every state meeting expr_body_pre, and with no internal call in the
   expression if nocalls.  With nocalls they are expr_sim_ok and
   expr_vv_ok (expr_sim_ok_case, expr_vv_ok_case), compile_expr_sim's
   induction predicate; without, what the body simulation's body_expr_ok
   gives in a frame of the lowered program.  So one case lemma serves
   both. *)
Definition expr_sim_case_def:
  expr_sim_case nocalls ctx func cenv cx e <=>
    !env ty es.
      expr_body_pre cenv cx env e es /\ (nocalls ==> int_calls_expr e = []) ==>
      expr_sim ctx func cenv cx ty e es
End

Definition expr_vv_case_def:
  expr_vv_case nocalls ctx func cenv cx e <=>
    !env ty es.
      expr_body_pre cenv cx env e es /\ (nocalls ==> int_calls_expr e = []) ==>
      expr_vv_sim ctx func cenv cx ty e es
End

(* The operands of an expression, evaluated and read in order, as
   evaluate_ind gives their judgments: each one's if the ones before it can
   evaluate (bodySim's body_exprs_ok). *)
Definition exprs_case_def:
  exprs_case nocalls ctx func cenv cx [] = T /\
  exprs_case nocalls ctx func cenv cx (e::es) =
    (expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      exprs_case nocalls ctx func cenv cx es))
End

(* AddMod, MulMod and PowMod256 applied to names: compile_expr lowers these
   itself (compile_addmod_names, ...), not through
   compile_builtin_dispatch. *)
Definition names_builtin_def:
  (names_builtin AddMod [Name _ _; Name _ _; Name _ _] <=> T) /\
  (names_builtin MulMod [Name _ _; Name _ _; Name _ _] <=> T) /\
  (names_builtin PowMod256 [Name _ _; Name _ _] <=> T) /\
  (names_builtin _ _ <=> F)
End

Definition builtin_sim_ok_def:
  builtin_sim_ok cenv ann bi args <=>
    ~names_builtin bi args ==> expr_ok cenv (Builtin ann bi args)
End

Definition type_builtin_sim_ok_def:
  type_builtin_sim_ok cenv ann tb t args <=>
    expr_ok cenv (TypeBuiltin ann tb t args)
End

(* ===== The induction hypothesis ===== *)

Theorem expr_sim_below_mono:
  !cenv m n. expr_sim_below cenv n /\ m <= n ==> expr_sim_below cenv m
Proof
  rw[expr_sim_below_def]
QED

Theorem expr_sim_below_mem:
  !cenv args e.
    expr_sim_below cenv (list_size expr_size args) /\ MEM e args ==>
    expr_ok cenv e
Proof
  rw[expr_sim_below_def] >> first_x_assum irule >>
  irule expr_list_member_bound >> simp[]
QED

(* ===== compile_expr of a builtin ===== *)

val expr_sizes = [listTheory.list_size_def, vyperASTTheory.expr_size_def,
                  basicSizeTheory.option_size_def];

Theorem compile_expr_type_builtin_dispatch:
  !cenv ty ann tb t args st.
    compile_expr cenv ty (TypeBuiltin ann tb t args) st =
    compile_type_builtin_dispatch cenv ann ty tb t args st
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       vyperASTTheory.expr_type_def] >>
  simp expr_sizes
QED

(* ===== Type soundness ===== *)

Theorem replace_popped_keys[local]:
  !h tv path r h'.
    replace_popped tv path r h = SOME h' ==> MAP FST h' = MAP FST h
Proof
  Induct >> simp[replace_popped_def] >> Cases >> rpt gen_tac >>
  simp[replace_popped_def] >> rw[AllCaseEqs()] >> gvs[] >> res_tac
QED

Theorem entry_pop_step_keys_indexed[local]:
  !entry path entry'.
    entry_pop_step entry path entry' /\
    EVERY (\k. ?p i. k = p ++ [ValueSubscript i]) (MAP FST entry.popped) ==>
    EVERY (\k. ?p i. k = p ++ [ValueSubscript i]) (MAP FST entry'.popped)
Proof
  rw[entry_pop_step_def] >> simp[record_pop_def] >>
  BasicProvers.every_case_tac >> imp_res_tac replace_popped_keys >> gvs[] >>
  metis_tac[]
QED

Theorem scope_pop_step_keys_indexed[local]:
  !sc ev sc'.
    scope_pop_step sc ev sc' /\ popped_keys_indexed sc ==>
    popped_keys_indexed sc'
Proof
  rpt gen_tac >> PairCases_on `ev` >> rw[scope_pop_step_def] >>
  drule find_containing_scope_structure >> strip_tac >>
  gvs[popped_keys_indexed_def, FLOOKUP_UPDATE] >> rw[] >> gvs[]
  >- (irule entry_pop_step_keys_indexed >> metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem scope_pop_trace_keys_indexed:
  !events sc sc'.
    scope_pop_trace sc events sc' /\ popped_keys_indexed sc ==>
    popped_keys_indexed sc'
Proof
  Induct >> simp[scope_pop_trace_def] >>
  metis_tac[scope_pop_step_keys_indexed]
QED

(* Evaluating an expression changes the scopes only by pops
   (eval_mutual_scope_pop_effect), so it keeps popped_keys_indexed. *)
Theorem eval_expr_popped_keys_indexed:
  !cx e es res es'.
    eval_expr cx e es = (res, es') /\ popped_keys_indexed es.scopes ==>
    popped_keys_indexed es'.scopes
Proof
  rpt strip_tac >>
  `scope_pop_effect (eval_expr cx e)` by
    simp[cj 5 eval_mutual_scope_pop_effect] >>
  gvs[scope_pop_effect_def] >> first_x_assum drule >> strip_tac >>
  drule_all scope_pop_trace_keys_indexed >> simp[]
QED

Theorem expr_body_pre_eval_result:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ no_type_error_result res /\
    !tv. res = INL tv ==>
         eval_result_typed (env,cx,es') tv (Type (expr_type e))
Proof
  rpt gen_tac >> simp[expr_body_pre_def, expr_sim_inv_def] >> strip_tac >>
  drule_all eval_expr_popped_keys_indexed >> strip_tac >>
  qspecl_then [`cx`, `e`] (mp_tac o CONJUNCT1)
    (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`, `es`, `res`, `es'`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  impl_tac >- gvs[] >>
  `outcomes_accounts_typed es'.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >>
     gvs[outcomes_accounts_typed_def]) >>
  Cases_on `res` >> gvs[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem expr_sim_pre_eval_result:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ no_type_error_result res /\
    !tv. res = INL tv ==>
         eval_result_typed (env,cx,es') tv (Type (expr_type e))
Proof
  metis_tac[expr_body_pre_eval_result, expr_sim_pre_body_pre]
QED

Theorem expr_body_pre_eval:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ no_type_error_result res /\
    !v. res = INL v ==> expr_result_typed env e (Value v)
Proof
  rpt strip_tac >>
  `state_well_typed es' /\ no_type_error_result res /\
   (case res of INL v => value_runtime_typed env (expr_type e) v | INR _ => T)` by
    (drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
     disch_then (qspec_then `env` mp_tac) >>
     gvs[expr_body_pre_def, expr_sim_inv_def]) >>
  qpat_x_assum `(do result <- eval_expr _ _; read_result _ result od) _ = _` mp_tac >>
  simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  drule_all expr_body_pre_eval_result >> strip_tac >> simp[] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_runtime_typed_def,
      value_result_typed_def, is_HashMapRef_def]
QED

Theorem expr_sim_pre_eval:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ no_type_error_result res /\
    !v. res = INL v ==> expr_result_typed env e (Value v)
Proof
  metis_tac[expr_body_pre_eval, expr_sim_pre_body_pre]
QED

Theorem expr_body_pre_res_ok:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_res_ok res
Proof
  rpt strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
  Cases_on `res` >> gvs[expr_res_ok_def] >>
  rename1 `INR exc` >>
  `no_control_exc exc` by
    (qpat_x_assum `(do result <- eval_expr _ _; read_result _ result od) _ = _` mp_tac >>
     simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control, read_result_no_control]) >>
  Cases_on `exc` >> gvs[no_control_exc_def, no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Theorem expr_sim_pre_res_ok:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_res_ok res
Proof
  metis_tac[expr_body_pre_res_ok, expr_sim_pre_body_pre]
QED

Theorem expr_body_pre_vv_res_ok:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_vv_res_ok res
Proof
  rpt strip_tac >> drule_all expr_body_pre_eval_result >> strip_tac >>
  Cases_on `res` >> gvs[expr_vv_res_ok_def]
  >- (rename1 `eval_result_typed _ tv _` >> Cases_on `tv` >>
      gvs[eval_result_typed_def]) >>
  drule (cj 1 eval_expr_no_control) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  gvs[no_control_exc_def, no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Theorem expr_sim_pre_vv_res_ok:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_vv_res_ok res
Proof
  metis_tac[expr_body_pre_vv_res_ok, expr_sim_pre_body_pre]
QED

Theorem word_value_type_typed:
  !t tenv tyv x.
    word_value_type t /\ evaluate_type tenv t = SOME tyv /\
    value_has_type tyv x ==>
    word_value x /\ value_has_type tyv x
Proof
  rpt strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT DecimalT \/ t = BaseT BoolT \/ (?nsid. t = FlagT nsid)` by
    (Cases_on `t` >> fs[word_value_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_int_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `x` >>
  gvs[vyperTypingTheory.value_has_type_def, word_value_def]
QED

Theorem expr_body_pre_word_result:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ word_value_type (expr_type e) /\
    (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ expr_res_ok res /\
    !tv. res = INL tv ==>
         ?tyv. word_value tv /\
                 evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
                 value_has_type tyv tv
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  Cases_on `res` >> gvs[]
  >- (gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
      drule_all word_value_type_typed >> strip_tac >> gvs[expr_res_ok_def]) >>
  irule expr_body_pre_res_ok >> simp[] >> metis_tac[]
QED

Theorem expr_sim_pre_word_result:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ word_value_type (expr_type e) /\
    (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ expr_res_ok res /\
    !tv. res = INL tv ==>
         ?tyv. word_value tv /\
                 evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
                 value_has_type tyv tv
Proof
  metis_tac[expr_body_pre_word_result, expr_sim_pre_body_pre]
QED

Theorem well_typed_exprs_mem:
  !args env e.
    well_typed_exprs env args /\ int_calls_exprs args = [] /\ MEM e args ==>
    well_typed_expr env e /\ int_calls_expr e = []
Proof
  Induct >> rw[well_typed_expr_def, int_calls_expr_def] >> metis_tac[]
QED

Theorem byte_widths_exprs_mem:
  !args e. byte_widths_exprs args /\ MEM e args ==> byte_widths_expr e
Proof
  Induct >> rw[byte_widths_expr_def] >> gvs[]
QED

Theorem alloc_limits_exprs_mem:
  !cenv args e. alloc_limits_exprs cenv args /\ MEM e args ==>
               alloc_limits_expr cenv e
Proof
  gen_tac >> Induct >> rw[alloc_limits_expr_def] >> gvs[]
QED

Theorem byte_widths_expr_type:
  !e. byte_widths_expr e ==> type_bits (expr_type e) MOD 8 = 0
Proof
  Cases >> rw[byte_widths_expr_def, expr_type_def]
QED

Theorem expr_sim_pre_builtin_arg:
  !cenv cx env ann bi args e es es'.
    expr_sim_pre cenv cx env (Builtin ann bi args) es /\ MEM e args /\
    expr_sim_inv cenv cx env es' ==>
    expr_sim_pre cenv cx env e es'
Proof
  rw[expr_sim_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def] >>
  drule_all well_typed_exprs_mem >> drule_all byte_widths_exprs_mem >>
  drule_all alloc_limits_exprs_mem >> gvs[]
QED

Theorem well_typed_exprs_member:
  !args env e. well_typed_exprs env args /\ MEM e args ==> well_typed_expr env e
Proof
  Induct >> rw[well_typed_expr_def] >> metis_tac[]
QED

Theorem call_evaluation_safe_exprs_mem:
  !args cx e.
    call_evaluation_safe cx (int_calls_exprs args) /\ MEM e args ==>
    call_evaluation_safe cx (int_calls_expr e)
Proof
  Induct >> rw[int_calls_expr_def] >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left,
            vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]
QED

Theorem int_calls_exprs_mem:
  !args e. int_calls_exprs args = [] /\ MEM e args ==> int_calls_expr e = []
Proof
  Induct >> rw[int_calls_expr_def] >> gvs[]
QED

Theorem expr_body_pre_builtin_arg:
  !cenv cx env ann bi args e es es'.
    expr_body_pre cenv cx env (Builtin ann bi args) es /\ MEM e args /\
    expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rw[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
QED

Theorem env_consistent_var_type_evaluates:
  !env cx st id ty.
    env_consistent env cx st /\ FLOOKUP env.var_types id = SOME ty ==>
    IS_SOME (evaluate_type (get_tenv cx) ty)
Proof
  rw[env_consistent_def, env_scopes_consistent_def] >>
  Cases_on `lookup_scopes id st.scopes` >>
  metis_tac[optionTheory.IS_SOME_DEF]
QED

(* The local types are well formed: they evaluate by env_scopes_consistent. *)
Theorem expr_body_pre_var_types_well_formed:
  !cenv cx env e es.
    expr_body_pre cenv cx env e es ==>
    !id t. FLOOKUP env.var_types id = SOME t ==>
           well_formed_type env.type_defs t
Proof
  rw[expr_body_pre_def, expr_sim_inv_def, well_formed_type_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  metis_tac[env_consistent_var_type_evaluates]
QED

Theorem expr_sim_pre_var_types_well_formed:
  !cenv cx env e es.
    expr_sim_pre cenv cx env e es ==>
    !id t. FLOOKUP env.var_types id = SOME t ==>
           well_formed_type env.type_defs t
Proof
  metis_tac[expr_body_pre_var_types_well_formed, expr_sim_pre_body_pre]
QED

(* A well-typed expression's type evaluates. *)
Theorem expr_body_pre_type_evaluates:
  !cenv cx env e es.
    expr_body_pre cenv cx env e es ==>
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e))
Proof
  rpt strip_tac >> drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\ env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  drule_all well_typed_expr_type_well_formed >> gvs[well_formed_type_def]
QED

Theorem well_typed_expr_type_evaluates:
  !cenv cx env e es.
    expr_sim_pre cenv cx env e es ==>
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e))
Proof
  metis_tac[expr_body_pre_type_evaluates, expr_sim_pre_body_pre]
QED

(* A case lemma that proves expr_vv_ok proves expr_ok. *)
Theorem expr_ok_of_vv:
  !cenv e. expr_vv_ok cenv e ==> expr_ok cenv e
Proof
  rw[expr_ok_def, expr_sim_ok_def] >>
  metis_tac[expr_sim_of_vv_sim, expr_vv_ok_def]
QED

(* A form lowered to a StackValue, with only values as results: expr_ok
   from expr_sim_ok (exprSim's expr_vv_sim_stack). *)
Theorem expr_ok_stack:
  !cenv e.
    expr_sim_ok cenv e /\
    (!ty sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op, sb)) /\
    (!cx es tv es'. eval_expr cx e es = (INL tv, es') ==> ?v. tv = Value v) ==>
    expr_ok cenv e
Proof
  rw[expr_ok_def, expr_vv_ok_def] >> irule expr_vv_sim_stack >>
  gvs[expr_sim_ok_def] >> metis_tac[]
QED

Theorem as_stack_val_stack:
  !ty p. ?op st. as_stack_val ty p = (StackValue ty op, st)
Proof
  Cases_on `p` >> simp[as_stack_val_def]
QED

Theorem eval_expr_builtin_value:
  !cx ann bi args es tv es'.
    eval_expr cx (Builtin ann bi args) es = (INL tv, es') ==> ?v. tv = Value v
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, COND_RATOR] >>
  rw[] >> gvs[AllCaseEqs()]
QED

Theorem eval_expr_literal_value:
  !cx ann l es tv es'.
    eval_expr cx (Literal ann l) es = (INL tv, es') ==> ?v. tv = Value v
Proof
  simp[Once evaluate_def, return_def]
QED

(* ===== The judgments of the shared case lemmas ===== *)

Theorem expr_sim_ok_case:
  !cenv e.
    expr_sim_ok cenv e <=> !ctx func cx. expr_sim_case T ctx func cenv cx e
Proof
  rw[expr_sim_ok_def, expr_sim_case_def, expr_sim_pre_body] >> metis_tac[]
QED

Theorem expr_vv_ok_case:
  !cenv e.
    expr_vv_ok cenv e <=> !ctx func cx. expr_vv_case T ctx func cenv cx e
Proof
  rw[expr_vv_ok_def, expr_vv_case_def, expr_sim_pre_body] >> metis_tac[]
QED

Theorem expr_ok_case:
  !cenv e.
    expr_ok cenv e <=>
    !ctx func cx. expr_sim_case T ctx func cenv cx e /\
                  expr_vv_case T ctx func cenv cx e
Proof
  metis_tac[expr_ok_def, expr_sim_ok_case, expr_vv_ok_case]
QED

(* expr_ok_of_vv for one ctx, func and cx. *)
Theorem expr_sim_case_of_vv:
  !nocalls ctx func cenv cx e.
    expr_vv_case nocalls ctx func cenv cx e ==>
    expr_sim_case nocalls ctx func cenv cx e
Proof
  rw[expr_sim_case_def, expr_vv_case_def] >> irule expr_sim_of_vv_sim >>
  metis_tac[]
QED

(* expr_ok_stack for one ctx, func and cx. *)
Theorem expr_vv_case_stack:
  !nocalls ctx func cenv cx e.
    expr_sim_case nocalls ctx func cenv cx e /\
    (!ty sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op, sb)) /\
    (!es tv es'. eval_expr cx e es = (INL tv, es') ==> ?v. tv = Value v) ==>
    expr_vv_case nocalls ctx func cenv cx e
Proof
  rw[expr_sim_case_def, expr_vv_case_def] >> irule expr_vv_sim_stack >>
  metis_tac[]
QED

Theorem expr_sim_case_apply:
  !nocalls ctx func cenv cx env ty e es.
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_body_pre cenv cx env e es /\ (nocalls ==> int_calls_expr e = []) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  metis_tac[expr_sim_case_def]
QED

(* With no internal call in it, an expression's case judgments are its
   expr_ok's, whatever the flag. *)
Theorem expr_case_of_ok:
  !nocalls ctx func cenv cx e.
    int_calls_expr e = [] /\ expr_ok cenv e ==>
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_vv_case nocalls ctx func cenv cx e
Proof
  rw[expr_ok_case] >> gvs[expr_sim_case_def, expr_vv_case_def] >>
  metis_tac[]
QED

(* expr_vv_ok gives the vv judgment of a form the typing gives no operand,
   so no internal call. *)
Theorem expr_vv_case_nil:
  !nocalls ctx func cenv cx e.
    (!env es. expr_body_pre cenv cx env e es ==> int_calls_expr e = []) /\
    expr_vv_ok cenv e ==>
    expr_vv_case nocalls ctx func cenv cx e
Proof
  rw[expr_vv_case_def, expr_vv_ok_def, expr_sim_pre_body] >> metis_tac[]
QED

(* compile_expr_ind's induction hypothesis gives the operands' judgments
   at nocalls = T. *)
Theorem exprs_case_every_ok:
  !ctx func cenv cx es.
    EVERY (expr_ok cenv) es ==> exprs_case T ctx func cenv cx es
Proof
  ntac 4 gen_tac >> Induct >> rw[exprs_case_def] >> gvs[expr_ok_case]
QED

Theorem exprs_case_below:
  !cenv args ctx func cx.
    expr_sim_below cenv (list_size expr_size args) ==>
    exprs_case T ctx func cenv cx args
Proof
  rpt strip_tac >> irule exprs_case_every_ok >> simp[EVERY_MEM] >>
  metis_tac[expr_sim_below_mem]
QED

(* An operand of a builtin: its judgments at a state where the operands
   before it evaluated. *)
Theorem int_calls_builtin_arg:
  !nocalls ann bi args e.
    (nocalls ==> int_calls_expr (Builtin ann bi args) = []) /\ MEM e args ==>
    (nocalls ==> int_calls_expr e = [])
Proof
  rw[int_calls_expr_def] >> metis_tac[int_calls_exprs_mem]
QED

Theorem int_calls_type_builtin_arg:
  !nocalls ann tb t args e.
    (nocalls ==> int_calls_expr (TypeBuiltin ann tb t args) = []) /\
    MEM e args ==>
    (nocalls ==> int_calls_expr e = [])
Proof
  rw[int_calls_expr_def] >> metis_tac[int_calls_exprs_mem]
QED

(* An operand evaluated and read: the condition evaluate_ind puts on the
   next operand's induction hypothesis holds. *)
Theorem eval_expr_read_INL:
  !cx e es v es'.
    (do result <- eval_expr cx e; read_result cx result od) es = (INL v, es') ==>
    ?tv t. eval_expr cx e es = (INL tv, t) /\ read_result cx tv t = (INL v, es')
Proof
  simp[bind_def, AllCaseEqs()] >> metis_tac[]
QED
