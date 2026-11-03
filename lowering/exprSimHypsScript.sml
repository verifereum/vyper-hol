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
 *                       held through pointer variables, the flag
 *                       member ids, flag member counts and struct fields
 *                       of the compile environment, and the storage
 *                       invariants
 *   expr_sim_pre      — expr_sim_inv, the expression well typed, its
 *                       integer types of whole bytes, its buffers below
 *                       the allocation limit, and no internal call,
 *                       raw_call or create in it
 *   byte_widths_expr  — every node's type has a width of whole bytes
 *   expr_body_pre     — expr_sim_pre less int_calls_expr e = []: the
 *                       body simulation's (bodySim); its calls are to
 *                       the main module of a supported program
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
 *   popped_keys_indexed — a local's popped history is typed and keyed
 *                       at dynamic-array indices
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
 *     function's return buffer.  lower_vyper_runtime_unit checks both
 *     (compileVyper's fn_allocs_ok).
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
 *   - The storage clauses: the outcomes are SOME (state_rel), every
 *     declared storage and transient region decodes
 *     (contract_storage_well_formed), the layout is safe, and every
 *     successful outcome still to consume keeps the regions decoding
 *     (oracle_storage_ok).  e2eDefs's source_storage_ok and
 *     call_outcomes_ok ask these of the entry state and the outcomes.
 *     Without them a storage read's slot need not decode: the source
 *     raises where the lowering reads the slot.  expr_sim_pre_eval
 *     carries them on by exprStoragePreservation, which needs no
 *     postulate about the code external calls run.
 *   - ~expr_has_evm_run e: no raw_call or create.  The source runs these
 *     on the EVM even with the outcome oracle, and a delegate raw_call can
 *     write anything into the contract's storage, so nothing keeps the
 *     storage clauses across them without a postulate on that code.
 *     The supported subset excludes both (supported_expr_no_evm_run).
 *   - The popped keys clause (popped_keys_indexed): a local's popped
 *     history is typed, and every key is an index into a dynamic array.
 *     Reading a field or a tuple element of a popped element reads the
 *     history, and a snapshot recorded at the field or element itself
 *     would be read instead of the one the element's snapshot holds, which
 *     memory at the pointer holds.  This is a fact about the source
 *     semantics, not the compiler: pop records the element it removes at
 *     path ++ [ValueSubscript (IntV i)] with a dynamic array at path
 *     (record_pop), a new local starts with no history, and evaluation
 *     changes the scopes only by pops (eval_expr_popped_keys_indexed).
 *   - The map table clauses: the compile environment's ce_hashmap_info
 *     agrees with env's toplevel_vtypes on the declared names
 *     (placeTypingProps's place_map_tables_agree_on_defined, which
 *     placeTypingBuildProps proves of build_compile_env), and has no entry
 *     for a bare global.  compile_subscript dispatches on place_type, which
 *     reads ce_hashmap_info; with these a well-typed expression's
 *     place_type is its own type (place_type_well_typed_on_defined).
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
 *     TopLevelName needs every immutable to be in ce_module_vars (#563);
 *     storage and transient variables are there by storage_vars_rel and
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
  vyperEvalOutcomeSuffix vyperRuntimeAccounts
  vyperStorageLayoutSafety vyperTypeStoragePreservation
  vyperTypeEvalStoragePreservation vyperCallOutcomeStorage
  supportedExprTraverse supportedStmtTraverse exprStoragePreservation
  vyperLookup vyperPlaceResultTyping supportedProgram bodyStoragePreservation
  structFieldsProps vyperTypeABI vyperValue vfmConstants valueEncoding pair
  vyperPlaceInvariants placeTypingProps allocLimits
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

(* A local's popped history is typed at its paths, and every key is an index
   into a dynamic array: pop records the element it removes at
   path ++ [ValueSubscript (IntV i)] where path holds a DynArrayV
   (record_pop), and replace_popped keeps the keys. *)
Definition popped_keys_indexed_def:
  popped_keys_indexed (scs : scope list) <=>
    EVERY (\sc. !id entry. FLOOKUP sc id = SOME entry ==>
                 popped_history_typed entry.type entry.popped /\
                 EVERY (\k. ?p i etv n.
                             k = p ++ [ValueSubscript i] /\
                             subscripts_type entry.type p =
                               SOME (ArrayTV etv (Dynamic n)))
                       (MAP FST entry.popped)) scs
End

(* The source takes external calls from the outcome oracle (state_rel's
   outcomes are SOME).  The storage conjuncts: every declared storage and
   transient region decodes (contract_storage_well_formed), the layout
   keeps the regions in
   range and apart (storage_layout_safe), and every successful outcome
   still to consume leaves the regions decoding (oracle_storage_ok), as
   e2eDefs's source_storage_ok and call_outcomes_ok ask of the entry state
   and the outcomes.  Every immutable or constant the source can read by
   name (env.bare_globals) is an immutable of the module being lowered, at
   an ImmutableLoc whose bytes end below 2 ** 256, as build_compile_env
   places a supported program's immutables (immutableLocationProps). *)
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
    IS_SOME es.outcomes /\
    contract_storage_well_formed cx es /\ storage_layout_safe cx /\
    oracle_storage_ok cx es /\
    popped_keys_indexed es.scopes /\
    place_map_tables_agree_on_defined cenv env /\
    (!nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==>
               cenv.ce_hashmap_info nsid = NONE) /\
    (!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==>
       src = cenv.ce_module /\
       ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
             !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
                  off + type_memory_size tv < dimword (:256))
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

Theorem well_formed_type_byte_bits:
  well_formed_type tenv ty ==> type_bits ty MOD 8 = 0
Proof
  Cases_on `ty` >> simp[type_bits_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[type_bits_def, well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
  metis_tac[]
QED

Theorem subscript_vtype_well_formed:
  well_formed_vtype tenv vt /\ subscript_vtype vt idx = SOME vt' ==>
  well_formed_vtype tenv vt'
Proof
  Cases_on `vt`
  >- (rename1 `Type ty` >> Cases_on `ty` >>
      simp[subscript_vtype_def, well_formed_vtype_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      gvs[well_formed_vtype_def, well_formed_type_def,
          vyperValueTheory.evaluate_type_def] >>
      Cases_on `evaluate_type tenv t` >> gvs[]) >>
  simp[subscript_vtype_def, well_formed_vtype_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem vtype_annotation_byte_bits:
  well_formed_vtype tenv vt /\ vtype_annotation_ok vt ty ==>
  type_bits ty MOD 8 = 0
Proof
  Cases_on `vt` >>
  simp[well_formed_vtype_def, vtype_annotation_ok_def, type_bits_def] >>
  metis_tac[well_formed_type_byte_bits]
QED

Theorem assignable_array_element_byte_bits:
  assignable_type tenv (ArrayT ty bd) ==> type_bits ty MOD 8 = 0
Proof
  simp[assignable_type_def] >>
  metis_tac[assignable_type_well_formed, well_formed_type_byte_bits]
QED

Theorem typed_byte_widths_mutual:
  let W = (\env.
    (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
    (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==> well_formed_vtype env.type_defs vt)) in
  (!env e. well_typed_expr env e ==> W env ==> byte_widths_expr e) /\
  (!env e. !vt. type_place_expr env e = SOME vt ==> W env ==>
    byte_widths_expr e /\ well_formed_vtype env.type_defs vt) /\
  (!env tgt. !vt. type_place_target env tgt = SOME vt ==> W env ==> byte_widths_target tgt) /\
  (!env es. well_typed_exprs env es ==> W env ==> byte_widths_exprs es) /\
  (!env opt. well_typed_opt env opt ==> W env ==> byte_widths_opt opt) /\
  (!env kes. well_typed_named_exprs env kes ==> W env ==> byte_widths_named_exprs kes)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  ho_match_mp_tac well_typed_expr_ind >> conj_tac
  >- (simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[assignable_array_element_byte_bits]) >>
  suspend "calls_places"
QED

Resume typed_byte_widths_mutual[calls_places]:
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      metis_tac[well_formed_type_byte_bits])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, type_bits_def] >>
      metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, raw_call_return_type_def,
           type_bits_def] >>
      Cases_on `flags.rcf_revert_on_failure` >>
      Cases_on `flags.rcf_max_outsize = 0` >>
      simp[type_bits_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, raw_call_return_type_def,
           type_bits_def] >>
      Cases_on `flags.rcf_revert_on_failure` >>
      Cases_on `flags.rcf_max_outsize = 0` >>
      simp[type_bits_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, type_bits_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, type_bits_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, type_bits_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def, type_bits_def] >> metis_tac[])
  >- (simp[well_typed_expr_def, byte_widths_expr_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      metis_tac[vtype_annotation_byte_bits])
  >- (rpt gen_tac >> strip_tac >>
      simp[well_typed_expr_def, byte_widths_expr_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      metis_tac[subscript_vtype_well_formed, vtype_annotation_byte_bits]) >>
  (* Impossible place expressions and empty containers simplify immediately. *)
  simp[well_typed_expr_def, byte_widths_expr_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Finalise typed_byte_widths_mutual

Theorem well_typed_expr_byte_widths:
  well_typed_expr env e /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) ==> byte_widths_expr e
Proof
  mp_tac typed_byte_widths_mutual >> simp[LET_THM] >> metis_tac[]
QED

Theorem type_place_target_byte_widths:
  type_place_target env tgt = SOME vt /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) ==> byte_widths_target tgt
Proof
  mp_tac typed_byte_widths_mutual >> simp[LET_THM] >> metis_tac[]
QED

Theorem byte_widths_exclude_bad_widths:
  (!e. byte_widths_expr e ==>
    ~supported_expr_exists (\e. ~byte_widths_expr e) e) /\
  (!tgt. byte_widths_target tgt ==>
    ~supported_target_exists (\e. ~byte_widths_expr e) tgt) /\
  (!es. byte_widths_exprs es ==>
    ~supported_exprs_exists (\e. ~byte_widths_expr e) es) /\
  (!opt. byte_widths_opt opt ==>
    ~supported_opt_exists (\e. ~byte_widths_expr e) opt) /\
  (!kes. byte_widths_named_exprs kes ==>
    ~supported_fields_exists (\e. ~byte_widths_expr e) kes)
Proof
  ho_match_mp_tac byte_widths_expr_ind >>
  simp[byte_widths_expr_def, supported_expr_exists_def]
QED

Theorem supported_assignments_exists_mem[local]:
  !ts. supported_assignments_exists p ts <=>
    ?t. MEM t ts /\ supported_assignment_exists p t
Proof
  Induct >> simp[supported_assignment_exists_def] >> metis_tac[]
QED

Theorem well_typed_atarget_excludes_bad_widths:
  !env tgt ty.
    well_typed_atarget env tgt ty /\
    (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
    (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype env.type_defs vt) ==>
    ~supported_assignment_exists (\e. ~byte_widths_expr e) tgt
Proof
  recInduct well_typed_atarget_ind >> conj_tac
  >- (simp[well_typed_atarget_def, well_typed_target_def,
           supported_assignment_exists_def] >> rpt strip_tac >>
      metis_tac[type_place_target_byte_widths, byte_widths_exclude_bad_widths]) >>
  simp[well_typed_atarget_def, supported_assignment_exists_def,
       supported_assignments_exists_mem] >> rpt strip_tac >>
  gvs[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]
QED

Theorem typed_expr_excludes_bad_widths:
  well_typed_expr env e /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) ==>
  ~supported_expr_exists (\e. ~byte_widths_expr e) e
Proof
  metis_tac[well_typed_expr_byte_widths, cj 1 byte_widths_exclude_bad_widths]
QED

Theorem typed_exprs_exclude_bad_widths:
  well_typed_exprs env es /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) ==>
  ~supported_exprs_exists (\e. ~byte_widths_expr e) es
Proof
  qid_spec_tac `es` >> Induct >>
  simp[well_typed_expr_def, supported_expr_exists_def] >>
  metis_tac[typed_expr_excludes_bad_widths]
QED

Theorem type_stmts_byte_widths_mutual:
  let W = \env.
    (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
    (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype env.type_defs vt)
  in
    (!env ret s env'. W env /\ type_stmt env ret s = SOME env' ==>
      W env' /\ ~supported_stmt_expr_exists (\e. ~byte_widths_expr e) s) /\
    (!env ret ss env'. W env /\ type_stmts env ret ss = SOME env' ==>
      W env' /\ ~supported_stmts_expr_exists (\e. ~byte_widths_expr e) ss)
Proof
  simp_tac bool_ss [LET_THM] >>
  ho_match_mp_tac type_stmt_ind >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def] >> rpt strip_tac >>
      gvs[AllCaseEqs()] >> metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_expr_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_expr_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_expr_excludes_bad_widths]) >>
  suspend "remaining_statements"
QED

Resume type_stmts_byte_widths_mutual[remaining_statements]:
  conj_tac
  >- simp[type_stmt_def, supported_stmt_expr_exists_def, supported_raise_exists_def] >> conj_tac
  >- simp[type_stmt_def, supported_stmt_expr_exists_def, supported_raise_exists_def] >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_raise_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_raise_exists_def,
           well_typed_custom_error_def, GSYM supported_exprs_exists_every] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_exprs_exclude_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_assert_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_assert_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_assert_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, supported_assert_exists_def,
           well_typed_custom_error_def, GSYM supported_exprs_exists_every] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      metis_tac[typed_expr_excludes_bad_widths, typed_exprs_exclude_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[typed_exprs_exclude_bad_widths]) >>
  suspend "assignments_and_control"
QED

Resume type_stmts_byte_widths_mutual[assignments_and_control]:
  conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      `well_formed_type env.type_defs typ` by metis_tac[assignable_type_well_formed] >>
      simp[extend_local_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
      gvs[extend_local_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
      metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      metis_tac[typed_expr_excludes_bad_widths, type_place_target_byte_widths,
                cj 2 byte_widths_exclude_bad_widths]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      gvs[type_stmt_def, supported_stmt_expr_exists_def, AllCaseEqs()] >>
      `~supported_expr_exists (\e. ~byte_widths_expr e) e` by
        metis_tac[typed_expr_excludes_bad_widths] >> simp[] >>
      Cases_on `tgt`
      >- (rename1 `atarget_accepts env (BaseTarget bt) _` >>
          gvs[atarget_accepts_def, supported_assignment_exists_def] >>
          Cases_on `type_place_target env bt` >> gvs[] >>
          rename1 `SOME vt` >> Cases_on `vt` >> gvs[] >>
          metis_tac[type_place_target_byte_widths, cj 2 byte_widths_exclude_bad_widths]) >>
      gvs[atarget_accepts_def] >>
      metis_tac[well_typed_atarget_excludes_bad_widths]) >> conj_tac
  >- (simp[type_stmt_def, supported_stmt_expr_exists_def, well_typed_target_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      metis_tac[typed_expr_excludes_bad_widths, type_place_target_byte_widths,
                cj 2 byte_widths_exclude_bad_widths]) >>
  suspend "control_and_lists"
QED

Resume type_stmts_byte_widths_mutual[control_and_lists]:
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
      pure_once_rewrite_tac[type_stmt_def] >>
      simp_tac std_ss [AllCaseEqs()] >> strip_tac >> gvs[] >>
      simp[supported_stmt_expr_exists_def] >>
      metis_tac[typed_expr_excludes_bad_widths, optionTheory.IS_SOME_EXISTS]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[type_stmt_def, supported_stmt_expr_exists_def, AllCaseEqs()] >>
      `well_formed_type env.type_defs typ` by metis_tac[assignable_type_well_formed] >>
      `!n ty. FLOOKUP (extend_local env id typ F).var_types n = SOME ty ==>
        well_formed_type (extend_local env id typ F).type_defs ty` by
        (simp[extend_local_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
         gvs[AllCaseEqs()] >> metis_tac[]) >>
      `!src nm vt. FLOOKUP (extend_local env id typ F).toplevel_vtypes (src,nm) = SOME vt ==>
        well_formed_vtype (extend_local env id typ F).type_defs vt` by
        (simp[extend_local_def] >> metis_tac[]) >>
      `~supported_stmts_expr_exists (\e. ~byte_widths_expr e) ss` by
        metis_tac[optionTheory.IS_SOME_EXISTS] >>
      simp[] >> Cases_on `it` >>
      gvs[well_typed_iterator_def, supported_iterator_exists_def] >>
      metis_tac[typed_expr_excludes_bad_widths]) >> conj_tac
  >- simp[type_stmt_def, supported_stmt_expr_exists_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[type_stmt_def, supported_stmt_expr_exists_def, AllCaseEqs()] >>
  qpat_x_assum `_ ==> _ /\ ~supported_stmt_expr_exists _ s` mp_tac >>
  (impl_tac >- (rpt strip_tac >> metis_tac[])) >> strip_tac >>
  qpat_x_assum `_ ==> _ /\ ~supported_stmts_expr_exists _ ss` mp_tac >>
  (impl_tac >- (rpt strip_tac >> metis_tac[])) >> strip_tac >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Finalise type_stmts_byte_widths_mutual

Theorem type_stmts_preserves_well_formed_maps:
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) /\
  type_stmts env ret ss = SOME env' ==>
  (!n ty. FLOOKUP env'.var_types n = SOME ty ==> well_formed_type env'.type_defs ty) /\
  (!src id vt. FLOOKUP env'.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env'.type_defs vt)
Proof
  strip_tac >>
  drule_all (cj 2 (SRULE [LET_THM] type_stmts_byte_widths_mutual)) >>
  strip_tac >> rpt strip_tac >> metis_tac[]
QED

Theorem type_stmts_excludes_bad_widths:
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) /\
  type_stmts env ret ss = SOME env' ==>
  ~supported_stmts_expr_exists (\e. ~byte_widths_expr e) ss
Proof
  strip_tac >>
  drule_all (cj 2 (SRULE [LET_THM] type_stmts_byte_widths_mutual)) >> simp[]
QED

Theorem type_stmt_excludes_bad_widths:
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> well_formed_type env.type_defs ty) /\
  (!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==>
    well_formed_vtype env.type_defs vt) /\
  type_stmt env ret s = SOME env' ==>
  ~supported_stmt_expr_exists (\e. ~byte_widths_expr e) s
Proof
  strip_tac >>
  drule_all (cj 1 (SRULE [LET_THM] type_stmts_byte_widths_mutual)) >> simp[]
QED

Theorem typed_parameter_body_excludes_bad_widths:
  env_context_consistent env cx /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> MEM (n,ty) args) /\
  EVERY (\(n,ty). assignable_type env.type_defs ty) args /\
  type_stmts env ret ss = SOME env' ==>
  ~supported_stmts_expr_exists (\e. ~byte_widths_expr e) ss
Proof
  strip_tac >> drule_all typing_maps_well_formed_params >> strip_tac >>
  drule_all type_stmts_excludes_bad_widths >> simp[]
QED

Definition expr_sim_pre_def:
  expr_sim_pre cenv cx env e es <=>
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    byte_widths_expr e /\ alloc_limits_expr cenv e /\
    int_calls_expr e = [] /\ call_evaluation_safe cx (int_calls_expr e) /\
    ~expr_has_evm_run e
End

(* expr_sim_pre without int_calls_expr e = []: the body simulation's
   (bodySim), where an operand may call an internal function.  Its calls
   are to the main module of a supported program, as supported_expr's
   are, so the callees' bodies keep storage well formed
   (bodyStoragePreservation). *)
Definition expr_body_pre_def:
  expr_body_pre cenv cx env e es <=>
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    byte_widths_expr e /\ alloc_limits_expr cenv e /\
    call_evaluation_safe cx (int_calls_expr e) /\ ~expr_has_evm_run e /\
    EVERY (\c. FST c = NONE /\
               ?tops. supported_program tops /\
                      get_module_code cx NONE = SOME tops)
          (int_calls_expr e)
End

Theorem expr_sim_pre_body:
  !cenv cx env e es.
    expr_sim_pre cenv cx env e es <=>
    expr_body_pre cenv cx env e es /\ int_calls_expr e = []
Proof
  rw[expr_sim_pre_def, expr_body_pre_def, EQ_IMP_THM] >> gvs[]
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

(* The storage conjuncts of expr_sim_inv after evaluating e: with no
   internal call by exprStoragePreservation, with one by
   bodyStoragePreservation.  The outcomes still to consume are a suffix of
   the earlier ones (vyperEvalOutcomeSuffix), so oracle_storage_ok
   carries over. *)
Theorem expr_body_pre_storage_preserved:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    contract_storage_well_formed cx es' /\ oracle_storage_ok cx es'
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (Cases_on `int_calls_expr e = []`
      >- (irule eval_expr_oracle_preserves_contract_storage_well_formed >>
          gvs[expr_body_pre_def, expr_sim_inv_def,
              runtime_storage_consistent_def, runtime_consistent_def] >>
          metis_tac[]) >>
      `?tops. supported_program tops /\ get_module_code cx NONE = SOME tops`
        by (Cases_on `int_calls_expr e` >> gvs[expr_body_pre_def] >>
            metis_tac[]) >>
      irule eval_expr_body_oracle_storage >>
      gvs[expr_body_pre_def, expr_sim_inv_def, listTheory.EVERY_CONJ,
          runtime_storage_consistent_def, runtime_consistent_def] >>
      metis_tac[]) >>
  irule oracle_storage_ok_suffix >> qexists_tac `es` >>
  gvs[expr_body_pre_def, expr_sim_inv_def] >>
  drule_then irule (cj 5 eval_outcome_suffix_mutual)
QED

(* The outcomes stay SOME: evaluation only drops some from the front. *)
Theorem eval_expr_outcomes_some:
  !cx e es res es'.
    IS_SOME es.outcomes /\ eval_expr cx e es = (res, es') ==>
    IS_SOME es'.outcomes
Proof
  rpt strip_tac >> drule (cj 5 eval_outcome_suffix_mutual) >>
  rw[outcome_suffix_def] >> gvs[]
QED

Theorem replace_popped_keys[local]:
  !h tv path r h'.
    replace_popped tv path r h = SOME h' ==> MAP FST h' = MAP FST h
Proof
  Induct >> simp[replace_popped_def] >> Cases >> rpt gen_tac >>
  simp[replace_popped_def] >> rw[AllCaseEqs()] >> gvs[] >> res_tac
QED

Theorem replace_popped_history_typed[local]:
  !h tv path ptv v h'.
    popped_history_typed tv h /\ well_formed_type_value tv /\
    subscripts_type tv path = SOME ptv /\ value_has_type ptv v /\
    replace_popped tv path v h = SOME h' ==>
    popped_history_typed tv h'
Proof
  Induct >> simp[replace_popped_def] >>
  qx_gen_tac `head` >> PairCases_on `head` >> rpt gen_tac >>
  simp[popped_history_typed_cons] >> rpt strip_tac >>
  gvs[Once replace_popped_def, AllCaseEqs()] >>
  simp[popped_history_typed_cons]
  >- (irule vyperPlaceStatePreservationTheory.assign_subscripts_replace_type_metadata >>
      goal_assum (drule_at Any) >> simp[] >>
      qpat_x_assum `IS_PREFIX path head0` mp_tac >>
      simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
      gvs[rich_listTheory.DROP_LENGTH_APPEND] >>
      metis_tac[subscripts_type_append]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem entry_pop_step_event_valid[local]:
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  popped_history_typed entry.type entry.popped /\
  entry_pop_step entry path next ==>
  entry_pop_event_valid (entry,path)
Proof
  rpt strip_tac >>
  `?arr p. read_memory_path entry path = INL arr /\
           popped_value arr = INL p` by
    metis_tac[entry_pop_step_def] >>
  qpat_x_assum `entry_pop_step _ _ _` kall_tac >>
  `?ptv. subscripts_type entry.type path = SOME ptv /\
         value_has_type ptv arr` by
    (qpat_x_assum `read_memory_path _ _ = _` mp_tac >>
     simp[read_memory_path_def, AllCaseEqs()] >> strip_tac
     >- metis_tac[vyperPlaceStatePreservationTheory.evaluate_subscripts_declared_type_exists] >>
     metis_tac[read_popped_declared_type_exists,
               vyperPlaceStatePreservationTheory.read_popped_type]) >>
  Cases_on `arr` >> gvs[vyperValueOperationTheory.popped_value_def] >>
  rename1 `popped_value (ArrayV av) = INL p` >>
  Cases_on `av` >> gvs[vyperValueOperationTheory.popped_value_def] >>
  Cases_on `ptv` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `value_has_type (ArrayTV etv bound) (ArrayV (DynArrayV xs))` >>
  Cases_on `bound` >> gvs[vyperTypingTheory.value_has_type_def] >>
  simp[entry_pop_event_valid_def, vyperTypingTheory.value_has_type_def]
QED

Theorem entry_pop_step_keys_indexed[local]:
  entry_pop_step entry path next /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  popped_history_typed entry.type entry.popped /\
  EVERY (\k. ?p i etv n. k = p ++ [ValueSubscript i] /\
    subscripts_type entry.type p = SOME (ArrayTV etv (Dynamic n)))
    (MAP FST entry.popped) ==>
  popped_history_typed next.type next.popped /\
  EVERY (\k. ?p i etv n. k = p ++ [ValueSubscript i] /\
    subscripts_type next.type p = SOME (ArrayTV etv (Dynamic n)))
    (MAP FST next.popped)
Proof
  strip_tac >>
  `entry_pop_event_valid (entry,path)` by
    (drule_all entry_pop_step_event_valid >> simp[]) >>
  gvs[entry_pop_event_valid_def] >>
  `well_formed_type_value etv` by
    (drule_all vyperPlaceStatePreservationTheory.subscripts_type_well_formed >>
     simp[vyperTypingTheory.well_formed_type_value_def]) >>
  qpat_x_assum `entry_pop_step _ _ _` mp_tac >>
  simp[entry_pop_step_def] >> strip_tac >> gvs[]
  >- (conj_tac
      >- (irule vyperPlaceStatePreservationTheory.record_pop_history_typed_at_path >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      Cases_on `arr` >> gvs[record_pop_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> gvs[record_pop_def] >>
      metis_tac[]) >>
  `value_has_type (ArrayTV etv (Dynamic n)) shortened` by
    metis_tac[vyperAssignPreservesTypeTheory.pop_element_preserves_type] >>
  `popped_history_typed entry.type history` by
    (irule replace_popped_history_typed >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `MAP FST history = MAP FST entry.popped` by metis_tac[replace_popped_keys] >>
  conj_tac
  >- (irule vyperPlaceStatePreservationTheory.record_pop_history_typed_at_path >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  Cases_on `arr` >> gvs[record_pop_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[record_pop_def] >>
  metis_tac[]
QED

Theorem scope_pop_step_keys_indexed[local]:
  !sc ev sc'.
    scope_pop_step sc ev sc' /\ EVERY scope_well_typed sc /\
    popped_keys_indexed sc ==>
    EVERY scope_well_typed sc' /\ popped_keys_indexed sc'
Proof
  rpt gen_tac >> PairCases_on `ev` >>
  simp[scope_pop_step_def] >> strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  gvs[popped_keys_indexed_def, scope_well_typed_def] >>
  `value_has_type ev1.type ev1.value /\ well_formed_type_value ev1.type` by
    metis_tac[] >>
  `popped_history_typed ev1.type ev1.popped` by metis_tac[] >>
  `entry_pop_event_valid (ev1,ev2)` by
    (drule_all entry_pop_step_event_valid >> simp[]) >>
  `value_has_type next.type next.value` by
    (drule_all vyperPlaceMutationSoundnessTheory.entry_pop_step_value_type >> simp[]) >>
  drule entry_pop_step_metadata >> strip_tac >>
  drule entry_pop_step_keys_indexed >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  rw[FLOOKUP_UPDATE] >> gvs[] >> metis_tac[]
QED

Theorem scope_pop_trace_keys_indexed:
  !events sc sc'.
    scope_pop_trace sc events sc' /\ EVERY scope_well_typed sc /\
    popped_keys_indexed sc ==>
    EVERY scope_well_typed sc' /\ popped_keys_indexed sc'
Proof
  Induct >> simp[scope_pop_trace_def] >> rpt strip_tac >>
  drule_all scope_pop_step_keys_indexed >> strip_tac >>
  first_x_assum drule >> simp[]
QED


(* Evaluating an expression changes the scopes only by pops
   (eval_mutual_scope_pop_effect).  A pop from a well-typed local, whose
   history is typed, removes the element of a dynamic array, records it at
   its index and keeps the local and its history typed. *)
Theorem eval_expr_popped_keys_indexed:
  !cx e es res es'.
    eval_expr cx e es = (res, es') /\ state_well_typed es /\
    popped_keys_indexed es.scopes ==>
    popped_keys_indexed es'.scopes
Proof
  rpt strip_tac >>
  `scope_pop_effect (eval_expr cx e)` by
    simp[cj 5 eval_mutual_scope_pop_effect] >>
  gvs[scope_pop_effect_def] >> first_x_assum drule >> strip_tac >>
  gvs[state_well_typed_def] >>
  drule_all scope_pop_trace_keys_indexed >> simp[]
QED

Theorem expr_body_pre_eval_result:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ no_type_error_result res /\
    !tv. res = INL tv ==>
         eval_result_typed (env,cx,es') tv (Type (expr_type e))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_body_pre_storage_preserved >> strip_tac >>
  `IS_SOME es'.outcomes` by
    (irule eval_expr_outcomes_some >>
     gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
  simp[expr_body_pre_def, expr_sim_inv_def] >> strip_tac >>
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
     byte_widths_expr_def, alloc_limits_expr_def, expr_has_evm_run_thm] >>
  drule_all well_typed_exprs_mem >> drule_all byte_widths_exprs_mem >>
  drule_all alloc_limits_exprs_mem >>
  gvs[expr_has_evm_run_thm, EVERY_MEM, EXISTS_MEM] >> metis_tac[]
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

Theorem int_calls_exprs_every_mem:
  !args e P. EVERY P (int_calls_exprs args) /\ MEM e args ==>
             EVERY P (int_calls_expr e)
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
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
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

(* Under expr_sim_inv the compile environment's memory size of a type is
   the source's (the struct fields clause sizes each field). *)
Theorem struct_layout_size_list:
  !fields tvs.
    OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
    EVERY (\(name, ty, sz). !tv. evaluate_type tenv ty = SOME tv ==>
                                  sz = type_memory_size tv) fields ==>
    SUM (MAP (SND o SND) fields) = type_memory_size_list tvs
Proof
  Induct >> simp[type_memory_size_def] >>
  Cases >> rename1 `(name, info)` >> Cases_on `info` >>
  simp[type_memory_size_def] >> rpt strip_tac >> gvs[type_memory_size_def]
QED

Theorem struct_layout_size_zip:
  !names tvs. LENGTH names = LENGTH tvs ==>
    type_memory_size_fields (ZIP (names, tvs)) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[type_memory_size_def]
QED

Theorem expr_sim_inv_memory_size:
  !cenv ty cx env es tv.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv
Proof
  ho_match_mp_tac type_memory_bytes_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt strip_tac >>
      gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          type_memory_bytes_def, type_memory_size_def] >>
      `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
        gvs[expr_sim_inv_def] >>
      `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
        EVERY (\(fname, fty, sz). !tv.
          evaluate_type (get_tenv cx) fty = SOME tv ==>
          sz = type_memory_size tv) fields` by
        (fs[expr_sim_inv_def] >> metis_tac[]) >>
      qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
      simp[sfields_tenv_consistent_def] >> strip_tac >>
      qpat_x_assum `!nsid args. _` drule >> strip_tac >>
      gvs[get_struct_fields_def, evaluate_types_OPT_MMAP] >>
      `LENGTH tvs = LENGTH (MAP FST args)` by
        (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
      simp[struct_layout_size_zip] >>
      irule struct_layout_size_list >>
      qexists_tac `get_tenv cx \\ nsid` >> conj_tac >- gvs[] >>
      qpat_x_assum `!name fields. _ ==> EVERY _ _` drule >>
      simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
      drule (cj 1 vyperTypeExprSoundnessTheory.evaluate_type_mono) >>
      metis_tac[])
  >~ [`TupleT tys`]
  >- (rpt strip_tac >>
      gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          type_memory_bytes_def, type_memory_size_def, evaluate_types_OPT_MMAP] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> irule tuple_memory_bytes_size >>
      qexists_tac `get_tenv cx` >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
      type_memory_bytes_def, type_memory_size_def, word_size_def] >>
  metis_tac[]
QED


(* alloc_limits_expr bounds the expression's own value. *)
Theorem alloc_limits_expr_type_alloc_ok:
  !cenv e. alloc_limits_expr cenv e ==> type_alloc_ok cenv (expr_type e)
Proof
  Cases_on `e` >> simp[alloc_limits_expr_def, vyperASTTheory.expr_type_def]
QED

(* What unwrap_value's copy of the expression's value out of storage,
   transient storage or code asks of its type (expr_sim_of_vv_sim). *)
Theorem expr_body_pre_copy_ok:
  !cenv cx env e es tvt.
    expr_body_pre cenv cx env e es /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    ~is_word_type (expr_type e) ==>
    type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64
Proof
  rpt gen_tac >> strip_tac >>
  `type_memory_bytes cenv (expr_type e) = type_memory_size tvt` by
    (irule expr_sim_inv_memory_size >> fs[expr_body_pre_def] >> metis_tac[]) >>
  `alloc_limits_expr cenv e` by fs[expr_body_pre_def] >>
  drule alloc_limits_expr_type_alloc_ok >> simp[type_alloc_ok_def]
QED

(* A case lemma that proves expr_vv_ok proves expr_ok. *)
Theorem expr_ok_of_vv:
  !cenv e. expr_vv_ok cenv e ==> expr_ok cenv e
Proof
  rw[expr_ok_def, expr_sim_ok_def] >> irule expr_sim_of_vv_sim >>
  rpt strip_tac
  >~ [`expr_vv_sim`] >- (fs[expr_vv_ok_def] >> metis_tac[]) >>
  metis_tac[expr_body_pre_copy_ok, expr_sim_pre_body_pre]
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
  conj_tac >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
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
