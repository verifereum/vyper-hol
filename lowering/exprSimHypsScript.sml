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
 *   - The outcomes clause (outcomes_accounts_typed): every call outcome
 *     still to consume has fewer than 2**256 bytes of return data, which
 *     RETURNDATASIZE reads as a word (raw_call stores the length it reads),
 *     and every successful one adopts runtime well-typed accounts.
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
 *   - ~expr_has_evm_run e: no delegate raw_call or create.  The source
 *     runs these on the EVM even with the outcome oracle, and a delegate
 *     raw_call can write anything into the contract's storage, so nothing
 *     keeps the storage clauses across them without a postulate on that
 *     code.
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
  exprSimSource
  exprSimHypsDefs exprSimProps
  exprSimDefs exprSimStack
  gasContext
  loweringPosts
  list finite_map abiTypeBoundProps
   exprCallBounds exprBopLowering exprLowering compileEnv loweringStateRelDefs
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallStackSoundness
  vyperTypeInitialState
  vyperTypeExprResult vyperTypeEvalSoundness vyperTypeBuiltins
  exprSimConcatSource vyperContext
  vyperExprNoControl loweringSlice exprSimUnwrap exprSafeOperand
  vyperEvalOutcomeSuffix vyperRuntimeAccounts
  vyperStorageLayoutSafety vyperTypeStoragePreservation
  vyperTypeEvalStoragePreservation vyperCallOutcomeStorage
  supportedExprTraverse exprStoragePreservation
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

(* A local's popped history is typed at its paths, and every key is an index
   into a dynamic array: pop records the element it removes at
   path ++ [ValueSubscript (IntV i)] where path holds a DynArrayV
   (record_pop), and replace_popped keeps the keys. *)

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
   places a supported program's immutables (immutableLocationProps).
   Every function signature the typing knows returns the type cenv records
   for it, as build_compile_env records the declared return types
   (build_func_return_type), so an internal call's value is described at a
   type its annotation widens (post_value_type). *)

(* The types whose values are word_values (loweringSlice): integers,
   decimals, booleans and flags.  address and bytesN values are BytesV. *)

(* Every node of an expression has a type whose width, type_bits, is a
   whole number of bytes: of the integer types, those Vyper has.  The same
   recursion as int_calls_expr. *)


(* expr_sim_pre without int_calls_expr e = []: the body simulation's
   (bodySim), where an operand may call an internal function.  Its calls
   are to the main module of a supported program, as supported_expr's
   are, so the callees' bodies keep storage well formed
   (bodyStoragePreservation). *)

(* A call-free expression is described at its annotation. *)
Theorem post_value_type_no_calls[simp]:
  !cenv e. int_calls_expr e = [] ==> post_value_type cenv e = expr_type e
Proof
  rpt strip_tac >> irule post_value_type_not_int_call >> rpt strip_tac >>
  gvs[int_calls_expr_def]
QED

(* An expression's value is described at a type its annotation widens: an
   internal call's at its callee's declared return type, which the typing
   lets the call site widen (well_typed_expr), and which expr_sim_inv says
   cenv records. *)
Theorem post_value_type_widens:
  !cenv cx env es e.
    expr_sim_inv cenv cx env es /\ well_typed_expr env e ==>
    type_widens_to env.type_defs (post_value_type cenv e) (expr_type e)
Proof
  rpt strip_tac >>
  Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
  >- (gvs[] >> rename1 `IntCall fid` >> PairCases_on `fid` >>
      gvs[expr_sim_inv_def, well_typed_expr_def, lowered_value_type_def,
          vyperASTTheory.expr_type_def] >>
      metis_tac[type_widens_to_def]) >>
  `post_value_type cenv e = expr_type e` by metis_tac[post_value_type_not_int_call] >>
  simp[type_widens_to_def]
QED

Theorem type_widens_to_ec_point:
  type_widens_to tenv t (ArrayT (BaseT (UintT 256)) (Fixed 2)) ==>
  t = ArrayT (BaseT (UintT 256)) (Fixed 2)
Proof
  Cases_on `t` >> simp[type_widens_to_def, arg_type_fits_def] >>
  rename1 `arg_type_fits (ArrayT elem bd) _` >>
  Cases_on `bd` >> simp[arg_type_fits_def] >>
  Cases_on `elem` >> simp[arg_type_fits_def] >> metis_tac[]
QED

Theorem post_value_type_ec_point:
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  post_value_type cenv e = expr_type e
Proof
  strip_tac >> drule_all post_value_type_widens >>
  simp[] >> metis_tac[type_widens_to_ec_point]
QED


(* The judgments a shared case lemma takes of its operands and concludes of
   its expression: expr_sim and expr_vv_sim at one ctx, func and cx, at
   every state meeting expr_body_pre, and with no internal call in the
   expression if nocalls.  With nocalls they are expr_sim_ok and
   expr_vv_ok (expr_sim_ok_case, expr_vv_ok_case), compile_expr_sim's
   induction predicate; without, what the body simulation's body_expr_ok
   gives in a frame of the lowered program.  So one case lemma serves
   both. *)


(* The operands of an expression, evaluated and read in order, as
   evaluate_ind gives their judgments: each one's if the ones before it can
   evaluate (bodySim's body_exprs_ok). *)

(* AddMod, MulMod and PowMod256 applied to names: compile_expr lowers these
   itself (compile_addmod_names, ...), not through
   compile_builtin_dispatch. *)



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
Theorem expr_sim_pre_res_ok:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_res_ok res
Proof
  metis_tac[expr_body_pre_res_ok, expr_sim_pre_body_pre]
QED



Theorem expr_sim_pre_vv_res_ok:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_vv_res_ok res
Proof
  metis_tac[expr_body_pre_vv_res_ok, expr_sim_pre_body_pre]
QED



Theorem expr_body_pre_vv_gas_admissible:
  expr_body_pre cenv cx env e es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  rw[gas_admissible_def] >>
  metis_tac[expr_body_pre_gas_obs, expr_body_pre_vv_res_ok]
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

Theorem byte_widths_expr_type:
  !e. byte_widths_expr e ==> type_bits (expr_type e) MOD 8 = 0
Proof
  Cases >> rw[byte_widths_expr_def, expr_type_def]
QED

Theorem expr_sim_pre_builtin_arg:
  !cenv cx env ann bi args e es es'.
    expr_sim_pre cenv cx env (Builtin ann bi args) es /\ MEM e args /\
    ((!n. bi <> Slice n) \/ ~is_extcode e) /\
    expr_sim_inv cenv cx env es' ==>
    expr_sim_pre cenv cx env e es'
Proof
  rpt gen_tac >> strip_tac >>
  `alloc_limits_expr cenv e` by
    (irule alloc_limits_builtin_arg >> gvs[expr_sim_pre_def] >> metis_tac[]) >>
  gvs[expr_sim_pre_def, well_typed_expr_def, int_calls_expr_def,
      byte_widths_expr_def, expr_has_evm_run_thm,
      supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
  drule_all well_typed_exprs_mem >> drule_all byte_widths_exprs_mem >>
  gvs[expr_has_evm_run_thm, EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

(* An operand that isn't of the account-code type is never a slice's
   .code source. *)
Theorem expr_sim_pre_builtin_typed_arg:
  !cenv cx env ann bi args e es es'.
    expr_sim_pre cenv cx env (Builtin ann bi args) es /\ MEM e args /\
    expr_type e <> BaseT (BytesT (Dynamic 24576)) /\
    expr_sim_inv cenv cx env es' ==>
    expr_sim_pre cenv cx env e es'
Proof
  rpt strip_tac >> irule expr_sim_pre_builtin_arg >> simp[] >>
  qexistsl_tac [`ann`, `args`, `bi`, `es`] >> simp[] >> disj2_tac >>
  strip_tac >> qpat_x_assum `expr_type e <> _` mp_tac >> simp[] >>
  irule well_typed_extcode_type >> simp[] >> qexists_tac `env` >>
  irule well_typed_exprs_member >> qexists_tac `args` >>
  gvs[expr_sim_pre_def, well_typed_expr_def]
QED

Theorem int_calls_exprs_mem:
  !args e. int_calls_exprs args = [] /\ MEM e args ==> int_calls_expr e = []
Proof
  Induct >> rw[int_calls_expr_def] >> gvs[]
QED

(* The local types are well formed: they evaluate by env_scopes_consistent. *)
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

Theorem callable_return_evaluates[local]:
  !cx env src ts fn fm nr args dflts ret body.
  functions_well_typed cx /\ env_context_consistent env cx /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,body) /\
  context_function_live cx (src,fn) ==>
  ?tv. evaluate_type (get_tenv cx) ret = SOME tv
Proof
  rw[functions_well_typed_def] >>
  first_x_assum
    (qspecl_then [`env.fn_sigs`, `env.bare_globals`,
                  `env.bare_global_assignable`,
                  `env.toplevel_vtypes`, `env.flag_members`] mp_tac) >>
  impl_tac
  >- (drule env_context_consistent_static_maps_function_side_condition >>
      strip_tac >> gvs[env_context_consistent_def] >>
      rw[] >> first_x_assum drule_all >> simp[]) >>
  rename1 `lookup_callable_function _ _ _ = SOME (_,_,_,_,_,bd)` >>
  disch_then
    (qspecl_then [`src`, `fn`, `ts`, `fm`, `nr`, `args`, `dflts`, `ret`, `bd`] mp_tac) >>
  simp[] >> strip_tac >> goal_assum (drule_at Any)
QED

Theorem signature_return_evaluates[local]:
  functions_well_typed cx /\ env_context_consistent env cx /\
  FLOOKUP env.fn_sigs fid = SOME sig ==>
  ?tv. evaluate_type (get_tenv cx) sig.ret_ty = SOME tv
Proof
  strip_tac >> PairCases_on `fid` >>
  `fn_sigs_consistent env.fn_sigs cx /\ fn_sigs_live env.fn_sigs cx` by
    gvs[env_context_consistent_def] >>
  gvs[fn_sigs_consistent_def, fn_sigs_live_def] >>
  first_x_assum drule >> strip_tac >>
  irule callable_return_evaluates >> metis_tac[]
QED

Theorem post_type_evaluates:
  !cenv cx env e es.
  expr_body_pre cenv cx env e es ==>
  ?tv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tv
Proof
  rpt strip_tac >>
  drule expr_body_pre_type_evaluates >> strip_tac >>
  Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
  >- (gvs[] >> rename1 `IntCall fid` >> PairCases_on `fid` >>
      gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def,
          lowered_value_type_def, vyperASTTheory.expr_type_def] >>
      `env_context_consistent env cx` by gvs[env_consistent_def] >>
      drule_all signature_return_evaluates >> strip_tac >>
      first_x_assum drule >> disch_then SUBST1_TAC >>
      IF_CASES_TAC >> simp[] >>
      Cases_on `evaluate_type (get_tenv cx) ty` >> gvs[]) >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[post_value_type_not_int_call] >>
  Cases_on `evaluate_type (get_tenv cx) (expr_type e)` >> gvs[]
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
  rw[expr_ok_def, expr_sim_ok_def] >>
  `expr_body_pre cenv cx env e es` by
    metis_tac[expr_sim_pre_body_pre] >>
  `post_value_type cenv e = expr_type e` by
    (fs[expr_sim_pre_def] >> simp[post_value_type_no_calls]) >>
  irule expr_sim_of_vv_sim >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
  fs[expr_vv_ok_def] >> metis_tac[]
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
    post_value_type cenv e = expr_type e /\
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

Theorem results_case_every_ok:
  !ctx func cenv cx es.
    EVERY (expr_ok cenv) es ==> results_case T ctx func cenv cx es
Proof
  ntac 4 gen_tac >> Induct >> rw[results_case_def] >> gvs[expr_ok_case]
QED

Theorem results_case_below:
  !cenv args ctx func cx.
    expr_sim_below cenv (list_size expr_size args) ==>
    results_case T ctx func cenv cx args
Proof
  rpt strip_tac >> irule results_case_every_ok >> simp[EVERY_MEM] >>
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

(* Result annotations are static: the interpreter uses the target type. *)
Theorem eval_type_builtin_annotation:
  !cx ty ty' tb target args.
    eval_expr cx (TypeBuiltin ty tb target args) =
    eval_expr cx (TypeBuiltin ty' tb target args)
Proof
  simp[Once evaluate_def, SimpLHS] >> simp[Once evaluate_def, SimpRHS]
QED

Theorem type_builtin_read_annotation_typed:
  !cenv cx env es es' ty ty' tb target args v.
    expr_sim_inv cenv cx env es /\
    well_typed_expr env (TypeBuiltin ty' tb target args) /\
    call_evaluation_safe cx (int_calls_expr (TypeBuiltin ty tb target args)) /\
    (do r <- eval_expr cx (TypeBuiltin ty tb target args);
        read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env ty' v
Proof
  rpt strip_tac >>
  `(do r <- eval_expr cx (TypeBuiltin ty' tb target args);
       read_result cx r od) es = (INL v, es')` by
    metis_tac[eval_type_builtin_annotation] >>
  drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
  disch_then (qspec_then `env` mp_tac) >>
  gvs[expr_sim_inv_def, int_calls_expr_def, expr_type_def]
QED

(* A zero produced capacity is stronger than an oversized result annotation,
   including the ABI encoder's computed capacity. *)
Theorem expr_body_pre_abi_encode_zero_size:
  !cenv cx env ann ensure mid target args es.
    expr_body_pre cenv cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
    lowered_value_type cenv (TypeBuiltin ann (AbiEncode ensure mid) target args) =
      BaseT (BytesT (Dynamic 0)) ==>
    abi_encode_size_ok env.type_defs ensure target mid 0
Proof
  rpt strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_exprs env args /\ target = TupleT (MAP expr_type args) /\
   env.type_defs = get_tenv cx /\
   sfields_tenv_consistent cenv.ce_struct_fields env.type_defs` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def,
        well_typed_type_builtin_args_def, env_consistent_def,
        env_context_consistent_def] >>
  `!a. MEM a args ==> IS_SOME (evaluate_type env.type_defs (expr_type a))` by
    (rpt strip_tac >>
     `well_typed_expr env a` by metis_tac[well_typed_exprs_member] >>
     drule_all well_typed_expr_type_well_formed >>
     simp[well_formed_type_def]) >>
  `!t. MEM t (MAP expr_type args) ==>
       IS_SOME (evaluate_type env.type_defs t)` by
    (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
  `!t. MEM t (MAP expr_type args) ==>
    abi_size_bound cenv.ce_struct_fields t = vyper_abi_size_bound env.type_defs t /\
    abi_embedded_static_size cenv.ce_struct_fields t +
      (if is_abi_dynamic cenv.ce_struct_fields t then
         abi_size_bound cenv.ce_struct_fields t else 0) =
      vyper_abi_embedded_size env.type_defs t` by
    (rpt strip_tac >>
     `?tv. evaluate_type env.type_defs t = SOME tv` by
       metis_tac[optionTheory.IS_SOME_EXISTS] >>
     drule_all abi_props_vyper_typed >> simp[]) >>
  `abi_size_bound cenv.ce_struct_fields (TupleT (MAP expr_type args)) =
   vyper_abi_size_bound env.type_defs (TupleT (MAP expr_type args))` by
    (irule abi_size_bound_tuple_agrees >> metis_tac[]) >>
  `mid = NONE` by
    (Cases_on `mid` >> gvs[lowered_value_type_def]) >>
  gvs[lowered_value_type_def, abi_encode_size_ok_def,
      abi_encode_method_id_size_def, vyperASTTheory.abi_encode_method_id_bytes_def] >>
  Cases_on `args` >> gvs[] >>
  rename1 `well_typed_exprs env (a::rest)` >> Cases_on `rest` >> gvs[] >>
  Cases_on `ensure` >> gvs[] >> metis_tac[]
QED

Theorem expr_body_pre_abi_encode_zero_annotation:
  !cenv cx env ann ensure mid target args es.
    expr_body_pre cenv cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
    lowered_value_type cenv (TypeBuiltin ann (AbiEncode ensure mid) target args) =
      BaseT (BytesT (Dynamic 0)) ==>
    well_typed_expr env
      (TypeBuiltin (BaseT (BytesT (Dynamic 0))) (AbiEncode ensure mid) target args)
Proof
  rpt strip_tac >> drule_all expr_body_pre_abi_encode_zero_size >> strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def, type_builtin_result_ok_def,
      well_formed_type_def, evaluate_type_def, type_slot_size_def,
      vfmConstantsTheory.word_size_def]
QED

Theorem value_runtime_typed_zero_bytestring_empty:
  !env v.
    (value_runtime_typed env (BaseT (BytesT (Dynamic 0))) v \/
     value_runtime_typed env (BaseT (StringT 0)) v) ==>
    (v = BytesV [] \/ v = StringV "")
Proof
  rpt strip_tac >>
  gvs[value_runtime_typed_def, evaluate_type_def, type_slot_size_def,
      vfmConstantsTheory.word_size_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED

Theorem expr_body_pre_read_value_typed[local]:
  !cenv cx env e es v es'.
    expr_body_pre cenv cx env e es /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env (expr_type e) v
Proof
  rpt strip_tac >>
  drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
  disch_then (qspec_then `env` mp_tac) >>
  gvs[expr_body_pre_def, expr_sim_inv_def]
QED

(* concat(...) evaluation and buffer sizing, shared with exprSimConcatResult. *)
Theorem eval_expr_concat_bind:
  !cx ann n args.
    2 <= LENGTH args ==>
    eval_expr cx (Builtin ann (Concat n) args) =
    bind (eval_exprs cx args)
      (\vs st. ((case evaluate_concat n vs of
                   INL v => INL (Value v)
                 | INR err => INR (Error err)), st))
Proof
  rw[FUN_EQ_THM] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, builtin_args_length_ok_def] >>
  Cases_on `eval_exprs cx args x` >>
  rename1 `eval_exprs cx args x = (rr, st)` >>
  Cases_on `rr` >>
  simp[get_accounts_def, lift_sum_def, evaluate_builtin_def, return_def,
       raise_def, bind_def, ignore_bind_def] >>
  rename1 `evaluate_concat n vs` >>
  Cases_on `evaluate_concat n vs` >>
  simp[return_def, raise_def, bind_def, ignore_bind_def]
QED

Theorem concat_payload_capacity_bound:
  !ts. EVERY (\t. (?bd. t = BaseT (BytesT bd)) \/ ?m. t = BaseT (StringT m)) ts ==>
       MAP bytelike_type_bound ts = MAP concat_payload_capacity ts
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[bytelike_type_bound_def, concat_payload_capacity_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[bound_length_def, concat_payload_capacity_def]
QED

Theorem concat_map_ctor_11:
  (!l1 l2. MAP BytesV l1 = MAP BytesV l2 <=> l1 = l2) /\
  (!l1 l2. MAP StringV l1 = MAP StringV l2 <=> l1 = l2)
Proof
  conj_tac >> Induct >> gen_tac >> Cases_on `l2` >> simp[]
QED

Theorem concat_alloc_size_bounds:
  !tys. 32 + SUM (MAP concat_payload_capacity tys) <= concat_alloc_size tys /\
        32 + concat_data_bound 0 tys <= concat_alloc_size tys
Proof
  gen_tac >> simp[concat_alloc_size_def, LET_THM] >>
  qabbrev_tac `c = SUM (MAP concat_payload_capacity tys)` >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `c + 31` strip_assume_tac) >>
  `(c + 31) MOD 32 < 32` by simp[] >>
  decide_tac
QED

Theorem concat_buffer_type_bytestring[local]:
  !ty n. is_bytestring_type (concat_buffer_type ty n)
Proof
  rw[concat_buffer_type_def] >> CASE_TAC >> simp[is_bytestring_type_def] >>
  CASE_TAC >> simp[is_bytestring_type_def]
QED

(* A concat result fits the buffer the lowering allocates for it. *)
Theorem concat_read_buffer_typed:
  !cenv cx env ty n args es v es'.
    expr_body_pre cenv cx env (Builtin ty (Concat n) args) es /\
    (do r <- eval_expr cx (Builtin ty (Concat n) args); read_result cx r od) es =
      (INL v, es') ==>
    value_runtime_typed env
      (concat_buffer_type ty (SUM (MAP (concat_payload_capacity o expr_type) args))) v
Proof
  rpt strip_tac >>
  `expr_sim_inv cenv cx env es /\
   well_typed_expr env (Builtin ty (Concat n) args) /\
   alloc_limits_expr cenv (Builtin ty (Concat n) args) /\
   call_evaluation_safe cx (int_calls_expr (Builtin ty (Concat n) args))` by
    fs[expr_body_pre_def] >>
  `well_typed_exprs env args /\ 2 <= LENGTH args /\
   SUM (MAP bytelike_type_bound (MAP expr_type args)) <= n /\
   ((ty = BaseT (BytesT (Dynamic n)) /\
     EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
    (ty = BaseT (StringT n) /\
     EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args)))` by
    (qpat_x_assum `well_typed_expr _ _` mp_tac >>
     simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
     rpt strip_tac >> fs[]) >>
  `call_evaluation_safe cx (int_calls_exprs args)` by
    (qpat_x_assum `call_evaluation_safe _ (int_calls_expr _)` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> simp[]) >>
  `concat_alloc_size (MAP expr_type args) < 2 ** 64` by
    (qpat_x_assum `alloc_limits_expr _ _` mp_tac >> simp[alloc_limits_expr_def]) >>
  `SUM (MAP (concat_payload_capacity o expr_type) args) < 2 ** 64` by
    (qspec_then `MAP expr_type args` strip_assume_tac concat_alloc_size_bounds >>
     fs[MAP_MAP_o]) >>
  `(SUM (MAP (concat_payload_capacity o expr_type) args) + 31) DIV 32 <=
   SUM (MAP (concat_payload_capacity o expr_type) args) + 31` by
    simp[arithmeticTheory.DIV_LESS_EQ] >>
  `MAP bytelike_type_bound (MAP expr_type args) =
   MAP concat_payload_capacity (MAP expr_type args)` by
    (irule concat_payload_capacity_bound >> fs[EVERY_MEM]) >>
  drule eval_expr_concat_bind >>
  disch_then (qspecl_then [`cx`, `ty`, `n`] SUBST_ALL_TAC) >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[bind_def] >>
  Cases_on `eval_exprs cx args es` >> rename1 `eval_exprs cx args es = (rr, st)` >>
  Cases_on `rr` >> simp[] >>
  rename1 `eval_exprs cx args es = (INL vs, st)` >>
  `exprs_runtime_typed env args vs` by
    (qspecl_then [`cx`, `args`] (assume_tac o cj 1) (cj 6 eval_scc_type_sound_mutual) >>
     first_x_assum (qspecl_then [`env`, `es`, `INL vs`, `st`] mp_tac) >>
     fs[expr_sim_inv_def]) >>
  `LIST_REL (\t v. ?tv. evaluate_type env.type_defs t = SOME tv /\ value_has_type tv v)
     (MAP expr_type args) vs` by
    (fs[exprs_runtime_typed_def, LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]) >>
  gvs[]
  >~ [`concat_buffer_type (BaseT (BytesT _)) _`]
  >- (drule_all typed_bytes_operands >> strip_tac >>
      mp_tac (Q.INST [`ts` |-> `MAP expr_type args`, `tenv` |-> `env.type_defs`]
                evaluate_concat_typed_bytes) >>
      impl_tac >- fs[] >> strip_tac >>
      gvs[concat_map_ctor_11, read_result_def, return_def] >> strip_tac >>
      gvs[concat_buffer_type_def, value_runtime_typed_def, evaluate_type_def,
          type_slot_size_def, vyperTypingTheory.value_has_type_def,
          MAP_MAP_o, vfmConstantsTheory.word_size_def, wordsTheory.dimword_def])
  >> drule_all typed_string_operands >> strip_tac >>
  mp_tac (Q.INST [`ts` |-> `MAP expr_type args`, `tenv` |-> `env.type_defs`]
            evaluate_concat_typed_string) >>
  impl_tac >- fs[] >> strip_tac >>
  gvs[concat_map_ctor_11, read_result_def, return_def] >> strip_tac >>
  gvs[concat_buffer_type_def, value_runtime_typed_def, evaluate_type_def,
      type_slot_size_def, vyperTypingTheory.value_has_type_def,
      MAP_MAP_o, vfmConstantsTheory.word_size_def, wordsTheory.dimword_def]
QED

Theorem lowered_zero_bytestring_read_empty:
  !cenv cx env e es v es'.
    expr_body_pre cenv cx env e es /\
    (!a f args d. e = Call a (IntCall f) args d ==>
       lowered_value_type cenv e = expr_type e) /\
    (lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
     lowered_value_type cenv e = BaseT (StringT 0)) /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
    (v = BytesV [] \/ v = StringV "")
Proof
  rpt gen_tac >>
  map_every qid_spec_tac [`es'`, `v`, `es`, `env`, `cx`, `e`, `cenv`] >>
  ho_match_mp_tac lowered_value_type_ind >>
  rpt conj_tac >> rpt gen_tac
  >~ [`Literal (BaseT (StringT _)) (StringL _)`]
  >- (simp[lowered_value_type_def] >> strip_tac >> gvs[] >>
      gvs[Once evaluate_def, vyperValueOperationTheory.evaluate_literal_def, bind_def, return_def,
          read_result_def])
  >~ [`Literal (BaseT (BytesT (Dynamic _))) (BytesL _)`]
  >- (simp[lowered_value_type_def] >> strip_tac >> gvs[] >>
      gvs[Once evaluate_def, vyperValueOperationTheory.evaluate_literal_def, bind_def, return_def,
          read_result_def])
  >~ [`TypeBuiltin _ (AbiEncode _ _) _ _`]
  >- (strip_tac >>
      rename1 `expr_body_pre cenv cx env
        (TypeBuiltin ann (AbiEncode ensure method_id) target args) es` >>
      `lowered_value_type cenv
         (TypeBuiltin ann (AbiEncode ensure method_id) target args) =
       BaseT (BytesT (Dynamic 0))` by
        gvs[lowered_value_type_def] >>
      drule_all expr_body_pre_abi_encode_zero_annotation >> strip_tac >>
      irule value_runtime_typed_zero_bytestring_empty >>
      qexists_tac `env` >> disj1_tac >>
      irule type_builtin_read_annotation_typed >>
      gvs[expr_body_pre_def] >> goal_assum drule >> simp[] >>
      metis_tac[])
  >~ [`Builtin _ (Concat _) _`]
  >- (rpt strip_tac >> drule_all concat_read_buffer_typed >> strip_tac >>
      irule value_runtime_typed_zero_bytestring_empty >> qexists_tac `env` >>
      gvs[lowered_value_type_def])
  >~ [`Call _ (IntCall _) _ _`]
  >- (strip_tac >> drule_all expr_body_pre_read_value_typed >> strip_tac >>
      irule value_runtime_typed_zero_bytestring_empty >> qexists_tac `env` >>
      gvs[lowered_value_type_def, expr_type_def])
  >> (strip_tac >> drule_all expr_body_pre_read_value_typed >> strip_tac >>
      irule value_runtime_typed_zero_bytestring_empty >> qexists_tac `env` >>
      qpat_x_assum `lowered_value_type _ _ = _` mp_tac >>
      simp[lowered_value_type_def] >> strip_tac >> gvs[])
QED

(* Operand syntax contracts transported through successful evaluation. *)
Theorem expr_int_literal_value:
  !e. expr_int_literal e = int_literal_value e
Proof
  Cases >> simp[expr_int_literal_def, int_literal_value_def] >>
  rename1 `Literal _ l` >> Cases_on `l` >>
  simp[expr_int_literal_def, int_literal_value_def]
QED

Theorem eval_expr_int_literal_agrees:
  !cx e es tv es' v es'' n.
    eval_expr cx e es = (INL tv, es') /\
    read_result cx tv es' = (INL v, es'') /\
    expr_int_literal e = SOME n ==> v = IntV n
Proof
  Cases_on `e` >> simp[expr_int_literal_def] >>
  rename1 `Literal _ l` >> Cases_on `l` >> simp[expr_int_literal_def] >>
  rpt strip_tac >>
  gvs[Once evaluate_def, return_def, vyperValueOperationTheory.evaluate_literal_def, read_result_def]
QED

Theorem eval_expr_shift_amount:
  !cx e es tv es' v es'' tenv vt.
    eval_expr cx e es = (INL tv, es') /\
    read_result cx tv es' = (INL v, es'') /\
    evaluate_type tenv (expr_type e) = SOME vt /\ value_has_type vt v /\
    shift_amount_ok e ==> ?i. v = IntV i /\ 0 <= i
Proof
  rpt gen_tac >> strip_tac >>
  gvs[shift_amount_ok_def]
  >- (gvs[is_uint_type_def, vyperValueTheory.evaluate_type_def,
          AllCaseEqs()] >>
      Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  gvs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
  Cases_on `expr_int_literal e` >> gvs[] >>
  drule_all eval_expr_int_literal_agrees >> strip_tac >> metis_tac[]
QED

Theorem expr_body_pre_bop_operands:
  !cenv cx env ann bop e1 e2 es.
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    (bop = Exp ==> IS_SOME (expr_int_literal e1) \/
      ?n. expr_int_literal e2 = SOME n /\ 0 <= n) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e2)
Proof
  simp[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
       builtin_operands_ok_def, nonneg_int_literal_def,
       GSYM expr_int_literal_value] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `expr_int_literal e2` >> gvs[]
QED

Theorem ifexp_arg_type_fits_refl[local]:
  !t. arg_type_fits t t
Proof
  Induct >> simp[arg_type_fits_def]
  >- (Cases >> simp[arg_type_fits_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> simp[arg_type_fits_def])
  >- (Induct_on `l` >> simp[arg_type_fits_def]) >>
  Cases >> simp[arg_type_fits_def]
QED

(* Physical return facts used by the revised IfExp layout alternative. *)
Theorem ifexp_body_pre_intcall_physical:
  expr_body_pre ce cx env (Call ty (IntCall fid) args drv) es ==>
  arg_type_fits (lowered_value_type ce (Call ty (IntCall fid) args drv)) ty /\
  ?tvp. evaluate_type (get_tenv cx)
    (lowered_value_type ce (Call ty (IntCall fid) args drv)) = SOME tvp
Proof
  strip_tac >> PairCases_on `fid` >>
  gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def,
      lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  `env_context_consistent env cx` by gvs[env_consistent_def] >>
  drule_all signature_return_evaluates >> strip_tac >>
  first_x_assum drule >> disch_then SUBST1_TAC >>
  gvs[type_widens_to_def, ifexp_arg_type_fits_refl]
QED

(* Typed IfExp adapters read an aggregate call at its physical return type. *)
Theorem ifexp_intcall_copy_source:
  expr_body_pre ce cx env (Call ty (IntCall fid) args drv) es /\
  ~is_word_type ty /\ ~is_bytestring_type ty ==>
  post_value_type ce (Call ty (IntCall fid) args drv) =
    lowered_value_type ce (Call ty (IntCall fid) args drv) /\
  type_widens_to (get_tenv cx)
    (lowered_value_type ce (Call ty (IntCall fid) args drv)) ty /\
  ?tvp. evaluate_type (get_tenv cx)
    (lowered_value_type ce (Call ty (IntCall fid) args drv)) = SOME tvp
Proof
  strip_tac >> drule ifexp_body_pre_intcall_physical >> strip_tac >>
  simp[] >>
  `expr_sim_inv ce cx env es /\ well_typed_expr env
     (Call ty (IntCall fid) args drv)` by gvs[expr_body_pre_def] >>
  drule_all post_value_type_widens >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  simp[vyperASTTheory.expr_type_def]
QED

Theorem ifexp_intcall_read_cast[local]:
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,params,dflts,ret,bd) /\
  (do r <- eval_expr cx (Call ty (IntCall (src,fn)) args drv);
      read_result cx r od) es = (INL v,es') ==>
  ?rtv rv. evaluate_type (get_tenv cx) ret = SOME rtv /\ safe_cast rtv rv = SOME v
Proof
  strip_tac >>
  qpat_x_assum `(do r <- eval_expr _ _; read_result _ r od) _ = _`
    (assume_tac o ONCE_REWRITE_RULE [evaluate_def]) >>
  fs[ignore_bind_def] >>
  rpt (dxrule vyperStatePreservationTheory.bind_split >> strip_tac >> gvs[]) >>
  gvs[lift_option_type_def, return_def, raise_def, read_result_def] >>
  Cases_on `evaluate_type (get_tenv cx) ret` >> gvs[raise_def, return_def] >>
  rename1 `safe_cast rtv rv` >>
  Cases_on `safe_cast rtv rv` >> gvs[raise_def, return_def] >>
  metis_tac[]
QED

Theorem ifexp_intcall_read_physical_typed:
  expr_body_pre ce cx env (Call ty (IntCall fid) args drv) es /\
  (do r <- eval_expr cx (Call ty (IntCall fid) args drv);
      read_result cx r od) es = (INL v,es') ==>
  ?stv. evaluate_type (get_tenv cx)
    (lowered_value_type ce (Call ty (IntCall fid) args drv)) = SOME stv /\
    value_has_type stv v
Proof
  strip_tac >> PairCases_on `fid` >>
  `env_context_consistent env cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def] >>
  fs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def,
     lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  qpat_x_assum `!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==> _` drule >>
  disch_then SUBST1_TAC >>
  `fn_sigs_consistent env.fn_sigs cx` by
    gvs[env_context_consistent_def] >>
  fs[fn_sigs_consistent_def] >>
  qpat_x_assum `!src fn sig. FLOOKUP env.fn_sigs (src,fn) = SOME sig ==> _` drule >>
  strip_tac >>
  drule_all ifexp_intcall_read_cast >> strip_tac >>
  goal_assum (drule_at Any) >>
  metis_tac[vyperTypingTheory.safe_cast_result_well_typed]
QED

Theorem word_size_monotone:
  !n m. n <= m ==> word_size n <= word_size m
Proof
  rpt strip_tac >> simp[vfmConstantsTheory.word_size_def] >>
  irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]
QED

Theorem abi_encode_lowered_well_typed_coherent:
  !cenv cx env ann ensure mid target args es.
    expr_body_pre cenv cx env
      (TypeBuiltin ann (AbiEncode ensure mid) target args) es ==>
    well_typed_expr env
      (TypeBuiltin
        (lowered_value_type cenv
          (TypeBuiltin ann (AbiEncode ensure mid) target args))
        (AbiEncode ensure mid) target args)
Proof
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env (TypeBuiltin ann (AbiEncode ensure mid) target args) /\
   sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  qpat_x_assum `expr_body_pre _ _ _ _ _` kall_tac >>
  gvs[well_typed_expr_def, type_builtin_result_ok_def,
      well_typed_type_builtin_args_def] >>
  `EVERY (well_formed_type (get_tenv cx)) (MAP expr_type args)` by
    (qpat_x_assum `abi_encode_size_ok _ _ _ _ _` kall_tac >>
     qpat_x_assum `args <> []` kall_tac >>
     qpat_x_assum `well_typed_exprs env args` mp_tac >>
     Induct_on `args` >> simp[well_typed_expr_def] >>
     metis_tac[well_typed_expr_type_well_formed]) >>
  qmatch_goalsub_abbrev_tac `lowered_value_type cenv be` >>
  qabbrev_tac `enc_ty0 = if LENGTH args = 1 /\ ~ensure then expr_type (HD args)
                     else TupleT (MAP expr_type args)` >>
  `abi_size_bound cenv.ce_struct_fields enc_ty0 =
   vyper_abi_size_bound (get_tenv cx) enc_ty0` by
    (simp[Abbr `enc_ty0`] >> IF_CASES_TAC
     >- (Cases_on `args` >> gvs[well_formed_type_def,
             optionTheory.IS_SOME_EXISTS] >>
         drule_all abi_props_vyper_typed >> simp[]) >>
     irule abi_size_bound_tuple_typed >>
     fs[well_formed_type_def, EVERY_MEM]) >>
  `!k. abi_encode_size_ok (get_tenv cx) ensure (TupleT (MAP expr_type args)) mid k =
   (vyper_abi_size_bound (get_tenv cx) enc_ty0 +
    (if IS_SOME mid then 4 else 0) <= k)` by
    (Cases_on `args` >> gvs[] >> Cases_on `t` >>
     Cases_on `mid` >> Cases_on `ensure` >>
     gvs[abi_encode_size_ok_def, abi_encode_method_id_size_def,
         abi_encode_method_id_bytes_def, Abbr `enc_ty0`]) >>
  simp[Abbr `be`, lowered_value_type_def] >>
  gvs[well_formed_type_def, evaluate_type_def, type_slot_size_def] >>
  drule word_size_monotone >> strip_tac >>
  qpat_x_assum `word_size _ <= word_size n` mp_tac >>
  qpat_x_assum `word_size n + 1 <= _` mp_tac >>
  qpat_x_assum `_ <= n` mp_tac >>
  qpat_x_assum `n < _` mp_tac >> decide_tac
QED

Theorem memory_rhs_read_annotation_typed:
  !cenv cx env e es v es'.
    expr_body_pre cenv cx env e es /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env (expr_type e) v
Proof
  rpt strip_tac >>
  drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
  disch_then (qspec_then `env` mp_tac) >>
  gvs[expr_body_pre_def, expr_sim_inv_def]
QED

Theorem memory_rhs_read_lowered_typed_unwidened:
  !cenv e env cx es v es'.
    expr_body_pre cenv cx env e es /\
    (!a f args d. e = Call a (IntCall f) args d ==>
       lowered_value_type cenv e = expr_type e) /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env (lowered_value_type cenv e) v
Proof
  ho_match_mp_tac lowered_value_type_ind >> rpt conj_tac
  >- (rpt gen_tac >> simp[lowered_value_type_def] >> strip_tac >>
      gvs[Once evaluate_def, bind_def, return_def, read_result_def,
          vyperValueOperationTheory.evaluate_literal_def] >>
      gvs[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def,
          well_formed_type_def, evaluate_type_def] >>
      simp[value_runtime_typed_def, evaluate_type_def,
           vyperTypingTheory.value_has_type_def, compatible_bound_def] >>
      gvs[type_slot_size_def, compatible_bound_def] >>
      imp_res_tac word_size_monotone >> decide_tac)
  >- (rpt gen_tac >> simp[lowered_value_type_def] >> strip_tac >>
      gvs[Once evaluate_def, bind_def, return_def, read_result_def,
          vyperValueOperationTheory.evaluate_literal_def] >>
      gvs[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def,
          well_formed_type_def, evaluate_type_def] >>
      simp[value_runtime_typed_def, evaluate_type_def,
           vyperTypingTheory.value_has_type_def, compatible_bound_def] >>
      gvs[type_slot_size_def, compatible_bound_def] >>
      imp_res_tac word_size_monotone >> decide_tac)
  >~ [`Builtin _ (Concat _) _`]
  >- (rpt strip_tac >> simp[lowered_value_type_def] >>
      drule_all concat_read_buffer_typed >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      drule abi_encode_lowered_well_typed_coherent >> strip_tac >>
      irule type_builtin_read_annotation_typed >>
      metis_tac[expr_body_pre_def])
  >~ [`Call _ (IntCall _) _ _`]
  >- (rw[] >> metis_tac[memory_rhs_read_annotation_typed]) >>
  rpt gen_tac >> strip_tac >> simp[lowered_value_type_def] >>
  metis_tac[memory_rhs_read_annotation_typed]
QED

Theorem lowered_value_type_bytestring:
  !cenv e.
    (!a f args d. e = Call a (IntCall f) args d ==>
       lowered_value_type cenv e = expr_type e) /\
    is_bytestring_type (expr_type e) ==>
    is_bytestring_type (lowered_value_type cenv e)
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, is_bytestring_type_def,
       concat_buffer_type_bytestring]
QED

(* Shared physical internal-call typing, formerly local to memoryLocalRhsProps. *)
Theorem frame_signature_return_well_formed:
  !cenv cx env es id sig.
    expr_sim_inv cenv cx env es /\ FLOOKUP env.fn_sigs id = SOME sig ==>
    well_formed_type env.type_defs sig.ret_ty
Proof
  rpt strip_tac >>
  `env_consistent env cx es /\ functions_well_typed cx` by
    gvs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx /\ fn_sigs_consistent env.fn_sigs cx` by
    (qpat_x_assum `env_consistent _ _ _` mp_tac >>
     simp[vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  Cases_on `id` >>
  qpat_assum `fn_sigs_consistent _ _` mp_tac >>
  pure_rewrite_tac[vyperTypeInvariantsTheory.fn_sigs_consistent_def] >>
  disch_then drule >> strip_tac >>
  `IS_SOME (FLOOKUP env.fn_sigs (q,r))` by simp[] >>
  drule_all callable_body_typing_from_env_consistent >>
  simp[] >> strip_tac >>
  simp[well_formed_type_def]
QED

Theorem internal_call_annotation_eval:
  !cx a b id args drv.
    eval_expr cx (Call a (IntCall id) args drv) =
    eval_expr cx (Call b (IntCall id) args drv)
Proof
  rpt gen_tac >> Cases_on `id` >> once_rewrite_tac[evaluate_def] >> REFL_TAC
QED

Theorem internal_call_read_signature_typed:
  !cenv cx env es ann id args drv sig v es'.
    expr_body_pre cenv cx env (Call ann (IntCall id) args drv) es /\
    expr_sim_inv cenv cx env es /\ FLOOKUP env.fn_sigs id = SOME sig /\
    (do r <- eval_expr cx (Call ann (IntCall id) args drv);
        read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env sig.ret_ty v
Proof
  rpt strip_tac >>
  `well_formed_type env.type_defs sig.ret_ty` by
    (drule_all frame_signature_return_well_formed >> simp[]) >>
  `well_typed_expr env (Call sig.ret_ty (IntCall id) args drv)` by
    (Cases_on `id` >>
     gvs[expr_body_pre_def, well_typed_expr_def, type_widens_to_def] >>
     metis_tac[]) >>
  `(do r <- eval_expr cx (Call sig.ret_ty (IntCall id) args drv);
       read_result cx r od) es = (INL v, es')` by
    metis_tac[internal_call_annotation_eval] >>
  drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
  disch_then (qspec_then `env` mp_tac) >>
  gvs[expr_body_pre_def, expr_sim_inv_def, int_calls_expr_def, expr_type_def]
QED

Theorem memory_rhs_read_post_typed:
  !ce cx env e es v es'.
    expr_body_pre ce cx env e es /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
    value_runtime_typed env (post_value_type ce e) v
Proof
  rpt strip_tac >>
  Cases_on `post_value_type ce e = expr_type e`
  >- metis_tac[memory_rhs_read_annotation_typed] >>
  `?ty fid args drv. e = Call ty (IntCall fid) args drv` by
    metis_tac[post_value_type_not_int_call] >> gvs[] >>
  `expr_sim_inv ce cx env es /\
   well_typed_expr env (Call ty (IntCall fid) args drv)` by
    gvs[expr_body_pre_def] >>
  `?sig. FLOOKUP env.fn_sigs fid = SOME sig` by
    (Cases_on `fid` >> gvs[well_typed_expr_def]) >>
  `value_runtime_typed env sig.ret_ty v` by
    (drule_all internal_call_read_signature_typed >> simp[]) >>
  `ce.ce_func_return_type (nsid_to_string fid) = sig.ret_ty` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  gvs[post_value_type_def, lowered_value_type_def, expr_type_def] >>
  Cases_on `is_word_type ty \/ is_bytestring_type ty` >> gvs[]
QED
