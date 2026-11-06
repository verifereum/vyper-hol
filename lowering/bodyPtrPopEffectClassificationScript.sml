Theory bodyPtrPopEffectClassification
Ancestors
  supportedExprs supportedExprForms vyperAST

(* Source support is much narrower than expr_body_pre. This is a support
   inversion, NOT an inversion of arbitrary compiled code containment. *)
Theorem pop_supported_target_shape:
  supported_expr tops (Pop ty bt) <=>
  ?id. bt = TopLevelNameTarget id /\ supported_storage_dynamic_array tops id
Proof
  Cases_on `bt` >>
  simp[supportedExprsTheory.supported_expr_def,
       supported_pure_expr_def, supported_effect_expr_def]
QED

Theorem pop_supported_dynamic_element:
  supported_storage_dynamic_array tops id ==>
  ?vis loc elem n slot.
    supported_variable_decl tops id =
      SOME (vis,loc,ArrayT elem (Dynamic n),SOME slot) /\
    vis = Private /\ (loc = Storage \/ loc = Transient) /\
    supported_full_word_type elem
Proof
  Cases_on `supported_variable_decl tops id` >>
  simp[supported_storage_dynamic_array_def] >>
  PairCases_on `x` >> Cases_on `x2` >> simp[] >>
  rename1 `ArrayT elem bd` >> Cases_on `bd` >> simp[] >>
  Cases_on `x0` >> simp[] >> Cases_on `x1` >> simp[] >>
  Cases_on `x3` >> simp[]
QED

(* C1.5.1 effect/interface inventory:
   body_base_target_ptr_ok supplies index body_expr_ptr_ok (see the unique
   pop_target_index_ptr_premise). At a source-success cut this gives index
   expr_sim_ptr once body_inv and intermediate expr_body_pre are established.
   expr_body_pre has typing, allocation and call-safety clauses; it does NOT
   contain supported_expr. body_inv has supported_program and actual unit
   lowering; stmt_state_rel additionally requires the executing function to
   be looked up in that unit. A source support exclusion below is therefore
   NOT a full-frame/code-containment exclusion for arbitrary compile states.

   Syntactically supported direct storage-changing expression branches:
   1. Pop: pop_supported_target_shape and pop_supported_dynamic_element
      restrict it to a top-level storage/transient array of full-word elems.
      compile_expr's Pop branch invokes compile_get_target_ptr, then
      compile_dynarray_pop: load len; ISZERO twice; ASSERT; SUB; store len;
      ADD/MUL/ADD for the element pointer. The only direct storage update is
      the enclosing header store. Existing nested_pop_suffix_shape gives the
      exact storage fragment; pop_region_taint_sstore_cut/tstore_cut handle
      an out-of-saved-region clean store, if layout proves key separation.
   2. Internal call: supported_effect_expr requires supported_function_decl
      Internal, a non-StructT result, and supported_pure_exprs arguments.
      compile_call obtains metadata from ce_func_info, stages arguments and
      emits INVOKE. There is no direct SSTORE in compile_call; storage effects
      arise inside the callee from Assign/AugAssign/Append/Pop or calls.
      supported_function_body prohibits internal calls in Internal bodies,
      not all storage writes. body_inv ties IDs/metadata to tops. Code lookup
      and gas-admissible source call safety must be preserved, not replaced
      by an arbitrary callee. Typed write compatibility still unresolved.
   3. ExtCall/Send: supported_external_call_contract exposes the pure operand
      and ABI restrictions; supported_call_default_rejected excludes a
      default operand. compile_call emits CALL/STATICCALL. Successful adopting
      CALL resets storage/transient taint (pop_adopting_call_storage_taint),
      but raw saved header agreement must follow source/target call adoption.
   4. supported_effect_expr otherwise only closes under Subscript/Attribute;
      there are no further direct expression effect constructors. Operands
      of general pure builtins must themselves be pure in this whitelist.
      NoneT Send cannot directly furnish an array index under typing; no
      additional exclusion theorem for wrapped sends is claimed here.

   Candidate disposition for C1.5.2:
   The S1 self.b[1][self.b.pop()[0][0]].pop() uses a Pop of an array whose
   elements are arrays, and a final Pop on a SubscriptTarget. Both violate
   the support characterization above. This excludes it as a supported
   source instance ONLY, not as an arbitrary fragment with fn_has_code.
   A supported effectful expression example is a word Subscript with a
   top-level word-array Pop as key; its Pop changes a top-level header but
   does not exhibit a previously captured dynamic-array child becoming dead.
   Thus there is currently NO validated supported source example realizing
   the requested lifetime transition. A compiled local layout test can still
   check nested_pop_suffix_shape against a disjoint saved child, but must
   explicitly retain this source-support/full-context gap.

   Finite missing operational rules: compiled-code containment inversion for
   unsupported frozen-target shapes OR saved-child raw/taint compatibility
   for actual typed stores and INVOKE; source/target adopting-call raw slot
   correspondence; memory saved-value/coverage transport. This inventory
   establishes no universal observer preservation and no target falsehood. *)
