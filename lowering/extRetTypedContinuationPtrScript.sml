Theory extRetTypedContinuationPtr
Ancestors
  vyperTypeSystem exprOpenPrimitives exprLowering compileEnv vyperContext

Theorem return_some_typing_inputs:
  IS_SOME (type_stmt env ret_ty (Return (SOME e))) ==>
  well_typed_expr env e /\
  type_widens_to env.type_defs (expr_type e) ret_ty /\ ret_ty <> NoneT
Proof
  simp[type_stmt_def] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem typed_binop_dispatch_open:
  well_typed_binop ty op t1 t2 /\
  compile_binop op x y ty blit elit sa = (v,sb) ==>
  ~block_is_terminated sb
Proof
  strip_tac >> irule compile_binop_open >>
  `op <> ExpMod` by (strip_tac >> gvs[well_typed_binop_def]) >>
  metis_tac[]
QED

(* Successful source dispatch does not exclude the compiler's Code fallback.
   This is dispatch evidence only, not a counterexample to the frame. *)
Theorem typed_code_dispatch_source_success:
  well_typed_builtin_app (BaseT (BytesT (Dynamic 24576))) (Acc Code)
    [BaseT AddressT] /\
  ?v. evaluate_builtin cx acc (BaseT (BytesT (Dynamic 24576))) (Acc Code)
        [BaseT AddressT] [BytesV bs] = INL v
Proof
  simp[well_typed_builtin_app_def, account_item_type_def,
       evaluate_builtin_def, evaluate_account_op_def]
QED

(* C1.34.6.8.7 continuation-interface diagnostic (not a theorem).

   Candidate at the exact word-consumer use site:
     expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
     call_evaluation_safe cx (int_calls_expr e) /\
     eval_expr cx e es = (INL tv,es1) /\
     lower_value compile_expr cenv aty e sa = (v,sb) /\
     ~block_is_terminated sa /\
     [the actual normal gas_path_ptr and its endpoint relations from
      external_return expression evidence]
       ==> ~block_is_terminated sb.
   aty and sa must remain arbitrary. This is an unresolved candidate: even
   typing + source success does NOT rule out every INVALID fallback.
   stmt_exprs_ok and both universal expression simulations are also available
   from frame_ret_ok_ptr_def; none implies supported_expr by definition.

   Exhaustive expression-constructor table, from compile_expr_body_def:
   Name: compile_expr_name_open already consumes exact typing and expr_sim_inv.
   TopLevelName: pass-through if ce_module_vars is bound, INVALID otherwise.
     Bare-global binding follows directly from expr_sim_inv. Non-bare names
     require an env-consistency/runtime-declaration lookup interface; the
     existing compile_expr_toplevel_open requires supported_storage_value and
     storage_vars_rel/transient_vars_rel, not supplied by frame_ret_ok_ptr.
   Literal: compile_literal_vv_open, no support assumption.
   FlagMember: pass-through, no compiler-state change (typing is unnecessary).
   IfExp: compile_ifexp_open, unconditional final new_block; no child IH.
   StructLit: compile_struct_literal_body_open uses exact typing/invariant
     plus acyclic_struct_metadata. The last premise is NOT a field of
     expr_sim_inv and must be justified separately from sfields consistency
     and well-formed source metadata, not silently borrowed from body_inv.
   Subscript: compile_subscript_open, no support or child IH.
   Attribute: compile_attribute_open, no support or child IH.
   Pop: compile_pop_body_open, no support or child IH.
   Builtin and TypeBuiltin: exhaustive dispatch groups below.
   Call: exhaustive call-target groups below.

   Builtin dispatch (compile_builtin_dispatch_body_def):
   Not: compile_dispatch_not_open, no support premise.
   Neg, Abs, AddMod, MulMod, PowMod256, Env, BlockHash, BlobHash,
     ECRecover, ECAdd, ECMul, Uint2Str, CalldataSlice:
     compile_dispatch_terminal_open; no child IH. The three named modular
     fast paths are covered by compile_*_names_open in exprOpenCases.
   Bop: typed_binop_dispatch_open above removes ExpMod only for compile_binop.
     Full typed dispatch still needs In/NotIn array membership openness;
     compile_dispatch_bop_open explicitly excludes membership using support.
     Bytestring Eq/NotEq ends with EQ/ISZERO and needs no IH.
   Acc: Balance/Codesize/Codehash/IsContract use compile_dispatch_acc_open;
     Address is pass-through lower_value of its head and needs an IH.
     Code emits INVALID unconditionally; typing permits it and source builtin
     dispatch succeeds (checked above). No type/source exclusion is valid.
     Slice special handling does not compile this Code expression itself.
   AsWeiValue: compile_dispatch_as_wei_value_open needs head lower_value open
     (integer scale-one fast path); decimal branch has unconditional lemma.
   MakeArray NONE: compile_make_tuple_open plus initial alloc buffer;
     needs acyclic metadata. SOME: compile_make_array_open additionally needs
     EVERY (\e. is_word_type elem \/ is_bytestring_type elem \/
                elem = expr_type e) args, which exact typing supplies via
     EVERY ($= elem) (MAP expr_type args). No child-evaluation IH needed.
   Keccak256, Sha256, CalldataLen, Len, Ceil, Floor, Concat, Slice, MethodId:
     missing support-free dispatch lemmas. Inspect each final helper rather
     than assume supported_builtin_form. MethodId literal branch can use
     compile_literal_vv_open; runtime branch needs helper openness. These
     branches have no unconditional INVALID in the dispatcher itself.

   TypeBuiltin dispatch (all eight constructors):
   Empty, MaxValue, MinValue, Epsilon: compile_type_dispatch_constant_open
     requires only initial openness.
   AbiEncode, AbiDecode: compile_type_dispatch_abi_open, no child IH.
   Convert: compile_type_dispatch_convert_open requires head lower_value open
     because its zero-capacity conversion returns the child state unchanged.
     Typing supplies a singleton argument and child typing, not child openness.
   Extract32: missing support-free dispatch lemma; final clamp can pass
     through, so prove extract32_load openness and propagate through clamp.

   Call targets (compile_call_def):
   IntCall: compile_intcall_open, no support/default restriction.
   ExtCall: compile_extcall_open needs args nonempty; typing length supplies it.
   Send: compile_send_open needs exact arity; typing supplies it.
   RawCallTarget, RawCallCalldataTarget: missing dispatch lemmas for final
     compile_raw_call_finish / SETFMP; typing excludes malformed-arity INVALID.
   CreateTarget: missing compile_create_call openness, including malformed
     layouts versus create_arg_types_ok.
   RawLog, RawRevert, SelfDestructTarget: INVALID unconditionally. Typing allows
     NoneT. RawRevert never source-succeeds; RawLog and SelfDestruct can return
     Value NoneV (evaluate_def). A word root excludes these by typing, but
     general recursion must not assume every child has non-None type.

   Minimal remaining interfaces before a direct induction is justified:
   (1) normal counted path + exact endpoint ==> exclude a terminal compiler
       fallback, WITHOUT the refuted untyped strict initial-bound premise;
       alternatively a typed strict-bound theorem with explicit fallback cases.
   (2) typed top-level lookup / metadata acyclicity from exact frame inputs.
   (3) support-free dispatch openness for the missing builtin/type/call groups
       listed above, with typed arity and aggregate-store conditions explicit.
   (4) child eval and invariant preservation ONLY for pass-through Address,
       AsWeiValue, Convert (and any pass-through uncovered by (3)). Existing
       eval_builtin_head_success/eval_type_builtin_head_success extract head
       success; preserving expr_sim_inv after evaluation is a separate task
       if a needed child is not the first evaluated expression.
   Suggested measure: expr_size e, with callback list_size bounds exactly as
   compile_expr_raw_def. Direct openness is preferable to initial bounds for
   unconditional final emit/new_block cases. Do not launch this induction
   until (1) resolves the reachable typed Code/NoneT fallbacks. This inventory
   is not proof that the candidate is true and not frozen-frame falsehood.
*)
