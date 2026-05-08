(*
 * Lowering Memory Safety — Definitions
 *
 * Predicates connecting the Vyper→Venom lowering to memory safety.
 * These are the definitions needed by the memory safety theorem
 * statements in loweringMemSafetyProps.
 *
 * TOP-LEVEL:
 *   value_within_alloca_size — value's runtime structure fits ALLOCA size
 *   cenv_matches_fn          — compile_env ALLOCA sizes match function
 *   alloca_sizes_match       — runtime ALLOCA sizes match function
 *   alloca_outputs_match     — ALLOCA outputs hold runtime base addresses
 *   state_matches_fn         — ALLOCA sizes and outputs match function
 *   well_typed_lowering      — source well-typed (enables type soundness)
 *   bp_result_is             — base_ptr analysis result validity
 *   reachable_by_execution   — RTC of non-terminating, non-ext-call steps
 *)

Theory loweringMemSafetyDefs
Ancestors
  allocaRemapDefs pointerConfinedDefs basePtrDefs
  venomMemDefs venomExecSemantics venomWf passSharedDefs
  compileEnv context vyperValue vyperTyping

(* value_within_alloca_size cenv ty v: v's runtime structure fits
   within the memory layout sized by type_memory_bytes(cenv, ty).
   - DynArray: runtime length ≤ declared capacity
   - DynBytes/DynString: data length ≤ declared max
   - Fixed arrays, structs, base types: structurally exact *)
Definition value_within_alloca_size_def:
  value_within_alloca_size cenv (ArrayT elem_ty (Dynamic n))
    (ArrayV (DynArrayV vs)) =
    (LENGTH vs ≤ n ∧
     EVERY (λv. value_within_alloca_size cenv elem_ty v) vs) ∧
  value_within_alloca_size cenv (BaseT (BytesT (Dynamic n)))
    (BytesV bs) =
    (LENGTH bs ≤ n) ∧
  value_within_alloca_size cenv (BaseT (StringT n))
    (StringV s) =
    (LENGTH s ≤ n) ∧
  value_within_alloca_size cenv (ArrayT elem_ty (Fixed n))
    (ArrayV (TupleV vs)) =
    (LENGTH vs = n ∧
     EVERY (λv. value_within_alloca_size cenv elem_ty v) vs) ∧
  value_within_alloca_size cenv (StructT name)
    (StructV al) =
    (EVERY (λ(name, v). T) al) ∧
  value_within_alloca_size cenv (TupleT tys)
    (ArrayV (TupleV vs)) =
    (LENGTH vs = LENGTH tys ∧
     LIST_REL (value_within_alloca_size cenv) tys vs) ∧
  value_within_alloca_size _ _ _ = T
Termination
  WF_REL_TAC `measure (type_size o (λ(c,t,_). t))`
End

(* cenv_matches_fn cenv fn: cenv accurately reflects fn's types and
   variable layout. For each ALLOCA in fn with output v and operand
   Lit n, cenv maps v's declared type ty such that
   type_memory_bytes cenv ty = w2n n. *)
Definition cenv_matches_fn_def:
  cenv_matches_fn cenv fn ⇔
    ∀inst out n ty tenv tv.
      MEM inst (fn_insts fn) ∧
      inst.inst_opcode = ALLOCA ∧
      inst_output inst = SOME out ∧
      inst.inst_operands = [Lit n] ∧
      cenv.ce_var_type out = SOME ty ∧
      evaluate_type tenv ty = SOME tv
      ⇒ type_memory_bytes cenv ty = w2n n
End

(* Runtime alloca entries have the sizes declared by fn's ALLOCA instructions. *)
Definition alloca_sizes_match_def:
  alloca_sizes_match fn s ⇔
    ∀inst n.
      MEM inst (fn_insts fn) ∧
      inst.inst_opcode = ALLOCA ∧
      inst.inst_operands = [Lit n]
      ⇒ ∃off. FLOOKUP s.vs_allocas inst.inst_id = SOME (off, w2n n)
End

(* ALLOCA output variables hold the base address of their runtime entries. *)
Definition alloca_outputs_match_def:
  alloca_outputs_match fn s ⇔
    ∀inst n out off sz.
      MEM inst (fn_insts fn) ∧
      inst.inst_opcode = ALLOCA ∧
      inst.inst_operands = [Lit n] ∧
      inst_output inst = SOME out ∧
      FLOOKUP s.vs_allocas inst.inst_id = SOME (off, sz)
      ⇒ lookup_var out s = SOME (n2w off)
End

(* Runtime ALLOCA sizes and output values match fn's ALLOCA instructions. *)
Definition state_matches_fn_def:
  state_matches_fn fn s ⇔
    alloca_sizes_match fn s ∧ alloca_outputs_match fn s
End

(* well_typed_lowering cenv: the Vyper source from which cenv was
   derived is well-typed. Enables eval_preserves_swt to guarantee
   runtime values match declared types. Equivalent to
   context_well_typed on the Vyper evaluation context. *)
Definition well_typed_lowering_def:
  well_typed_lowering cenv ⇔
    well_formed_cenv cenv ∧
    (∀var ty. cenv.ce_var_type var = SOME ty ⇒
               ∃tenv tv. evaluate_type tenv ty = SOME tv ∧
                         well_formed_type_value tv)
End

(* bp_result_is fn bp: bp is a valid base_ptr analysis result for fn.
   Connects to bp_process_block or bp_analyze_function. *)
Definition bp_result_is_def:
  bp_result_is fn bp ⇔
    ∃bb c. MEM bb fn.fn_blocks ∧
           SOME bb.bb_label = fn_entry_label fn ∧
           bp_process_block FEMPTY bb.bb_instructions = (c, bp)
End

(* reachable_by_execution fn s s': s' is reachable from s by
   executing non-terminating, non-external-call instructions of fn.
   Defined via RTC of single step. *)
Definition reachable_by_execution_def:
  reachable_by_execution fn s s' ⇔
    RTC (λs1 s2. ∃inst bb.
      MEM bb fn.fn_blocks ∧ MEM inst bb.bb_instructions ∧
      step_inst_base inst s1 = OK s2 ∧
      ¬is_terminator inst.inst_opcode ∧
      ¬is_ext_call_op inst.inst_opcode) s s'
End
