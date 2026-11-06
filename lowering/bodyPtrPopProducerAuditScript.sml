Theory bodyPtrPopProducerAudit
Ancestors
  exprLowering emitHelper compileEnv venomInst list context

(* Div/mod are the other arithmetic producers of two ISZEROs followed by
   ASSERT. The very next instruction is inside their template, so no later
   monadic continuation can insert the Pop decrement at this position. *)
Theorem pop_unsigned_div_opcodes:
  ~is_signed_type ty /\ compile_safe_div x y ty sa = (out,sb) ==>
  MAP (\i. i.inst_opcode)
    (DROP (LENGTH sa.cs_current_insts) sb.cs_current_insts) =
    [ISZERO; ISZERO; ASSERT; Div]
Proof
  strip_tac >>
  gvs[compile_safe_div_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def, mk_inst_def, rich_listTheory.DROP_APPEND1]
QED

Theorem pop_mod_opcodes:
  compile_safe_mod x y ty sa = (out,sb) ==>
  MAP (\i. i.inst_opcode)
    (DROP (LENGTH sa.cs_current_insts) sb.cs_current_insts) =
    [ISZERO; ISZERO; ASSERT; if is_signed_type ty then SMOD else Mod]
Proof
  Cases_on `is_signed_type ty` >>
  simp[compile_safe_mod_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def, mk_inst_def, rich_listTheory.DROP_APPEND1] >> strip_tac >> gvs[rich_listTheory.DROP_APPEND1]
QED

(* Producer audit (compiler-shape evidence, NOT a language-exclusion theorem).
   Store-adjacent templates:
   - compile_ptr_store / compile_store_at_loc: one store; the preceding code
     belongs to the caller and cannot be ignored.
   - compile_dynarray_pop: SUB immediately before the header store; root Pop
     gets a literal header from compile_get_target_ptr's TopLevelNameTarget.
   - compile_dynarray_append: element store follows address ADD (or copy),
     header store follows ADD, not SUB (exprLowering 1099-1134).
   - compile_word_copy_loop: load/address then store, followed by loop control
     (context); dynamic array copies have ADD before element store and an
     exit-block-start header store (context 930-981).
   - compile_nonreentrant_enter/exit: literal slot and literal stored value;
     enter has a single ISZERO then ASSERT (context 388-420).
   - Assign / AugAssign can join an UnsafeSub directly to a store. Therefore
     a SUB/STORE pair alone is NOT an invariant. Checked Sub instead emits
     range/overflow checks after SUB (exprLowering 318-337).
   - Calls have INVOKE in the caller. The same audit must apply to callee
     bodies; generic memory/precompile calls do not emit storage opcodes.

   The useful candidate invariant is a forbidden five-instruction window:
     SLOAD/TLOAD [Var h] -> a; ISZERO a -> b; ISZERO b -> c;
     ASSERT c; SUB [a; Lit 1] -> d.
   Retain identities and outputs, not just this opcode string. Source Pop is
   the intended owner of this prefix; supported root Pop has a literal h.
   Div/mod also have the double-negation assertion, but consume it internally
   with Div/SDIV/Mod/SMOD, before any continuation. Negation's SUB has left
   operand Lit 0 and predecessor SGT/ASSERT; PrevHash's SUB follows NUMBER;
   floor's SUB follows SLT; byte extraction has left Lit 32. String conversion,
   create-size and range-loop SUB sites likewise need their fixed local
   neighbors included in a formal template proof.

   Cross-bind cases still require a language induction, not inspection alone:
   a suffix of one operand can meet the ASSERT of addmod/mulmod (which then
   must emit ADDMOD/MULMOD), or a copy/conversion guard; returned operands and
   partial windows must be tracked. Bare source Assert uses JNZ/new blocks,
   not ASSERT. ABI clamps use SHR/SHL or SIGNEXTEND/EQ before their ASSERT;
   module entry checks and nonreentrancy have one ISZERO, not two.

   Transport domain: bodySim.body_inv_def requires a raw lower_vyper_*_unit.
   compileVyper.lower_vyper_*_unit calls vyperCompiler.run_*_lowering, then
   extract_context_with_internals: reverse finalized blocks, append current
   block, split at internal labels, package unchanged basic blocks. No IR
   optimization is run on this path. checked_unit_pipeline is separate.
   This supports a block-local window invariant; it is not permission to infer
   source occurrence from fn_has_code. A universal proof must additionally
   establish the invariant from initial_compile_state through all wrappers,
   supported expression/statement lowering, and internal function bodies. *)
