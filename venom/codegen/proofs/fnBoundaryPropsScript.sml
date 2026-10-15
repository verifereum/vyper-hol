(* Function-boundary facts, NOT a proof or alias of gen_fn_simulation.
 * TOP-LEVEL: entry re-framing/length; closure mask; return spill frame and
 * merge interface; GAS freedom. Proofs use definitions and existing merge
 * semantics only. No admitted simulator is used. *)
Theory fnBoundaryProps
Ancestors
  venomToAsmProps codegenRel contextCodegenRel contextCodegenRelProps
  venomExecSemantics venomState asmSem list rich_list arithmetic

(* Verifereum's overloaded [cp] is not a context-plan variable. *)
val _ = Parse.hide "cp";

(* An opaque return address and any caller suffix can replace the old frame. *)
Theorem fn_entry_state_rel_reframe:
  fn_entry_state_rel cp fn vs as ra rest ==>
  fn_entry_state_rel cp fn vs
    (as with as_stack :=
      (if fn_has_retpc fn then [ra'] else []) ++ REVERSE vs.vs_params ++ rest')
    ra' rest'
Proof
  simp[fn_entry_state_rel_def, shared_state_rel_def, venom_asm_terminal_rel_def]
QED

Theorem fn_entry_state_rel_stack_length:
  fn_entry_state_rel cp fn vs as ra rest ==>
  LENGTH as.as_stack =
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) + LENGTH rest
Proof
  rw[fn_entry_state_rel_def] >> Cases_on `fn_has_retpc fn` >> gvs[]
QED

(* The closure is a submask of the ambient spill mask, not the whole mask. *)
Theorem closure_spill_byte_in_context:
  closure_spill_byte ctx cp name b ==> context_spill_byte cp b
Proof
  rw[closure_spill_byte_def] >> drule_all context_spill_byte_of_region >> simp[]
QED

Theorem fn_return_state_rel_spill_frame:
  fn_return_state_rel ctx cp fn vs' as as' /\
  context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
  read_byte b as'.as_memory = read_byte b as.as_memory
Proof
  simp[fn_return_state_rel_def]
QED

(* Compose the explicit return contract with the actual source merge.
   Caller environment is retained; effects, requests and leftover outcomes
   come from the callee. Does not assert any execution produced the relation. *)
Theorem fn_return_state_rel_merge:
  shared_state_rel caller as /\
  fn_return_state_rel ctx cp fn callee as as' ==>
  shared_state_rel (merge_callee_state caller callee) as'
Proof
  simp[shared_state_rel_def, fn_return_state_rel_def,
       merge_callee_state_def, venom_asm_terminal_rel_def]
QED

(* No GAS premise is smuggled into any of the new function relations. *)
Theorem fn_boundary_gas_readings_free:
  (shared_state_rel vs (as with as_gas_readings := readings) <=>
   shared_state_rel vs as) /\
  (fn_entry_state_rel cp fn vs (as with as_gas_readings := readings) ra rest <=>
   fn_entry_state_rel cp fn vs as ra rest) /\
  (fn_return_state_rel ctx cp fn vs'
     (as with as_gas_readings := before_readings)
     (as' with as_gas_readings := after_readings) <=>
   fn_return_state_rel ctx cp fn vs' as as')
Proof
  simp[shared_state_rel_def, fn_entry_state_rel_def, fn_return_state_rel_def,
       venom_asm_terminal_rel_def]
QED
