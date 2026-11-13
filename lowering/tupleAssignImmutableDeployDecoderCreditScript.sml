(* Diagnostic only: instruction-interval credit is not actual ALLOCA credit.
   These closed probes do not assert failure of the source theorem. *)
Theory tupleAssignImmutableDeployDecoderCredit
Ancestors
  abiEncoder vyperCompiler compileEnv exprLoweringProps abiCallerAllocation
  abiDecoderTypedContract abiDecoderAllocation venomMemDefs venomInst venomState
  finite_map pred_set words arithmetic list

(* Even a static tuple with no scratch emits ordinary instruction IDs. *)
Theorem tuple_immutable_static_decoder_credit_probe[local]:
  let st = SND (compile_abi_decode_to_buf (Lit 64w) (Lit 0w) MLOAD
    (Lit 0w) (Lit 32w) (DecComplex F [(DecPrimWord NoClamp,32,32)])
    (initial_compile_state "entry")) in
  1 < st.cs_next_id /\
  FILTER (\i. i.inst_opcode = ALLOCA) st.cs_current_insts = []
Proof
  EVAL_TAC >>
  simp[wordsTheory.n2w_11, wordsTheory.dimword_def,
       initial_compile_state_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >> EVAL_TAC
QED

(* A clamped dynamic array has one real scratch allocation, not one per ID. *)
Theorem tuple_immutable_dynamic_decoder_credit_probe[local]:
  let st = SND (compile_abi_decode_to_buf (Lit 64w) (Lit 0w) MLOAD
    (Lit 0w) (Lit 0w) (DecDynArray (DecPrimWord (IntClamp 8 F)) 32 32 F 1)
    (initial_compile_state "entry")) in
  2 < st.cs_next_id /\
  LENGTH (FILTER (\i. i.inst_opcode = ALLOCA)
    (FLAT (MAP (\bb. bb.bb_instructions) st.cs_blocks) ++ st.cs_current_insts)) = 1 /\
  EVERY (\i. alloca_lit_size i = 32)
    (FILTER (\i. i.inst_opcode = ALLOCA)
    (FLAT (MAP (\bb. bb.bb_instructions) st.cs_blocks) ++ st.cs_current_insts))
Proof
  rewrite_tac [initial_compile_state_def] >>
  EVAL_TAC >>
  simp[wordsTheory.n2w_11, wordsTheory.dimword_def,
       initial_compile_state_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >> EVAL_TAC
QED

(* A resource-model example, not an execution/caller counterexample. Two
   ordinary unregistered IDs cost 64 in the interval interface but zero in
   a function with no ALLOCA. Even alloca_inv does not repair that gap. *)
Theorem tuple_immutable_interval_overcharge_probe[local]:
  !s f.
  let u = s with <| vs_allocas := FEMPTY; vs_alloca_next := dimword (:256) - 32 |> in
  pending_alloca_size (f with fn_blocks := []) u = 0 /\
  alloca_inv u /\
  u.vs_alloca_next + pending_alloca_size (f with fn_blocks := []) u < dimword (:256) /\
  ~(u.vs_alloca_next + 32 * CARD (abi_decoder_missing 1 3 u) < dimword (:256))
Proof
  rpt gen_tac >>
  `abi_decoder_ids 1 3 = {1;2}` by
    (rw[abi_decoder_ids_def, EXTENSION] >> decide_tac) >>
  simp[pending_alloca_size_def, fn_insts_def, fn_insts_blocks_def,
       alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       abi_decoder_missing_def, dimword_def]
QED

(* C0.14.27 bounded diagnostic (not a theorem about a complete caller).

   At the u of tuple_immutable_external_allocated_guard take start=endst
   of that theorem, and compile_abi_decode_to_buf ... start=((),final).
   The minimal allowed interval is first=start.cs_next_id+1,
   last=final.cs_next_id (abi_decoder_entry_floor_def). Widening it
   cannot improve the missing-ID charge. The output allocation at
   sr.cs_next_id and the input allocation live<sr.cs_next_id are outside
   this interval, by the guard's exported inequalities.

   extcall_returned gives stmt_state_rel at THIS u. Its alloca_room gives
     u.vs_alloca_next + pending_alloca_size func u +
       CARD {g | TC (fn_directly_calls ctx) func.fn_name g} *
       unit_alloca_frame ctx < dimword (:256).
   Applying abi_caller_allocation_budget_zero still requires
     u.vs_alloca_next + 32*CARD(abi_decoder_missing first last u)
       < dimword (:256),
   and
     !id off sz. id IN abi_decoder_ids first last /\
       FLOOKUP u.vs_allocas id = SOME(off,sz) ==> sz=32.
   The first is NOT the actual pending-ALLOCA sum. The static probe
   emits nonallocation IDs with no scratch; the dynamic probe has one
   32-byte site despite multiple emitted IDs. The abstract resource
   model above checks strict numeric nonimplication even with alloca_inv.
   It is not claimed reachable, source-valid, or a frozen-task counterexample.
   The dynamic probe uses the unbounded hi=0 convention to keep this
   computation small; it does not certify the bounded external decoder.

   Size provenance is a separate residual. stmt_state_rel constrains a
   registered ALLOCA's size when there is a matching instruction;
   alloca_history is the block-order/past-site predicate, NOT
   abi_alloca_history (allocation-origin provenance). The latter's
   abi_alloca_history_decoder_sizes additionally needs function/decoder
   interval membership, and cannot be applied merely by spelling
   alloca_history differently. Decoder-only ALLOCAs are compile_alloc_buffer
   32, but arbitrary registered IDs in the interval need exclusion or
   provenance before concluding sz=32. Neither actual fn_has_code nor
   ID distinctness creates numeric credit for nonallocation instructions.

   Task-private repair interface to plan, not implemented here:
   retain alloca_room/stmt_state_rel for the actual func, and track only
   actual scratch ALLOCA sites plus their literal byte sizes; discharge
   fresh-site execution with the pending-size bound and reentry with
   the matching site's size equation. Carry allocation preservation,
   scratch/write footprint and gas at the same execution endpoint.
   This needs an actual-site counterpart to the allocation step in
   abiScratchDecoderArraySetup (dynamic_prefix/setup_sequence), budget
   transport/effect composition in abiScratchEffect/abiDecoderEffect,
   recursive array/member/tuple consumers (abiScratchDecoderRecursive,
   abiScratchDecoderMemberCons and abiScratchDecoderTuple), and the
   source-valid dispatch abi_decoder_valid_decode. It is not a one-line
   conversion from alloca_room to the existing interval budget.
   Existing decode-owned paths remain correct conditional theorems with
   their explicit interval budget; leave them unchanged. A new actual-site
   path must join the retained u directly, not identify separate witnesses.
   No full recursive migration, source-validity/truncation join, default
   stores, whole external producer, or gate release is established here.
*)
