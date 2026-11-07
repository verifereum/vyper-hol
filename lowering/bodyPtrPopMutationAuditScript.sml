Theory bodyPtrPopMutationAudit
Ancestors vyperPlaceResultTyping vyperState

(* Source mutation classification for a retained local.  This is a source
   trace, not a coupling of that trace to the compiler's concrete stores. *)
Theorem pop_index_local_mutation_trace:
  eval_expr cx e st = (res,st') /\
  lookup_scopes id st.scopes = SOME entry ==>
  ?events entry'.
    lookup_scopes id st'.scopes = SOME entry' /\
    entry_pop_trace entry events entry'
Proof
  strip_tac >>
  `?events. scope_pop_trace st.scopes events st'.scopes` by
    (mp_tac (cj 5 eval_mutual_scope_pop_effect) >>
     simp[scope_pop_effect_def] >> metis_tac[]) >>
  drule_all scope_pop_trace_lookup >> metis_tac[]
QED

(* A stale source write is successful, but does not update even the historical
   snapshot that a subsequent read can select. This is not a memory frame. *)
Theorem pop_stale_replace_source_step:
  evaluate_subscripts entry.type entry.value path = INR err ==>
  replace_memory_entry entry path v = INL entry
Proof
  simp[replace_memory_entry_def]
QED

(* Conversely a live replacement removes all fallback records. If the new
   live value cannot answer a query, old history cannot rescue that query. *)
Theorem pop_live_replace_invalidated_read:
  evaluate_subscripts entry.type entry.value path = INL old /\
  assign_subscripts entry.type entry.value path (Replace v) = INL updated /\
  evaluate_subscripts entry.type updated query = INR err ==>
  replace_memory_entry entry path v =
    INL (entry with <|value := updated; popped := []|>) /\
  read_memory_path (entry with <|value := updated; popped := []|>) query = INR err
Proof
  simp[replace_memory_entry_def, read_memory_path_def, read_popped_def]
QED

(* Mutation matrix (caller-local memory, NOT storage/transient observers):

   Family                 Source boundary             Concrete obligation
   ----------------------------------------------------------------------
   Repeated live Pop      entry_pop_step / trace        Selected header store;
   Historical-owner Pop   replace_popped + record_pop   E0223 handles removed
                                                       child, not all reads.
   Assign / AugAssign     replace_memory_entry          Stale source no-op is
   Tuple assignment                                    NOT a memory no-op.
   Live replacement       clears history               Failed new live read
                                                       loses fallback, above.
   Append / regrowth      append_place uses write_place Same stale/live split;
                                                       payload/header writes.
   Internal call body     push_function [callee env],   Must frame caller's
                          finally pop_function prev    original allocation.
   Call args              eval_expr_results, then      Nested Pops may update
                          read_results                 caller before saving.
   Call defaults          isolated [FEMPTY], finally   Must frame caller's
                          restores prev                original allocation.
   External/raw calls     scope-preserving call helpers Storage changes are not
   Send/Create/Log                                      caller-local mutation.
   Pure wrappers          bind of recursive evals      Scratch allocations,
                                                       copying, taint framing.

   The source column is more than a syntax guess: the existing theorem
   eval_mutual_scope_pop_effect, combined with scope_pop_trace_lookup in
   pop_index_local_mutation_trace, gives an entry_pop_trace for EVERY eval_expr
   and every initially resolved caller local, without a purity hypothesis.
   Thus caller-visible value/history changes during an index evaluation are
   Pop-only. Append/Assign/AugAssign are statements, not expression branches;
   when reached in callees their scopes are isolated and restored. This does
   not exclude invisible source no-op writes, and is not a concrete frame.
   The exact source stale/live equations above explain why a universal
   invariant over arbitrary statement execution would be wrong-shaped.

   Compiler alignment inspected at exprLowering.compile_dynarray_pop_def:
   Pop mutates the selected header, not the removed payload. E0223 supplies
   that actual counted clean-store edge. compile_stage_intcall_args_def
   copies memory-passed arguments into freshly allocated buffers and unwraps
   stack-passed arguments. To turn the source callee isolation into a memory
   frame requires freshness/non-alias of those allocations AND a semantic
   callee frame. The source scope trace alone cannot establish either.
   Compiler-shape closures in earlier leaf theories are not semantic frames.

   Exact auxiliary residual, NOT an authorized global definition/theorem:
   an induction on actual paired eval/compile derivations, with a retained
   caller-local identity, initial live typed path, original root allocation
   and path offset, coverage, robust initial representation, and saved operand.
   The relation must quantify over successful current read_memory_path at
   retained paths, not over all raw records. Its Pop step must handle the
   shortened owner, overlapping ancestors and older-deeper successful fallback
   with compatible original-layout addresses (E0223 residual). Its call step
   must frame this original allocation through staging, default evaluation,
   callee execution and return copying; storage effects need their own branch.

   Premise audit against the frozen consumer: pop_index_counted_handoff
   already derives the counted index outcome from body_base_target_ptr_ok,
   body_inv and expr_body_pre plus the ordinary entry/run premises. Initial
   live representation is obtainable from ghost_inv at capture, and initial
   layout/coverage from the target's live traversal. The source entry trace
   above follows from actual eval_expr independently of support or typing.
   But neither the supplied endpoint judgment nor this source trace provides
   coupled per-mutation layout compatibility or callee memory framing. Event
   validity/typed intermediate-owner premises must also be established, not
   inferred from an untyped entry_pop_trace. These are remaining proof
   obligations, not extra hypotheses permitted on the frozen Pop theorem.

   Disposition: the source mutation domain can be narrowed to caller-local
   Pop traces, but concrete closure/initialization of the proposed all-read
   relation is NOT validated. No global simulation is commissioned here.
   No counterexample satisfying the frozen theorem's full premises is known.
*)
