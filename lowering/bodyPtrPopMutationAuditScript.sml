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

(* Coupled-induction validation (E0225 follow-up; UNPROVED CANDIDATE ONLY).

   Concrete active-owner sequent, with all variables universally quantified:

   !cx tops ctx func cenv env d PG ty e sa sb op es ee s0 s G0 tn0 G tn
    marks v id initial_entry final_entry root root_addr sz aid allocation
    saved p off tv before Q.
     body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
     lower_value compile_expr cenv ty e sa = (op,sb) /\
     fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
     local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
     stmt_state_rel ctx func cenv cx es s0 /\
     ghost_inv d cenv cx es G0 tn0 s0 /\
     lookup_scopes id es.scopes = SOME initial_entry /\
     FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) sz) /\
     lookup_var root s0 = SOME root_addr /\
     FLOOKUP s0.vs_allocas aid = SOME allocation /\
     mem_path_offset initial_entry.type p = SOME (off,tv) /\
     evaluate_subscripts initial_entry.type initial_entry.value p = INL before /\
     lookup_var saved s0 = SOME (root_addr + n2w off) /\ not_fresh_at sa saved /\
     ptr_covers G0 tn0 root s0 (type_memory_size initial_entry.type) /\
     (!q. MEM q Q ==> ?k qtv w.
        mem_path_offset initial_entry.type q = SOME (k,qtv) /\
        evaluate_subscripts initial_entry.type initial_entry.value q = INL w /\
        (!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
           val_in_memory qtv w (w2n root_addr + k) mem)) /\
     gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
       (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
       marks (INL v) ee G tn (OK s) /\
     expr_post ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) v op s /\
     ghost_inv d cenv cx (ee with gas_obs := []) G tn s /\
     ghost_kept cenv es sa G0 tn0 s0 G tn /\
     lookup_scopes id ee.scopes = SOME final_entry ==>
     lookup_var saved s = SOME (root_addr + n2w off) /\
     FLOOKUP s.vs_allocas aid = SOME allocation /\
     ptr_covers G tn root s (type_memory_size initial_entry.type) /\
     (!q k qtv w. MEM q Q /\
        mem_path_offset initial_entry.type q = SOME (k,qtv) /\
        read_memory_path final_entry q = INL w ==>
        !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory qtv w (w2n root_addr + k) mem)

   The allocation lookup alone intentionally does NOT assert
   allocation ownership or non-aliasing; those are missing preconditions to
   derive from the actual frame, not implicit facts of this candidate.
   The caller-return-buffer/pc freshness and gas_admissible clauses of the
   exact saved-index candidate must additionally be carried at specialization.
   Q must include p. A singleton Q=[p] matches the final consumer but is not
   enough to establish the representation of arbitrary selected Pop owners.
   Taking Q as all initially live typed paths would require a generic robust
   live-path projection at initialization; the consumer currently supplies
   the captured path's representation explicitly and the root from ghost_inv.

   Pop closure implication (schema, NOT a theorem): for EVERY initial root,
   retained path set Q, current entry, current memory and synchronized actual
   pop_place/compiled-header-store pair, the displayed final relation as a
   PRE-state relation must imply it for the updated entry and post-store
   memory. E0223 handles newest-child success when owner robustness and layout
   address are supplied. It does not derive owner representation from Q=[p],
   nor covers an overlapping ancestor or older deeper fallback. Those owner
   and query layout premises cannot silently be new hypotheses on the target.

   Protected-call implication (schema, NOT a theorem): for EVERY retained
   original allocation and actual compile_call/eval_expr IntCall segment,
   initialized retained-read relation + actual staging/default/callee/return
   subexecutions must imply the relation at return. Recursive callee instances
   use a protected caller mode whose needed premise is that its concrete
   writes are disjoint from the retained allocation; source scopes are saved
   and restored, but that does not discharge this premise. Actual allocation
   ownership, staging freshness and non-aliasing must be supplied by the
   compiler frame, not assumed from a FLOOKUP membership fact.

   FIRST UNAVAILABLE RECURSIVE PREMISE: a derivation aligning recursive source
   calls to compiler subsegments. evaluate_ind is available with the actual
   well-founded bound in vyperInterpreterScript.sml:1783-1849: expression and
   statement bounds over remcode cx, internal-call stack exclusion, and the
   finite eval_for list bound. Thus syntax size is not the justified measure.
   But gas_marked_exec_ptr_def is only a source endpoint observation equation
   AND a gas_path_ptr. Its definition has no intermediate source/compiler cut
   relation. gas_marked_exec_ptr_bind_normal composes already aligned prefix
   and suffix witnesses in the forward direction; it does not decompose an
   arbitrary given marked whole run at the next source recursive evaluation.
   gas_path_ptr_ind supplies target edges only. Therefore evaluate_ind's
   recursive source hypotheses cannot yet be instantiated with paired segment
   premises from the exact candidate's whole marked execution. This is a
   construction obligation for a compiler-indexed execution decomposition,
   not a theorem refuted by this inspection and not a reason to raise a tactic
   timeout. Stop here before a claimed Pop/call closure or taint transport.
*)
