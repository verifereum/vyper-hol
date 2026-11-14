(* Checked audit of the inherited external-return admission.
   This is NOT an owned external-call producer theorem. *)
Theory tupleAssignImmutableDeployAdmissionRoute
Ancestors
  exprSimExtCallCase gasSummary gasOutcome loweringPosts compileEnv
  venomState finite_map words

(* Unlike IntCall, ExtCall never changes the post's physical type. Thus the
   conditional vv_own clause in vv_post is vacuous, even if ann is a tuple.
   ret_type is the declared ABI return type; ann is the expression annotation. *)
Theorem external_post_type[local]:
  post_value_type ce (Call ann (ExtCall stat skip sig opts) args dflt) = ann
Proof
  simp[post_value_type_def, vyperASTTheory.expr_type_def]
QED

(* Inventory of the located-memory alternative, at the very state in the
   admitted post. The middle disjunct is NOT expression-owned allocation. *)
Theorem external_post_memory_alternatives[local]:
  vv_post ctx func ce cx
    (Call ann (ExtCall stat skip sig opts) args dflt)
    es sa sb s0 ee raw (LocatedValue ann (mk_ptr op LocMemory)) t /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ann = SOME tv ==>
  ?w. eval_operand op t = SOME w /\ val_wf tv v /\
    ((?aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
        sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
        b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
        (!n lb len. local_region ce ee.scopes t n lb len ==>
                    b + sz <= lb \/ lb + len <= b)) \/
     (?n b sz. local_region ce ee.scopes t n b sz /\
        b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
        local_val_at ce cx n (w2n w - b) tv v /\
        local_place_at ce cx n (w2n w - b) tv raw) \/
     val_footprint tv v = 0)
Proof
  simp[vv_post_def, external_post_type, vv_at_def, contextTheory.mk_ptr_def] >>
  metis_tac[]
QED

(* This is the precise same-witness elimination/strengthening interface.
   The missing frame must apply to the execution in the admission, NOT
   just construct some path to an independently obtained endpoint.
   Kept private: it is a diagnostic logical interface, not a new framework. *)
Theorem admission_same_witness_frame[local]:
  gas_summary_at F (ctx,func) marks source (es,s0) Q R /\
  (!res raw t.
     gas_marked_exec F (ctx,func) source (es,s0) marks res raw (OK t) /\
     Q res (raw with gas_obs := []) t ==>
     Owned res (raw with gas_obs := []) t) ==>
  gas_summary_at F (ctx,func) marks source (es,s0)
    (\res ee t. Q res ee t /\ Owned res ee t) R
Proof
  simp[gas_summary_at_def] >> metis_tac[]
QED

(* Missing semantic boundary (not asserted as a theorem here):

   Under the compiler equation and entry premises of extcall_return_values,
   for EVERY successful gas_marked_exec of its source return handler whose
   endpoint satisfies its Q, establish at THAT endpoint t:

     ?w aid b sz. eval_operand result_op t = SOME w /\
       FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
       sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
       b <= w2n w /\ w2n w + type_memory_bytes ce ret_type <= b+sz /\
       (!name lb len. local_region ce ee.scopes t name lb len ==>
                     b+sz <= lb \/ lb+len <= b).

   A zero-physical-size alternative is allowed. For positive tuples the
   footprint above is the declared physical envelope, not merely the live
   bytes/val_footprint supplied by vv_at. Needed execution facts:
   (1) the result ALLOCA at sr.cs_next_id is traversed on successful paths;
   (2) its output operand and allocation row survive the return suffix;
   (3) the row is disjoint from final local regions. Both default and decode
   branches must be covered, including the default copy/re-layout suffix.

   Caller discharge sites:
   * compiler equation, fn_has_code, distinct IDs: extcall_return_values;
   * entry stmt_state_rel, PC, safe operands, reserved locals, input buffer:
     extcall_returned_def;
   * literal allocation size/room: stmt_state_rel's actual ALLOCA clause;
   * default value typing/layout: extcall_default_ready, not ABI bytes;
   * source result and typed target bytes: admitted Q's vv_post, at t;
   * age: sa <= sr and the result allocation is before sb.

   Existing tuple_immutable_external_result_allocated proves (1)-(3) for a
   NEW allocation-prefix path, not this arbitrary admitted execution.
   tuple_immutable_external_allocated_guard extends that constructed path.
   tuple_immutable_external_decode_owned_path retains its allocation row
   but constructs another decode path and requires interval budget.
   rest_word_marked_allocation_posts preserves history/frontier only.
   alloca_history_def DOES certify rows for ALLOCAs before the current
   cursor in the current block (and block-local allocation order), but not
   arbitrary earlier blocks or the equality of an output variable to that
   row's base. The default branch exits in a separate empty exit block;
   recursive decode can also leave the allocation block. In addition,
   extcall_returned does not include alloca_history as an entry premise.
   stmt_state_rel certifies sizes of registered actual ALLOCAs, not their
   existence nor their output variable's value. These facts do not by
   themselves provide the missing result certificate.
   abi_decode_footprint_frame concerns bytes, not allocation origin.

   No inspected exported frame eliminates the local-region alternative or
   proves (1)-(3) for the admission's arbitrary successful trace. A new
   control-flow/trace frame (covering output definitions and no-INVOKE
   suffixes) would be required for this route; a PC equality alone is not
   such a proof. This audit therefore does not remove decoder migration,
   discharge the producer join, or release C0. *)
