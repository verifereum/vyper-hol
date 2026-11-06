(* Full-child boundary audit; no new predicate or producer invariant. *)
Theory bodyPtrStructLitChildInterface
Ancestors bodyPtrDefs loweringPosts bodyPtrStructLitRepresentationProbe
  bodyPtrStructLitFrameLinkage

Theorem ptr_val_ok_memory_representation:
  !cx t v op G tn s tv w.
    ptr_val_ok cx t v op G tn s /\ ~is_word_type t /\
    evaluate_type (get_tenv cx) t = SOME tv /\ eval_operand op s = SOME w ==>
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem
Proof
  simp[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]
QED

Theorem ptr_buf_ok_lowered_coverage:
  !cenv e op G s w.
    ptr_buf_ok cenv e op G s /\ eval_operand op s = SOME w /\
    type_memory_bytes cenv (lowered_value_type cenv e) <> 0 ==>
    ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
      b <= w2n w /\
      w2n w + type_memory_bytes cenv (lowered_value_type cenv e) <= b+sz
Proof
  simp[ptr_buf_ok_def]
QED

(* SUPPLIED CONTRACT (all variables universally quantified):
   body_expr_ptr_ok cx e plus body_inv tops ctx cenv cx and
   expr_body_pre cenv cx env e es gives expr_sim_ptr and expr_vv_sim_ptr.
   expr_sim_ptr_def additionally requires lower_value, fn_has_code,
   fn_inst_ids_distinct, local_ptrs_reserved, no DALLOCA/no constructor,
   old return variables, gas_admissible, stmt_state_rel, ghost_inv, and the
   cursor/halted conditions at s0.  It yields gas_outcome_ptr whose normal
   post is (exists v. res=INL v /\ expr_post ... e ... v op s /\ cursor /\
   ghost_inv ... /\ ptr_val_ok cx (expr_type e) v op G tn s /\
   (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G s) /\ ghost_kept ...).

   expr_post (loweringPosts lines251-265) contains expr_val_rel and
   expr_val_at at expr_type e, NOT lowered_value_type cenv e. Neither
   predicate mentions tn. expr_val_at gives val_wf at the annotation and
   placement; stmt_state_rel and locals_kept describe source state/locals.
   They are not a cleanliness theorem at the declared layout.

   REQUIRED CONTRACT at compile_copy_memory_robust_counted
   (bodyPtrStructLitCopyPath lines75-86), for every successful child value
   v/op/s/G/tn and evaluated declared tv at source address w:
     val_wf tv v /\ val_footprint tv v <= n /\
     (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
            val_in_memory tv v (w2n w) mem)
   plus clean source operand and ptr_covers G tn src s n, with n the
   declared type's copy size, and independent destination resources.
   Coverage follows from ptr_buf_ok when declared lowered type matches n;
   operand cleanliness follows ptr_val_ok. Robust representation at tv
   and its val_wf are not supplied at this boundary when layouts differ.

   Exact residual implication: under ALL normal child post conjuncts,
   legal-frame antecedents above, actual callable linkage and declared to
   annotation widening, derive the REQUIRED CONTRACT for evaluated declared
   tv. No such transfer is proved here. LayoutProbe's correctly oriented
   tuple widening and RepresentationProbe's post_representation_gap show
   ptr_val_ok + ptr_buf_ok + sufficient capacity alone do NOT imply it.
   That local witness does NOT certify expr_post, ghost_inv, ghost_kept,
   a legal frame, reachability, or the universal body_expr_ptr_ok premise.

   Universality cannot be specialized to a taint-perturbed final memory:
   its quantifiers are over initial legal frames, not arbitrary post-states.
   Such a use needs preservation of every antecedent and a relational
   execution theorem identifying the resulting value/address/memory.
   No such cross-run theorem is available in these diagnostics. This audit
   neither proves the residual full-post implication nor refutes it, and
   does not certify or refute structlit_expr_ptr_ok. *)
