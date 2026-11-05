(* Endpoint integration audit: no claim about existence of an S1 entry. *)
Theory bodyPtrBopInEndpointAudit
Ancestors bodyPtrBopInEntryExclusion bodyPtrBopInEndpoint bodyPtrBopInSuffix
  loweringPosts exprLoweringProps

Theorem expr_post_endpoint_allocation_facts:
  expr_post ctx func cenv cx e es sa sb s0 es' v op t ==>
  alloca_inv t /\ t.vs_alloca_next < dimword (:256) /\
  (!inst n base sz.
     MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_operands = [Lit n] /\
     FLOOKUP t.vs_allocas inst.inst_id = SOME (base, sz) ==>
     sz = w2n n)
Proof
  simp_tac bool_ss [expr_post_def, stmt_state_rel_def] >> strip_tac >>
  drule alloca_room_next_lt >> strip_tac >>
  asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC
QED

(* Bounded symbolic applicability audit (not a no-entry theorem).
   string_membership_semantic_path supplies expr_post at its final t, so
   expr_post_endpoint_allocation_facts obtains the final allocation invariant,
   frontier bound, and sizes for recorded instructions without any invariant
   propagation through the unrestricted prefix.

   Remaining obligations before endpoint_literal_pair_eq can apply:
   1. Symbolic lower_value shape: for arbitrary cenv, ty and sa, identify op,
      sb.cs_current_bb = sa.cs_current_bb, unchanged finished blocks, and
      sb.cs_current_insts = sa.cs_current_insts ++ the nine-instruction segment
      with the fresh names/IDs based on sa. probe_exact_instructions only
      checks one concrete cenv, BoolT, and zero counters/empty prefix; it does
      not provide this symbolic equation or the lower_value wrapper equation.
   2. Code placement: fn_has_code yields an isPREFIX witness at the final
      block. After obligation 1, express its instructions as pre++seg++post.
      Establish non-PHI/nonterminator and non-INVOKE facts for seg, then apply
      marked_path_segment_suffix with j = 9. Arbitrary earlier reentries are
      allowed by that theorem, not excluded by assumption.
   3. Local execution: unfold the nine-step NRC only, select each instruction
      using get_instruction, use nonterminating_edge_instruction, and erase
      fuel using step_inst_non_invoke. Reconcile the successive index updates
      with run_inst_seq via instruction-index independence. This supplies the
      two three-instruction runs and three single steps of the endpoint lemma.
   4. Allocation sizes: show both literal ALLOCAs are in fn_insts func (from
      the block lookup/code placement), then specialize the recorded-size
      clause above to 64w. Final alloca_inv and frontier bound already match.
   5. Names and result: establish a<>b and ALL_DISTINCT [x;px;y;py;z] from
      symbolic fresh names; identify op = Var z and use expr_val_rel for BoolV T
      to obtain lookup_var z t = SOME 1w, contradicting the endpoint's zero.

   None of obligations 1--5 is silently assumed as a theorem here. Completing
   them would only exclude this particular string-membership S1 entry. It
   would neither exhibit a genuine bad pointer frame nor prove the general
   frozen target for arbitrary operands, In and NotIn. A strategy review is
   needed before adding symbolic compiler or no-entry infrastructure. *)
