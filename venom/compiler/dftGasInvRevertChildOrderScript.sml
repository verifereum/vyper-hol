Theory dftGasInvRevertChildOrder
Ancestors
  dftDefs dftGasInvStackLineage dftGasInvJointConeProbe venomInst

(* REVERT is not an abort-kind instruction in the frozen cost definition.
   These checks refute the proposed zero-cost boundary, not the task theorem. *)
Theorem inv_revert_abort_kind_probe:
  dft_abort_kind REVERT = NoFail
Proof
  EVAL_TAC
QED

Theorem inv_revert_copy_cost_probe:
  dft_cost [] [] [] FEMPTY
    (mk_inst 1 REVERT [Lit 0w; Lit 8w] [])
    (mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 8w] []) = 2
Proof
  EVAL_TAC
QED

Definition inv_child_order_bi_def:
  inv_child_order_bi =
    [mk_inst 0 ADD [Lit 16w; Lit 16w] ["p"];
     mk_inst 1 ADD [Lit 4w; Lit 4w] ["n"];
     mk_inst 2 RETURNDATACOPY [Var "p"; Lit 0w; Var "n"] [];
     mk_inst 3 REVERT [Var "p"; Var "n"] []]
End

Definition inv_child_alias_bi_def:
  inv_child_alias_bi =
    [mk_inst 0 ADD [Lit 16w; Lit 16w] ["p"];
     mk_inst 1 ADD [Lit 4w; Lit 4w] ["n"];
     mk_inst 2 RETURNDATACOPY [Var "p"; Lit 0w; Var "n"] [];
     mk_inst 3 ASSIGN [Var "p"] ["q"];
     mk_inst 4 ASSIGN [Var "n"] ["m"];
     mk_inst 5 REVERT [Var "q"; Var "m"] []]
End

Definition inv_child_audit_def:
  inv_child_audit bi =
    MAP (\i. (i.inst_id,
       dft_cost bi [] (dft_eda bi) (build_offspring_map bi []) (LAST bi) i))
       (inst_all_deps bi [] (dft_eda bi) (LAST bi))
End

Theorem inv_child_direct_audit:
  inv_child_audit inv_child_order_bi = [(1,2); (0,3); (2,1)] /\
  MAP (\i. i.inst_id) (inv_line_children inv_child_order_bi []
    (dft_eda inv_child_order_bi) (build_offspring_map inv_child_order_bi [])
    (LAST inv_child_order_bi)) = [2;1;0]
Proof
  EVAL_TAC
QED

Theorem inv_child_alias_audit:
  inv_child_audit inv_child_alias_bi = [(4,2); (3,3); (2,1)] /\
  MAP (\i. i.inst_id) (inv_line_children inv_child_alias_bi []
    (dft_eda inv_child_alias_bi) (build_offspring_map inv_child_alias_bi [])
    (LAST inv_child_alias_bi)) = [2;4;3]
Proof
  EVAL_TAC
QED

Definition inv_child_cut_def:
  inv_child_cut bi = inv_cone_state bi [] (inv_joint_before bi RETURNDATACOPY)
End

Theorem inv_child_initialized_cuts:
  MAP (\i. i.inst_id) (inv_child_cut inv_child_order_bi).ds_output = [1;0] /\
  MEM 0 (inv_child_cut inv_child_order_bi).ds_visited /\
  MEM 1 (inv_child_cut inv_child_order_bi).ds_visited /\
  MAP (\i. i.inst_id) (inv_child_cut inv_child_alias_bi).ds_output = [1;0] /\
  MEM 0 (inv_child_cut inv_child_alias_bi).ds_visited /\
  MEM 1 (inv_child_cut inv_child_alias_bi).ds_visited
Proof
  EVAL_TAC
QED

Theorem inv_revert_effect_cost:
  r.inst_opcode = REVERT /\ ~MEM x (inst_data_deps bi order r) ==>
  dft_cost bi order eda om r x =
    if (case FLOOKUP om x.inst_id of NONE => F | SOME ds => ds <> [])
    then 1 else 2
Proof
  simp[dft_cost_def, dft_abort_kind_def]
QED

(* Literal COPY has no data offspring. Its cost 2 ties the first data
   child, whose original DDA position precedes the EDA COPY position. *)
Definition inv_child_tie_bi_def:
  inv_child_tie_bi =
    [mk_inst 0 RETURNDATACOPY [Lit 32w; Lit 0w; Lit 8w] [];
     mk_inst 1 ASSIGN [Lit 32w] ["p"];
     mk_inst 2 ASSIGN [Lit 8w] ["n"];
     mk_inst 3 REVERT [Var "p"; Var "n"] []]
End

Theorem inv_child_tie_audit:
  inv_child_audit inv_child_tie_bi = [(2,2); (1,3); (0,2)] /\
  MAP (\i. i.inst_id) (inv_line_children inv_child_tie_bi []
    (dft_eda inv_child_tie_bi) (build_offspring_map inv_child_tie_bi [])
    (LAST inv_child_tie_bi)) = [2;0;1] /\
  MAP (\i. i.inst_id) (inv_child_cut inv_child_tie_bi).ds_output = [2]
Proof
  EVAL_TAC
QED

(* Definition audit for REVERT with scheduling order []:
   - REVERT is NoFail and not flippable; the abort-priority branch is dead.
   - Effect-only children have cost 1 iff their offspring lookup is nonempty,
     and cost 2 otherwise (inv_revert_effect_cost).
   - Data children use the first matching python_stack_operands position + 2,
     or the first direct-output matching position + 2. With no matching
     position the order-index list is empty and the fallback is 2.
     Thus data costs are at least 2, not strictly above effect-only costs.
   - inst_all_deps places nub_first(DDA ++ EDA); tied data children precede
     an effect-only COPY, because the stable index is the original index.
   - build_offspring_map records data ANCESTORS despite its name. A COPY
     using produced operands therefore gets cost 1 in the direct and alias
     probes above; a literal COPY gets cost 2 and exhibits the real tie.

   Candidate interval argument, not a theorem: at the COPY emission cut,
   each pending non-ASSIGN in a residual REVERT sibling cone must already
   be emitted/pseudo, while new residual work consists of ASSIGN aliases.
   The direct and alias cuts check that both shared ADD producers have
   already emitted, even though their REVERT sibling processes remain.
   The literal tie checks that an ASSIGN data sibling can emit BEFORE COPY.

   Remaining obstruction: the initialized lineage alone does not establish
   REVERT ancestry or this cone classification. One needs a source-forwarding
   theorem saying each non-ASSIGN producer in a REVERT operand cone is also
   a producer in COPY's operand cones (or is already emitted); cost ordering
   cannot supply that producer correspondence. Literal aliases after COPY
   require a separate ASSIGN-chain case. Origin equivalence must be at the
   two actual use prefixes, not merely at a normalized final environment.
   No universal forwarding preservation is asserted by these finite tests. *)
