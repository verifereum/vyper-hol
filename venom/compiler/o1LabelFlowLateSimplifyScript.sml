Theory o1LabelFlowLateSimplify
Ancestors
  codegenSymRel symFrameBoundary simplifyCfgShape simplifyCfgStruct

(* PHI input exclusion is phi_input_not_code_end, not a new duplicate.
   This boundary covers all changed PHIs, including the new singleton
   ASSIGN case, without assuming that the input PHI is well formed. *)
Theorem fix_phi_inst_changed_no_code_end:
  label_flow_ok ctx /\ MEM f ctx.ctx_functions /\
  MEM i (fn_insts f) /\ fix_phi_inst ps i <> i /\
  MEM (Var x) (fix_phi_inst ps i).inst_operands ==>
  ~code_end_var f x
Proof
  rpt strip_tac >>
  `i.inst_opcode = PHI` by metis_tac[fix_phi_inst_non_phi] >>
  `MEM (Var x) i.inst_operands` by
    metis_tac[fix_phi_inst_var_subset] >>
  metis_tac[phi_input_not_code_end]
QED

(* For a tainted operand there was no PHI repair at all.  In particular,
   the original permitted-use shape transports without inspecting the
   NOP/single-input/multiple-input branches again. *)
Theorem fix_phi_inst_code_end_use:
  label_flow_ok ctx /\ MEM f ctx.ctx_functions /\
  MEM i (fn_insts f) /\ code_end_var f x /\
  MEM (Var x) (fix_phi_inst ps i).inst_operands ==>
  ((fix_phi_inst ps i).inst_opcode = ASSIGN /\
   (fix_phi_inst ps i).inst_operands = [Var x]) \/
  ((fix_phi_inst ps i).inst_opcode = CODECOPY /\
   ?dst sz. (fix_phi_inst ps i).inst_operands = [dst; Var x; sz] /\
            dst <> Var x /\ sz <> Var x)
Proof
  strip_tac >>
  `fix_phi_inst ps i = i` by
    metis_tac[fix_phi_inst_changed_no_code_end] >>
  gvs[label_flow_ok_def] >> metis_tac[]
QED

(* Retention audit for the late assembly consumer (not an assumed theorem):

   For g = FST (simplify_cfg_fn_with_labels f), the positive obligation is
     MEM i (fn_insts g) /\ MEM (Var x) i.inst_operands /\ code_end_var f x
       ==> code_end_var g x.
   It must be established together with negative provenance reflection.
   Literal old-instruction inclusion is false: PHIs and terminators change.

   remove_unreachable_blocks_def_available_at and
   remove_unreachable_blocks_def_dominates_uses (simplifyCfgDataflow) retain
   an available definition at a surviving reader.  wf_ssa's uniqueness is
   needed to identify that witness with the particular ADD/ASSIGN producer
   on the code_end_var chain; PHI inputs are excluded by the existing
   phi_input_not_code_end.  The raw reader-definition closure condition of
   o1LabelFlowRetention is therefore appropriate for this deletion substep,
   but not for the whole transform.

   fix_all_phis keeps ADD/ASSIGN producers unchanged (fix_phi_inst_non_phi);
   the two facts above rule out newly tainted PHI-to-ASSIGN copies.
   chain merging drops only the predecessor terminator (merge_blocks_def);
   jump bypass removes a singleton jump block (can_bypass_jump_def), changes
   jumps via canon_jnz_inst/subst_label_inst, and rewrites target PHI inputs
   via update_phi_bypass.  Positive ADD/ASSIGN producer transport through
   these operations is still owed, as is preservation of code_end seed
   operand contents through subst_block_labels_fn.  simplify_cfg_seed_source
   preserves only opcode/output origin, not [op; Label "code_end"], and
   simplify_cfg_copy_source permits a PHI origin: neither alone discharges
   the code_end_var obligation.

   collapse_dfs_preserves_predicate supplies the joint function-invariant
   induction after chain_merge and do_merge_jump are proved.  The existing
   chain_merge_ssa_invariant, do_merge_jump_ssa_invariant,
   collapse_ssa_invariant_joint, and simplify_cfg_iter_ssa_invariant thread
   the required wf_ssa/wf_function/fn_inst_wf/first_block_no_preds/
   scfg_phi_safe/fn_defs_reach_uses/label_positions_ok package.  Finally
   simplify_cfg_round_with_labels_def performs unreachable deletion and PHI
   repair both before and after collapse, and simplify_cfg_iter_with_labels
   iterates the round.  These are concrete remaining proof obligations for
   the assembly leaf, not missing premises of the frozen target. *)
