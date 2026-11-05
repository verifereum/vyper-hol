Theory makeSsaCurrentCutCounterexample
Ancestors
  makeSsaCurrentCutProbe makeSsaCurrentCutInv makeSsaCurrentWfSsa
  makeSsaCurrentSourceCuts venomInst venomWf o1FrameLockstep pair

Theorem current_cut_fork_context_exists:
  ?renamed A H events.
    current_wf_phi_context (current_wf_probe_supply current_wf_probe_fork)
      current_wf_probe_fork renamed
      (SND (make_ssa_current_fn (current_wf_probe_supply current_wf_probe_fork)
        current_wf_probe_fork)) A H events /\
    FST (make_ssa_current_fn (current_wf_probe_supply current_wf_probe_fork)
      current_wf_probe_fork) = current_wf_probe_fork with fn_blocks :=
        simplify_current_phis_if (blocks_have_leading_phi current_wf_probe_fork.fn_blocks)
          renamed
Proof
  `entry_block current_wf_probe_fork = SOME (HD current_wf_probe_fork.fn_blocks)` by
    EVAL_TAC >>
  `?A H events. current_structural_certificate
      (current_wf_probe_supply current_wf_probe_fork) current_wf_probe_fork
      (FST (make_ssa_current_fn (current_wf_probe_supply current_wf_probe_fork)
        current_wf_probe_fork))
      (SND (make_ssa_current_fn (current_wf_probe_supply current_wf_probe_fork)
        current_wf_probe_fork)) A H events` by
    (irule current_structural_certificate_exists >>
     metis_tac[current_wf_probe_fork_structural, current_wf_probe_input_reachable, PAIR]) >>
  gvs[current_wf_precleanup_certificate_stages] >>
  qexistsl_tac [`renamed`, `A`, `H`, `events`] >> simp[] >>
  irule current_wf_phi_context_intro >>
  simp[current_wf_probe_fork_structural, current_wf_probe_input_definite_assignment,
       current_wf_probe_input_reachable] >>
  qspec_then `current_wf_probe_fork` mp_tac current_wf_probe_phi_contract >>
  simp[] >> metis_tac[]
QED

Definition current_cut_fork_defs_def:
  current_cut_fork_defs = compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl current_wf_probe_fork.fn_blocks)
      (current_dom_postorder current_wf_probe_fork))))
End

Definition current_cut_fork_insertion_def:
  current_cut_fork_insertion = add_phi_nodes_supply
    (current_wf_probe_supply current_wf_probe_fork)
    (current_frontier_map current_wf_probe_fork) (current_pred_map current_wf_probe_fork)
    (select_current_live_in (blocks_have_leading_phi current_wf_probe_fork.fn_blocks)
      (liveness_analyze current_wf_probe_fork) current_wf_probe_fork)
    current_wf_probe_fork.fn_blocks current_cut_fork_defs
End

Definition current_cut_fork_rename_def:
  current_cut_fork_rename = rename_current_blocks
    (SND current_cut_fork_insertion) (init_current_rename_state current_cut_fork_defs)
    (FST current_cut_fork_insertion) (current_succ_map current_wf_probe_fork)
    (current_dom_tree current_wf_probe_fork)
End

(* The suspected counterexample fails: the ORIGINAL PHI receives the fresh
   name formal_var_0; v is the INSERTED PHI's name, not vice versa. *)
Theorem current_cut_fork_precleanup_shape:
  MAP (\bb. (bb.bb_label, MAP (\i. (i.inst_id,i.inst_opcode,i.inst_operands,i.inst_outputs))
      bb.bb_instructions)) (SND (SND current_cut_fork_rename)) =
  [("E",[(0,ASSIGN,[Lit 1w],["a"]); (1,JMP,[Label "H"],[])]);
   ("H",[(20,PHI,[Label "E"; Var "v"; Label "D"; Var "formal_var_0";
                  Label "F"; Var "formal_var_0"],["v"]);
         (2,PHI,[Label "E"; Var "a"; Label "D"; Var "b"; Label "F"; Var "c"],
           ["formal_var_0"]);
         (3,JNZ,[Var "formal_var_0"; Label "D"; Label "F"],[])]);
   ("D",[(4,ASSIGN,[Lit 2w],["b"]);
         (5,JNZ,[Var "formal_var_0"; Label "H"; Label "X"],[])]);
   ("F",[(6,ASSIGN,[Lit 3w],["c"]); (7,JMP,[Label "H"],[])]);
   ("X",[(8,STOP,[],[])])]
Proof
  EVAL_TAC
QED
