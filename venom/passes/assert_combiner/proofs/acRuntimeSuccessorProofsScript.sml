Theory acRuntimeSuccessorProofs
Ancestors
  acRuntimeInvariantDefs acChainProofs venomExecProofs venomState

(* A successor retains only its strict-dominator certificates. In particular,
   local equations from a previous loop iteration are not carried back. *)
Theorem ac_cursor_inv_successor:
  wf_function fn /\
  ac_cursor_inv fn bb (LENGTH bb.bb_instructions) s /\
  MEM sb fn.fn_blocks /\ fn_cfg_edge fn bb.bb_label sb.bb_label ==>
  ac_cursor_inv fn sb 0
    (s with <|vs_current_bb := sb.bb_label; vs_inst_idx := 0|>)
Proof
  `!op. eval_operand op
      (s with <|vs_current_bb := sb.bb_label; vs_inst_idx := 0|>) =
      eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[ac_cursor_inv_def] >> rpt strip_tac >> simp[]
  >- metis_tac[fn_reachable_step]
  >- (`ac_dfg_inv_local (dfg_build_function fn)
         (ac_def_before fn sb 0) s` by
        (irule ac_dfg_inv_local_restrict >>
         qexists `ac_def_before fn bb (LENGTH bb.bb_instructions)` >>
         simp[] >> metis_tac[ac_def_before_successor]) >>
      gvs[ac_dfg_inv_local_def, lookup_var_def]) >>
  `ac_def_before fn bb (LENGTH bb.bb_instructions) inst` by
    metis_tac[ac_def_before_successor] >>
  `IS_SOME (lookup_var v s)` by metis_tac[] >>
  gvs[lookup_var_def]
QED

(* The runner also installs the predecessor label for parallel PHIs. *)
Theorem ac_cursor_inv_successor_prev:
  wf_function fn /\
  ac_cursor_inv fn bb (LENGTH bb.bb_instructions) s /\
  MEM sb fn.fn_blocks /\ fn_cfg_edge fn bb.bb_label sb.bb_label ==>
  ac_cursor_inv fn sb 0
    (s with <|vs_current_bb := sb.bb_label; vs_inst_idx := 0;
              vs_prev_bb := SOME bb.bb_label|>)
Proof
  rpt strip_tac >> drule_all ac_cursor_inv_successor >>
  `!op t. eval_operand op (t with vs_prev_bb := SOME bb.bb_label) =
          eval_operand op t` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[ac_cursor_inv_def, ac_dfg_inv_local_def, lookup_var_def] >>
  metis_tac[]
QED
