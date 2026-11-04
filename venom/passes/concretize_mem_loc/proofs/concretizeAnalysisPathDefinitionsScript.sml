(* Availability on a specified first-visit CFG path; no runtime path claim. *)
Theory concretizeAnalysisPathDefinitions
Ancestors venomWf list

Theorem fn_defs_reach_uses_ordinary:
  fn_defs_reach_uses fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode <> PHI /\
  MEM (Var v) inst.inst_operands ==>
  def_on_all_paths fn bb (SOME inst) v
Proof
  simp[fn_defs_reach_uses_def] >> metis_tac[]
QED

Theorem fn_defs_reach_uses_phi_edge:
  fn_defs_reach_uses fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
  MEM (pred,v) (phi_pairs inst.inst_operands) /\
  MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = pred /\
  fn_cfg_edge fn pred bb.bb_label ==>
  def_on_all_paths fn pred_bb NONE v
Proof
  simp[fn_defs_reach_uses_def] >> metis_tac[]
QED

Theorem def_on_all_paths_first_visit:
  def_on_all_paths fn bb point v /\
  is_fn_path fn (prefix ++ [bb.bb_label]) /\
  (?entry. fn_entry_label fn = SOME entry /\
           HD (prefix ++ [bb.bb_label]) = entry) /\
  ~MEM bb.bb_label prefix ==>
  (?k def_bb def_inst.
     k < LENGTH prefix /\ MEM def_bb fn.fn_blocks /\
     def_bb.bb_label = EL k prefix /\ def_bb <> bb /\
     MEM def_inst def_bb.bb_instructions /\ MEM v def_inst.inst_outputs) \/
  (?i. i < LENGTH bb.bb_instructions /\
       MEM v (EL i bb.bb_instructions).inst_outputs /\
       case point of NONE => T | SOME use_inst =>
         ?j. i < j /\ j < LENGTH bb.bb_instructions /\
             EL j bb.bb_instructions = use_inst)
Proof
  simp[def_on_all_paths_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `prefix ++ [bb.bb_label]` mp_tac) >>
  simp[] >> strip_tac
  >- (disj1_tac >> qexistsl_tac [`k`,`def_bb`,`def_inst`] >>
      gvs[EL_APPEND_EQN] >> metis_tac[MEM_EL]) >>
  metis_tac[]
QED
