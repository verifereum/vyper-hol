Theory simplifyCfgStructProbe
Ancestors
  simplifyCfgStruct unitShapeDefs codegenReadyCompute

(* A bypass makes the two branch targets meet; the terminator must be
   canonicalized before the subsequent chain merge. *)
Definition probe_meeting_def:
  probe_meeting = mk_raw_function "entry"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JNZ [Lit 1w; Label "via"; Label "join"] []] |>;
     <| bb_label := "via"; bb_instructions :=
        [mk_inst 1 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
        [mk_inst 2 PHI [Label "entry"; Var "x"; Label "via"; Var "x"] ["y"];
         mk_inst 3 STOP [] []] |>]
End

(* The bypass target is the source itself. *)
Definition probe_self_def:
  probe_self = mk_raw_function "entry"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JMP [Label "loop"] []] |>;
     <| bb_label := "loop"; bb_instructions :=
        [mk_inst 1 PHI [Label "entry"; Var "x"; Label "back"; Var "y"] ["y"];
         mk_inst 2 JNZ [Lit 1w; Label "back"; Label "exit"] []] |>;
     <| bb_label := "back"; bb_instructions :=
        [mk_inst 3 JMP [Label "loop"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 4 STOP [] []] |>]
End

Definition probe_empty_phi_def:
  probe_empty_phi = mk_raw_function "entry"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 PHI [] ["x"]; mk_inst 1 STOP [] []] |>]
End

Theorem probe_phi_inputs:
  wf_function probe_meeting /\ fn_inst_wf probe_meeting /\
  wf_function probe_self /\ fn_inst_wf probe_self /\
  wf_function probe_empty_phi /\ fn_inst_wf probe_empty_phi
Proof
  EVAL_TAC
QED

Theorem probe_phi_outputs:
  (!inst. MEM inst (fn_insts (simplify_cfg_fn probe_meeting)) /\
          inst.inst_opcode = PHI ==>
          2 <= LENGTH (phi_pairs inst.inst_operands)) /\
  (!inst. MEM inst (fn_insts (simplify_cfg_fn probe_self)) /\
          inst.inst_opcode = PHI ==>
          2 <= LENGTH (phi_pairs inst.inst_operands)) /\
  (!inst. MEM inst (fn_insts (simplify_cfg_fn probe_empty_phi)) /\
          inst.inst_opcode = PHI ==>
          2 <= LENGTH (phi_pairs inst.inst_operands))
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[venomInstTheory.phi_pairs_def]
QED

Theorem probe_jnz_inputs:
  wf_function probe_meeting /\ fn_shape_ok probe_meeting /\
  (!inst. MEM inst (fn_insts probe_meeting) /\ inst.inst_opcode = JNZ ==>
     ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f)
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[venomInstTheory.phi_pairs_def]
QED

Theorem probe_jnz_output:
  !inst. MEM inst (fn_insts (simplify_cfg_fn probe_meeting)) /\
         inst.inst_opcode = JNZ ==>
         ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[venomInstTheory.phi_pairs_def]
QED

Definition probe_defined_def:
  probe_defined fn = fn with fn_blocks :=
    (HD fn.fn_blocks with bb_instructions :=
      mk_inst 10 ASSIGN [Lit 7w] ["x"] :: (HD fn.fn_blocks).bb_instructions)
    :: TL fn.fn_blocks
End

Theorem probe_ssa_inputs:
  wf_ssa (probe_defined probe_meeting) /\
  wf_function (probe_defined probe_meeting) /\
  fn_inst_wf (probe_defined probe_meeting) /\
  first_block_no_preds (probe_defined probe_meeting) /\
  EVERY (\inst. inst.inst_opcode <> PHI)
    (HD (probe_defined probe_meeting).fn_blocks).bb_instructions /\
  wf_ssa (probe_defined probe_self) /\
  wf_function (probe_defined probe_self) /\
  fn_inst_wf (probe_defined probe_self) /\
  first_block_no_preds (probe_defined probe_self) /\
  EVERY (\inst. inst.inst_opcode <> PHI)
    (HD (probe_defined probe_self).fn_blocks).bb_instructions
Proof
  EVAL_TAC
QED

Theorem probe_ssa_outputs:
  wf_ssa (simplify_cfg_fn (probe_defined probe_meeting)) /\
  wf_ssa (simplify_cfg_fn (probe_defined probe_self))
Proof
  EVAL_TAC
QED

(* Distinct branches define the same name: definite assignment, not SSA. *)
Definition probe_diamond_def:
  probe_diamond = mk_raw_function "entry"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JNZ [Lit 1w; Label "left"; Label "right"] []] |>;
     <| bb_label := "left"; bb_instructions :=
        [mk_inst 1 ASSIGN [Lit 2w] ["x"];
         mk_inst 2 JMP [Label "join"] []] |>;
     <| bb_label := "right"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit 3w] ["x"];
         mk_inst 4 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
        [mk_inst 5 ADD [Var "x"; Lit 1w] ["z"];
         mk_inst 6 STOP [] []] |>]
End

Theorem probe_diamond_fixed:
  simplify_cfg_fn probe_diamond = probe_diamond
Proof
  EVAL_TAC
QED

Theorem probe_diamond_no_opaque:
  (!x. ~copy_phi_var GAS probe_diamond x) /\
  (!x. ~copy_phi_var RETPC_PARAM probe_diamond x)
Proof
  conj_tac >> irule copy_phi_var_no_seed >>
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem probe_diamond_shape:
  wf_function probe_diamond /\ fn_inst_wf probe_diamond /\
  fn_shape_ok probe_diamond /\ first_block_no_preds probe_diamond /\
  ~ssa_form probe_diamond
Proof
  simp[fn_shape_ok_def, opaque_use_ok_def, gas_var_def, retpc_var_def,
       probe_diamond_no_opaque] >> EVAL_TAC
QED

Theorem probe_diamond_edges:
  fn_cfg_edge probe_diamond a b <=>
  (a = "entry" /\ (b = "left" \/ b = "right")) \/
  ((a = "left" \/ a = "right") /\ b = "join")
Proof
  simp[venomWfTheory.fn_cfg_edge_def, probe_diamond_def,
       venomInstTheory.mk_raw_function_def, RIGHT_AND_OVER_OR,
       EXISTS_OR_THM] >> EVAL_TAC >> simp[] >> metis_tac[]
QED

Theorem probe_diamond_paths:
  is_fn_path probe_diamond path /\ path <> [] /\
  HD path = "entry" /\ LAST path = "join" ==>
  path = ["entry"; "left"; "join"] \/
  path = ["entry"; "right"; "join"]
Proof
  namedCases_on `path` ["", "a tail"] >- simp[] >>
  namedCases_on `tail` ["", "b rest"] >- simp[] >>
  namedCases_on `rest` ["", "c more"]
  >- simp[venomWfTheory.is_fn_path_def, probe_diamond_edges] >>
  namedCases_on `more` ["", "d final"] >>
  rw[venomWfTheory.is_fn_path_def, probe_diamond_edges] >> gvs[] >>
  spose_not_then strip_assume_tac >> gvs[] >>
  Cases_on `b = "left"` >> gvs[]
QED

Theorem probe_diamond_entry:
  fn_entry_label probe_diamond = SOME "entry"
Proof
  EVAL_TAC
QED

Theorem probe_diamond_defined:
  fn_defs_reach_uses probe_diamond
Proof
  simp[venomWfTheory.fn_defs_reach_uses_def, probe_diamond_def,
       venomInstTheory.mk_raw_function_def, venomInstTheory.mk_inst_def] >>
  rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `def_on_all_paths fn _ _ _` >>
  `fn = probe_diamond` by
    simp[Abbr `fn`, probe_diamond_def, venomInstTheory.mk_raw_function_def,
         venomInstTheory.mk_inst_def] >>
  gvs[] >>
  simp[venomWfTheory.def_on_all_paths_def, probe_diamond_entry] >>
  rpt strip_tac >> drule_all probe_diamond_paths >> strip_tac >> gvs[] >>
  disj1_tac >> qexists_tac `1` >>
  simp[NoAsms, probe_diamond_def, venomInstTheory.mk_raw_function_def,
       venomInstTheory.mk_inst_def, RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem probe_diamond_ok:
  simplify_cfg_fn_ok probe_diamond
Proof
  simp[simplifyCfgDefsTheory.simplify_cfg_fn_ok_def, probe_diamond_defined] >>
  simp[probe_diamond_def, venomInstTheory.mk_raw_function_def,
       venomInstTheory.mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem probe_diamond_output_defined:
  fn_defs_reach_uses (simplify_cfg_fn probe_diamond)
Proof
  simp[probe_diamond_fixed, probe_diamond_defined]
QED

(* Two PHIs converted to assignments retain their dependency order. *)
Definition probe_ordered_def:
  probe_ordered = mk_raw_function "entry"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit 7w] ["x"];
         mk_inst 1 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
        [mk_inst 2 PHI [Label "entry"; Var "x"] ["y"];
         mk_inst 3 PHI [Label "entry"; Var "x"] ["z"];
         mk_inst 4 ADD [Var "y"; Var "z"] ["sum"];
         mk_inst 5 STOP [] []] |>]
End

Theorem probe_ordered_input:
  wf_ssa probe_ordered /\ wf_function probe_ordered /\
  fn_inst_wf probe_ordered /\ first_block_no_preds probe_ordered /\
  EVERY (\inst. inst.inst_opcode <> PHI)
    (HD probe_ordered.fn_blocks).bb_instructions
Proof
  EVAL_TAC
QED

Theorem probe_ordered_output:
  wf_ssa (simplify_cfg_fn probe_ordered)
Proof
  EVAL_TAC
QED

(* Disagreeing incoming values must prevent the tempting branch bypass. *)
Definition probe_disagree_def:
  probe_disagree = mk_raw_function "entry"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit 7w] ["x"];
         mk_inst 1 ASSIGN [Lit 8w] ["z"];
         mk_inst 2 JNZ [Lit 1w; Label "via"; Label "join"] []] |>;
     <| bb_label := "via"; bb_instructions :=
        [mk_inst 3 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
        [mk_inst 4 PHI [Label "entry"; Var "x"; Label "via"; Var "z"] ["y"];
         mk_inst 5 STOP [] []] |>]
End

Theorem probe_disagree_input:
  wf_ssa probe_disagree /\ wf_function probe_disagree /\
  fn_inst_wf probe_disagree /\ first_block_no_preds probe_disagree /\
  EVERY (\inst. inst.inst_opcode <> PHI)
    (HD probe_disagree.fn_blocks).bb_instructions
Proof
  EVAL_TAC
QED

Theorem probe_disagree_output:
  simplify_cfg_fn probe_disagree = probe_disagree /\
  wf_ssa (simplify_cfg_fn probe_disagree)
Proof
  EVAL_TAC
QED
