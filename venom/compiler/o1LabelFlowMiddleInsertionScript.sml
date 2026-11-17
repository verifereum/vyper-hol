Theory o1LabelFlowMiddleInsertion
Ancestors
  o1LabelFlowMiddleLive makeSsaCurrentPlacementCut makeSsaCurrentPlacement codegenSymRel
  makeSsaDefs venomInst o1PassContract list alist

(* Exact placement already records each inserted variable's selected liveness.
   Specializing that interface avoids re-proving the insertion traversal. *)

Theorem exact_prefix_protected:
  current_exact_prefix df pm li defs old new /\
  (!x l vs. P x /\ ALOOKUP li l = SOME vs ==> ~MEM x vs) ==>
  ?pre. new = old with bb_instructions := pre ++ old.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI /\
      !x. P x ==> ~MEM (Var x) i.inst_operands /\ ~MEM x i.inst_outputs) pre
Proof
  simp[current_exact_prefix_def] >> rpt strip_tac >>
  qexists `pre` >> simp[] >> gvs[EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i pre ==> _` drule >> strip_tac >> gvs[] >>
  simp[build_phi_inst_supply_def] >> rpt strip_tac >>
  `x = v` by (gvs[build_phi_inst_supply_def, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `!v. _ <=> _` (qspec_then `v` mp_tac) >>
  simp[build_phi_inst_supply_def] >>
  `?i. MEM i pre /\ MEM v i.inst_outputs` by
    (goal_assum $ drule_at Any >> simp[build_phi_inst_supply_def]) >>
  strip_tac >>
  `?roots. ALOOKUP defs v = SOME roots /\
    current_pruned_reach df li v roots old.bb_label` by metis_tac[] >>
  drule current_pruned_reach_live >>
  simp[current_placement_live_def] >> metis_tac[]
QED

Theorem add_phi_nodes_protected_prefix:
  add_phi_nodes_supply s df pm li bbs (compute_defs ordered) = (bbs',s') /\
  (!x l vs. P x /\ ALOOKUP li l = SOME vs ==> ~MEM x vs) ==>
  LIST_REL (\old new. ?pre.
    new = old with bb_instructions := pre ++ old.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI /\
      !x. P x ==> ~MEM (Var x) i.inst_operands /\ ~MEM x i.inst_outputs) pre)
    bbs bbs'
Proof
  strip_tac >> drule current_add_phi_nodes_exact_prefix >>
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  irule exact_prefix_protected >> metis_tac[]
QED

Theorem phi_prefix_nonphi_insts:
  !Q f bbs. LIST_REL (\old new. ?pre.
    new = old with bb_instructions := pre ++ old.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI /\ Q i) pre) f.fn_blocks bbs ==>
  (!i. MEM i (fn_insts f) ==> MEM i (fn_insts (f with fn_blocks := bbs))) /\
  (!i. MEM i (fn_insts (f with fn_blocks := bbs)) ==>
    MEM i (fn_insts f) \/ (i.inst_opcode = PHI /\ Q i))
Proof
  rpt gen_tac >> simp[LIST_REL_EL_EQN, fn_insts_def, fn_insts_blocks_MEM] >> strip_tac >>
  conj_tac >> rpt strip_tac >> gvs[]
  >- (qpat_x_assum `MEM bb _` (strip_assume_tac o REWRITE_RULE[MEM_EL]) >>
      first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
      qexists `EL n bbs` >> simp[EL_MEM] >> metis_tac[EL_MEM]) >>
  qpat_x_assum `MEM bb _` (strip_assume_tac o REWRITE_RULE[MEM_EL]) >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >> gvs[]
  >- (disj2_tac >> gvs[EVERY_MEM]) >>
  disj1_tac >> qexists `EL n f.fn_blocks` >> simp[EL_MEM]
QED

Theorem phi_prefix_code_end_var:
  !f x. code_end_var f x ==> !g.
    (!i. MEM i (fn_insts f) /\ i.inst_opcode <> PHI ==>
      MEM i (fn_insts g)) ==> code_end_var g x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  `inst.inst_opcode <> PHI` by simp[] >>
  metis_tac[code_end_var_rules]
QED

Theorem phi_prefix_code_end_eq:
  LIST_REL (\old new. ?pre.
    new = old with bb_instructions := pre ++ old.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI /\ Q i) pre) f.fn_blocks bbs ==>
  (code_end_var (f with fn_blocks := bbs) x <=> code_end_var f x)
Proof
  strip_tac >> drule phi_prefix_nonphi_insts >> strip_tac >>
  eq_tac >> strip_tac >> drule phi_prefix_code_end_var >>
  disch_then irule >> metis_tac[]
QED

Theorem protected_prefix_read:
  new = old with bb_instructions := pre ++ old.bb_instructions /\
  EVERY (\i. ~MEM (Var x) i.inst_operands) pre /\
  (!j. MEM j old.bb_instructions /\ MEM (Var x) j.inst_operands ==>
    j.inst_opcode = CODECOPY /\
    (?dst sz. j.inst_operands = [dst; Var x; sz] /\
      dst <> Var x /\ sz <> Var x) /\
    ?a b. old.bb_instructions = a ++ [d;j] ++ b) ==>
  !j. MEM j new.bb_instructions /\ MEM (Var x) j.inst_operands ==>
    j.inst_opcode = CODECOPY /\
    (?dst sz. j.inst_operands = [dst; Var x; sz] /\
      dst <> Var x /\ sz <> Var x) /\
    ?a b. new.bb_instructions = a ++ [d;j] ++ b
Proof
  rpt strip_tac >> gvs[EVERY_MEM] >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  qexistsl [`pre ++ a`,`b`] >> simp[APPEND_ASSOC]
QED

Theorem protected_prefix_lifetime:
  LIST_REL (\old new. ?pre.
    new = old with bb_instructions := pre ++ old.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI /\
      ~MEM (Var x) i.inst_operands /\ ~MEM x i.inst_outputs) pre)
    f.fn_blocks bbs /\
  MEM d (fn_insts f) /\
  (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
  (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
    MEM (Var x) j.inst_operands ==>
    j.inst_opcode = CODECOPY /\
    (?dst sz. j.inst_operands = [dst; Var x; sz] /\
      dst <> Var x /\ sz <> Var x) /\
    ?a b. bb.bb_instructions = a ++ [d;j] ++ b) ==>
  MEM d (fn_insts (f with fn_blocks := bbs)) /\
  (!k. MEM k (fn_insts (f with fn_blocks := bbs)) /\ MEM x k.inst_outputs ==>
    k = d) /\
  (!bb j. MEM bb bbs /\ MEM j bb.bb_instructions /\
    MEM (Var x) j.inst_operands ==>
    j.inst_opcode = CODECOPY /\
    (?dst sz. j.inst_operands = [dst; Var x; sz] /\
      dst <> Var x /\ sz <> Var x) /\
    ?a b. bb.bb_instructions = a ++ [d;j] ++ b)
Proof
  strip_tac >>
  qspec_then `\i. ~MEM (Var x) i.inst_operands /\ ~MEM x i.inst_outputs`
    mp_tac phi_prefix_nonphi_insts >>
  simp[] >> disch_then drule >> strip_tac >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  drule_all LIST_REL_MEM_IMP_R >> simp[] >> strip_tac >>
  irule protected_prefix_read >> simp[] >>
  qexistsl [`x'`,`pre`] >> simp[] >>
  conj_tac >- metis_tac[] >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem protected_prefix_label_flow:
  LIST_REL (\old new. ?pre.
    new = old with bb_instructions := pre ++ old.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI /\ Q i) pre) f.fn_blocks bbs /\
  (!i x. Q i /\ code_end_var f x ==> ~MEM (Var x) i.inst_operands) /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions := [f with fn_blocks := bbs])
Proof
  strip_tac >>
  `!x. code_end_var (f with fn_blocks := bbs) x <=> code_end_var f x` by
    (gen_tac >> irule phi_prefix_code_end_eq >> goal_assum $ drule_at Any) >>
  drule phi_prefix_nonphi_insts >> strip_tac >>
  gvs[label_flow_ok_def] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i (fn_insts (f with fn_blocks := bbs)) ==> _`
    drule >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem local_adjacent_insertion_prefix:
  wf_function f /\
  (!x. code_end_var f x ==>
    ?d. d.inst_opcode = ADD /\ d.inst_outputs = [x] /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
        MEM (Var x) j.inst_operands ==>
        ?a b. bb.bb_instructions = a ++ [d;j] ++ b)) /\
  add_phi_nodes_supply s df pm
    (select_current_live_in had_phis (liveness_analyze f) f)
    f.fn_blocks (compute_defs ordered) = (bbs,s') ==>
  LIST_REL (\old new. ?pre.
    new = old with bb_instructions := pre ++ old.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI /\
      !x. code_end_var f x ==>
        ~MEM (Var x) i.inst_operands /\ ~MEM x i.inst_outputs) pre)
    f.fn_blocks bbs
Proof
  strip_tac >> irule add_phi_nodes_protected_prefix >>
  goal_assum $ drule_at Any >> rpt strip_tac >>
  qpat_x_assum `!x. code_end_var f x ==> _` drule >> strip_tac >>
  `~MEM x vs` suffices_by simp[] >>
  irule local_adjacent_selected_not_live >> goal_assum $ drule_at Any >>
  qexistsl [`had_phis`,`l`] >> simp[]
QED

Theorem local_adjacent_insertion_label_flow:
  wf_function f /\ label_flow_ok (ctx with ctx_functions := [f]) /\
  (!x. code_end_var f x ==>
    ?d. d.inst_opcode = ADD /\ d.inst_outputs = [x] /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
        MEM (Var x) j.inst_operands ==>
        ?a b. bb.bb_instructions = a ++ [d;j] ++ b)) /\
  add_phi_nodes_supply s df pm
    (select_current_live_in had_phis (liveness_analyze f) f)
    f.fn_blocks (compute_defs ordered) = (bbs,s') ==>
  label_flow_ok (ctx with ctx_functions := [f with fn_blocks := bbs])
Proof
  strip_tac >> drule_all local_adjacent_insertion_prefix >> strip_tac >>
  irule protected_prefix_label_flow >> simp[] >>
  qexists `\i. !x. code_end_var f x ==>
    ~MEM (Var x) i.inst_operands /\ ~MEM x i.inst_outputs` >> simp[]
QED

Theorem local_adjacent_insertion_lifetime:
  wf_function f /\
  (!x. code_end_var f x ==>
    ?d op. MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
        MEM (Var x) j.inst_operands ==>
        j.inst_opcode = CODECOPY /\
        (?dst sz. j.inst_operands = [dst; Var x; sz] /\
          dst <> Var x /\ sz <> Var x) /\
        ?a b. bb.bb_instructions = a ++ [d;j] ++ b)) /\
  add_phi_nodes_supply s df pm
    (select_current_live_in had_phis (liveness_analyze f) f)
    f.fn_blocks (compute_defs ordered) = (bbs,s') ==>
  !x. code_end_var (f with fn_blocks := bbs) x ==>
    ?d op. MEM d (fn_insts (f with fn_blocks := bbs)) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts (f with fn_blocks := bbs)) /\ MEM x k.inst_outputs ==>
        k = d) /\
      (!bb j. MEM bb bbs /\ MEM j bb.bb_instructions /\
        MEM (Var x) j.inst_operands ==>
        j.inst_opcode = CODECOPY /\
        (?dst sz. j.inst_operands = [dst; Var x; sz] /\
          dst <> Var x /\ sz <> Var x) /\
        ?a b. bb.bb_instructions = a ++ [d;j] ++ b)
Proof
  strip_tac >>
  `LIST_REL (\old new. ?pre.
    new = old with bb_instructions := pre ++ old.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI /\
      !x. code_end_var f x ==>
        ~MEM (Var x) i.inst_operands /\ ~MEM x i.inst_outputs) pre)
    f.fn_blocks bbs` by
    (irule local_adjacent_insertion_prefix >> goal_assum $ drule_at Any >>
     simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `code_end_var f x` by
    (irule phi_prefix_code_end_var >> goal_assum $ drule_at Any >>
     qspec_then `\i. !x. code_end_var f x ==>
       ~MEM (Var x) i.inst_operands /\ ~MEM x i.inst_outputs`
       mp_tac phi_prefix_nonphi_insts >> simp[] >> disch_then drule >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `!x. code_end_var f x ==> _` drule >> strip_tac >>
  qexistsl [`d`,`op`] >> simp[] >>
  irule protected_prefix_lifetime >>
  goal_assum $ drule_at Any >> simp[] >>
  gvs[LIST_REL_EL_EQN, EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!n. n < LENGTH bbs ==> _` drule >> strip_tac >>
  goal_assum $ drule_at Any >> simp[] >> metis_tac[]
QED
