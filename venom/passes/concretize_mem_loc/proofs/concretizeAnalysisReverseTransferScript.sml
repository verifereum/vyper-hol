Theory concretizeAnalysisReverseTransfer
Ancestors
  concretizeAnalysisExclusiveWriters concretizeAnalysisExclusiveSources concretizeAnalysisAffine
  frameOriginHistoryPreservation frameOriginUpdates ptrDiscipline
  pointerConfinedDefs pointerClosure removeUnusedSsaProofs venomWf venomExecSemantics venomState venomInst finite_map pred_set list rich_list

Definition origin_reverse_covered_def:
  origin_reverse_covered P fn written om <=>
    !v. v IN written /\ allocation_exclusive P fn v ==>
      ?aid site. FLOOKUP om v = SOME (OriginLocal aid,site)
End

Definition origin_exclusive_ready_def:
  origin_exclusive_ready P fn inst om <=>
    !v. MEM (Var v) inst.inst_operands /\ allocation_exclusive P fn v ==>
      ?aid site. FLOOKUP om v = SOME (OriginLocal aid,site)
End

Definition origin_phi_ready_def:
  origin_phi_ready P fn lbl om [] = T /\
  origin_phi_ready P fn lbl om (i::is) =
    (i.inst_opcode = PHI ==>
      (!v. MEM v i.inst_outputs /\ allocation_exclusive P fn v ==>
        ?u aid site. resolve_phi lbl i.inst_operands = SOME (Var u) /\
          allocation_exclusive P fn u /\
          FLOOKUP om u = SOME (OriginLocal aid,site)) /\
      origin_phi_ready P fn lbl om is)
End

Theorem origin_reverse_covered_empty[simp]:
  origin_reverse_covered P fn {} om
Proof simp[origin_reverse_covered_def]
QED

Theorem origin_reverse_covered_lookup:
  origin_reverse_covered P fn written om /\ v IN written /\ allocation_exclusive P fn v ==>
    ?aid site. FLOOKUP om v = SOME (OriginLocal aid,site)
Proof simp[origin_reverse_covered_def]
QED

Theorem origin_reverse_covered_subset:
  origin_reverse_covered P fn written om /\ V SUBSET written ==>
  origin_reverse_covered P fn V om
Proof simp[origin_reverse_covered_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem origin_exclusive_ready_covered:
  origin_reverse_covered P fn written om /\
  (!v. MEM (Var v) inst.inst_operands /\ allocation_exclusive P fn v ==> v IN written) ==>
  origin_exclusive_ready P fn inst om
Proof simp[origin_reverse_covered_def, origin_exclusive_ready_def] >> metis_tac[]
QED

Theorem origin_reverse_resume:
  ssa_form fn /\ fn_inst_wf fn /\ fn_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  origin_reverse_covered P fn written om ==>
  origin_reverse_covered P fn (written UNION set inst.inst_outputs)
    (DRESTRICT om (COMPL (set inst.inst_outputs)))
Proof
  strip_tac >>
  `!v. MEM v inst.inst_outputs ==> ~allocation_exclusive P fn v` by
    (rpt strip_tac >> drule_all allocation_exclusive_opcode >> simp[]) >>
  gvs[origin_reverse_covered_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem origin_reverse_phis:
  !is. origin_phi_ready P fn lbl om is /\
  (!i v. MEM i is /\ i.inst_opcode = PHI /\ MEM v i.inst_outputs /\
    allocation_exclusive P fn v ==> i.inst_outputs = [v]) /\
  origin_reverse_covered P fn written om ==>
  origin_reverse_covered P fn (written UNION origin_phi_writes is)
    (origin_phis (SOME lbl) om is)
Proof
  Induct >> simp[origin_phi_ready_def, origin_phi_writes_def, origin_phis_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[] >> strip_tac >>
  `origin_reverse_covered P fn (written UNION origin_phi_writes is)
    (origin_phis (SOME lbl) om is)` by (first_x_assum irule >> simp[] >> metis_tac[]) >>
  rewrite_tac[origin_reverse_covered_def] >> gen_tac >> disch_tac >>
  `allocation_exclusive P fn v` by gvs[] >>
  Cases_on `MEM v h.inst_outputs`
  >- (`h.inst_outputs = [v]` by metis_tac[] >>
      `?u aid site. resolve_phi lbl h.inst_operands = SOME (Var u) /\
         FLOOKUP om u = SOME (OriginLocal aid,site)` by metis_tac[] >>
      simp[origin_set_lookup, origin_phi_def, origin_op_def] >> metis_tac[]) >>
  `h.inst_outputs <> [v]` by (strip_tac >> gvs[]) >>
  `v IN written UNION origin_phi_writes is` by gvs[] >>
  simp[origin_set_lookup] >> metis_tac[origin_reverse_covered_lookup]
QED

Theorem origin_first_local[local]:
  !ops. (?v aid site. MEM (Var v) ops /\
      FLOOKUP om v = SOME (OriginLocal aid,site)) /\
    (!v p. MEM (Var v) ops /\ FLOOKUP om v = SOME p ==>
      ?aid site. p = (OriginLocal aid,site)) ==>
    ?aid site. origin_first om ops = SOME (OriginLocal aid,site)
Proof
  Induct >> simp[origin_first_def] >> gen_tac >> strip_tac >>
  Cases_on `origin_op om h`
  >- (simp[] >> first_x_assum irule >>
      gvs[origin_op_def, AllCaseEqs()] >> metis_tac[]) >>
  simp[] >> gvs[origin_op_some] >> metis_tac[]
QED

Theorem origin_affine_local[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  MEM inst.inst_opcode [ADD; SUB; ASSIGN] /\
  MEM (Var u) inst.inst_operands /\ allocation_exclusive P fn u /\
  origin_exclusive_ready P fn inst om /\
  (!v p. FLOOKUP om v = SOME p ==> v IN fn_pv P fn) ==>
  ?aid site. origin_first om inst.inst_operands = SOME (OriginLocal aid,site)
Proof
  strip_tac >>
  `u IN fn_pv P fn` by
    gvs[allocation_exclusive_def, fn_pv_root_decomposition] >>
  `?aid site. FLOOKUP om u = SOME (OriginLocal aid,site)` by
    metis_tac[origin_exclusive_ready_def] >>
  irule origin_first_local >> reverse conj_tac
  >- (qexistsl [`u`, `aid`, `site`] >> simp[]) >>
  rpt strip_tac >>
  `v IN fn_pv P fn` by metis_tac[] >>
  `u IN fn_pv P fn` by metis_tac[] >>
  `v = u` suffices_by metis_tac[origin_exclusive_ready_def, optionTheory.SOME_11] >>
  gvs[MEM] >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  drule fn_ptr_ok_add_exclusion >> strip_tac >>
  drule fn_ptr_ok_sub_exclusion >> strip_tac >> metis_tac[]
QED

Theorem successful_alloca_origin[local]:
  inst.inst_opcode = ALLOCA /\ step_inst fuel ctx inst s = OK post ==>
  ?site. FLOOKUP post.vs_allocas inst.inst_id = SOME site
Proof
  simp[Once step_inst_def] >>
  simp[step_inst_base_def, exec_alloca_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem origin_reverse_step:
  ssa_form fn /\ fn_inst_wf fn /\ fn_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  step_inst fuel ctx inst s = OK post /\
  origin_reverse_covered P fn written om /\
  origin_exclusive_ready P fn inst om /\
  (!v p. FLOOKUP om v = SOME p ==> v IN fn_pv P fn) ==>
  origin_reverse_covered P fn (written UNION set inst.inst_outputs)
    (origin_step PG om inst post)
Proof
  strip_tac >> rewrite_tac[origin_reverse_covered_def] >> gen_tac >> strip_tac >>
  Cases_on `MEM v inst.inst_outputs`
  >- (drule_all allocation_exclusive_writer >> strip_tac >>
      simp[origin_step_def, origin_set_lookup] >>
      Cases_on `inst.inst_opcode = ALLOCA`
      >- (drule_all successful_alloca_origin >> strip_tac >>
          simp[origin_out_def] >> metis_tac[]) >> gvs[] >>
      `MEM inst.inst_opcode [ADD; SUB; ASSIGN]` by
        (Cases_on `inst.inst_opcode` >> gvs[is_pointer_preserving_op_def]) >>
      `inst_wf inst` by
        (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
         metis_tac[]) >>
      drule_all origin_affine_local >> strip_tac >>
      gvs[MEM] >> simp[origin_out_def] >> metis_tac[]) >>
  `inst.inst_outputs <> [v]` by (strip_tac >> gvs[]) >>
  simp[origin_step_def, origin_set_lookup] >>
  metis_tac[origin_reverse_covered_lookup, IN_UNION, LIST_TO_SET]
QED

Definition origin_phi_prefix_def:
  origin_phi_prefix [] = [] /\
  origin_phi_prefix (i::is) =
    if i.inst_opcode = PHI then i::origin_phi_prefix is else []
End

Theorem origin_phi_ready_covered:
  !is. origin_reverse_covered P fn written om /\
  (!i v. MEM i (origin_phi_prefix is) /\
    MEM v i.inst_outputs /\ allocation_exclusive P fn v ==>
    ?u. resolve_phi lbl i.inst_operands = SOME (Var u) /\
        allocation_exclusive P fn u /\ u IN written) ==>
  origin_phi_ready P fn lbl om is
Proof
  Induct >> simp[origin_phi_ready_def] >> gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[origin_phi_prefix_def] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >>
      `?u. resolve_phi lbl h.inst_operands = SOME (Var u) /\
           allocation_exclusive P fn u /\ u IN written` by metis_tac[] >>
      drule_all origin_reverse_covered_lookup >> strip_tac >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem origin_reverse_phi_batch:
  ssa_form fn /\ fn_inst_wf fn /\ fn_ptr_ok P fn /\ MEM bb fn.fn_blocks /\
  origin_reverse_covered P fn written om /\
  origin_phi_ready P fn lbl om bb.bb_instructions ==>
  origin_reverse_covered P fn (written UNION origin_phi_writes bb.bb_instructions)
    (origin_phis (SOME lbl) om bb.bb_instructions)
Proof
  strip_tac >> irule origin_reverse_phis >> simp[] >> rpt strip_tac >>
  `MEM i (fn_insts fn)` by
    (gvs[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  drule_all allocation_exclusive_writer >> simp[]
QED
