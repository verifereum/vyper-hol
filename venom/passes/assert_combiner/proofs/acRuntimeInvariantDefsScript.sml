Theory acRuntimeInvariantDefs
Ancestors
  acChainProofs venomWf venomWfProps venomExecProofs venomExecProps
  venomState venomInst venomExecSemantics dfgDefs dfgAnalysisProps finite_map list relation
  algebraicOptFreshnessProofs algebraicOptDominanceProofs

(* A static program point, not a test of the runtime variable domain. *)
Definition ac_def_before_def:
  ac_def_before fn bb idx inst <=>
    (?j. j < idx /\ j < LENGTH bb.bb_instructions /\
         EL j bb.bb_instructions = inst) \/
    (?db. MEM db fn.fn_blocks /\ MEM inst db.bb_instructions /\
          db.bb_label <> bb.bb_label /\
          fn_dominates fn db.bb_label bb.bb_label)
End

Definition ac_cursor_inv_def:
  ac_cursor_inv fn bb idx s <=>
    MEM bb fn.fn_blocks /\ s.vs_current_bb = bb.bb_label /\
    s.vs_inst_idx = idx /\ idx <= LENGTH bb.bb_instructions /\
    fn_reachable fn bb.bb_label /\
    ac_dfg_inv_local (dfg_build_function fn) (ac_def_before fn bb idx) s /\
    (!inst v. ac_def_before fn bb idx inst /\ MEM v inst.inst_outputs ==>
              IS_SOME (lookup_var v s))
End

Theorem ac_def_before_entry:
  fn_entry_label fn = SOME bb.bb_label ==>
  !inst. ~ac_def_before fn bb 0 inst
Proof
  strip_tac >> gen_tac >> spose_not_then assume_tac >>
  gvs[ac_def_before_def] >>
  qpat_x_assum `fn_dominates _ _ _` mp_tac >>
  pure_rewrite_tac[fn_dominates_def] >> strip_tac >>
  first_x_assum (qspec_then `[bb.bb_label]` mp_tac) >>
  simp[is_fn_path_def]
QED

Theorem ac_cursor_inv_entry:
  MEM bb fn.fn_blocks /\ fn_entry_label fn = SOME bb.bb_label /\
  s.vs_current_bb = bb.bb_label /\ s.vs_inst_idx = 0 ==>
  ac_cursor_inv fn bb 0 s
Proof
  rpt strip_tac >> drule ac_def_before_entry >> strip_tac >>
  simp[ac_cursor_inv_def, ac_dfg_inv_local_def, fn_reachable_def] >>
  metis_tac[RTC_REFL]
QED

Theorem ac_def_before_mono:
  i <= j /\ ac_def_before fn bb i inst ==> ac_def_before fn bb j inst
Proof
  simp[ac_def_before_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

(* Restriction changes only the proof cursor; the state index is normalized
   explicitly. No execution or PHI-preservation claim is hidden here. *)
Theorem ac_cursor_inv_restrict:
  ac_cursor_inv fn bb j s /\ i <= j ==>
  ac_cursor_inv fn bb i (s with vs_inst_idx := i)
Proof
  `!op. eval_operand op (s with vs_inst_idx := i) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[ac_cursor_inv_def] >> rpt strip_tac >> simp[]
  >- (`ac_dfg_inv_local (dfg_build_function fn) (ac_def_before fn bb i) s` by
        (irule ac_dfg_inv_local_restrict >>
         qexists `ac_def_before fn bb j` >>
         simp[] >> metis_tac[ac_def_before_mono]) >>
      gvs[ac_dfg_inv_local_def, lookup_var_def]) >>
  `ac_def_before fn bb j inst` by metis_tac[ac_def_before_mono] >>
  `IS_SOME (lookup_var v s)` by metis_tac[] >>
  gvs[lookup_var_def]
QED

Theorem ac_available_before_cursor:
  wf_function fn /\ MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions /\
  def_available_at fn bb (SOME (EL idx bb.bb_instructions)) v ==>
  ?inst. MEM v inst.inst_outputs /\ ac_def_before fn bb idx inst
Proof
  rpt strip_tac >> drule_all ao_available_at_index >> strip_tac >>
  qexists `di` >> simp[ac_def_before_def] >>
  Cases_on `db.bb_label = bb.bb_label`
  >- (`db = bb` by
        (`lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
           (irule venomExecProofsTheory.MEM_lookup_block >>
            gvs[wf_function_def, fn_labels_def]) >>
         `lookup_block bb.bb_label fn.fn_blocks = SOME db` by
           (irule venomExecProofsTheory.MEM_lookup_block >>
            gvs[wf_function_def, fn_labels_def]) >> gvs[]) >>
      gvs[] >> disj1_tac >> qexists `i` >> simp[] >> decide_tac) >>
  disj2_tac >> qexists `db` >> simp[]
QED

(* DFG lookup is pinned to the SSA definition of this queried use, not to
   arbitrary values already present in the initial runtime map. *)
Theorem ac_query_use_before:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL idx bb.bb_instructions).inst_operands /\
  dfg_get_def (dfg_build_function fn) v = SOME inst ==>
  ac_def_before fn bb idx inst
Proof
  rpt strip_tac >>
  `def_available_at fn bb (SOME (EL idx bb.bb_instructions)) v` by
    (fs[wf_ssa_def, def_dominates_uses_def] >>
     first_x_assum drule >>
     disch_then (qspec_then `EL idx bb.bb_instructions` mp_tac) >>
     simp[EL_MEM]) >>
  drule_all ac_available_before_cursor >> strip_tac >>
  drule dfg_build_function_correct >> strip_tac >>
  `MEM inst' (fn_insts fn)` by
    (gvs[ac_def_before_def, fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[EL_MEM, arithmeticTheory.LESS_TRANS]) >>
  `inst = inst'` by
    (fs[wf_ssa_def, fn_insts_def] >> metis_tac[ssa_outputs_same_inst]) >>
  gvs[]
QED

Theorem ac_def_before_location:
  wf_function fn /\ MEM bb fn.fn_blocks /\ MEM db fn.fn_blocks /\
  j < LENGTH db.bb_instructions ==>
  (ac_def_before fn bb idx (EL j db.bb_instructions) <=>
   (db = bb /\ j < idx) \/
   (db.bb_label <> bb.bb_label /\ fn_dominates fn db.bb_label bb.bb_label))
Proof
  rpt strip_tac >> eq_tac
  >- (simp[ac_def_before_def] >> strip_tac
      >- (`db = bb` by metis_tac[wf_function_instruction_block, EL_MEM] >>
          gvs[] >>
          `j = j'` by metis_tac[ao_wf_instruction_index] >> gvs[]) >>
      `db = db'` by metis_tac[wf_function_instruction_block, EL_MEM] >>
      gvs[]) >>
  strip_tac >> gvs[ac_def_before_def] >> metis_tac[EL_MEM]
QED

Theorem ac_def_before_trans:
  wf_function fn /\ MEM bb fn.fn_blocks /\ MEM db fn.fn_blocks /\
  j < LENGTH db.bb_instructions /\
  ac_def_before fn bb idx (EL j db.bb_instructions) /\
  ac_def_before fn db j inst ==>
  ac_def_before fn bb idx inst
Proof
  rpt strip_tac >>
  `((db = bb /\ j < idx) \/
    (db.bb_label <> bb.bb_label /\ fn_dominates fn db.bb_label bb.bb_label))` by
    metis_tac[ac_def_before_location] >> gvs[]
  >- (irule ac_def_before_mono >> qexists `j` >> simp[]) >>
  qpat_x_assum `ac_def_before fn bb idx _` kall_tac >>
  gvs[ac_def_before_def]
  >- (disj2_tac >> qexists `db` >> simp[EL_MEM]) >>
  disj2_tac >> qexists `db'` >> simp[] >>
  conj_tac >- metis_tac[ao_fn_dominates_antisym] >>
  metis_tac[ao_fn_dominates_trans]
QED

Theorem ac_query_before_closed:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  MEM db fn.fn_blocks /\ j < LENGTH db.bb_instructions /\
  ac_def_before fn bb idx (EL j db.bb_instructions) /\
  (EL j db.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL j db.bb_instructions).inst_operands /\
  dfg_get_def (dfg_build_function fn) v = SOME inst ==>
  ac_def_before fn bb idx inst
Proof
  rpt strip_tac >>
  `ac_def_before fn db j inst` by (irule ac_query_use_before >> metis_tac[]) >>
  irule ac_def_before_trans >> metis_tac[]
QED

Theorem ac_cursor_use_defined:
  wf_function fn /\ wf_ssa fn /\ ac_cursor_inv fn bb idx s /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL idx bb.bb_instructions).inst_operands ==>
  IS_SOME (lookup_var v s)
Proof
  simp[ac_cursor_inv_def] >> rpt strip_tac >>
  `def_available_at fn bb (SOME (EL idx bb.bb_instructions)) v` by
    (fs[wf_ssa_def, def_dominates_uses_def] >>
     first_x_assum drule >>
     disch_then (qspec_then `EL idx bb.bb_instructions` mp_tac) >>
     simp[EL_MEM]) >>
  drule_all ac_available_before_cursor >> strip_tac >> metis_tac[]
QED

(* At a PHI-only prefix, no local ASSIGN/ISZERO equation is required yet. *)
Theorem ac_def_before_phi_prefix:
  EVERY (\i. i.inst_opcode = PHI) (TAKE k bb.bb_instructions) /\
  inst.inst_opcode <> PHI ==>
  (ac_def_before fn bb k inst <=> ac_def_before fn bb 0 inst)
Proof
  rpt strip_tac >> simp[ac_def_before_def] >>
  `~(?j. j < k /\ j < LENGTH bb.bb_instructions /\
          EL j bb.bb_instructions = inst)` by
    (strip_tac >> fs[EVERY_EL] >>
     first_x_assum (qspec_then `j` mp_tac) >> simp[EL_TAKE, LENGTH_TAKE_EQ]) >>
  simp[]
QED

(* Includes back edges: restrict to the new strict dominators instead of
   retaining equations from an earlier visit to the successor block. *)
Theorem ac_def_before_successor:
  wf_function fn /\ MEM bb fn.fn_blocks /\ MEM sb fn.fn_blocks /\
  fn_cfg_edge fn bb.bb_label sb.bb_label /\ fn_reachable fn bb.bb_label /\
  ac_def_before fn sb 0 inst ==>
  ac_def_before fn bb (LENGTH bb.bb_instructions) inst
Proof
  rpt strip_tac >>
  qpat_x_assum `ac_def_before _ _ _ _` mp_tac >>
  simp[ac_def_before_def] >> strip_tac >>
  `fn_dominates fn db.bb_label bb.bb_label` by
    (irule fn_dominates_predecessor >> metis_tac[]) >>
  Cases_on `db.bb_label = bb.bb_label`
  >- (`db = bb` by
        (`lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
           (irule venomExecProofsTheory.MEM_lookup_block >>
            gvs[wf_function_def, fn_labels_def]) >>
         `lookup_block bb.bb_label fn.fn_blocks = SOME db` by
           (irule venomExecProofsTheory.MEM_lookup_block >>
            gvs[wf_function_def, fn_labels_def]) >> gvs[]) >>
      gvs[MEM_EL] >> metis_tac[]) >>
  metis_tac[]
QED
