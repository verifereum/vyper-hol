(* Consumer-facing universal transfer probes.  No finite-fuel claim yet. *)
Theory concretizeAnalysisBoundary
Ancestors concretizeMemLocDefs basePtrProofs basePtrDefs list pred_set combin venomInst
  venomExecSemantics venomState finite_map words

Definition bp_bases_def:
  bp_bases r v = set (MAP ptr_base (bp_get_ptrs r v))
End

Definition bp_base_covers_def:
  bp_base_covers r s <=> !v. bp_bases r v SUBSET bp_bases s v
End

Theorem bp_normalize_base_set:
  set (MAP ptr_base (bp_normalize ps)) = set (MAP ptr_base ps)
Proof
  simp[EXTENSION, MEM_MAP] >> gen_tac >> eq_tac
  >- metis_tac[MEM_bp_normalize]
  >> rpt strip_tac >> drule bp_normalize_covers >> strip_tac >>
  gvs[ptr_base_def] >> metis_tac[ptr_base_def]
QED

Theorem bp_assign_base_transfer:
  inst_output inst = SOME out /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [Var src] ==>
  bp_bases (SND (bp_handle_inst r inst)) out = bp_bases r src
Proof
  rpt strip_tac >>
  simp[bp_bases_def, bp_handle_inst_def, bp_get_ptrs_update]
QED

Theorem bp_add_base_transfer:
  inst_output inst = SOME out /\ inst.inst_opcode = ADD /\
  inst.inst_operands = [Var x; Var y] /\
  bp_get_ptrs r x <> [] /\ bp_get_ptrs r y = [] ==>
  bp_bases (SND (bp_handle_inst r inst)) out = bp_bases r x
Proof
  rpt strip_tac >>
  simp[bp_bases_def, bp_handle_inst_def, bp_get_ptrs_update, MAP_MAP_o, o_DEF] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[] >> Cases >> rename1 `Ptr a off` >> Cases_on `off` >> simp[offset_by_def, ptr_base_def]
QED

(* ALLOCA caches sites within a frame; a loop does not create new instances. *)
Theorem exec_alloca_cached_site:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  exec_alloca inst s n = OK (update_var out (n2w b) s)
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def]
QED

Theorem exec_alloca_cached_frame:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  exec_alloca inst s n = OK s' ==>
  s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >>
  gvs[venomExecSemanticsTheory.exec_alloca_def, venomStateTheory.update_var_def]
QED

Theorem setup_callee_empty_allocas:
  setup_callee fn args caller = SOME callee ==>
  callee.vs_allocas = FEMPTY
Proof
  rw[venomExecSemanticsTheory.setup_callee_def] >> gvs[]
QED

Theorem bp_sub_base_transfer:
  inst_output inst = SOME out /\ inst.inst_opcode = SUB /\
  inst.inst_operands = [Var x; Var y] /\
  bp_get_ptrs r x <> [] /\ bp_get_ptrs r y = [] ==>
  bp_bases (SND (bp_handle_inst r inst)) out = bp_bases r x
Proof
  rpt strip_tac >>
  simp[bp_bases_def, bp_handle_inst_def, bp_get_ptrs_update, MAP_MAP_o, o_DEF] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[] >> Cases >>
  rename1 `Ptr a off` >> Cases_on `off` >>
  simp[offset_by_def, ptr_base_def]
QED

Theorem bp_phi_base_transfer:
  inst_output inst = SOME out /\ inst.inst_opcode = PHI ==>
  bp_bases (SND (bp_handle_inst r inst)) out =
    bp_bases r out UNION
    BIGUNION (set (MAP (bp_bases r) (MAP SND (phi_pairs inst.inst_operands))))
Proof
  rpt strip_tac >>
  `bp_bases (SND (bp_handle_inst r inst)) out =
   set (MAP ptr_base (bp_normalize (bp_get_ptrs r out ++
     FLAT (MAP (bp_get_ptrs r) (MAP SND (phi_pairs inst.inst_operands))))))`
    by (simp[bp_handle_inst_def] >>
        Cases_on `bp_normalize (bp_get_ptrs r out ++
          FLAT (MAP (bp_get_ptrs r) (MAP SND (phi_pairs inst.inst_operands)))) = []`
        >- gvs[bp_normalize_eq_nil, bp_bases_def] >>
        simp[bp_bases_def, bp_get_ptrs_update]) >>
  asm_rewrite_tac[] >>
  simp[bp_normalize_base_set, bp_bases_def, MAP_APPEND, MAP_FLAT,
       MAP_MAP_o, o_DEF, LIST_TO_SET_APPEND, LIST_TO_SET_FLAT]
QED

(* A false flag preserves lookups, not necessarily the finite map's domain.
   Instruction and block versions are bp_handle_inst_stable_ptrs and
   bp_process_block_unchanged in basePtrProofsTheory. *)
Theorem bp_one_pass_aux_stable_ptrs:
  !order fn bp.
    FST (bp_one_pass_aux fn bp order) = F ==>
    !v. bp_get_ptrs (SND (bp_one_pass_aux fn bp order)) v = bp_get_ptrs bp v
Proof
  Induct >> simp[bp_one_pass_aux_def] >> rpt gen_tac >>
  Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks`
  >- (simp[] >> metis_tac[]) >>
  rename1 `_ = SOME bb` >>
  Cases_on `bp_process_block bp bb.bb_instructions` >>
  rename1 `_ = (c1,r1)` >>
  Cases_on `bp_one_pass_aux fn r1 order` >>
  rename1 `_ = (c2,r2)` >>
  simp[] >> strip_tac >>
  `FST (bp_process_block bp bb.bb_instructions) = F` by simp[] >>
  drule bp_process_block_unchanged >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`fn`,`r1`] mp_tac) >> simp[]
QED

Theorem bp_one_pass_stable_ptrs:
  FST (bp_one_pass fn order bp) = F ==>
  !v. bp_get_ptrs (SND (bp_one_pass fn order bp)) v = bp_get_ptrs bp v
Proof
  simp[bp_one_pass_def, bp_one_pass_aux_stable_ptrs]
QED

Theorem bp_iterate_fuel_fixed:
  !n fn order bp.
    bp_one_pass fn order bp = (F,bp) ==>
    bp_iterate_fuel n fn order bp = bp
Proof
  Induct >> simp[bp_iterate_fuel_def]
QED
