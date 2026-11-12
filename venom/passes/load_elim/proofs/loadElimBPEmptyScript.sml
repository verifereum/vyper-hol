Theory loadElimBPEmpty
Ancestors
  finite_map pred_set list basePtrDefs venomInst venomExecProps dfIterateDefs While loadElimAllocationExclusion venomWf

Definition le_bp_empty_writes_def:
  le_bp_empty_writes inst =
    {out | inst.inst_opcode = ASSIGN /\ inst_output inst = SOME out /\
           ?src. inst.inst_operands = [Var src]}
End

Theorem le_bp_empty_lookup:
  (!v. bp_get_ptrs r v = []) <=>
  (!v ps. FLOOKUP r v = SOME ps ==> ps = [])
Proof
  simp[bp_get_ptrs_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then `v` mp_tac) >> simp[])
  >> Cases_on `FLOOKUP r v` >> simp[] >> metis_tac[]
QED

Theorem le_bp_empty_phi:
  (!v. bp_get_ptrs r v = []) ==>
  bp_normalize (FLAT (MAP (bp_get_ptrs r) vs)) = []
Proof
  strip_tac >> simp[bp_normalize_def, MAP_EQ_f, FLAT_EQ_NIL, EVERY_MAP,
                    EVERY_MEM]
QED

Theorem le_bp_empty_transfer_form:
  (!v. bp_get_ptrs r v = []) /\ inst.inst_opcode <> ALLOCA ==>
  SND (bp_handle_inst r inst) =
    case inst_output inst of
      NONE => r
    | SOME out => if inst.inst_opcode = ASSIGN /\
                      (?src. inst.inst_operands = [Var src])
                  then r |+ (out, []) else r
Proof
  strip_tac >> Cases_on `inst_output inst` >> simp[bp_handle_inst_def]
  >> Cases_on `inst.inst_opcode`
  >> gvs[bp_handle_inst_def, le_bp_empty_phi]
  >> namedCases_on `inst.inst_operands` ["", "a rest"] >> gvs[]
  >> Cases_on `a` >> gvs[]
  >> namedCases_on `rest` ["", "b tail"] >> gvs[]
  >> Cases_on `b` >> gvs[]
  >> Cases_on `tail` >> gvs[]
QED

Theorem le_bp_empty_transfer:
  (!v. bp_get_ptrs r v = []) /\ inst.inst_opcode <> ALLOCA ==>
  (!v. bp_get_ptrs (SND (bp_handle_inst r inst)) v = [])
Proof
  strip_tac >> drule_all le_bp_empty_transfer_form >> disch_then SUBST1_TAC
  >> Cases_on `inst_output inst` >> simp[]
  >> IF_CASES_TAC >> simp[]
  >> gen_tac >> Cases_on `x = v`
  >> gvs[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

Theorem le_bp_empty_transfer_domain:
  (!v. bp_get_ptrs r v = []) /\ inst.inst_opcode <> ALLOCA ==>
  FDOM (SND (bp_handle_inst r inst)) =
    FDOM r UNION le_bp_empty_writes inst
Proof
  strip_tac >> drule_all le_bp_empty_transfer_form >> disch_then SUBST1_TAC
  >> Cases_on `inst_output inst` >> simp[le_bp_empty_writes_def]
  >> IF_CASES_TAC >> gvs[EXTENSION] >> metis_tac[]
QED

Theorem le_bp_empty_ext:
  (!v. bp_get_ptrs r v = []) /\
  (!v. bp_get_ptrs r' v = []) /\ FDOM r = FDOM r' ==>
  r = r'
Proof
  simp[le_bp_empty_lookup, fmap_eq_flookup] >> rpt strip_tac
  >> Cases_on `FLOOKUP r x` >> Cases_on `FLOOKUP r' x`
  >> gvs[FLOOKUP_DEF, AllCaseEqs()] >> metis_tac[]
QED

Definition le_bp_block_empty_writes_def:
  le_bp_block_empty_writes insts = BIGUNION (IMAGE le_bp_empty_writes (set insts))
End

Definition le_bp_pass_empty_writes_def:
  le_bp_pass_empty_writes fn [] = {} /\
  le_bp_pass_empty_writes fn (lbl::lbls) =
    case FIND (\bb. bb.bb_label = lbl) fn.fn_blocks of
      NONE => le_bp_pass_empty_writes fn lbls
    | SOME bb => le_bp_block_empty_writes bb.bb_instructions UNION
                 le_bp_pass_empty_writes fn lbls
End

Theorem le_bp_empty_block:
  !insts r.
    (!v. bp_get_ptrs r v = []) /\
    EVERY (\inst. inst.inst_opcode <> ALLOCA) insts ==>
    (!v. bp_get_ptrs (SND (bp_process_block r insts)) v = []) /\
    FDOM (SND (bp_process_block r insts)) =
      FDOM r UNION le_bp_block_empty_writes insts
Proof
  Induct >> simp[bp_process_block_def, le_bp_block_empty_writes_def]
  >> rpt strip_tac
  >> drule_all le_bp_empty_transfer_domain >> strip_tac
  >> drule_all le_bp_empty_transfer >> strip_tac
  >> first_x_assum drule_all >> strip_tac
  >> Cases_on `bp_handle_inst r h`
  >> Cases_on `bp_process_block (SND (bp_handle_inst r h)) insts`
  >> gvs[bp_process_block_def, le_bp_block_empty_writes_def,
         UNION_ASSOC]
QED

Theorem le_bp_empty_pass_aux:
  !order r.
    (!v. bp_get_ptrs r v = []) /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
               inst.inst_opcode <> ALLOCA) ==>
    (!v. bp_get_ptrs (SND (bp_one_pass_aux fn r order)) v = []) /\
    FDOM (SND (bp_one_pass_aux fn r order)) =
      FDOM r UNION le_bp_pass_empty_writes fn order
Proof
  Induct >> simp[bp_one_pass_aux_def, le_bp_pass_empty_writes_def]
  >> rpt gen_tac >> strip_tac
  >> Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks`
  >- (simp[bp_one_pass_aux_def, le_bp_pass_empty_writes_def] >>
      first_x_assum irule >> metis_tac[])
  >> `MEM x fn.fn_blocks` by metis_tac[FIND_MEM]
  >> `EVERY (\inst. inst.inst_opcode <> ALLOCA) x.bb_instructions` by
       (simp[EVERY_MEM] >> metis_tac[])
  >> drule_all le_bp_empty_block >> strip_tac
  >> first_x_assum drule_all >> strip_tac
  >> Cases_on `bp_process_block r x.bb_instructions`
  >> Cases_on `bp_one_pass_aux fn (SND (bp_process_block r x.bb_instructions)) order`
  >> gvs[bp_one_pass_aux_def, le_bp_pass_empty_writes_def, UNION_ASSOC]
QED

Theorem le_bp_empty_pass:
  (!v. bp_get_ptrs r v = []) /\
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
             inst.inst_opcode <> ALLOCA) ==>
  (!v. bp_get_ptrs (SND (bp_one_pass fn order r)) v = []) /\
  FDOM (SND (bp_one_pass fn order r)) =
    FDOM r UNION le_bp_pass_empty_writes fn order
Proof
  rewrite_tac[bp_one_pass_def] >> metis_tac[le_bp_empty_pass_aux]
QED

Theorem le_bp_empty_pass_idempotent:
  (!v. bp_get_ptrs r v = []) /\
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
             inst.inst_opcode <> ALLOCA) ==>
  SND (bp_one_pass fn order (SND (bp_one_pass fn order r))) =
    SND (bp_one_pass fn order r)
Proof
  strip_tac >> drule_all le_bp_empty_pass
  >> disch_then (qspec_then `order` strip_assume_tac)
  >> drule_all le_bp_empty_pass
  >> disch_then (qspec_then `order` strip_assume_tac)
  >> irule le_bp_empty_ext >> simp[EXTENSION] >> metis_tac[]
QED

Theorem le_df_iterate_one_step:
  f (f x) = f x ==> df_iterate f x = f x
Proof
  strip_tac >> simp[df_iterate_def]
  >> once_rewrite_tac[WHILE]
  >> Cases_on `f x = x` >> simp[]
  >> once_rewrite_tac[WHILE] >> simp[]
QED

Theorem le_bp_analyze_empty:
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
             inst.inst_opcode <> ALLOCA) ==>
  (!v. bp_get_ptrs (bp_analyze cfg fn) v = [])
Proof
  strip_tac
  >> `!v. bp_get_ptrs FEMPTY v = []` by simp[bp_get_ptrs_def]
  >> drule_all le_bp_empty_pass_idempotent
  >> disch_then (qspec_then `cfg.cfg_dfs_pre` assume_tac)
  >> drule_all le_bp_empty_pass
  >> disch_then (qspec_then `cfg.cfg_dfs_pre` strip_assume_tac)
  >> simp[bp_analyze_def, le_df_iterate_one_step]
QED

Theorem le_step_preserves_analyze_empty:
  fn_inst_wf fn /\ le_step_preserves bp dfg fn /\
  bp_assigns_stable bp dfg /\ dfg_assigns_sound dfg s ==>
  (!v. bp_get_ptrs (bp_analyze cfg fn) v = [])
Proof
  strip_tac >> irule le_bp_analyze_empty >> rpt gen_tac >> strip_tac
  >> irule le_step_preserves_no_alloca
  >> gvs[fn_inst_wf_def] >> metis_tac[]
QED

Theorem le_bp_empty_ptr_from_op:
  (!v. bp_get_ptrs bp v = []) ==> bp_ptr_from_op bp op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[bp_ptr_from_op_def]
QED

Theorem le_step_preserves_analyze_ptr_none:
  fn_inst_wf fn /\ le_step_preserves bp dfg fn /\
  bp_assigns_stable bp dfg /\ dfg_assigns_sound dfg s ==>
  bp_ptr_from_op (bp_analyze cfg fn) op = NONE
Proof
  strip_tac >> irule le_bp_empty_ptr_from_op
  >> metis_tac[le_step_preserves_analyze_empty]
QED
