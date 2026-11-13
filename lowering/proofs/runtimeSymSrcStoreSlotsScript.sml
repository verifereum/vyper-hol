Theory runtimeSymSrcStoreSlots
Ancestors
  runtimeSymSrcStoreSlotsStatic runtimeSymSrcStoreSlotsLoop
  runtimeSymSrcContextCopy runtimeSymSrcContext runtimeSymSrcEmission
  context compileEnv emitHelper list venomInst stackPlanTypes

Theorem runtime_sym_store_slots_all[local]:
  (!cenv src slot ty tr. !s u s'.
    ~is_label_operand src /\ ~is_label_operand slot /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_slots cenv src slot ty tr s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!cenv src slot members mo so tr. !s u s'.
    ~is_label_operand src /\ ~is_label_operand slot /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_slots_members cenv src slot members mo so tr s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!cenv src slot elem count_op tr. !s u s'.
    ~is_label_operand src /\ ~is_label_operand slot /\
    ~is_label_operand count_op /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_copy_elements_to_slots cenv src slot elem count_op tr s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s'))
Proof
  ho_match_mp_tac compile_store_slots_ind >> rpt conj_tac
  >- suspend "store"
  >- (simp[Once compile_store_slots_def, comp_return_def] >> rpt strip_tac >> gvs[])
  >- suspend "members"
  >> rpt strip_tac >> irule runtime_sym_copy_elements_to_slots_step >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Resume runtime_sym_store_slots_all[members]:
  rpt strip_tac >>
  qpat_x_assum `compile_store_slots_members _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, Once compile_store_slots_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qpat_x_assum `compile_lit_byte_offset src _ _ = _`
    (mp_then Any mp_tac runtime_sym_lit_byte_offset) >> simp[] >> strip_tac >>
  qpat_x_assum `compile_lit_byte_offset slot _ _ = _`
    (mp_then Any mp_tac runtime_sym_lit_byte_offset) >> simp[] >> strip_tac >>
  qpat_x_assum `!a b st st'. _` (fn ih =>
    qpat_assum `compile_store_slots _ _ _ _ _ _ = _`
      (mp_then Any mp_tac ih)) >> simp[] >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Resume runtime_sym_store_slots_all[store]:
  rpt strip_tac >>
  Cases_on `is_abi_dynamic cenv.ce_struct_fields ty`
  >- (Cases_on `is_bytestring_type ty`
      >- (drule_all runtime_sym_store_slots_bytestring >> simp[]) >>
      qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
      simp[NoAsms, Once compile_store_slots_def] >>
      Cases_on `acyclic_struct_metadata cenv.ce_struct_fields` >>
      qpat_assum `is_abi_dynamic _ _` (fn th => rewrite_tac[th]) >>
      qpat_assum `~is_bytestring_type _` (fn th => rewrite_tac[th]) >>
      first_assum (fn th => CHANGED_TAC (rewrite_tac[th]))
      >- (Cases_on `ty` >> simp[NoAsms] >>
          rule_assum_tac (SIMP_RULE (srw_ss()) [])
          >- (strip_tac >> qpat_x_assum `emit_void _ _ _ = _`
              (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]) 
          >- (strip_tac >> first_x_assum drule_all >> simp[]) 
          >- (rename1 `ArrayT elem sz` >> Cases_on `sz` >>
              simp[NoAsms] >> rule_assum_tac (SIMP_RULE (srw_ss()) [])
              >- (strip_tac >> first_x_assum irule >> simp[is_label_operand_def] >>
                  goal_assum (drule_at Any) >> simp[]) >>
              suspend "dynamic")
          >- (strip_tac >> first_x_assum drule_all >> simp[]) 
          >> strip_tac >> qpat_x_assum `emit_void _ _ _ = _`
              (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]) >>
      rpt (qpat_x_assum `!store_opc store_loc. _` kall_tac) >>
      strip_tac >> qpat_x_assum `emit_void _ _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]) >>
  drule_all runtime_sym_store_slots_static >> simp[]
QED

Resume runtime_sym_store_slots_all[dynamic]:
  qpat_x_assum `!src slot count_op. _` mp_tac >> simp[] >> disch_tac >>
  simp[NoAsms, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qpat_x_assum `emit_op MLOAD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_op ADD [src; _] _ = _`
    (mp_then (Pat `emit_op _ _ _ = _`) mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_op ADD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `!src slot count_op s s'. _` drule_all >> strip_tac >>
  qpat_x_assum `emit_void _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >>
  Cases_on `tr` >> simp[]
QED

Finalise runtime_sym_store_slots_all

Theorem runtime_sym_store_slots:
  ~is_label_operand src /\ ~is_label_operand slot /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_slots cenv src slot ty tr s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[CONJUNCT1 runtime_sym_store_slots_all]
QED

Theorem runtime_sym_store_slots_members:
  ~is_label_operand src /\ ~is_label_operand slot /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_slots_members cenv src slot members mo so tr s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[CONJUNCT1 (CONJUNCT2 runtime_sym_store_slots_all)]
QED

Theorem runtime_sym_copy_elements_to_slots:
  ~is_label_operand src /\ ~is_label_operand slot /\
  ~is_label_operand count_op /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_copy_elements_to_slots cenv src slot elem count_op tr s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[CONJUNCT2 (CONJUNCT2 runtime_sym_store_slots_all)]
QED
