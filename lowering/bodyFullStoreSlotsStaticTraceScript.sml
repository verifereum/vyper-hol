Theory bodyFullStoreSlotsStaticTrace
Ancestors
  fragGasOriginPtr fragGasOrigin fragGasPathPtr fragExec
  exprSimAbiGasBridge abiEncoderObserver exprSimAbiDecodeSetupObserve
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst
  contextCodegenRel codegenRel unitTransformDefs
  list rich_list finite_map arithmetic

Theorem store_slots_path_finite:
  !cx st marks out.
    gas_origin_ptr_path cx st marks out ==>
    !t Gf tnf. marks = [] /\ out = (OK t,Gf,tnf) ==>
    ?L. L <> [] /\ HD L = st /\ LAST L = (t,Gf,tnf) /\
      (!n a Ga tna b Gb tnb.
        SUC n < LENGTH L /\ EL n L = (a,Ga,tna) /\
        EL (SUC n) L = (b,Gb,tnb) ==>
        gas_origin_ptr_edge cx (a,Ga,tna) [] (OK b,Gb,tnb))
Proof
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> qexists_tac `[(s,G,tn)]` >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
      qexists_tac `(s,G,tn)::L` >> simp[] >>
      conj_tac >- (Cases_on `L` >> gvs[]) >>
      rpt gen_tac >> Cases_on `n` >> simp[] >> rpt strip_tac
      >- (Cases_on `L` >> gvs[]) >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >> rpt strip_tac >> gvs[exit_result_def]
QED

Theorem store_slots_observer_edge_step:
  cs_extends sa sb /\ fn_has_code sa sb func /\ frag_gas_free sa sb /\
  EVERY (\i. MEM i.inst_opcode
    [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ;SSTORE;TSTORE;INVALID])
    (frag_code sa sb) /\
  (!i lbl. MEM i (frag_code sa sb) /\ MEM i.inst_opcode [JMP;JNZ] /\
    MEM (Label lbl) i.inst_operands ==>
    lbl <> sa.cs_current_bb /\
    ?bb. lookup_block lbl (frag_observer sa sb func id).fn_blocks = SOME bb) /\
  (a.vs_current_bb,a.vs_inst_idx) IN frag_observer_region sa sb /\
  (a.vs_current_bb,a.vs_inst_idx) <> frag_observer_cut sb /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,frag_observer sa sb func id,PG)
    (a,Ga,tna) [] (OK b,Gb,tnb) ==>
  abi_observer_step ctx (frag_observer sa sb func id) (frag_observer_cut sb) a b
Proof
  strip_tac >> drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `fuel` (qx_choose_then `bb` (qx_choose_then `i`
      (qx_choose_then `middle` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  `MEM i (frag_code sa sb)` by metis_tac[frag_observer_code_provenance] >>
  `i.inst_opcode <> INVOKE` by metis_tac[frag_observer_off_cut_opcodes] >>
  `step_inst 0 ctx i a = middle` by metis_tac[step_inst_non_invoke] >>
  qpat_x_assum `(?t. middle = OK t /\ _) \/ _` mp_tac >>
  strip_tac
  >- (gvs[] >> simp[abi_observer_step_def] >> metis_tac[])
  >- gvs[]
  >- (gvs[] >> simp[abi_observer_step_def] >> metis_tac[])
  >- (gvs[] >>
      `MEM i.inst_opcode [JMP;JNZ]` by
        (qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
         disch_then (qspec_then `i` mp_tac) >> simp[] >>
         strip_tac >> gvs[is_terminator_def] >>
         metis_tac[deadStoreElimAssertionStepsTheory.dse_invalid_abort,
                   exec_result_distinct]) >>
      `MEM (Label lbl) i.inst_operands` by
        (spose_not_then assume_tac >>
         `step_inst_base i a = OK (jump_to lbl a)` by
           metis_tac[step_inst_non_invoke] >>
         `MEM i.inst_opcode [JMP;JNZ;DJMP]` by fs[] >>
         drule_all frag_observer_jump_no_reentry >> simp[jump_to_def]) >>
      `lbl <> sa.cs_current_bb /\
       ?target. lookup_block lbl (frag_observer sa sb func id).fn_blocks = SOME target`
        by (fs[MEM] >> metis_tac[]) >>
      `phi_prefix_length target.bb_instructions = 0` by
        metis_tac[abi_decode_observer_nonentry_phi_zero] >>
      `eval_phis (jump_to lbl a) target.bb_instructions = OK (jump_to lbl a)` by
        metis_tac[eval_phis_no_phi] >>
      simp[abi_observer_step_def, jump_to_def] >>
      qexists_tac `jump_to lbl a` >> simp[jump_to_def, eval_phis_no_phi]) >>
  qpat_x_assum `OK b = middle` (assume_tac o SYM) >>
  gvs[exit_result_def]
QED
