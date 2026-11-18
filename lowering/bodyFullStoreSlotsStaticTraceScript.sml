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

Theorem store_slots_observer_first_cut:
  cs_extends sa sb /\ fn_has_code sa sb func /\ frag_gas_free sa sb /\
  EVERY (\i. MEM i.inst_opcode
    [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ;SSTORE;TSTORE;INVALID])
    (frag_code sa sb) /\
  (!i lbl. MEM i (frag_code sa sb) /\ MEM i.inst_opcode [JMP;JNZ] /\
    MEM (Label lbl) i.inst_operands ==>
    lbl <> sa.cs_current_bb /\
    ?bb. lookup_block lbl (frag_observer sa sb func id).fn_blocks = SOME bb) /\
  (!i x. MEM i (frag_code sa sb) /\ MEM x i.inst_outputs ==>
    ~not_fresh_at sa x) /\
  (!i. MEM i (frag_code sa sb) /\ MEM i.inst_opcode [SSTORE;TSTORE] ==>
    i.inst_opcode = (if tr then TSTORE else SSTORE)) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_origin_ptr_path (D,lo,explicit,ctx,frag_observer sa sb func id,PG)
    (s,G,tn) [] (OK t,Gf,tnf) /\
  (t.vs_current_bb,t.vs_inst_idx) = frag_observer_cut sb ==>
  ?L k. L <> [] /\ HD L = (s,G,tn) /\ LAST L = (t,Gf,tnf) /\
    k < LENGTH L /\
    (!n a Ga tna b Gb tnb.
      SUC n < LENGTH L /\ EL n L = (a,Ga,tna) /\
      EL (SUC n) L = (b,Gb,tnb) ==>
      gas_origin_ptr_edge (D,lo,explicit,ctx,frag_observer sa sb func id,PG)
        (a,Ga,tna) [] (OK b,Gb,tnb)) /\
    (!n a Ga tna. n <= k /\ EL n L = (a,Ga,tna) ==>
      (a.vs_current_bb,a.vs_inst_idx) IN frag_observer_region sa sb) /\
    (!n a Ga tna. n < k /\ EL n L = (a,Ga,tna) ==>
      (a.vs_current_bb,a.vs_inst_idx) <> frag_observer_cut sb /\
      ?bb i. lookup_block a.vs_current_bb (frag_observer sa sb func id).fn_blocks = SOME bb /\
        get_instruction bb a.vs_inst_idx = SOME i /\ MEM i (frag_code sa sb) /\
        MEM i.inst_opcode [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ] /\
        (!x. MEM x i.inst_outputs ==> ~not_fresh_at sa x)) /\
    (!a Ga tna. EL k L = (a,Ga,tna) ==>
      (a.vs_current_bb,a.vs_inst_idx) = frag_observer_cut sb \/
      (SUC k < LENGTH L /\
       ?bb i. lookup_block a.vs_current_bb (frag_observer sa sb func id).fn_blocks = SOME bb /\
         get_instruction bb a.vs_inst_idx = SOME i /\ MEM i (frag_code sa sb) /\
         i.inst_opcode = (if tr then TSTORE else SSTORE)))
Proof
  strip_tac >> drule store_slots_path_finite >>
  disch_then (qspecl_then [`t`,`Gf`,`tnf`] mp_tac) >> simp[] >> strip_tac >>
  qabbrev_tac `P = \n. n < LENGTH L /\
    ((FST (EL n L)).vs_current_bb,(FST (EL n L)).vs_inst_idx) = frag_observer_cut sb \/
    n < LENGTH L /\ ?bb i.
      lookup_block (FST (EL n L)).vs_current_bb (frag_observer sa sb func id).fn_blocks = SOME bb /\
      get_instruction bb (FST (EL n L)).vs_inst_idx = SOME i /\
      MEM i.inst_opcode [SSTORE;TSTORE]` >>
  `?n. P n` by suspend "candidate" >>
  qspec_then `P` mp_tac WOP >>
  (impl_tac >- metis_tac[]) >> qpat_x_assum `P _` kall_tac >>
  strip_tac >> rename1 `P k` >>
  `k < LENGTH L` by (gvs[Abbr `P`]) >>
  `!n a Ga tna. n <= k /\ EL n L = (a,Ga,tna) ==>
    (a.vs_current_bb,a.vs_inst_idx) IN frag_observer_region sa sb`
    by suspend "region" >>
  qexistsl_tac [`L`,`k`] >> simp[] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "readonly" >>
  suspend "terminal"
QED

Resume store_slots_observer_first_cut[candidate]:
  `EL (LENGTH L - 1) L = (t,Gf,tnf)` by
    metis_tac[LAST_EL, PRE_SUB1] >>
  `0 < LENGTH L` by (Cases_on `L` >> gvs[]) >>
  qexists_tac `LENGTH L - 1` >> simp[Abbr `P`]
QED

Resume store_slots_observer_first_cut[region]:
  Induct_on `n`
  >- (rpt strip_tac >> `EL 0 L = (s,G,tn)` by (Cases_on `L` >> gvs[]) >>
      gvs[] >> metis_tac[frag_observer_start_region]) >>
  rpt strip_tac >>
  Cases_on `EL n L` >> rename1 `EL n L = (a0,rest)` >>
  Cases_on `rest` >> rename1 `EL n L = (a0,Ga0,tna0)` >>
  `(a0.vs_current_bb,a0.vs_inst_idx) IN frag_observer_region sa sb` by
    (first_x_assum irule >> simp[] >> decide_tac) >>
  `(a0.vs_current_bb,a0.vs_inst_idx) <> frag_observer_cut sb` by
    (qpat_x_assum `!m. m < k ==> ~P m` (qspec_then `n` mp_tac) >>
     simp[Abbr `P`] >> decide_tac) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,frag_observer sa sb func id,PG)
    (a0,Ga0,tna0) [] (OK a,Ga,tna)` by
    (first_x_assum irule >> qexists_tac `n` >> simp[] >> decide_tac) >>
  `abi_observer_step ctx (frag_observer sa sb func id) (frag_observer_cut sb) a0 a`
    by (irule store_slots_observer_edge_step >> metis_tac[]) >>
  drule_all frag_observer_region_closed >>
  simp[observer_region_closed_def] >> metis_tac[]
QED

Resume store_slots_observer_first_cut[readonly]:
  rpt strip_tac >>
  `n < LENGTH L /\ SUC n < LENGTH L` by decide_tac >>
  qpat_x_assum `!m. m < k ==> ~P m` (qspec_then `n` mp_tac) >>
  simp[Abbr `P`] >> strip_tac >>
  `(a.vs_current_bb,a.vs_inst_idx) IN frag_observer_region sa sb` by
    (first_x_assum irule >> qexistsl_tac [`Ga`,`n`,`tna`] >> simp[]) >>
  Cases_on `EL (SUC n) L` >> rename1 `EL (SUC n) L = (b,rest)` >>
  Cases_on `rest` >> rename1 `EL (SUC n) L = (b,Gb,tnb)` >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,frag_observer sa sb func id,PG)
    (a,Ga,tna) [] (OK b,Gb,tnb)` by metis_tac[] >>
  `abi_observer_step ctx (frag_observer sa sb func id) (frag_observer_cut sb) a b`
    by (irule store_slots_observer_edge_step >> metis_tac[]) >>
  pop_assum mp_tac >> simp[abi_observer_step_def] >> strip_tac >>
  `MEM inst (frag_code sa sb)` by metis_tac[frag_observer_code_provenance] >>
  `inst.inst_opcode <> INVALID` by
    metis_tac[deadStoreElimAssertionStepsTheory.dse_invalid_abort, exec_result_distinct] >>
  qexistsl_tac [`bb`,`inst`] >> simp[] >>
  qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then (qspec_then `inst` mp_tac) >> simp[] >> metis_tac[]
QED

Resume store_slots_observer_first_cut[terminal]:
  rpt strip_tac >>
  Cases_on `(a.vs_current_bb,a.vs_inst_idx) = frag_observer_cut sb` >> simp[] >>
  `SUC k < LENGTH L` by
    (spose_not_then assume_tac >>
     `k = LENGTH L - 1` by decide_tac >>
     `EL k L = LAST L` by metis_tac[LAST_EL, PRE_SUB1] >> gvs[]) >>
  `(a.vs_current_bb,a.vs_inst_idx) IN frag_observer_region sa sb` by
    (first_x_assum irule >> qexistsl_tac [`Ga`,`k`,`tna`] >> simp[]) >>
  qpat_x_assum `P k` mp_tac >> simp[Abbr `P`] >> strip_tac >>
  `MEM i (frag_code sa sb)` by metis_tac[frag_observer_code_provenance] >>
  qexistsl_tac [`bb`,`i`] >> simp[] >>
  qpat_x_assum `!i. MEM i _ /\ _ ==> _` (qspec_then `i` mp_tac) >> simp[]
QED

Finalise store_slots_observer_first_cut
