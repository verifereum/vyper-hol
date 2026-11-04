(* Local provenance boundaries; not a reachable-frame coherence theorem. *)
Theory o1LowerDloadGhost
Ancestors
  lowerDloadClassify venomExecProps o1LowerDloadClosure ptrDiscipline finite_map pointerConfinedDefs venomInst memLocDefs pred_set list

Theorem first_prov_origin:
  !ops G site. first_prov G ops = SOME site ==>
    ?v. MEM (Var v) ops /\ FLOOKUP G v = SOME site
Proof
  Induct >> simp[first_prov_def] >> rpt gen_tac >>
  Cases_on `op_prov G h` >> simp[]
  >- metis_tac[] >>
  Cases_on `h` >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem step_prov_origin:
  MEM inst (fn_insts fn) /\
  (!k site. k < LENGTH PG /\ EL k PG = SOME site ==> k IN P fn.fn_name) /\
  FLOOKUP (step_prov PG G inst s') v = SOME site ==>
  (FLOOKUP G v = SOME site /\ ~MEM v inst.inst_outputs) \/
  v IN ptr_roots P fn \/
  (MEM v inst.inst_outputs /\
   (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/ inst.inst_opcode = ASSIGN) /\
   ?u. MEM (Var u) inst.inst_operands /\ FLOOKUP G u = SOME site)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_outputs` >>
  gvs[step_prov_def, set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >>
  gvs[step_prov_def, set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `out_prov PG G inst s'` >>
  gvs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, AllCaseEqs()] >>
  `inst_output inst = SOME h` by simp[inst_output_def] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (disj1_tac >> simp[ptr_roots_def, alloca_roots_def] >>
      metis_tac[inst_output_def]) >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (disj1_tac >> simp[ptr_roots_def] >>
      metis_tac[inst_output_def]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[out_prov_def, AllCaseEqs()] >>
      simp[ptr_roots_def] >>
      metis_tac[inst_output_def]) >>
  gvs[out_prov_def, AllCaseEqs()] >>
  metis_tac[first_prov_origin]
QED

Theorem ret_operand_not_pointer:
  ptr_use_ok P pv inst /\ inst.inst_opcode = RET /\
  MEM (Var v) inst.inst_operands ==> v NOTIN pv
Proof
  rw[ptr_use_ok_def, is_pointer_preserving_op_def] >>
  first_x_assum (qspec_then `v` mp_tac) >>
  simp[mem_write_ops_def, mem_read_ops_def, is_pointer_preserving_op_def]
QED

Theorem ret_operand_untainted:
  taint_ok fn tn inst s /\ inst.inst_opcode = RET /\
  MEM op inst.inst_operands ==> op_taint tn op = {}
Proof
  rw[taint_ok_def] >>
  qpat_x_assum `!op. MEM op _ /\ _ ==> _` (qspec_then `op` mp_tac) >>
  simp[]
QED

Theorem ret_operand_no_provenance:
  ptr_use_ok P (fn_pv P fn) inst /\ inst.inst_opcode = RET /\
  FDOM G SUBSET fn_pv P fn /\ MEM op inst.inst_operands ==>
  op_prov G op = NONE
Proof
  rpt strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  drule_all ret_operand_not_pointer >>
  fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem step_prov_support:
  FDOM G SUBSET fn_pv P fn /\
  (!k site. k < LENGTH PG /\ EL k PG = SOME site ==> k IN P fn.fn_name) /\
  MEM inst (fn_insts fn) ==>
  FDOM (step_prov PG G inst s') SUBSET fn_pv P fn
Proof
  rpt strip_tac >> simp[SUBSET_DEF] >> rpt strip_tac >>
  rename1 `v IN FDOM (step_prov PG G inst s')` >>
  `?site. FLOOKUP (step_prov PG G inst s') v = SOME site` by
    metis_tac[FLOOKUP_DEF, optionTheory.IS_SOME_EXISTS] >>
  drule_all step_prov_origin >> strip_tac
  >- (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) 
  >- metis_tac[ptr_roots_subset_fn_pv, SUBSET_DEF] >>
  `u IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  metis_tac[fn_pv_forward, is_pointer_preserving_op_def]
QED

Theorem phis_prov_support:
  !insts. EVERY (\i. MEM i (fn_insts fn)) insts /\
    FDOM G SUBSET fn_pv P fn ==>
    FDOM (phis_prov prev G insts) SUBSET fn_pv P fn
Proof
  Induct >> simp[phis_prov_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phis_prov_def] >>
  `FDOM (phis_prov prev G insts) SUBSET fn_pv P fn` by metis_tac[] >>
  Cases_on `h.inst_outputs` >>
  gvs[set_prov_def, FDOM_DRESTRICT, SUBSET_DEF] >>
  Cases_on `t` >> gvs[set_prov_def, FDOM_DRESTRICT, SUBSET_DEF] >>
  Cases_on `phi_prov prev G h` >>
  gvs[FDOM_DRESTRICT, SUBSET_DEF] >>
  gvs[phi_prov_def, AllCaseEqs()] >>
  rename1 `resolve_phi lbl h.inst_operands = SOME op` >>
  drule resolve_phi_MEM >> strip_tac >>
  Cases_on `op` >> gvs[op_prov_def] >>
  `s IN fn_pv P fn` by (fs[FLOOKUP_DEF] >> metis_tac[]) >>
  `h' IN fn_pv P fn` by
    (irule fn_pv_forward >> qexistsl_tac [`h`, `s`] >>
     simp[is_pointer_preserving_op_def]) >>
  metis_tac[]
QED

Theorem entry_prov_support:
  FDOM G SUBSET fn_pv P fn ==>
  FDOM (entry_prov fn s G) SUBSET fn_pv P fn
Proof
  strip_tac >> simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  irule phis_prov_support >> simp[] >>
  drule lookup_block_MEM >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[]
QED

Theorem invoke_prov_positions:
  ptr_use_ok P (fn_pv P fn) inst /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\ FDOM G SUBSET fn_pv P fn ==>
  !k site. k < LENGTH (MAP (op_prov G) ops) /\
    EL k (MAP (op_prov G) ops) = SOME site ==> k IN P nm
Proof
  simp[ptr_use_ok_def] >> rpt strip_tac >> gvs[] >>
  gvs[EL_MAP] >>
  Cases_on `EL k ops` >> gvs[op_prov_def] >>
  `s IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  metis_tac[]
QED
