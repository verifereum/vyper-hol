Theory o1CodeEndLowerObservation
Ancestors
  o1CodeEndLowerReadTransport lowerDloadPublicTrace lowerDloadSafetyAmbient
  lowerDloadSafetyValues lowerDloadSafetyRelation lowerDloadSafetyKernel
  lowerDloadSafetyAssemblyPremises o1PassContract contextCodegenRel unitLabelMapIdentity
  memSafeRun memLocDefs pointerConfinedDefs ptrDiscipline venomExecSemantics venomState
  finite_map words list

Theorem lower_dload_offset_equal[local]:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  ((inst.inst_opcode = DLOAD /\ inst.inst_operands = [op]) \/
   (inst.inst_opcode = DLOADBYTES /\
    ?dst len. inst.inst_operands = [dst;op;len])) ==>
  eval_operand op f.lf_src = eval_operand op f.lf_tgt
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `inst.inst_opcode = DLOAD`
  >- (gvs[] >> irule ld_dload_operand_equal >> metis_tac[]) >>
  gvs[] >>
  `MEM op inst.inst_operands` by gvs[] >>
  `!v. op = Var v ==> v NOTIN fn_pv P f.lf_fn` by
    (gen_tac >> disch_tac >> gvs[] >>
     irule ld_dloadbytes_scalar_nonpointer >> metis_tac[]) >>
  `op_prov f.lf_H op = NONE` by
    (irule ld_vars_nonpointer_provenance >> metis_tac[]) >>
  irule ld_vars_operand_equal >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> disch_tac >> conj_tac
  >- (irule ld_inst_input_ir >> metis_tac[]) >> conj_tac
  >- (irule ld_numeric_operand_nonopaque >> simp[] >>
      qexists `inst` >> gvs[]) >>
  `op_taint tn op = {}` by
    (irule ld_numeric_operand_untainted >> simp[] >>
     qexistsl [`f.lf_fn`,`inst`,`f.lf_src`] >> gvs[]) >>
  gvs[op_taint_def]
QED

Theorem lower_dload_sync_section[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
    s.vs_code = v.vs_code /\ s.vs_data_section = v.vs_data_section) C vs ==>
  inst_dload_in_section inst t0 /\ t0.vs_data_section = v.vs_data_section
Proof
  strip_tac >>
  drule_all ld_sync_source_mem_inv >> simp[] >> strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
  `s.vs_data_section = t0.vs_data_section /\ s.vs_labels = t0.vs_labels` by
    (drule ld_sync_memory >> simp[ld_nonghost_def]) >>
  `MEM inst (fn_insts fn) /\ fn_ptr_ok P fn` by
    (conj_tac
     >- (drule ld_sync_source >> strip_tac >>
         gvs[active_inst_def, fn_insts_MEM] >>
         metis_tac[MEM_EL]) >>
     gvs[ld_sync_def, EVERY_MEM] >> metis_tac[]) >>
  conj_tac >-
    (rewrite_tac[inst_dload_in_section_def] >> rpt gen_tac >> strip_tac >>
     `eval_operand op s = eval_operand op t0` by
       (drule lower_dload_offset_equal >> simp[] >>
        metis_tac[]) >>
     qpat_x_assum `inst_dload_in_section inst s` mp_tac >>
     simp[inst_dload_in_section_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem lower_dload_sync_codecopy_bound:
  ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\
  ir_supply_covers_fn f.lf_supply fn /\
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
    s.vs_code = v.vs_code /\ s.vs_data_section = v.vs_data_section) C vs /\
  LENGTH v.vs_data_section < dimword(:256) DIV 2 /\
  ~MEM (Label "code_end") inst.inst_operands /\
  (inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' fn' X p h t0 t /\
  (EL h X).inst_opcode = CODECOPY /\
  (EL h X).inst_operands = [dst; Var x; sz] /\
  eval_operand (Var x) t = SOME w /\
  FLOOKUP t.vs_labels "code_end" = SOME bword ==>
  w2n (w-bword) < dimword(:256) DIV 2
Proof
  strip_tac >>
  drule_all lower_dload_sync_section >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  drule ld_sync_source >> strip_tac >>
  drule_all ld_active_envelope_origin >> strip_tac >>
  `?rest. lower_dload_inst_supply ui inst = (X,rest)` by
    metis_tac[pairTheory.PAIR] >>
  `!z. MEM (Var z) inst.inst_operands ==> MEM z ui.irs_used_vars` by
    metis_tac[ld_inst_input_ir] >>
  `LENGTH t0.vs_data_section < dimword(:256) DIV 2` by metis_tac[] >>
  metis_tac[lower_dload_codecopy_delta]
QED
