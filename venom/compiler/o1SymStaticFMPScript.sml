Theory o1SymStaticFMP
Ancestors
  fmpStepStructural fmpStepPredicateTransport fmpAnalysisProps
  fmpLowerDefs venomInst callLayoutDefs
  list rich_list

Theorem fmp_resolve_invoke_label_origin:
  fmp_resolve_invoke infos ctx inst = SOME (callee,info,args) ==>
  MEM (Label label) (Label callee.fn_name::args) ==>
  MEM (Label label) inst.inst_operands
Proof
  strip_tac >> drule fmp_resolve_invoke_some >> strip_tac >>
  drule lookup_function_name >> simp[]
QED

Theorem fmp_lower_inst_label_origin:
  fmp_lower_inst infos ctx runner s inst = SOME (head,s') ==>
  !i. MEM i head /\ MEM (Label label) i.inst_operands ==>
      MEM (Label label) inst.inst_operands
Proof
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[mk_inst_def, AllCaseEqs()]
  >- (gvs[NULL_EQ] >> metis_tac[APPEND_FRONT_LAST, MEM_APPEND])
  >- (gvs[NULL_EQ] >> metis_tac[APPEND_FRONT_LAST, MEM_APPEND, MEM])
  >- (drule fmp_resolve_invoke_label_origin >> simp[])
  >- (drule fmp_resolve_invoke_label_origin >> simp[])
  >> Cases_on `info.fi_needs_fmp` >> gvs[]
QED

Theorem fmp_emit_restores_no_labels:
  !s out s'. fmp_emit_restores runner s bases = (out,s') ==>
  EVERY (\i. ~MEM (Label label) i.inst_operands) out
Proof
  Induct_on `bases` >>
  simp[fmp_emit_restores_def, AllCaseEqs(), mk_inst_def] >>
  rpt strip_tac >> gvs[mk_inst_def] >> first_x_assum irule >> metis_tac[]
QED

Theorem fmp_make_root_layout_label_free:
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root pc s') /\
  EVERY (\i. ~MEM (Label label) i.inst_operands) (fn_insts fn) ==>
  EVERY (\i. ~MEM (Label label) i.inst_operands) (OPTION_TO_LIST root) /\
  EVERY (\i. ~MEM (Label label) i.inst_operands) (OPTION_TO_LIST pc)
Proof
  simp[fmp_make_root_layout_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all split_fmp_entry_retpc_every >>
  simp[OPTION_TO_LIST_def, set_param_index_def, mk_inst_def]
QED

Theorem fmp_lower_function_label_free:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  EVERY (\i. ~MEM (Label label) i.inst_operands) (fn_insts fn) ==>
  EVERY (\i. ~MEM (Label label) i.inst_operands) (fn_insts fn')
Proof
  strip_tac >> irule fmp_lower_function_every >>
  conj_tac >- metis_tac[fmp_emit_restores_no_labels] >>
  qexistsl [`ctx`, `fn`, `s`, `s'`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
      drule_all fmp_lower_inst_label_origin >>
      gvs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[fmp_make_root_layout_label_free]
QED

Theorem fmp_lower_function_label_origin:
  fmp_lower_function ctx s fn = SOME (fn',s') ==>
  ((?i. MEM i (fn_insts fn') /\ MEM (Label label) i.inst_operands) ==>
   (?i. MEM i (fn_insts fn) /\ MEM (Label label) i.inst_operands))
Proof
  strip_tac >> strip_tac >> spose_not_then assume_tac >>
  `EVERY (\i. ~MEM (Label label) i.inst_operands) (fn_insts fn)` by
    gvs[EVERY_MEM] >>
  `EVERY (\i. ~MEM (Label label) i.inst_operands) (fn_insts fn')` by
    (irule fmp_lower_function_label_free >>
     qexistsl [`ctx`, `fn`, `s`, `s'`] >> simp[EVERY_MEM]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED
