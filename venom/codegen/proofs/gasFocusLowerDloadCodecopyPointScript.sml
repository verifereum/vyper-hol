Theory gasFocusLowerDloadCodecopyPoint
Ancestors
  lowerDloadPublicTrace lowerDloadSafetyAmbient lowerDloadSafetyRelation
  lowerDloadSafetyKernel lowerDloadSafetyValues lowerDloadSafetyWriteAssembly
  lowerDloadOracleCallAssembly lowerDloadDefs
  o1CodeEndLowerReadTransport o1CodeEndLowerProvenance
  memSafeRun venomInst list pair words

(* Transport only the offset check; neither the destination nor the size of
   DLOADBYTES has to be evaluated at this point. *)
Theorem focus_ld_section_transfer[local]:
  !tn inst.
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  f.lf_src.vs_data_section = f.lf_tgt.vs_data_section /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ tn.t_var = f.lf_tv /\
  ((inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES) ==>
     taint_ok f.lf_fn tn inst f.lf_src) /\
  inst_dload_in_section inst f.lf_src ==>
  inst_dload_in_section inst f.lf_tgt
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[inst_dload_in_section_def] >>
  rpt gen_tac >> strip_tac
  >- (`taint_ok f.lf_fn tn inst f.lf_src` by simp[] >>
      drule_all ld_dload_operand_equal >> strip_tac >>
      fs[inst_dload_in_section_def] >> metis_tac[]) >>
  `taint_ok f.lf_fn tn inst f.lf_src` by simp[] >>
  `MEM op inst.inst_operands` by simp[] >>
  drule_all ld_write_operand_defined >> strip_tac >>
  `x = off` by (irule ld_dloadbytes_scalar_observation >> metis_tac[]) >>
  fs[inst_dload_in_section_def] >> metis_tac[]
QED

Theorem focus_lower_dload_codecopy_point:
  ld_sync lo P C vs stk PG G tn fn si s t0 A (f::fs) N /\ o1_ctx_shape C /\
  ir_supply_covers_fn f.lf_supply fn /\ fn' = ld_image f /\
  (!i. MEM i (fn_insts fn) ==> ~MEM (Label "code_end") i.inst_operands) /\
  ((si.inst_opcode = DLOAD \/ si.inst_opcode = DLOADBYTES) ==> taint_ok fn tn si s) /\
  inst_dload_in_section si s /\ LENGTH s.vs_data_section < dimword (:256) DIV 2 /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\ ld_prefix C' fn' X p h t0 t /\
  (EL h X).inst_opcode = CODECOPY /\ (EL h X).inst_operands = [dst; Var x; sz] /\
  code_end_var fn' x /\ eval_operand (Var x) t = SOME w /\
  FLOOKUP t.vs_labels "code_end" = SOME bword ==>
  w2n (w - bword) < dimword (:256) DIV 2
Proof
  strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  drule ld_sync_source >> strip_tac >>
  drule_all ld_active_envelope_origin >> strip_tac >>
  rename1 `X = FST (lower_dload_inst_supply u si)` >>
  Cases_on `si.inst_opcode = DLOAD \/ si.inst_opcode = DLOADBYTES`
  >- (drule ld_sync_active >> simp[] >> strip_tac >>
      drule ld_sync_ptr_ok >> strip_tac >>
      `s.vs_data_section = t0.vs_data_section /\ s.vs_labels = t0.vs_labels` by
        (drule ld_sync_memory >> simp[ld_nonghost_def]) >>
      `inst_dload_in_section si t0` by
        (drule focus_ld_section_transfer >>
         disch_then (qspecl_then [`tn`,`si`] mp_tac) >>
         simp[] >> metis_tac[]) >>
      `LENGTH t0.vs_data_section < dimword (:256) DIV 2` by metis_tac[] >>
      `~MEM (Label "code_end") si.inst_operands` by metis_tac[] >>
      `lower_dload_inst_supply u si = (X,SND (lower_dload_inst_supply u si))` by
        metis_tac[PAIR] >>
      `!z. MEM (Var z) si.inst_operands ==> MEM z u.irs_used_vars` by
        metis_tac[ld_inst_input_ir] >>
      drule_all lower_dload_codecopy_delta >> strip_tac >> simp[]) >>
  `X = [si]` by fs[lower_dload_inst_supply_def] >>
  `h = 0` by (drule ld_prefix_bound >> simp[]) >>
  `MEM x (fn_ir_vars fn)` by (irule ld_inst_input_ir >> qexists `si` >> gvs[]) >>
  `?rest. lower_dload_function_supply f.lf_supply fn = (fn',rest)` by
    (drule ld_sync_active >> simp[ld_image_def] >> metis_tac[PAIR]) >>
  metis_tac[lower_dload_code_end_var_fresh]
QED
