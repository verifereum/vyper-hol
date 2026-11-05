Theory bodyPtrPrecompileBuiltinsSuffix
Ancestors bodyPtrPrecompileBuiltinsBoundary fragGasSeqPtr
          emitHelperProps ptrSafeRun ptrDiscipline venomInstProofs
          venomExecSemantics venomInst venomState finite_map
          contextCodegenRel codegenRel memLocDefs exprSimHash
          decoderGhostFramePtr

Theorem gas_ptr_inst_ok:
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id GAS [] [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       mem_read_ops_def, mem_write_ops_def, step_inst_non_invoke, step_GAS,
       update_var_def]
QED

Theorem gas_output_taint:
  op_taint (step_taint (mk_inst id GAS [] [out]) s t tn) (Var out) = {}
Proof
  simp[step_taint_def, op_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem gas_ptr_covers:
  p <> out /\ ptr_covers G tn p s sz /\
  step_inst_base (mk_inst id GAS [] [out]) s = OK t ==>
  ptr_covers (step_prov PG G (mk_inst id GAS [] [out]) t)
    (step_taint (mk_inst id GAS [] [out]) s t tn) p t sz
Proof
  strip_tac >> irule ptr_covers_step_frame >> simp[mk_inst_def] >>
  gvs[step_GAS, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem assert_ptr_inst_ok:
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ op_taint tn op = {} ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id ASSERT [op] []) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       mem_read_ops_def, mem_write_ops_def, step_inst_non_invoke,
       step_inst_base_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  rename1 `eval_operand op s = SOME w` >> Cases_on `w = 0w` >> simp[]
QED

Theorem staticcall_ptr_inst_ok:
  inst = mk_inst id STATICCALL
    [gp; Lit addr; Var src; Lit an; Var dst; Lit rn] [out] /\
  ptr_covers G tn src s (w2n an) /\ ptr_covers G tn dst s (w2n rn) /\
  op_taint tn gp = {} /\ eval_operand (Var src) s = SOME ai /\
  (!i. w2n ai <= i /\ i < w2n ai + w2n an ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  (!t. step_inst_base inst s <> Halt t) ==>
  ptr_inst_ok D lo fuel ctx fn G tn inst s
Proof
  strip_tac >>
  `access_ok lo G fn inst s` by
    (gvs[] >> irule staticcall_access_ok >> qexists_tac `tn` >> simp[]) >>
  `taint_ok fn tn inst s` by
    (gvs[] >> irule staticcall_taint_ok >>
     gvs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  simp[ptr_inst_ok_def] >>
  gvs[mk_inst_def, step_inst_non_invoke] >> metis_tac[]
QED

Theorem gas_step_taint:
  step_inst_base (mk_inst id GAS [] [out]) s = OK t ==>
  step_taint (mk_inst id GAS [] [out]) s t tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >> gvs[step_GAS] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, written_taint_def, range_bytes_def,
       source_memory_write_ranges_def, set_var_taint_def, out_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def,
       mk_inst_def, update_var_def] >>
  simp[finite_mapTheory.FLOOKUP_DEF, taint_component_equality,
       pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem assert_step_ghost:
  step_prov PG G (mk_inst id ASSERT [op] []) s = G /\
  step_taint (mk_inst id ASSERT [op] []) s s tn = tn
Proof
  simp[step_prov_def, set_prov_def, step_taint_def, mem_taint_def,
       new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, set_var_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
       DRESTRICT_UNIV, FLOOKUP_DEF, taint_component_equality,
       pred_setTheory.EXTENSION] >>
  metis_tac[]
QED
