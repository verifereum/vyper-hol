(* Allocation ownership and robust input transport at dynamic tuple entry. *)
Theory logTupleEntryPtr
Ancestors
  logCursorAllocPtr logAllocFramePtr logMembersInvariantPtr
  stmtSimLogEncodeLayout abiEncoderComplexDynamic abiEncoderInput
  allocationPtr loweringHalt bodyPtrDefs abiBuiltinAllocation emitHelperProps exprLoweringProps
  context compileEnv venomExecSemantics venomState venomInst ptrDiscipline ptrSafeRun
  finite_map words list arithmetic pred_set

(* ALLOCA can taint its own newly registered bytes, never exterior bytes. *)
Theorem alloca_step_taint_outside_site:
  stmt_state_rel ctx func ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
  FLOOKUP t.vs_allocas id = SOME (p,n) ==>
  !tn.
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_trans = tn.t_trans /\
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_imm = tn.t_imm /\
    (!i. ~(p <= i /\ i < p+n) ==>
      (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem <=>
       i IN tn.t_mem))
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`[]`,`FEMPTY`] assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def, FLOOKUP_UPDATE] >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`,`[]`,`FEMPTY`] assume_tac) >> simp[]
QED

(* The layout constructor needs no initialization of destination bytes when the
   processed prefix is empty.  Only source robustness and output capacity matter. *)
Theorem log_tuple_layout_entry:
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos /\
  (!q. mem_agree_outside m mem q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q) /\
  mem_agree_outside writes mem' mem /\
  (!i. sb <= i /\ i < sb+abi_encoder_member_span infos ==> i NOTIN writes) /\
  (!i. sb <= i /\ i < sb+abi_encoder_member_span infos ==> (i IN m' <=> i IN m)) /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= cap ==>
  log_members_layout infos tys avs [] [] sb 0 0 d
    (SUM (MAP (\(_,asz,_,_). asz) infos)) cap mem' /\
  (!q. mem_agree_outside m' mem' q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q)
Proof
  strip_tac >>
  `!q. mem_agree_outside m' mem' q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q` by
    (rpt strip_tac >> irule robust_abi_encoder_input_separated_write >>
     qexistsl_tac [`m`,`m'`,`mem`,`mem'`,`writes`] >> asm_simp_tac bool_ss []) >>
  `abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) mem'` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule abi_encoder_complex_input_metadata >> strip_tac >>
  conj_tac >- (asm_rewrite_tac[] >> irule log_members_layout_initial >> simp[] >>
    qexists_tac `abi_encoder_member_span infos` >> simp[]) >>
  first_assum ACCEPT_TAC
QED
