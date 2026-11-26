(* Successful Abs suffix: source-independent path and register/ghost frame. *)
Theory bodyWordAbsSuccessPathMods
Ancestors
  bodyPtrWordBuiltinsAbsSuffix bodyFullBuiltinWordAbs augAssignFullScalarSuccess
  augAssignPtrScalarCertificate exprSimUnopProps freshWrites fragGasOriginPtr
  fragGasSeqPtr fragExecMem fragExec ptrDiscipline venomExecSemantics
  compileEnv venomState venomInst list rich_list pred_set finite_map

Theorem abs_scalar_code[local]:
  compile_builtin_abs x sa = (op,sb) /\ (!l. x <> Label l) ==>
  ?A. scalar_code A (emitted_insts sa sb) /\
      (!v. v IN A ==> x = Var v) /\
      scalar_available
        (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) (emitted_insts sa sb)))) op
Proof
  strip_tac >> drule_then strip_assume_tac word_abs_emitted_insts >>
  qexists_tac `{v | x = Var v}` >>
  Cases_on `x` >>
  gvs[scalar_code_def, scalar_available_def, scalar_shape_def,
      scalar_binary_def, scalar_unary_def, mk_inst_def] >-
    (qexists_tac `{STRING #"%" (toString (sa.cs_next_var + 7))}` >> simp[]) >>
  disj2_tac >> qexists_tac `{STRING #"%" (toString (sa.cs_next_var + 7))}` >> simp[]
QED

Theorem abs_suffix_ordinary[local]:
  compile_builtin_abs x sa = (op,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
        (emitted_insts sa sb)
Proof
  strip_tac >> drule abs_suffix_opcodes >> strip_tac >>
  `EVERY (\k. k <> INVOKE /\ ~is_terminator k /\ k <> ALLOCA /\ k <> GAS)
     (MAP (\i. i.inst_opcode) (emitted_insts sa sb))` by simp[is_terminator_def] >>
  fs[EVERY_MAP]
QED

Theorem abs_writes_fresh[local]:
  compile_builtin_abs x sa = (op,sb) ==>
  writes_fresh sa (emitted_insts sa sb)
Proof
  strip_tac >>
  qspec_then `x` mp_tac straight_fresh_abs >> simp[straight_fresh_def] >>
  disch_then drule >> simp[]
QED

Theorem abs_no_output_old[local]:
  writes_fresh sa code /\ not_fresh_at sa v ==>
  ~MEM v (FLAT (MAP (\i. i.inst_outputs) code))
Proof
  simp[writes_fresh_def, EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem abs_suffix_success_path:
  compile_builtin_abs x s1 = (op,sb) /\
  run_inst_seq (emitted_insts s1 sb) s = OK u /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  (!v. x = Var v ==> not_fresh_at s1 v) /\ (!l. x <> Label l) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts s1 sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?z G' tn'.
    z = (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts s1 sb)) /\
    u = (s with vs_vars := u.vs_vars) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK z,G',tn')) /\
    (!v. not_fresh_at s1 v ==>
      lookup_var v z = lookup_var v s /\ FLOOKUP G' v = FLOOKUP G v /\
      op_taint tn' (Var v) = op_taint tn (Var v)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all_then (qx_choose_then `A` strip_assume_tac) abs_scalar_code >>
  `!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]) >>
  drule_then assume_tac abs_writes_fresh >>
  drule_all_then strip_assume_tac run_inst_seq_writes_fresh >>
  drule_then assume_tac abs_suffix_ordinary >>
  drule_then (qspec_then `s` assume_tac) abs_suffix_mem_ok >>
  drule_all augassign_scalar_success_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts s1 sb)`,
               `G'`, `tn'`] >>
  conj_tac >- REFL_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qx_gen_tac `D` >>
      qpat_assum `!D lo explicit. _` (qspecl_then [`D`,`lo`,`explicit`] mp_tac) >>
      disch_then drule >> simp[]) >>
  conj_tac
  >- (qx_gen_tac `v` >> strip_tac >> conj_tac
      >- (simp[NoAsms, lookup_var_def] >>
          qpat_assum `!x. not_fresh_at s1 x ==> FLOOKUP u.vs_vars x = _`
            (drule_then ACCEPT_TAC)) >>
      drule_all_then assume_tac abs_no_output_old >>
      qpat_assum `!v. ~MEM v _ ==> _` (drule_then strip_assume_tac) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
