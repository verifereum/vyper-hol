(* The runtime Len suffix is a DLOAD of the selected immutable header. *)
Theory bodyLenRuntimeCodeRunMods
Ancestors
  builtinSimple context loweringShapeRules valueEncodingDefs exprSimUnwrap
  fragExec fragGasOriginPtr fragGasSeqPtr exprPtrUnwrapCodeEdges stmtAppendStorageRunPtr
  stmtReasonLitFragMemory bodyBinopFragMemory memSafeRun unitTransformDefs contextCodegenRel codegenRel
  bodyPtrDefs ptrDiscipline venomInst venomState venomExecSemantics
  words arithmetic list rich_list finite_map pred_set

Theorem len_runtime_code_run_mods:
  ~cenv.ce_is_ctor /\ vv_location vv = SOME LocCode /\
  compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
    (case vv_location vv of NONE => LocMemory | SOME l => l) sm = (op,sb) /\
  fn_has_code sm sb func /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand (vv_operand vv) t = SOME w /\ op_taint tn (vv_operand vv) = {} /\
  w2n w <= LENGTH t.vs_data_section /\ mem_word_at (w2n w) t.vs_data_section = n2w n /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  ?z G2 tn2.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2)) /\
    eval_operand op z = SOME (n2w n) /\ op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (alloca_history func t ==> alloca_history func z) /\
    z = t with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|> /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t /\
      FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)) /\
    tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
    tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm
Proof
  strip_tac >>
  `emit_op DLOAD [vv_operand vv] sm = (op,sb)` by
    (qpat_x_assum `compile_builtin_len _ _ _ _ _ = _` mp_tac >>
     simp[compile_builtin_len_def,compile_ptr_load_def,compile_imm_load_word_runtime]) >>
  drule_then strip_assume_tac emit_op_facts >>
  qpat_x_assum `op = Var out` SUBST_ALL_TAC >>
  qabbrev_tac `i = mk_inst sm.cs_next_id DLOAD [vv_operand vv] [out]` >>
  qabbrev_tac `u = update_var out (mem_word_at (w2n w) t.vs_data_section) t` >>
  qabbrev_tac `z = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `sb.cs_current_insts = sm.cs_current_insts ++ [i]` by simp[Abbr `i`] >>
  drule_all_then strip_assume_tac fn_has_code_same_block >>
  `get_instruction bb t.vs_inst_idx = SOME i` by
    (qpat_assum `!j. j < LENGTH [i] ==> _` (qspec_then `0` mp_tac) >>
     gvs[Abbr `i`]) >>
  `step_inst_base i t = OK u` by
    (qpat_assum `eval_operand _ _ = SOME _`
       (mp_then Any mp_tac exprSimUnwrapTheory.step_DLOAD) >>
     disch_then (qspecl_then [`sm.cs_next_id`,`out`] assume_tac) >>
     qpat_assum `mem_word_at _ _ = _` mp_tac >>
     gvs[Abbr `i`,Abbr `u`,mem_word_at_def]) >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn i t` by
    (simp[Abbr `i`] >> gen_tac >> irule ptr_inst_ok_code_load >> simp[]) >>
  `!D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (t,G,tn) []
     (OK z,step_prov PG G i u,step_taint i t u tn)` by
    (gen_tac >>
     mp_tac (straight_line_origin_ptr_edge |> Q.INST
       [`s` |-> `t`, `G` |-> `G`, `tn` |-> `tn`, `i` |-> `i`, `u` |-> `u`]) >>
     simp[Abbr `i`,Abbr `z`,mk_inst_def,is_terminator_def,dalloca_no_wrap_def,
          inst_mem_below_frontier_def,source_memory_read_ranges_def,
          source_memory_write_ranges_def,inst_dload_in_section_def]) >>
  `~z.vs_halted` by simp[Abbr `z`,Abbr `u`,update_var_def] >>
  qexistsl [`z`,`step_prov PG G i u`,`step_taint i t u tn`] >>
  conj_tac
  >- (gen_tac >>
      `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (t,G,tn) []
         (OK z,step_prov PG G i u,step_taint i t u tn)` by simp[] >>
      drule (cj 2 gas_origin_ptr_path_rules) >>
      disch_then (qspec_then `[]` mp_tac) >> simp[cj 1 gas_origin_ptr_path_rules]) >>
  `alloca_history func t ==> alloca_history func z` by
    (strip_tac >> drule_all_then strip_assume_tac fn_has_code_code >>
     fs[IS_PREFIX_APPEND] >> gvs[Abbr `z`,arithmeticTheory.ADD1] >>
     qpat_assum `t.vs_inst_idx = LENGTH sm.cs_current_insts`
       (SUBST1_TAC o SYM) >>
     `alloca_history func (u with vs_inst_idx := t.vs_inst_idx + LENGTH [i])`
       suffices_by simp[Abbr `i`] >>
     irule alloca_history_no_alloca_slice >>
     simp[Abbr `u`,update_var_def] >>
     conj_tac
     >- (qexists_tac `TL (DROP (LENGTH sm.cs_current_insts) bb.bb_instructions)` >>
         Cases_on `DROP (LENGTH sm.cs_current_insts) bb.bb_instructions` >> gvs[])
     >- simp[Abbr `i`,mk_inst_def,update_var_def,arithmeticTheory.ADD1]) >>
  `op_prov (step_prov PG G i u) (Var out) = NONE` by
    (simp[Abbr `i`] >> irule step_prov_out_none >> simp[mk_inst_def] >>
     irule out_prov_other_none >> simp[mk_inst_def]) >>
  `!x. not_fresh_at sm x ==> x <> out` by (rpt strip_tac >> gvs[]) >>
  simp[Abbr `z`,Abbr `i`,Abbr `u`,update_var_def,eval_operand_def,lookup_var_def,
       FLOOKUP_UPDATE,arithmeticTheory.ADD1,runtime_code_load_clean,
       scalar_step_old_prov,scalar_step_old_taint] >>
  simp[step_taint_def,mk_inst_def,mem_taint_def,store_taint_def,imm_taint_def,
       step_writes_def,source_memory_write_ranges_def,written_taint_def,range_bytes_def,
       adopt_reset_def,new_site_bytes_def,FLOOKUP_DEF,EXTENSION,SF CONJ_ss]
QED
