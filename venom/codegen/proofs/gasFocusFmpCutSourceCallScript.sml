Theory gasFocusFmpCutSourceCall
Ancestors
  o1PassContract unitShapeDefs o1ContractSimplifyCfgSrcFrame
  simplifyCfgAvailability ptrDiscipline contextCodegenRel
  venomExecSemantics venomState venomInst venomWf stackPlanTypes finite_map list

(* Row 3 supplies definite assignment on the actual caller history.  Decode
   and enter that call before the lowering inserts any ABI arguments. *)
Theorem focus_fmp_cut_source_call_entry:
  o1_ctx_shape C /\ o1_fn_row 3 fn /\ root.vs_vars = FEMPTY /\
  ~root.vs_halted /\ frame_reachable root C stk PG G tn fn ivk s /\
  active_inst fn ivk s /\ ivk.inst_opcode = INVOKE ==>
  ?nm ops callee args cs i.
    decode_invoke ivk = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs cs /\ active_inst callee i cs
Proof
  strip_tac >>
  `!g. MEM g C.ctx_functions ==> o1_fn_shape C g` by
    fs[o1_ctx_shape_def, EVERY_MEM] >>
  `MEM fn C.ctx_functions` by metis_tac[scfg_frame_reachable_functions] >>
  `MEM ivk (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `wf_function fn /\ fn_inst_wf fn /\ fn_invoke_ok (ctx_fn_names C) fn /\
   fn_shape_ok fn` by metis_tac[o1_fn_shape_def] >>
  `?nm ops. ivk.inst_operands = Label nm :: ops /\ MEM nm (ctx_fn_names C)` by
    metis_tac[fn_invoke_ok_def] >>
  `?callee. lookup_function nm C.ctx_functions = SOME callee` by
    (Cases_on `lookup_function nm C.ctx_functions` >>
     fs[ctx_fn_names_def] >> metis_tac[lookup_function_not_mem]) >>
  `!nm g. lookup_function nm C.ctx_functions = SOME g ==> wf_function g` by
    metis_tac[lookup_function_MEM, o1_fn_shape_def] >>
  drule_all scfg_frame_reachable_entry_root >> strip_tac >>
  `fn_defs_reach_uses fn` by fs[o1_fn_row_def, make_ssa_input_ok_def] >>
  `inst_shape_ok ivk` by fs[fn_shape_ok_def, EVERY_MEM] >>
  `EVERY (\op. ~is_label_operand op) ops` by
    (qpat_x_assum `inst_shape_ok ivk` mp_tac >>
     simp[inst_shape_ok_def, label_positions_ok_def]) >>
  `IS_SOME (eval_operands ops s)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_MEM] >> rpt strip_tac >>
     Cases_on `op` >> simp[eval_operand_def]
     >- (rename1 `MEM (Var v) ops` >>
         `MEM (Var v) ivk.inst_operands /\ ivk.inst_opcode <> PHI` by simp[] >>
         drule_all scfg_frame_operand_defined >> simp[]) >>
     rename1 `MEM (Label l) ops` >>
     qpat_x_assum `EVERY (\op. ~is_label_operand op) ops` mp_tac >>
     simp[EVERY_MEM] >> disch_then (qspec_then `Label l` mp_tac) >>
     simp[is_label_operand_def]) >>
  Cases_on `eval_operands ops s` >> gvs[] >>
  `wf_function callee /\ first_block_no_phi callee` by
    metis_tac[lookup_function_MEM, o1_fn_shape_def] >>
  Cases_on `callee.fn_blocks` >- fs[wf_function_def, fn_has_entry_def] >>
  rename1 `callee.fn_blocks = bb::bbs` >>
  `bb.bb_instructions <> []` by
    metis_tac[wf_function_def, bb_well_formed_def, MEM] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  rename1 `bb.bb_instructions = first::rest` >>
  `first.inst_opcode <> PHI` by fs[first_block_no_phi_def] >>
  qexistsl_tac [`nm`, `ops`, `callee`] >>
  simp[decode_invoke_def, setup_callee_def] >>
  simp[enters_block_def, active_inst_def, lookup_block_def,
       eval_phis_def, phi_prefix_length_def, FIND_thm] >>
  qexists_tac `bb` >> simp[]
QED
