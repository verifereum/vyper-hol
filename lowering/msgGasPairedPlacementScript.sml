(* The canonical source gas observation has corresponding raw instructions. *)
Theory msgGasPairedPlacement
Ancestors
  fragExec msgGasSim gasExplicitSites gasShadowUnit gasShadowState
  exprLowering emitHelper compileEnv
  venomInst venomState venomExecSemantics venomExecProofs list rich_list

Theorem msg_gas_paired_placement:
  compile_env_var MsgGas sa = (op, sb) /\
  compile_env_var GasPrice ta = (shadow_op, tb) /\
  gas_shadow_state sa ta /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code ta tb shadow_func ==>
  ?out id bb. op = Var out /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
    lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst id GAS [] [out]) /\
    (func.fn_name,id) IN gas_explicit_sites ctx shadow_ctx /\
    (?shadow_bb.
      lookup_block ta.cs_current_bb shadow_func.fn_blocks = SOME shadow_bb /\
      get_instruction shadow_bb (LENGTH ta.cs_current_insts) =
        SOME (mk_inst id GASPRICE [] [out]))
Proof
  strip_tac >> drule_all msg_gas_placement >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id GAS [] [out]] /\
   tb.cs_current_bb = ta.cs_current_bb /\
   tb.cs_current_insts = ta.cs_current_insts ++
      [mk_inst ta.cs_next_id GASPRICE [] [out]]` by
    (gvs[compile_env_var_def, emit_op_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def, fresh_id_def,
         fresh_var_def, emit_def, gas_shadow_state_def]) >>
  `id = sa.cs_next_id` by
    (qpat_x_assum `fn_has_code ta tb shadow_func` kall_tac >>
     drule_all fn_has_code_same_block >> strip_tac >>
     first_x_assum (qspec_then `0` mp_tac) >>
     simp[] >> strip_tac >> gvs[mk_inst_def] >>
     metis_tac[optionTheory.SOME_11, instruction_component_equality]) >>
  `?shadow_bb.
     lookup_block ta.cs_current_bb shadow_func.fn_blocks = SOME shadow_bb /\
     get_instruction shadow_bb (LENGTH ta.cs_current_insts) =
       SOME (mk_inst ta.cs_next_id GASPRICE [] [out])` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb'` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `MEM (mk_inst id GAS [] [out]) (fn_insts func)` by
    (irule lookup_block_fn_insts >>
     gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[EL_MEM]) >>
  `MEM (mk_inst ta.cs_next_id GASPRICE [] [out]) (fn_insts shadow_func)` by
    (irule lookup_block_fn_insts >>
     gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[EL_MEM]) >>
  qexistsl_tac [`out`, `id`, `bb`] >> simp[] >>
  reverse conj_tac
  >- (gvs[gas_shadow_state_def] >> metis_tac[]) >>
  simp[gas_explicit_sites_def] >>
  qexistsl_tac [`func`, `shadow_func`, `mk_inst id GAS [] [out]`,
               `mk_inst ta.cs_next_id GASPRICE [] [out]`] >>
  gvs[gas_shadow_state_def, gas_shadow_function_def, mk_inst_def] >>
  qpat_x_assum `_ with fn_blocks := _ = _` mp_tac >>
  simp[ir_function_component_equality]
QED
