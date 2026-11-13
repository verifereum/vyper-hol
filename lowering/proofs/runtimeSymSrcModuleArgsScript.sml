Theory runtimeSymSrcModuleArgs
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission moduleLowering finite_map compileEnv loweringShapeDefs emitHelper
  exprLowering builtinStrings stackPlanTypes

Theorem runtime_sym_register_kwarg_vars:
  !vars ce. runtime_sym_env ce /\
    EVERY (\(n,op,ty,e). ~is_label_operand op) vars ==>
    runtime_sym_env (compile_register_kwarg_vars ce vars)
Proof
  Induct >> simp[compile_register_kwarg_vars_def] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  simp[compile_register_kwarg_vars_def] >> first_x_assum irule >>
  gvs[runtime_sym_env_def, runtime_sym_loc_def, FLOOKUP_UPDATE,
      AllCaseEqs()] >> metis_tac[runtime_sym_loc_def]
QED

Theorem runtime_sym_create_kwarg_allocas:
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_alloc_buffer n s = (b,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\
     ~is_label_operand b.buf_operand) ==>
  !specs ce s vars s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_create_kwarg_allocas ce specs s = (vars,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\(n,op,ty,e). ~is_label_operand op) vars /\
    MAP (\(n,op,ty,e). (n,ty,e)) vars = specs
Proof
  strip_tac >> Induct >>
  simp[compile_create_kwarg_allocas_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_create_kwarg_allocas_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[comp_return_def] >>
  first_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then drule >> strip_tac >>
  first_x_assum (drule_at (Pat `compile_create_kwarg_allocas _ _ _ = _`)) >>
  simp[]
QED

Theorem runtime_sym_register_positional_args:
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_alloc_buffer n s = (b,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\
     ~is_label_operand b.buf_operand) /\
  (!ce args off s u s'. runtime_sym_env ce /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_decode_args ce args off CALLDATALOAD (Lit 0w) 4 s = (u,s') ==>
     EVERY runtime_sym_inst (state_insts s')) ==>
  !args ce off s ce' s'. runtime_sym_env ce /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_register_positional_args ce args off s = (ce',s') ==>
    runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> Induct >>
  simp[compile_register_positional_args_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
  >- metis_tac[] >>
  Cases_on `var_location_memory_size x` >> simp[]
  >- metis_tac[] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >>
  first_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then drule >> strip_tac >>
  `runtime_sym_env (ce with ce_vars updated_by
      (\m. m |+ (h0,PtrVar buf.buf_operand x')))` by
    (irule runtime_sym_env_update >> simp[runtime_sym_loc_def]) >>
  first_assum (drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`)) >>
  disch_then drule >> disch_then drule >> strip_tac >>
  first_x_assum (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)) >>
  simp[]
QED

Theorem runtime_sym_kwarg_calldata_source:
  EVERY runtime_sym_inst (state_insts s) /\
  (do head <- emit_op ADD [Lit 4w; Lit (n2w (off - 4))];
      if dyn then
        do relative <- emit_op CALLDATALOAD [head];
           emit_op ADD [Lit 4w; relative] od
      else return head od) s = (src,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand src
Proof
  simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def] >> strip_tac >>
  Cases_on `dyn` >> gvs[comp_return_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[] >> strip_tac >>
  qpat_x_assum `emit_op CALLDATALOAD _ _ = _` kall_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_init_kwargs:
  (!dst src info s u s'. ~is_label_operand dst /\ ~is_label_operand src /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) info s = (u,s') ==>
     EVERY runtime_sym_inst (state_insts s')) /\
  (!ce ty e s v s'. runtime_sym_env ce /\ supported_expr tops e /\
     ~supported_expr_exists is_self_code e /\ EVERY runtime_sym_inst (state_insts s) /\
     lower_value compile_expr ce ty e s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!src dst s u s'. ~is_label_operand src /\ ~is_label_operand dst /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_store_bytestring src dst s = (u,s') ==>
     EVERY runtime_sym_inst (state_insts s')) ==>
  !vars ce off n hi s u s'. runtime_sym_env ce /\
    EVERY (\(name,op,ty,e). ~is_label_operand op /\ supported_expr tops e /\
      ~supported_expr_exists is_self_code e) vars /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_init_kwargs ce (vars:(string # operand # type # expr) list) off n (hi:operand) s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> Induct
  >- (simp[compile_init_kwargs_def, comp_return_def] >> metis_tac[]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  pure_once_rewrite_tac[compile_init_kwargs_def] >>
  pure_rewrite_tac[listTheory.EVERY_DEF, pairTheory.pair_case_thm] >>
  BETA_TAC >> IF_CASES_TAC
  >- (simp[NoAsms, comp_bind_def, comp_ignore_bind_def] >>
      pairarg_tac >> pure_asm_rewrite_tac[] >> CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
      pairarg_tac >> pure_asm_rewrite_tac[] >> CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
      pairarg_tac >> pure_asm_rewrite_tac[] >> CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
      strip_tac >>
      `EVERY runtime_sym_inst (state_insts cs'') /\ ~is_label_operand src` by
        (irule runtime_sym_kwarg_calldata_source >>
         qexistsl [`is_abi_dynamic ce.ce_struct_fields h2`, `off`, `s`] >>
         simp[NoAsms, comp_bind_def] >>
         pure_asm_rewrite_tac[] >> CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
         asm_rewrite_tac[]) >>
      first_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
      disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
      first_x_assum (drule_at (Pat `compile_init_kwargs _ _ _ _ _ _ = _`)) >>
      simp[]) >>
  simp[NoAsms, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> pure_asm_rewrite_tac[] >> CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  pairarg_tac >> pure_asm_rewrite_tac[] >> CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  strip_tac >>
  first_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  disch_then drule >> disch_then drule >> disch_then drule >> disch_then drule >>
  strip_tac >>
  `EVERY runtime_sym_inst (state_insts cs'')` by
    (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
     IF_CASES_TAC
     >- (simp[] >> strip_tac >> drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
         simp[NoAsms] >> disch_then irule >> asm_rewrite_tac[]) >>
     IF_CASES_TAC >- (simp[] >> metis_tac[]) >>
     simp[] >> strip_tac >> drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
     simp[NoAsms, is_label_operand_def] >> disch_then irule >> asm_rewrite_tac[]) >>
  first_x_assum (drule_at (Pat `compile_init_kwargs _ _ _ _ _ _ = _`)) >> simp[]
QED

Theorem runtime_sym_entry_point_kwargs:
  (!ce vars off n hi s u s'. runtime_sym_env ce /\
     EVERY (\(name,op,ty,e). ~is_label_operand op /\ supported_expr tops e /\
       ~supported_expr_exists is_self_code e) vars /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_init_kwargs ce (vars:(string # operand # type # expr) list) off n (hi:operand) s = (u,s') ==>
     EVERY runtime_sym_inst (state_insts s')) /\
  runtime_sym_env ce /\ runtime_sym_label label /\
  EVERY (\(name,op,ty,e). ~is_label_operand op /\ supported_expr tops e /\
    ~supported_expr_exists is_self_code e) vars /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_entry_point_kwargs ce (vars:(string # operand # type # expr) list) off n label s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[NoAsms, compile_entry_point_kwargs_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> pure_asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >> strip_tac >>
  Cases_on `_0` >>
  first_x_assum (drule_at (Pat `compile_init_kwargs _ _ _ _ _ _ = _`)) >>
  disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_jump >> simp[]
QED
