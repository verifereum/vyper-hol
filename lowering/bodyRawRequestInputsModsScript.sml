(* Static inputs for the linked Send and raw-request operand runs. *)
Theory bodyRawRequestInputsMods
Ancestors
  exprBodyPreProps exprSimHypsDefs exprSimSource allocLimits compileEnv words
  supportedExprTraverse vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperAST list arithmetic

Theorem send_pre_types_mods:
  expr_body_pre_mods mods cenv cx env (Call ann (Send has_gas) args dflt) es ==>
  ann = NoneT /\ dflt = NONE /\
  MAP expr_type args =
    [BaseT AddressT; BaseT (UintT 256)] ++
    (if has_gas then [BaseT (UintT 256)] else []) /\
  LENGTH args = (if has_gas then 3 else 2) /\
  EVERY (\e. is_word_type (expr_type e)) args
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def] >> strip_tac >>
  `LENGTH (MAP expr_type args) = (if has_gas then 3 else 2)` by
    (asm_rewrite_tac[] >> Cases_on `has_gas` >> simp[]) >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  `MEM (expr_type e) (MAP expr_type args)` by
    (simp[MEM_MAP] >> qexists_tac `e` >> simp[]) >>
  pop_assum mp_tac >> asm_rewrite_tac[] >>
  Cases_on `has_gas` >> simp[] >> strip_tac >> simp[is_word_type_def]
QED

Theorem raw_call_pre_operands_flags_mods:
  expr_body_pre_mods mods cenv cx env (Call ann (RawCallTarget flags) args dflt) es ==>
  flags.rcf_max_outsize < dimword (:256) /\
  LENGTH args = 2 + LENGTH flags.rcf_kws /\
  ann = raw_call_return_type flags /\ dflt = NONE /\
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  ?a d kws n. args = a::d::kws /\
    expr_type a = BaseT AddressT /\ expr_type d = BaseT (BytesT (Dynamic n)) /\
    LENGTH kws = LENGTH flags.rcf_kws /\ raw_call_kws_ok flags kws
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >>
  namedCases_on `args` ["", "a rest"] >- simp[Once well_typed_expr_def] >>
  Cases_on `rest` >> simp[Once well_typed_expr_def]
QED

Theorem raw_calldata_pre_operands_flags_mods:
  expr_body_pre_mods mods cenv cx env
    (Call ann (RawCallCalldataTarget flags) args dflt) es ==>
  ?a kws. args = a::kws /\ expr_type a = BaseT AddressT /\
    LENGTH kws = LENGTH flags.rcf_kws /\ raw_call_kws_ok flags kws /\
    ann = raw_call_return_type flags /\ dflt = NONE /\
    ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
    flags.rcf_max_outsize < dimword (:256)
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >>
  Cases_on `args` >> simp[Once well_typed_expr_def]
QED

Theorem request_operand_pre_mods:
  (tgt = Send has_gas \/ tgt = RawCallTarget flags \/
   tgt = RawCallCalldataTarget flags) /\
  expr_body_pre_mods mods cenv cx env (Call ann tgt args dflt) es /\
  MEM e args /\ expr_sim_inv_mods mods cenv cx env ee ==>
  expr_body_pre_mods mods cenv cx env e ee
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` mp_tac >>
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, int_calls_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, supported_expr_exists_def,
       supported_exprs_exists_every, expr_has_evm_run_thm, EXISTS_MEM] >>
  strip_tac >>
  drule_all_then assume_tac well_typed_exprs_member >>
  drule_all_then assume_tac byte_widths_exprs_mem >>
  drule_all_then assume_tac alloc_limits_exprs_mem >>
  drule_all_then assume_tac call_evaluation_safe_exprs_mem >>
  drule_all_then assume_tac int_calls_exprs_every_mem >>
  simp[] >> metis_tac[]
QED
