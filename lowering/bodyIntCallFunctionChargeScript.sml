(* Charge of an actual internal-function compilation, including constructors. *)
Theory bodyIntCallFunctionCharge
Ancestors
  bodyIntCallPackageResource intCallCallee externalEntryShape compileEnv
  moduleLowering emitHelper context list rich_list finite_map words
  exprLoweringProps loweringShapeDefs venomInst bodyIntCallFnChargeMaterialize bodyIntCallFnChargePhases

Theorem internal_param_capture_projection:
  !ps idx sa caps next sb.
  compile_internal_param_decls ps idx sa = ((caps,next),sb) ==>
  MAP (\c. (FST c,FST (SND c))) caps = ps
Proof
  rpt gen_tac >> strip_tac >>
  drule intCallCalleeTheory.compile_internal_param_decls_shape >>
  simp[] >> strip_tac >>
  irule LIST_EQ >> simp[EL_MAP]
QED

Theorem internal_entry_prefix_layout:
  !ce ps hr sa cep caps rpc sb.
  compile_internal_entry_prefix ce ps hr sa = ((cep,caps,rpc),sb) ==>
  cep.ce_vars = ce.ce_vars /\ MAP (\c. (FST c,FST (SND c))) caps = ps
Proof
  rpt gen_tac >>
  simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  Cases_on `pr` >> drule internal_param_capture_projection >> simp[]
QED

(* FROZEN OWNER LEAF: proved by its own run, cheat until then.
   Historical obligation C1.5.3.1.1. The additive formulation counts
   only the new charge even when sa already contains other functions. *)
Theorem compile_internal_function_stack_charge:
  !ce params has_rb is_nr key trans view ctor imm body rt sa sb.
    compile_internal_function ce params has_rb is_nr key trans view
      ctor imm body rt sa = ((),sb) /\
    ALL_DISTINCT (MAP FST params) /\
    (!nm off sz. MEM nm (MAP FST params) /\
       FLOOKUP ce.ce_vars nm = SOME (MemLoc off sz) ==>
       sz < dimword (:256)) ==>
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts sa))) +
    internal_stack_size ce params <=
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts sb)))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_internal_function _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_function_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_internal_param_decls _ _ _ = (decls,_)` >>
  Cases_on `decls` >> gvs[] >>
  qmatch_asmsub_abbrev_tac `materialize_internal_params cep caps sp = (ceq,sm)` >>
  drule internal_param_decls_projection >> strip_tac >>
  drule materialize_internal_params_state_charge >>
  (impl_tac >- (simp[Abbr `cep`] >> metis_tac[])) >> strip_tac >>
  drule internal_return_param_extends >> strip_tac >>
  drule internal_immutable_region_extends >> strip_tac >>
  drule (SRULE [comp_ignore_bind_def] internal_return_region_extends) >> strip_tac >>
  drule (SRULE [comp_ignore_bind_def] internal_function_exit_extends) >> strip_tac >>
  rename1 `compile_internal_param_decls _ _ sr = (_,sd)` >>
  rename1 `emit_op RETPC_PARAM _ sd = (_,se)` >>
  `cs_extends sr sd` by
    metis_tac[cj 1 compile_internal_param_decls_labels, pairTheory.SND] >>
  `cs_extends sd se` by metis_tac[cj 1 emit_op_labels, pairTheory.SND] >>
  `cs_extends sa sp` by metis_tac[cs_extends_trans] >>
  rename1 `compile_stmts _ _ _ _ sl = (_,sc)` >>
  rename1 `comp_get sc = (_,sg)` >>
  `cs_extends sl sc` by metis_tac[cj 2 compile_stmt_labels, pairTheory.SND] >>
  `cs_extends sc sg` by metis_tac[cj 1 comp_get_labels, pairTheory.SND] >>
  rename1 `(if is_nr then compile_nonreentrant_lock _ _ _ else _) sn = (_,sl)` >>
  `cs_extends sn sl` by
    (Cases_on `is_nr` >> gvs[comp_return_def] >>
     metis_tac[cj 1 compile_nonreentrant_lock_labels, pairTheory.SND, cs_extends_refl]) >>
  rename1 `(if block_is_terminated _ then _ else _) sg = ((),sf)` >>
  `cs_extends sm sf` by
    (irule cs_extends_trans >> qexists_tac `sn` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `sl` >> simp[] >>
     metis_tac[cs_extends_trans]) >>
  qspecl_then [`sp`,`sa`] mp_tac (GEN_ALL state_alloca_charge_mono) >> simp[] >> strip_tac >>
  qspecl_then [`sf`,`sm`] mp_tac (GEN_ALL state_alloca_charge_mono) >> simp[] >> strip_tac >>
  `internal_stack_size cep params = internal_stack_size ce params` by
    (irule internal_stack_size_vars >> simp[Abbr `cep`]) >>
  gvs[] >> decide_tac
QED
