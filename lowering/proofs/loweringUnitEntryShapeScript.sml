Theory loweringUnitEntryShape
Ancestors
  list unitShapeDefs o1PassContract

Theorem unit_entry_no_params_from_first:
  o1_source_unit_ok unit /\
  ALL_DISTINCT (MAP (\f. f.fn_name) unit.cu_context.ctx_functions) /\
  EVERY (\i. ~is_param_opcode i.inst_opcode)
    (fn_insts (HD unit.cu_context.ctx_functions)) ==>
  unit_entry_no_params unit
Proof
  strip_tac >>
  `entry_fn_first unit.cu_context` by
    fs[o1_source_unit_ok_def, unit_shape_ok_def] >>
  qpat_x_assum `entry_fn_first _`
    (strip_assume_tac o REWRITE_RULE [entry_fn_first_def]) >>
  rename1 `_ = efn :: rest` >>
  qpat_x_assum `_.ctx_functions = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >>
              rewrite_tac [unit_entry_no_params_def, entry_fn_no_params_def, th]) >>
  qx_gen_tac `g` >> simp_tac std_ss [MEM] >> rpt strip_tac
  >- fs[] >>
  `MEM g.fn_name (MAP (\f. f.fn_name) rest)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  gs[]
QED
