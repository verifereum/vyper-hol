(* Whitelist removal, S2: the O1 shape extras of the lowered runtime unit
   (no PARAM in the entry function, no FMP convention set) from the type
   checker instead of supported_program.

   The no-PARAM fact comes out of the body-shape invariant
   (lowered_inst_ok in shape_step), which has no case for raw_call or
   creation, so the statement keeps raw_shape_free_program, as
   lower_vyper_runtime_unit_source_unit_ok_checked does. *)
Theory whitelistS2Extras
Ancestors
  vyperLoweringCorrect loweringShapeSource loweringShapeProps vyperCompiler
  unitShapeDefs o1PassContract venomInst

Theorem lower_vyper_runtime_unit_o1_shape_extras_rawfree:
  !tops rpolicy unit layouts addr art.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    check_contract F layouts addr [(NONE, tops)] = SOME art /\
    raw_shape_free_program tops
    ==> unit_entry_no_params unit /\ unit_fmp_unsealed unit
Proof
  rpt gen_tac >> strip_tac >>
  drule lower_vyper_runtime_unit_run_lowering >> strip_tac >>
  reverse conj_tac >- metis_tac[run_lowering_fmp_unsealed] >>
  drule lower_vyper_runtime_unit_source_unit_ok_shape_with_no_params >>
  impl_tac
  >- metis_tac[check_contract_runtime_bodies_shape_ok,
               check_contract_internal_names_distinct] >>
  strip_tac >>
  `entry_fn_first unit.cu_context` by
    fs[o1_source_unit_ok_def, unit_shape_ok_def] >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) unit.cu_context.ctx_functions)` by
    (drule run_lowering_context_ok >>
     simp[lowering_context_ok_def, ctx_fn_names_def]) >>
  qpat_x_assum `entry_fn_first _`
    (strip_assume_tac o REWRITE_RULE [entry_fn_first_def]) >>
  rename1 `_ = efn :: rest` >>
  qpat_x_assum `_.ctx_functions = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >>
              rewrite_tac [unit_entry_no_params_def, entry_fn_no_params_def,
                           th]) >>
  qx_gen_tac `g` >> simp_tac std_ss [listTheory.MEM] >> rpt strip_tac
  >- fs[] >>
  `MEM g.fn_name (MAP (\f. f.fn_name) rest)` by
    (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
  gs[]
QED
