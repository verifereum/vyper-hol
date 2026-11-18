(* Static user arity of the INVOKEs that FMP lowering resolves. *)
Theory fmpStageCoverBackFmpArity
Ancestors
  fmpLowerDefs callLayoutDefs venomInst list o1PassContract

Theorem fmp_lower_invoke_user_arity:
  fn.fn_fmp_signature = NONE /\
  fmp_lower_function_with_info infos ctx sp fn = SOME (fn',sp') /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label name::args ==>
  ?callee. lookup_function name ctx.ctx_functions = SOME callee /\
    LENGTH args = LENGTH (fn_user_param_insts callee)
Proof
  strip_tac >>
  `fmp_lower_input infos ctx fn` by
    (gvs[fmp_lower_function_with_info_def, AllCaseEqs()]) >>
  `IS_SOME (fmp_resolve_invoke infos ctx inst)` by
    (gvs[fmp_lower_input_def, fmp_lower_blocks_shape_def,
         fmp_lower_insts_shape_def, fn_insts_def, fn_insts_blocks_MEM,
         EVERY_MEM] >>
     `fmp_lower_inst_shape infos ctx inst` by metis_tac[] >>
     gvs[fmp_lower_inst_shape_def]) >>
  Cases_on `fmp_resolve_invoke infos ctx inst` >> gvs[] >>
  PairCases_on `x` >>
  drule fmp_resolve_invoke_some >> strip_tac >> gvs[] >> metis_tac[]
QED
