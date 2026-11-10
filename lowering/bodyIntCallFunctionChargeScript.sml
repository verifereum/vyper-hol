(* Charge of an actual internal-function compilation, including constructors. *)
Theory bodyIntCallFunctionCharge
Ancestors
  bodyIntCallPackageResource intCallCallee externalEntryShape compileEnv
  moduleLowering emitHelper context list rich_list finite_map words
  exprLoweringProps loweringShapeDefs venomInst

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
  cheat
QED
