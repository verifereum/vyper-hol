(* Entry-only instruction predicates survive internal-function packaging. *)
Theory ctorCallFreeEntry
Ancestors
  ctorCallFreeRules externalEntryShape ctorDeployLoweringNoCtor
  vyperCompiler loweringShapeDefs venomInst list

Theorem packaged_entry_every:
  compile_internal_fn_bodies packages se = ((),sf) /\
  (packages <> [] ==>
    ~MEM (FST (HD packages)) (MAP (\bb. bb.bb_label) (all_blocks se))) /\
  extract_context_with_internals entry packages sf = SOME (ctx,data) /\
  EVERY P (state_insts se) ==>
  ?efn.
    ctx.ctx_entry = SOME efn.fn_name /\
    lookup_function efn.fn_name ctx.ctx_functions = SOME efn /\
    EVERY P (fn_insts efn)
Proof
  simp[extract_context_with_internals_def, GSYM all_blocks_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all compile_internal_fn_bodies_entry_prefix >> strip_tac >>
  qexists_tac `mk_raw_function entry (all_blocks se)` >>
  gvs[mk_venom_context_def, mk_raw_function_def, lookup_function_def,
      FIND_thm, fn_insts_def, EVERY_fn_insts_blocks,
      every_state_insts_blocks]
QED

Theorem immutable_reservation_entry_every:
  ctx.ctx_entry = SOME efn.fn_name /\
  lookup_function efn.fn_name ctx.ctx_functions = SOME efn /\
  EVERY P (fn_insts efn) ==>
  (install_immutable_reservation imm ctx).ctx_entry = SOME efn.fn_name /\
  lookup_function efn.fn_name
    (install_immutable_reservation imm ctx).ctx_functions = SOME efn /\
  EVERY P (fn_insts efn)
Proof
  simp[install_immutable_reservation_def]
QED

Theorem no_ctor_lowering_entry_call_free:
  run_deploy_lowering F rpolicy bytes imm args sz [] cenv stmts
    pay nr nkey ut entry = SOME unit ==>
  ?efn.
    unit.cu_context.ctx_entry = SOME efn.fn_name /\
    lookup_function efn.fn_name unit.cu_context.ctx_functions = SOME efn /\
    EVERY (\inst. inst.inst_opcode <> RETURNDATACOPY /\
                  inst.inst_opcode <> INVOKE) (fn_insts efn)
Proof
  strip_tac >> drule no_ctor_lowering_context_shape >> strip_tac >>
  qexists_tac `HD unit.cu_context.ctx_functions` >>
  gvs[install_immutable_reservation_def, mk_venom_context_def,
      mk_raw_function_def, lookup_function_def, FIND_thm,
      fn_insts_def, fn_insts_blocks_def, mk_inst_def]
QED
