(* Stage-facing backwards ASSIGN transport at a retained copy endpoint. *)
Theory fmpStageCoverForwardBoundary
Ancestors
  fmpStageCoverForwardActual fmpStageCoverForwardPrefix
  fmpStageRel irSupply unitMemInv venomInst venomExecSemantics

Theorem fmp_stage_copy_prefix_same_after:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block lbl fn'.fn_blocks = SOME bb' /\
  get_instruction bb p = SOME inst /\ inst.inst_opcode = RETURNDATACOPY /\
  get_instruction bb' tp = SOME inst /\
  (!v. a = Var v ==> MEM v (fn_ir_vars fn)) /\
  (!v. b = Var v ==> MEM v (fn_ir_vars fn)) /\
  same_after_assigns (REVERSE (TAKE p bb.bb_instructions)) a b ==>
  same_after_assigns (REVERSE (TAKE tp bb'.bb_instructions)) a b
Proof
  strip_tac >>
  drule_all fmp_stage_covered_lowering >> strip_tac >>
  drule_all fmp_stage_target_block_ids_distinct >> strip_tac >>
  drule_all fmp_prefix_function_same_after >> simp[]
QED
