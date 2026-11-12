(*
 * The arity of a source INVOKE under FmpLowering's stage context: its
 * arguments match the callee's user parameters.  Admitted: the callee is
 * observed through the walk view (o1_walk_view rpolicy 3), and row 3 has no
 * fact relating INVOKE arity to the observed callee's PARAMs.  Proving it
 * needs a hub change, either carrying the shape and rows through walk_view
 * with per-pass PARAM-count lemmas (route A) or an o1_inv arity row
 * (route B).
 *
 * TOP-LEVEL:
 *   fmp_stage_invoke_arity  - LENGTH args = LENGTH (fn_user_param_insts callee)
 *)
Theory fmpStageCallArity
Ancestors
  fmpStageRel callLayoutDefs venomExecSemantics

Theorem fmp_stage_invoke_arity:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ MEM fn C.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,args) /\
  lookup_function nm C.ctx_functions = SOME callee ==>
  LENGTH args = LENGTH (fn_user_param_insts callee)
Proof
  cheat
QED
