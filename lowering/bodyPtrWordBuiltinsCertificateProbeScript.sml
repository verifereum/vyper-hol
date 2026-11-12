(* Compiler certificate interface probe. The prospective word-path boundary
   was typechecked (not proved) during the bounded interface audit.
   This theory deliberately exports only a checked call-transfer fact, not
   an unvalidated compiler certificate. *)
Theory bodyPtrWordBuiltinsCertificateProbe
Ancestors bodyPtrWordBuiltinsScalar ptrSafeRun ptrDiscipline finite_map pred_set

Theorem ghost_step_invoke_scalar_set:
  (!x. x IN scalars ==> FLOOKUP G x = NONE) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  (!x. x IN scalars UNION set inst.inst_outputs ==>
       FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) x = NONE)
Proof
  strip_tac >> drule_all ghost_step_invoke >>
  disch_then (qspecl_then [`fuel`, `PG`, `G`, `tn`] SUBST1_TAC) >>
  simp[FLOOKUP_DRESTRICT] >> metis_tac[]
QED
