(* Package the selected request-buffer allocation at its ready state. *)
Theory bodyExtRequestSiteMods
Ancestors
  compileEnv venomInst venomState words finite_map list

Theorem extcall_request_site_witness_mods:
  (cenv.ce_is_ctor /\ cap <> 0 ==>
   ?root w. buf = Var root /\
     MEM (mk_inst aid ALLOCA [Lit (n2w n)] [root]) (fn_insts func) /\
     eval_operand buf s = SOME w /\
     FLOOKUP s.vs_allocas aid = SOME (w2n w,n) /\ cap <= n) ==>
  (cenv.ce_is_ctor /\ cap <> 0 ==>
   ?i w k. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
     eval_operand buf s = SOME w /\
     FLOOKUP s.vs_allocas i.inst_id = SOME (w2n w,k) /\ cap <= k)
Proof
  disch_tac >> disch_tac >>
  qpat_x_assum `_ ==> ?root w. _` mp_tac >> simp[] >>
  disch_then (qx_choosel_then [`root`,`w`] strip_assume_tac) >>
  qexistsl [`mk_inst aid ALLOCA [Lit (n2w n)] [root]`,`w`,`n`] >>
  fs[mk_inst_def]
QED
