(* Concrete pointer checks for RawLog's fixed-data continuation. *)
Theory bodyFullRawLogFixedTail
Ancestors
  bodyFullRawLogFixedBoundary rawLogPtrInst bodyPtrDefs ptrDiscipline
  ptrSafeRun venomState venomInst venomExecSemantics words list

Theorem raw_log_fixed_log_inst_ok:
  LENGTH topics < dimword (:256) /\
  eval_operand pop s = SOME off /\
  eval_operands topics s = SOME vals /\
  (?p b sz. pop = Var p /\ FLOOKUP G p = SOME (b,sz) /\
    b <= w2n off /\ w2n off + 32 <= b + sz) /\
  EVERY (\op. op_taint tn op = {}) topics /\
  op_taint tn pop = {} /\
  (!i. w2n off <= i /\ i < w2n off + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  stor_taint_ok_at D tn s /\
  step_inst_base
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s = OK t ==>
  ptr_inst_ok D lo fuel ctx fn G tn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s
Proof
  strip_tac >>
  `access_ok 0 G fn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s` by
    (irule log_access_ok >> simp[eval_operand_def, dimword_def] >> metis_tac[]) >>
  `access_ok lo G fn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s` by
    (gvs[access_ok_def] >> rpt strip_tac >> metis_tac[arithmeticTheory.ADD_EQ_0]) >>
  `taint_ok fn tn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s` by
    (irule log_taint_ok >> simp[eval_operand_def, op_taint_def, dimword_def] >> metis_tac[]) >>
  gvs[ptr_inst_ok_def, stor_taint_ok_at_def, mk_inst_def, step_inst_non_invoke]
QED
