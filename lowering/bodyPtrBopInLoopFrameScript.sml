Theory bodyPtrBopInLoopFrame
Ancestors emitHelperProps exprSimWordBuiltins intCallFrame
  ptrDiscipline compileEnv venomState finite_map list pred_set

(* Lookup/update and restriction algebra are already FLOOKUP_UPDATE and
   FLOOKUP_DRESTRICT. This is their variable-taint constructor boundary. *)
Theorem set_var_taint_other:
  !tv outs marks x.
    ~MEM x outs ==>
    FLOOKUP (set_var_taint tv outs marks) x = FLOOKUP tv x
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `outs` >- simp[set_var_taint_def, FLOOKUP_DRESTRICT] >>
  rename1 `~MEM x (h::tail)` >> Cases_on `tail` >>
  gvs[set_var_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem variable_taint_frame:
  !tn outs marks op.
    (!x. op = Var x ==> ~MEM x outs) ==>
    op_taint (tn with t_var := set_var_taint tn.t_var outs marks) op =
      op_taint tn op /\
    (tn with t_var := set_var_taint tn.t_var outs marks).t_mem = tn.t_mem /\
    (tn with t_var := set_var_taint tn.t_var outs marks).t_stor = tn.t_stor /\
    (tn with t_var := set_var_taint tn.t_var outs marks).t_trans = tn.t_trans /\
    (tn with t_var := set_var_taint tn.t_var outs marks).t_imm = tn.t_imm
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[op_taint_def, set_var_taint_other]
QED

(* Concrete record equation records every unchanged state field, including
   predecessor field at a jump. Operand transport is handled locally in
   the combined fresh-update/jump boundary below. *)
Theorem update_jump_record:
  !s dst value lbl.
    jump_to lbl (update_var dst value s) = s with <|
      vs_vars := s.vs_vars |+ (dst,value);
      vs_prev_bb := SOME s.vs_current_bb;
      vs_current_bb := lbl; vs_inst_idx := 0 |>
Proof
  simp[jump_to_def, update_var_def]
QED

(* Old operands survive any generated destination at/above the frontier;
   the provenance may either be assigned there or restricted away there. *)
Theorem old_name_fresh_ghost_frame:
  !sa x j G p tn marks.
    not_fresh_at sa x ==>
    FLOOKUP (G |+ (STRING #"%" (toString (sa.cs_next_var+j)),p)) x =
      FLOOKUP G x /\
    FLOOKUP (DRESTRICT G (COMPL {STRING #"%" (toString (sa.cs_next_var+j))})) x =
      FLOOKUP G x /\
    op_taint (tn with t_var := set_var_taint tn.t_var
      [STRING #"%" (toString (sa.cs_next_var+j))] marks) (Var x) =
      op_taint tn (Var x)
Proof
  rpt gen_tac >> strip_tac >>
  `x <> STRING #"%" (toString (sa.cs_next_var+j))` by
    (fs[not_fresh_at_def]) >>
  `x <> STRING #"%" (toString (j+sa.cs_next_var))` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def, set_var_taint_def]
QED

(* This composes the existing fresh-update operand boundary with raw jump
   transport; equality transitivity composes arbitrary successive frames. *)
Theorem old_operand_fresh_update_jump:
  !sa op j w s lbl.
    (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op (jump_to lbl
      (update_var (STRING #"%" (toString (sa.cs_next_var+j))) w s)) =
    eval_operand op s
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand op (jump_to lbl
    (update_var (STRING #"%" (toString (sa.cs_next_var+j))) w s)) =
   eval_operand op (update_var (STRING #"%" (toString (sa.cs_next_var+j))) w s)` by
    (Cases_on `op` >> simp[eval_operand_def, jump_to_def, lookup_var_def]) >>
  simp[] >> irule eval_operand_update_not_fresh >> qexists_tac `sa` >> simp[]
QED
