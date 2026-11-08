(* Guarded recursive callbacks preserve the weak first-emission interface. *)
Theory guardedCallbackFirstEmission
Ancestors
  compilerFirstEmission exprCallBounds exprPlaceFirstEmission exprLowering
  fragExec compileEnv emitHelper venomInst context

Theorem first_emission_invalid_expr_call:
  !a x b. invalid_expr_call ty a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> simp[invalid_expr_call_def, LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_at (Pos (el 2)) (cj 1 first_emission_emit_helpers) >> simp[]
QED

Theorem first_emission_expr_child_callback:
  (!ce ty e a x b. expr_size e < bound /\ cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce ty e a x b. expr_child_callback bound cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `expr_size e < bound` >>
  simp[expr_child_callback_def] >> metis_tac[first_emission_invalid_expr_call]
QED

Theorem first_emission_builtin_child_callback:
  (!ce rt ty bi es a x b. list_size expr_size es < bound /\
    dispatch ce rt ty bi es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce rt ty bi es a x b. builtin_child_callback bound dispatch ce rt ty bi es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `list_size expr_size es < bound` >>
  simp[builtin_child_callback_def] >> metis_tac[first_emission_invalid_expr_call]
QED

Theorem first_emission_type_child_callback:
  (!ce vt ty tb rt es a x b. list_size expr_size es < bound /\
    dispatch ce vt ty tb rt es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce vt ty tb rt es a x b. type_child_callback bound dispatch ce vt ty tb rt es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `list_size expr_size es < bound` >>
  simp[type_child_callback_def] >> metis_tac[first_emission_invalid_expr_call]
QED

Theorem first_emission_guarded_attribute:
  (!ce ty e a x b. expr_size e < expr_size (Attribute ann base_e fld) /\
    cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_attribute
    (expr_child_callback (expr_size (Attribute ann base_e fld)) cfn)
    ce rt ty base_e fld a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> match_mp_tac first_emission_attribute >>
  rpt gen_tac >> simp[expr_child_callback_def, expr_attribute_child_bound] >>
  metis_tac[expr_attribute_child_bound]
QED

(* The actual compile_expr_ind has predicates P0 ce ty e st,
   P1 ce rt ty bi es st and P2 ce vt ty tb rt es st.  Instantiate each
   predicate with: for every result x and endpoint b, evaluation at st
   implies the full weak first-emission contract above.  Its recursive
   premises quantify over ALL environments, types and states below the
   expression/list-size bound.  They therefore match the three guarded
   lifting hypotheses directly.  The type dispatcher has an additional
   F-guarded builtin premise, which simplifies away.  The Attribute
   consumer above checks the exact expression-child bound at a use site. *)
