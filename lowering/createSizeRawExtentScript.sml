(* Extent of a raw CREATE at its observed dispatch, before the instruction runs. *)
Theory createSizeRawExtent
Ancestors
  bodyPtrMakeArrayEmission emitHelperProps loweringShapeRules loweringShapeDefs
  stmtReasonMemory fragGasOrigin fragExec venomExecSemantics venomInst venomState
  loweringStateRelDefs words arithmetic list

Theorem raw_add_observed[local]:
  emit_op ADD [lhs;rhs] a = (out,b) /\ fn_has_code a b func /\
  p.vs_current_bb = a.cs_current_bb /\
  p.vs_inst_idx = LENGTH a.cs_current_insts /\
  gas_origin_edge F explicit ctx func p ms (OK q) ==>
  ?x u v. out = Var x /\ not_fresh_at b x /\
          eval_operand lhs p = SOME u /\ eval_operand rhs p = SOME v /\
          lookup_var x q = SOME (u + v) /\
          (!y. not_fresh_at a y ==> lookup_var y q = lookup_var y p)
Proof
  strip_tac >>
  drule_all emit_op_fetch_boundary >> strip_tac >>
  drule emit_op_facts >> strip_tac >> gvs[] >>
  qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _` mp_tac >>
  simp[gas_origin_edge_def] >> strip_tac >>
  gvs[step_inst_non_invoke, is_terminator_def, exit_result_def, step_add_eq,
      AllCaseEqs(), lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem create_raw_pre_dispatch_extent:
  emit_op MLOAD [snap] ch = (len,cl) /\
  eval_operand len l = SOME (n2w (LENGTH code)) /\
  emit_op ADD [snap;Lit 32w] cl = (data,cd) /\ fn_has_code cl cd func /\
  l.vs_current_bb = cl.cs_current_bb /\
  l.vs_inst_idx = LENGTH cl.cs_current_insts /\
  gas_origin_edge F explicit ctx func l ms (OK r) /\
  (if ctor_args = [] then
     payload = [] /\ size_op = len /\ cv = cd /\ v0 = r
   else
     ?ce z alen ems.
       (!x d. not_fresh_at cd x /\ lookup_var x r = SOME d ==>
              lookup_var x z = SOME d) /\
       eval_operand alen z = SOME (n2w (LENGTH payload)) /\
       emit_op ADD [len;alen] ce = (size_op,cv) /\ fn_has_code ce cv func /\
       z.vs_current_bb = ce.cs_current_bb /\
       z.vs_inst_idx = LENGTH ce.cs_current_insts /\
       gas_origin_edge F explicit ctx func z ems (OK v0)) /\
  (!x d. not_fresh_at cv x /\ lookup_var x v0 = SOME d ==>
         lookup_var x v1 = SOME d) /\
  cv.cs_next_var <= csalt.cs_next_var /\
  (!x d. not_fresh_at csalt x /\ lookup_var x v1 = SOME d ==>
         lookup_var x s = SOME d) /\
  eval_operand size_op s = SOME w ==>
  w2n w <= LENGTH code + LENGTH payload
Proof
  strip_tac >>
  drule_all raw_add_observed >> strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (qx_choose_then `lenvar` strip_assume_tac o MATCH_MP (SPEC_ALL emit_op_facts)) >>
  `not_fresh_at cd lenvar` by
    (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `cl` >>
     drule_all emitted_insts_emit_op >> simp[]) >>
  `lookup_var lenvar r = SOME (n2w (LENGTH code))` by
    (fs[eval_operand_def] >> metis_tac[]) >>
  qpat_x_assum `emit_op ADD [snap;Lit 32w] cl = _` kall_tac >>
  `?x. size_op = Var x /\ not_fresh_at cv x /\
       lookup_var x v0 = SOME (n2w (LENGTH code + LENGTH payload))` by
    (Cases_on `ctor_args = []` >> fs[] >>
     TRY (qexists_tac `lenvar` >> simp[] >> NO_TAC) >>
     `eval_operand (Var lenvar) z = SOME (n2w (LENGTH code))` by
       (simp[eval_operand_def] >>
        qpat_assum `!x d. not_fresh_at cd x /\ lookup_var x r = SOME d ==> _` irule >>
        simp[]) >>
     drule_all raw_add_observed >>
     disch_then (qx_choose_then `sizevar` strip_assume_tac) >>
     qexists_tac `sizevar` >> gvs[word_add_n2w]) >>
  qmatch_asmsub_rename_tac `size_op = Var sizevar` >>
  `not_fresh_at csalt sizevar` by
    (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `cv` >> simp[]) >>
  `lookup_var sizevar v1 = SOME (n2w (LENGTH code + LENGTH payload))` by
    (qpat_assum `!x d. not_fresh_at cv x /\ lookup_var x v0 = SOME d ==> _` irule >> simp[]) >>
  `lookup_var sizevar s = SOME (n2w (LENGTH code + LENGTH payload))` by
    (qpat_assum `!x d. not_fresh_at csalt x /\ lookup_var x v1 = SOME d ==> _` irule >> simp[]) >>
  gvs[eval_operand_def, w2n_n2w, MOD_LESS_EQ, ZERO_LT_dimword]
QED
