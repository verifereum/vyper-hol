Theory bodyPtrTypeBuiltinsConsumerResidual
Ancestors
  bodyPtrTypeBuiltinsIndexContinue bodyPtrTypeBuiltinsBounds
  bodyPtrTypeBuiltinsSourcePrefix bodyPtrPreds bodyPtrDefs loweringPosts
  ptrDiscipline ptrSafeRun venomExecSemantics venomState venomInst
  builtinBytes exprLowering emitHelper compileEnv finite_map words fragExec contextCodegenRel codegenRel
Libs intLib wordsLib

(* Reproducible diagnostic skeleton, NOT a theorem or an admission.
   The attempted conclusion below normalizes to x NOTIN FDOM G. The
   full-context residual is recorded in tool output m1217_t001.
Theorem extract32_consumer_probe:
  body_exprs_ptr_ok cx [src;idx] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 typ [src;idx]) es0 /\
  lower_value compile_expr cenv (expr_type src) src sa = (sop,sb) /\
  compile_bytestring_src sop sb = ((Var len,data),sc) /\
  lower_value compile_expr cenv ty idx sc = (Var x,sd) /\
  compile_assert_slice_bounds (Var x) (Lit 32w) (Var len) sd = ((),se) /\
  fn_has_code sa se func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  stmt_state_rel ctx func cenv cx es0 s0 /\ ghost_inv d cenv cx es0 G0 tn0 s0 /\
  expr_post ctx func cenv cx src es0 sa sb s0 es sv sop ss /\
  expr_post ctx func cenv cx idx es sc sd s ee iv (Var x) t /\
  t.vs_current_bb = sd.cs_current_bb /\ t.vs_inst_idx = LENGTH sd.cs_current_insts /\
  ghost_inv d cenv cx ee G tn t /\
  ptr_val_ok cx (expr_type idx) iv (Var x) G tn t /\
  ghost_kept cenv es sc Gs tns s G tn /\ ptr_mem_ok cx (expr_type src) sv sop G tn t /\
  FLOOKUP G len = NONE /\ lookup_var x t = SOME w /\
  z = STRING #"%" (toString sd.cs_next_var) /\
  ov = STRING #"%" (toString (sd.cs_next_var+1)) /\
  z <> x /\ z <> len /\ ov <> z /\ ov <> len /\
  u = update_var z (w+32w) t /\
  H1 = step_prov PG G (mk_inst sd.cs_next_id ADD [Var x;Lit 32w] [z]) u /\
  v = update_var ov (bool_to_word (w2n (w+32w) < w2n w)) u /\
  H2 = step_prov PG H1 (mk_inst (sd.cs_next_id+1) LT [Var z;Var x] [ov]) v ==>
  access_ok 0 H2 func
    (mk_inst (sd.cs_next_id+2) GT [Var z;Var len]
      [STRING #"%" (toString (sd.cs_next_var+2))]) v
Proof
  strip_tac >>
  gvs[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
      op_prov_def, mk_inst_def, FLOOKUP_UPDATE] >>
  simp[access_ok_def, mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, FDOM_FUPDATE, FLOOKUP_UPDATE] >>
  Cases_on `FLOOKUP G x` >>
  gvs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, FDOM_DRESTRICT,
      FDOM_FUPDATE, FLOOKUP_DEF] >>
  FAIL_TAC "full-context GT comparison residual"
QED
*)

(* The implementation-level boundary: one clean variable operand forces
   the other to be clean as well. Applicable to every comparison family. *)
Theorem comparison_clean_right_iff:
  (i.inst_opcode = LT \/ i.inst_opcode = GT \/ i.inst_opcode = EQ) /\
  i.inst_operands = [Var x;Var y] /\ FLOOKUP G y = NONE ==>
  (access_ok lo G fn i s <=> FLOOKUP G x = NONE)
Proof
  strip_tac >>
  gvs[access_ok_def, source_memory_write_ranges_def,
      source_memory_read_ranges_def, FLOOKUP_DEF]
QED
