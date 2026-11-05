Theory bodyPtrTypeBuiltinsConsumerResidual
Ancestors
  bodyPtrTypeBuiltinsIndexContinue bodyPtrTypeBuiltinsBounds
  bodyPtrTypeBuiltinsSourcePrefix bodyPtrPreds bodyPtrDefs loweringPosts
  ptrDiscipline ptrSafeRun venomExecSemantics venomState venomInst
  builtinBytes exprLowering emitHelper compileEnv finite_map words fragExec contextCodegenRel codegenRel
Libs intLib wordsLib

(* Reproducible diagnostic only, NOT a theorem or an admission.
   Full linked-frame residual: TO_typebuiltin-20261105T170415Z_m1242_t001.
   All saved_source_index_outcome antecedents are present: drule_all below
   succeeds, retaining its outcome. The displayed normal witness additionally
   carries the same source/index gas equations and three linked safe paths.
   This is a residual, NOT a satisfiability proof or target counterexample.

   Comparison audit for compile_extract32_load (Var start case):
   instruction       operands          provenance obligation
   ADD end           [start; Lit 32]   forwards start provenance, no comparison
   LT overflow       [end; start]      both absent OR same-site coverage of both
   GT oob            [end; len]        clean len forces end absent (boundary below)
   OR / ISZERO       booleans          no comparison clause
   ASSERT            [ok]              no comparison clause
   ADD data+start    [data; start]     not a comparison; later MLOAD needs coverage
   clamp comparisons value / literals  no two-variable comparison restriction
   No EQ is emitted by compile_assert_slice_bounds. Literal start removes
   LT's two-variable clause and gives end absent through ADD's first_prov.

   The initial length MLOAD gives absent len, preserved to the index endpoint
   by freshness/ghost_kept (supplied explicitly below). ADD forwards start's
   provenance to end; LT clears overflow only. Thus GT asks for absence at
   the SAME normal index witness. ptr_val_ok supplies clean taint, not that
   absence. An adequate missing compiler interface must select a complete
   source/index witness with absent scalar result while preserving the same
   ctx/func, initial ghost, counted path and entire semantic post. Alternatively
   a reachable-state compiler ownership invariant could imply absence here.
   Neither is established by this diagnostic; no semantic post is transported
   backwards and no arbitrary endpoint is identified with the outcome witness.
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
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (vyperState$bind (eval_expr cx src) (read_result cx)) expr_res_ok es0 /\
  (!tail. vyperState$bind (eval_expr cx src) (read_result cx)
     (es0 with gas_obs := gas_explicit srcmarks s0.vs_gas_readings ++ tail) =
     (INL sv, es with gas_obs := tail)) /\
  gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 (LENGTH srcmarks) Gsrc tnsrc (OK ss) /\
  expr_post ctx func cenv cx src es0 sa sb s0 es sv sop ss /\
  ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ghost_inv d cenv cx es Gsrc tnsrc ss /\
  gas_path_ptr (cx_dead cx) 0 ctx func PG Gsrc tnsrc ss 0 Gs tns (OK s) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es Gs tns s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (expr_type src) sa sc es sv sop s /\
  ~is_word_type (expr_type src) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type src) = SOME tv ==> dynarray_free tv) /\
  ptr_mem_ok cx (expr_type src) sv sop Gs tns s /\
  (!q. sop = Var q ==> not_fresh_at sc q) /\ (!l. sop <> Label l) /\
  (!q sz. cenv.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at sc q) /\
  (!q sz. cenv.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at sc q) /\
  expr_sim_ptr d ctx PG func cenv cx ty idx es /\ fn_has_code sc sd func /\
  gas_admissible (vyperState$bind (eval_expr cx idx) (read_result cx)) expr_res_ok es /\
  (!tail. vyperState$bind (eval_expr cx idx) (read_result cx)
     (es with gas_obs := gas_explicit idxmarks s.vs_gas_readings ++ tail) =
     (INL iv, ee with gas_obs := tail)) /\
  gas_path_ptr (cx_dead cx) 0 ctx func PG Gs tns s (LENGTH idxmarks) G tn (OK t) /\
  expr_post ctx func cenv cx idx es sc sd s ee iv (Var x) t /\
  t.vs_current_bb = sd.cs_current_bb /\ t.vs_inst_idx = LENGTH sd.cs_current_insts /\
  ghost_inv d cenv cx ee G tn t /\
  ptr_val_ok cx (expr_type idx) iv (Var x) G tn t /\
  (~is_word_type (expr_type idx) ==> ptr_buf_ok cenv idx (Var x) G t) /\
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
  drule_all saved_source_index_outcome >> disch_then assume_tac >>
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
