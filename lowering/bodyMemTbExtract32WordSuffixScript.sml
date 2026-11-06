(* Word-result boundary for the readonly extract32 suffix. *)
Theory bodyMemTbExtract32WordSuffix
Ancestors
  bodyMemTbExtract32SuffixPost exprSimMemoryStack exprSimDefs exprSimMemDefs
  loweringPosts compileEnv exprLowering vyperAST vyperInterpreter

Theorem extract32_word_suffix_success:
  compile_extract32_load l d off ca = (raw,cm) /\
  compile_clamp_basetype raw (BaseT bt) cm = (op,cb) /\
  fn_has_code ca cb func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\ alloca_history func s /\
  stmt_state_rel ctx func cenv cx es' s /\ wb_frame cenv es c0 s0 s /\
  local_ptrs_reserved cenv ca /\ c0.cs_next_var <= ca.cs_next_var /\
  is_word_type (BaseT bt) /\
  eval_operand l s = SOME (n2w (LENGTH bs)) /\
  eval_operand d s = SOME (n2w (p + 32)) /\
  eval_operand off s = SOME (n2w n) /\
  (!x. l = Var x \/ d = Var x \/ off = Var x ==> not_fresh_at ca x) /\
  LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
  n + 32 <= LENGTH bs /\ p + 32 + n < dimword (:256) /\
  p + 32 < dimword (:256) /\ p + 32 + LENGTH bs <= s.vs_alloca_next /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p s.vs_memory /\
  extract32_result_base_ok bt /\ well_formed_type tenv (BaseT bt) /\
  evaluate_extract32 bs n bt = INL v /\ ~s.vs_halted ==>
  ?u. gas_path_mem ctx func s
        (LENGTH (FILTER (\i. i.inst_opcode = GAS)
          (emitted_insts ca cm ++ emitted_insts cm cb))) (OK u) /\
    expr_post ctx func cenv cx
      (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;ofs])
      es c0 cb s0 es' v op u /\
    expr_store_bound cx (BaseT bt) v op u /\
    alloca_history func u /\ ~u.vs_halted /\
    u.vs_current_bb = cb.cs_current_bb /\
    u.vs_inst_idx = LENGTH cb.cs_current_insts /\
    s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST
    [`code` |-> `emitted_insts sa sc ++ emitted_insts sc sb`,
     `e` |-> `TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;ofs]`]
    extract32_suffix_success_entry) |> SRULE [expr_type_def]) >>
  disch_then (qspecl_then [`src`, `ofs`, `BaseT bt`] strip_assume_tac) >>
  qexists_tac `u` >> simp[] >>
  fs[expr_post_def, vv_post_def, vv_holds_def, vv_at_def,
     expr_store_bound_def, vv_store_bound_def, expr_type_def,
     vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  metis_tac[]
QED

Theorem extract32_word_suffix_revert:
  compile_extract32_load l d off ca = (raw,cm) /\
  compile_clamp_basetype raw (BaseT bt) cm = (op,cb) /\
  fn_has_code ca cb func /\
  s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  eval_operand l s = SOME (n2w (LENGTH bs)) /\
  eval_operand d s = SOME (n2w (p + 32)) /\
  eval_operand off s = SOME (n2w n) /\
  (!x. l = Var x \/ d = Var x \/ off = Var x ==> not_fresh_at ca x) /\
  LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
  (n + 32 <= LENGTH bs ==> p + 32 + n < dimword (:256)) /\
  p + 32 < dimword (:256) /\ p + 32 + LENGTH bs <= s.vs_alloca_next /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p s.vs_memory /\
  extract32_result_base_ok bt /\ well_formed_type tenv (BaseT bt) /\
  evaluate_extract32 bs n bt = INR (RuntimeError msg) /\ ~s.vs_halted ==>
  ?t k j. gas_path_mem ctx func s k (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST
    [`code` |-> `emitted_insts sa sc ++ emitted_insts sc sb`]
    extract32_suffix_revert_entry)) >> simp[]
QED
