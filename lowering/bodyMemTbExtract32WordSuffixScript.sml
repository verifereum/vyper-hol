(* Word-result boundary for the readonly extract32 suffix. *)
Theory bodyMemTbExtract32WordSuffix
Ancestors
  bodyMemTbExtract32SuffixPost exprSimMemoryStack exprSimDefs exprSimMemDefs
  exprSimUnwrap vyperStorageFootprint loweringPosts compileEnv exprLowering vyperAST vyperInterpreter

Theorem extract32_word_suffix_success:
  compile_extract32_load l d off ca = (raw,cm) /\
  compile_clamp_basetype raw (BaseT bt) cm = (op,cb) /\
  fn_has_code ca cb func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\ alloca_history func s /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es' s /\
     storage_well_formed_on cx es' (FST H)) /\
  (?H. valid_horizon cx st0 H es'.storage_trace) /\
  wb_frame cenv es es' c0 s0 s /\
  (~expr_has_effect (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;ofs]) ==>
   pure_frame cenv func es c0 s0 s) /\
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
    (!H. valid_horizon cx st0 H es'.storage_trace ==>
       expr_post H ctx func cenv cx
         (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;ofs])
         es c0 cb s0 es' v op u) /\
    expr_store_bound cx (BaseT bt) v op u /\
    alloca_history func u /\ ~u.vs_halted /\
    u.vs_current_bb = cb.cs_current_bb /\
    u.vs_inst_idx = LENGTH cb.cs_current_insts /\
    s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  `?H. valid_horizon cx st0 H es'.storage_trace` by metis_tac[] >>
  qpat_x_assum `~expr_has_effect _ ==> _` (assume_tac o SRULE []) >>
  drule_all (SRULE [] (Q.INST
    [`code` |-> `emitted_insts sa sc ++ emitted_insts sc sb`,
     `e` |-> `TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;ofs]`]
    extract32_suffix_success_entry) |> SRULE [expr_type_def]) >>
  disch_then (qspec_then `BaseT bt` strip_assume_tac) >>
  qexists_tac `u` >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (qx_gen_tac `H1` >> strip_tac >>
      qpat_x_assum `!H. valid_horizon cx st0 H es'.storage_trace ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `H1` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      strip_tac >> drule expr_post_of_vv_post_stack >> simp[])
  >- simp[expr_store_bound_def]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
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
