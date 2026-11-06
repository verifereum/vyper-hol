(* Counted memory paths for the concrete EC scratch/precompile runs. *)
Theory bodyMemEcArithPaths
Ancestors
  bodyMemEcArithInstructionSafety bodyMemEcArithResultBounds exprSimECArith
  bodyMemBiMethodIdSuffix bodyMemBiSha256Compose exprSimVVFrame
  fragGasSeqAbort fragGasSeqMem exprLoweringProps compileEnv
  venomInstProps venomExecSemantics exprSimDefs loweringPosts fragExec

Theorem ec_counted_success_mem:
  (compile_ecadd_points p q sa = (op,sb) \/
   compile_ecmul_point p q sa = (op,sb)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  vv_post ctx func cenv cx e es sa sb s es' (Value v) vv t /\
  vv = LocatedValue (expr_type e) rp /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  lowered_value_type cenv e = expr_type e ==>
  ?u n. gas_marked_path T ctx func s n (OK u) /\
    vv_post ctx func cenv cx e es sa sb s es' (Value v) vv u /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es'
      (Value v) vv u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   same_blocks sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by metis_tac[ec_points_code_shape] >>
  `alloca_inv s` by fs[stmt_state_rel_def, state_rel_def] >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  drule_all method_id_run_path_mem >> strip_tac >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    metis_tac[sha256_run_inst_seq_alloca_next_mono] >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb`
       run_inst_seq_preserves_field)) >> goal_assum (drule_at Any) >>
     rpt strip_tac >> fs[listTheory.EVERY_MEM] >>
     metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qexists_tac `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))` >>
  first_x_assum (qspec_then `ctx` strip_assume_tac) >>
  simp[vv_post_inst_idx] >>
  metis_tac[ec_result_vv_store_bound, vv_post_inst_idx]
QED

Theorem ec_counted_revert_mem:
  (compile_ecadd_points p q sa = (op,sb) \/
   compile_ecmul_point p q sa = (op,sb)) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t ==>
  ?n rr. gas_marked_path T ctx func s n rr /\
    exit_result rr /\ expr_exit (INR (Error (RuntimeError msg))) rr
Proof
  strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   same_blocks sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by metis_tac[ec_points_code_shape] >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fn_has_code_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
     qexists_tac `l` >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     REFL_TAC) >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[rich_listTheory.IS_PREFIX_APPEND] >>
  drule_at (Pat `run_inst_seq _ _ = _`)
    (Q.SPEC `T` run_inst_seq_abort_gas_path) >> simp[] >>
  disch_then (qspecl_then [`ctx`,`func`,`bb`] mp_tac) >> simp[] >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[exit_result_def, expr_exit_def]
QED
