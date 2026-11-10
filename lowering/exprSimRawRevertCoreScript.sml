(*
 * raw_revert(data) simulates for any operand that simulates.
 *
 * The lowering evaluates the bytes operand with lower_value, then
 * compile_raw_revert loads its length word, adds 32 for the data start and
 * REVERTs.  The source evaluates the operand, then raises.  An operand exit
 * is the expression's exit; an operand value runs the three-instruction
 * tail, which reads no GAS, to Abort Revert_abort.
 *
 * raw_revert_vv_sim serves both the expression case (raw_revert_expr_vv_ok)
 * and the body case (raw_revert_body_expr_ok).
 *)

Theory exprSimRawRevertCore
Ancestors
  exprSimSource exprSimHypsDefs exprSimDefs exprSimSend loweringPosts
  gasContext gasSummary gasOutcome gasSummaryCompose gasExemptCert
  fragGasMode fragGasPath fragGasSeq gasCount fragExec
  exprLowering exprLoweringProps exprOperandVar emitHelper emitHelperProps
  builtinSystem compileEnv loweringStateRelDefs
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  allocLimits venomExecSemantics venomExecProps venomInst venomState
  venomInstProofs list rich_list arithmetic finite_map
Libs
  pairLib

(* ===== Source ===== *)

Theorem eval_raw_revert_action:
  !cx ann e dflt.
    eval_expr cx (Call ann RawRevert [e] dflt) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. raise (Error (RuntimeError "raw_revert")))
Proof
  rw[FUN_EQ_THM] >>
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  simp[bind_def, ignore_bind_def, return_def, type_check_def, assert_def,
       raise_def] >>
  rpt (CASE_TAC >> gvs[])
QED

Theorem expr_body_pre_raw_revert_arg:
  !cenv cx env ann args dflt e es es'.
    expr_body_pre cenv cx env (Call ann RawRevert args dflt) es /\
    MEM e args /\ expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rw[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def,
     supportedExprTraverseTheory.expr_has_evm_run_thm,
     supportedExprTraverseTheory.supported_expr_exists_def,
     supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM]
  >~ [`well_typed_expr _ _`] >- metis_tac[well_typed_exprs_member]
  >~ [`byte_widths_expr _`] >- metis_tac[byte_widths_exprs_mem]
  >~ [`alloc_limits_expr _ _`] >- metis_tac[alloc_limits_exprs_mem]
  >~ [`call_evaluation_safe _ _`]
  >- metis_tac[call_evaluation_safe_exprs_mem]
  >~ [`EVERY _ (int_calls_expr _)`]
  >- metis_tac[int_calls_exprs_every_mem] >>
  metis_tac[]
QED

Theorem raw_revert_pre_arg:
  !cenv cx env ann args dflt es.
    expr_body_pre cenv cx env (Call ann RawRevert args dflt) es ==>
    ?e. args = [e] /\ expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `?e. args = [e]` by
    (gvs[expr_body_pre_def, well_typed_expr_def, LENGTH_EQ_NUM_compute]) >>
  gvs[] >> irule expr_body_pre_raw_revert_arg >>
  gvs[expr_body_pre_def] >> metis_tac[MEM]
QED

(* ===== Compile ===== *)

Theorem compile_expr_raw_revert_arg:
  !cenv ty ann e dflt st.
    compile_expr cenv ty (Call ann RawRevert [e] dflt) st =
    let (data, st1) = lower_value compile_expr cenv (expr_type e) e st in
    let (_, st2) = compile_raw_revert data st1 in
    (StackValue ann (Lit 0w), st2)
Proof
  simp[compile_expr_call, compile_call_def]
QED

Theorem raw_revert_compile:
  !cenv ty ann e dflt sa vv sb.
    compile_expr cenv ty (Call ann RawRevert [e] dflt) sa = (vv,sb) ==>
    ?data sm. lower_value compile_expr cenv (expr_type e) e sa = (data,sm) /\
      compile_raw_revert data sm = ((),sb)
Proof
  rpt gen_tac >>
  simp[compile_expr_raw_revert_arg] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `compile_raw_revert data st1 = (u,_)` >> Cases_on `u` >> simp[]
QED

Theorem raw_revert_tail_layout:
  !data sa u sb.
    compile_raw_revert data sa = (u,sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id MLOAD [data]
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id + 1) ADD [data; Lit 32w]
         [STRING #"%" (toString (sa.cs_next_var + 1))];
       mk_inst (sa.cs_next_id + 2) REVERT
         [Var (STRING #"%" (toString (sa.cs_next_var + 1)));
          Var (STRING #"%" (toString sa.cs_next_var))] []]
Proof
  simp[compile_raw_revert_def, emit_op_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, same_blocks_def,
       APPEND_ASSOC]
QED

Theorem raw_revert_extends:
  !data sa u sb.
    compile_raw_revert data sa = (u,sb) ==> cs_extends sa sb
Proof
  rpt strip_tac >> drule raw_revert_tail_layout >> strip_tac >>
  simp[cs_extends_def] >> qexists_tac `[]` >>
  gvs[same_blocks_def, IS_PREFIX_APPEND]
QED

(* ===== Target tail ===== *)

Theorem straight_edge_zero[local]:
  !ctx func s bb i u.
    ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS /\
    step_inst_base i s = OK u ==>
    gas_path_edge ctx func s 0 (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `(if i.inst_opcode = GAS then 1 else 0) = 0` by simp[] >>
  metis_tac[tuple_straight_line_edge]
QED

(* MLOAD, ADD, then an aborting REVERT: no GAS read on the way. *)
Theorem tail3_path[local]:
  !ctx func t bb i1 i2 i3 t1 t2 a w.
    ~t.vs_halted /\ lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME i1 /\
    get_instruction bb (SUC t.vs_inst_idx) = SOME i2 /\
    get_instruction bb (SUC (SUC t.vs_inst_idx)) = SOME i3 /\
    i1.inst_opcode = MLOAD /\ i2.inst_opcode = ADD /\
    i3.inst_opcode = REVERT /\
    step_inst_base i1 t = OK t1 /\
    step_inst_base i2 (t1 with vs_inst_idx := SUC t.vs_inst_idx) = OK t2 /\
    step_inst_base i3 (t2 with vs_inst_idx := SUC (SUC t.vs_inst_idx)) =
      Abort a w ==>
    gas_path ctx func t 0 (Abort a w)
Proof
  rpt strip_tac >>
  `step_inst 0 ctx i1 t = OK t1` by simp[step_inst_non_invoke] >>
  `step_inst 0 ctx i2 (t1 with vs_inst_idx := SUC t.vs_inst_idx) = OK t2` by
    simp[step_inst_non_invoke] >>
  `~t1.vs_halted /\ t1.vs_current_bb = t.vs_current_bb` by
    (qspecl_then [`0`, `ctx`, `i1`, `t`, `t1`] mp_tac
       venomInstProofsTheory.step_preserves_halted >>
     qspecl_then [`0`, `ctx`, `i1`, `t`, `t1`] mp_tac
       venomInstProofsTheory.step_preserves_control_flow >>
     fs[is_terminator_def]) >>
  `~t2.vs_halted /\ t2.vs_current_bb = t.vs_current_bb` by
    (qspecl_then [`0`, `ctx`, `i2`, `t1 with vs_inst_idx := SUC t.vs_inst_idx`,
                  `t2`] mp_tac venomInstProofsTheory.step_preserves_halted >>
     qspecl_then [`0`, `ctx`, `i2`, `t1 with vs_inst_idx := SUC t.vs_inst_idx`,
                  `t2`] mp_tac
       venomInstProofsTheory.step_preserves_control_flow >>
     fs[is_terminator_def]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `t`, `bb`, `i1`, `t1`] straight_edge_zero) >>
  (impl_tac >- fs[is_terminator_def]) >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `t1 with vs_inst_idx := SUC t.vs_inst_idx`,
                   `bb`, `i2`, `t2`] straight_edge_zero) >>
  (impl_tac >- fs[is_terminator_def]) >> simp[] >> strip_tac >>
  `gas_count_step 0 ctx i3 (t2 with vs_inst_idx := SUC (SUC t.vs_inst_idx)) = 0`
    by simp[gas_count_step_def] >>
  `step_inst 0 ctx i3 (t2 with vs_inst_idx := SUC (SUC t.vs_inst_idx)) =
     Abort a w` by simp[step_inst_non_invoke] >>
  `gas_path_edge ctx func (t2 with vs_inst_idx := SUC (SUC t.vs_inst_idx)) 0
     (Abort a w)` by
    (rewrite_tac[gas_path_edge_def] >> simp[exit_result_def] >>
     qexists_tac `0` >> simp[exit_result_def]) >>
  `gas_path ctx func (t2 with vs_inst_idx := SUC (SUC t.vs_inst_idx)) 0
     (Abort a w)` by
    (irule (cj 3 gas_path_rules) >> simp[exit_result_def]) >>
  `gas_path ctx func (t1 with vs_inst_idx := SUC t.vs_inst_idx) (0 + 0)
     (Abort a w)` by
    (irule (cj 2 gas_path_rules) >> metis_tac[]) >>
  `gas_path ctx func t (0 + (0 + 0)) (Abort a w)` by
    (irule (cj 2 gas_path_rules) >> fs[] >> metis_tac[]) >>
  fs[]
QED

Theorem raw_revert_tail_path:
  !ctx func data sm u sb t p.
    compile_raw_revert data sm = (u,sb) /\ fn_has_code sm sb func /\
    (!v. data = Var v ==> not_fresh_at sm v) /\
    eval_operand data t = SOME p /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?w. gas_path ctx func t 0 (Abort Revert_abort w)
Proof
  rpt strip_tac >> drule raw_revert_tail_layout >> strip_tac >>
  qmatch_asmsub_abbrev_tac `sb.cs_current_insts = sm.cs_current_insts ++ new` >>
  `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
        !i. i < LENGTH new ==>
            get_instruction bb (LENGTH sm.cs_current_insts + i) =
            SOME (EL i new)` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >>
     gvs[same_blocks_def]) >>
  qabbrev_tac `x = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `y = STRING #"%" (toString (sm.cs_next_var + 1))` >>
  `data <> Var x` by
    (strip_tac >> `not_fresh_at sm x` by metis_tac[] >>
     fs[not_fresh_at_def, Abbr `x`] >> metis_tac[LESS_EQ_REFL]) >>
  `x <> y` by simp[Abbr `x`, Abbr `y`, ASCIInumbersTheory.toString_11] >>
  `get_instruction bb (LENGTH sm.cs_current_insts) =
     SOME (mk_inst sm.cs_next_id MLOAD [data] [x]) /\
   get_instruction bb (SUC (LENGTH sm.cs_current_insts)) =
     SOME (mk_inst (sm.cs_next_id + 1) ADD [data; Lit 32w] [y]) /\
   get_instruction bb (SUC (SUC (LENGTH sm.cs_current_insts))) =
     SOME (mk_inst (sm.cs_next_id + 2) REVERT [Var y; Var x] [])` by
    (rpt conj_tac >| [
       first_x_assum (qspec_then `0` mp_tac),
       first_x_assum (qspec_then `1` mp_tac),
       first_x_assum (qspec_then `2` mp_tac)] >>
     simp[Abbr `new`, ADD1]) >>
  `step_inst_base (mk_inst sm.cs_next_id MLOAD [data] [x]) t =
     OK (update_var x (mload (w2n p) t) t)` by
    (irule step_MLOAD >> simp[]) >>
  `eval_operand data
     (update_var x (mload (w2n p) t) t with vs_inst_idx := SUC t.vs_inst_idx) =
   SOME p` by
    (Cases_on `data` >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst (sm.cs_next_id + 1) ADD [data; Lit 32w] [y])
     (update_var x (mload (w2n p) t) t with vs_inst_idx := SUC t.vs_inst_idx) =
   OK (update_var y (p + 32w)
     (update_var x (mload (w2n p) t) t with vs_inst_idx := SUC t.vs_inst_idx))` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  `?w. step_inst_base (mk_inst (sm.cs_next_id + 2) REVERT [Var y; Var x] [])
         (update_var y (p + 32w)
           (update_var x (mload (w2n p) t) t with
              vs_inst_idx := SUC t.vs_inst_idx) with
            vs_inst_idx := SUC (SUC t.vs_inst_idx)) = Abort Revert_abort w` by
    (simp[mk_inst_def] >> irule_at Any step_revert_behavior >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  qexists_tac `w` >>
  qspecl_then [`ctx`, `func`, `t`, `bb`,
    `mk_inst sm.cs_next_id MLOAD [data] [x]`,
    `mk_inst (sm.cs_next_id + 1) ADD [data; Lit 32w] [y]`,
    `mk_inst (sm.cs_next_id + 2) REVERT [Var y; Var x] []`,
    `update_var x (mload (w2n p) t) t`,
    `update_var y (p + 32w)
       (update_var x (mload (w2n p) t) t with vs_inst_idx := SUC t.vs_inst_idx)`,
    `Revert_abort`, `w`] mp_tac tail3_path >>
  impl_tac >- gvs[mk_inst_def] >>
  simp[]
QED

(* ===== Composition ===== *)

Theorem ignore_bind_bind_unit[local]:
  ignore_bind (bind a k) (return ()) =
  bind a (\v. ignore_bind (k v) (return ()))
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
  Cases_on `a x` >> Cases_on `q` >> simp[]
QED

Theorem raw_revert_vv_sim:
  !ctx func cenv cx ty ann e dflt es.
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    expr_vv_sim ctx func cenv cx ty (Call ann RawRevert [e] dflt) es
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  drule raw_revert_compile >> strip_tac >>
  `cs_extends sa sm` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sb` by metis_tac[raw_revert_extends] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `!v. data = Var v ==> not_fresh_at sm v` by
    metis_tac[compile_lower_value_var] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (rw[gas_admissible_def] >> Cases_on `res` >- simp[expr_res_ok_def] >>
     qpat_x_assum `gas_admissible _ _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspecl_then [`gs`, `INR y`, `ee`] mp_tac) >>
     simp[eval_raw_revert_action] >>
     qpat_x_assum `bind _ _ _ = _` (fn th => simp[Once bind_def, th]) >>
     simp[expr_vv_res_ok_def, expr_res_ok_def]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `data`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[eval_raw_revert_action] >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      gvs[]
      >- (`?w. eval_operand data t = SOME w` by
            gvs[expr_post_def, expr_val_rel_def] >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec,
                      gas_path_normal] >>
          drule_all raw_revert_tail_path >>
          disch_then (qspec_then `ctx` strip_assume_tac) >>
          simp[gas_summary_at_def] >>
          qexistsl_tac [`INR (Error (RuntimeError "raw_revert"))`, `es_end`,
                        `Abort Revert_abort w'`] >>
          simp[exit_result_def, expr_exit_def] >>
          irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                 |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl_tac [`es_end`, `t`, `v`] >> simp[] >>
          simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def,
               raise_def]) >>
      Cases_on `res` >> gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      Cases_on `r` >> Cases_on `y` >> simp[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_raw_revert_action, ignore_bind_bind_unit] >>
  irule gas_exempt_cert_error_value >> simp[]
QED
