(*
 * A first body slice of the lowering simulation (#625)
 *
 * Three lemmas on top of state_rel (compileEnv), local_ptrs_rel
 * (localPtrsProps) and the fragment judgment frag_exec_in (fragExec), each
 * stated in the form the statement and expression induction will use: the
 * sub-fragments (a right-hand side, a condition, branch bodies) enter as
 * hypotheses of the same shape as the conclusion.
 *
 * TOP-LEVEL:
 *   frag_rel                — state_rel at a compile point, with the
 *                             fresh-variable invariant, no halt and
 *                             alloca_inv
 *   word_value              — a value held in one word as val_to_w256
 *   compile_if_frag         — slice 2: an if/else whose branches join again
 *   compile_safe_add_runtime_error — slice 3: a checked uint256 addition
 *                             whose source result is a RuntimeError aborts
 *   compile_safe_add_overflow_frag — the Venom side of slice 3
 *   compile_annassign_word_frag — slice 1: declaring a word local
 *   compile_name_word_frag  — slice 1: reading it back
 *
 * Helpers:
 *   frag_rel_next_var, frag_rel_next_var_le, frag_rel_jump_to,
 *   state_rel_jump_to, state_rel_push_scope, state_rel_pop_scope,
 *   state_rel_frame, local_ptrs_rel_inst_idx, alloca_inv_fields,
 *   eval_stmt_if_success, eval_stmt_annassign_value, fn_has_code_start,
 *   fn_has_code_mid, fn_has_code_new_block, run_from_jump_last,
 *   run_from_step, lookup_block_fn_insts, fresh_label_state,
 *   emit_inst_state, new_block_state, step_jnz, step_jmp,
 *   w2n_add_overflow, bounded_int_op_add_overflow, word_value_in_memory,
 *   word_value_wf
 *)

Theory loweringSlice
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps venomMemDefs
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperValueOperation
  vyperEvalExprPreservesScopesDom
  vyperEvalPreservesScopes arithmeticProps
  venomExecSemantics venomExecProofs venomInst venomInstProofs venomState
Libs
  monadsyntax

(* ===== The relation at a compile point ===== *)

(* What holds at the point where compile state st leaves off: the states
   are related (state_rel in func, the function running), no compiler
   variable at or above st's counter is bound yet, execution has not
   halted, and the frame's allocations are disjoint and below the frontier
   (alloca_inv, which tells a new local's region from the live ones). *)
Definition frag_rel_def:
  frag_rel func cenv cx (st:compile_state) es (s:venom_state) <=>
    state_rel func cenv cx es s /\ fresh_vars_wrt st s /\ ~s.vs_halted /\
    alloca_inv s
End

Theorem frag_rel_next_var:
  !func cenv cx st st' es s.
    st'.cs_next_var = st.cs_next_var ==>
    (frag_rel func cenv cx st' es s <=> frag_rel func cenv cx st es s)
Proof
  rw[frag_rel_def, fresh_vars_wrt_def]
QED

(* The fresh-variable invariant holds for any later counter. *)
Theorem frag_rel_next_var_le:
  !func cenv cx st st' es s.
    st.cs_next_var <= st'.cs_next_var /\ frag_rel func cenv cx st es s ==>
    frag_rel func cenv cx st' es s
Proof
  rw[frag_rel_def, fresh_vars_wrt_def] >> first_x_assum irule >> fs[]
QED

(* ===== state_rel does not read control state or the scope order ===== *)

Theorem state_rel_jump_to:
  !func cenv cx es s lbl.
    state_rel func cenv cx es (jump_to lbl s) <=> state_rel func cenv cx es s
Proof
  simp[state_rel_def, local_ptrs_rel_def, local_region_def, local_backed_def,
       lookup_var_def, storage_rel_def, transient_rel_def, immutables_rel_def,
       logs_rel_def, call_ctx_rel_def, contract_storage_def,
       contract_transient_def, jump_to_def]
QED

Theorem frag_rel_jump_to:
  !func cenv cx st es s lbl.
    frag_rel func cenv cx st es (jump_to lbl s) <=>
    frag_rel func cenv cx st es s
Proof
  simp[frag_rel_def, state_rel_jump_to, fresh_vars_wrt_def, jump_to_def,
       alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem state_rel_push_scope:
  !func cenv cx es s.
    state_rel func cenv cx (es with scopes := FEMPTY :: es.scopes) s <=>
    state_rel func cenv cx es s
Proof
  simp[state_rel_def, storage_rel_def, transient_rel_def, immutables_rel_def,
       logs_rel_def, local_ptrs_rel_push_scope]
QED

Theorem state_rel_pop_scope:
  !func cenv cx es s sc rest.
    state_rel func cenv cx es s /\ es.scopes = sc :: rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
    state_rel func cenv cx (es with scopes := rest) s
Proof
  rpt strip_tac >>
  fs[state_rel_def, storage_rel_def, transient_rel_def, immutables_rel_def,
     logs_rel_def] >>
  irule local_ptrs_rel_pop_scope >> qexists_tac `sc` >> gvs[]
QED

(* ===== Source side of if/else ===== *)

Theorem eval_stmt_if_success:
  !cx c ss1 ss2 es es'.
    eval_stmt cx (If c ss1 ss2) es = (INL (), es') ==>
    ?b es1 es2 sc rest.
      eval_expr cx c es = (INL (Value (BoolV b)), es1) /\
      eval_stmts cx (if b then ss1 else ss2)
        (es1 with scopes := FEMPTY :: es1.scopes) = (INL (), es2) /\
      es2.scopes = sc :: rest /\ es' = es2 with scopes := rest /\
      !n. n IN FDOM sc ==> lookup_scopes n rest = NONE
Proof
  rpt gen_tac >>
  `!x. x with scopes updated_by CONS FEMPTY =
       x with scopes := FEMPTY :: x.scopes` by
    simp[evaluation_state_component_equality] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, push_scope_def,
       finally_def, return_def] >>
  Cases_on `eval_expr cx c es` >> rename1 `eval_expr cx c es = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  rename1 `switch_BoolV tv` >>
  Cases_on `switch_BoolV tv (eval_stmts cx ss1) (eval_stmts cx ss2)
              (es1 with scopes := FEMPTY :: es1.scopes)` >>
  rename1 `_ = (r2, es2)` >> Cases_on `r2` >>
  simp[pop_scope_def] >> Cases_on `es2.scopes` >>
  simp[raise_def, return_def] >> strip_tac >> gvs[] >>
  `!id. id IN FDOM h ==> lookup_scopes id t = NONE` by
    (rpt strip_tac >>
     qpat_x_assum `switch_BoolV _ _ _ _ = _` mp_tac >>
     rw[switch_BoolV_def, raise_def] >>
     drule eval_stmts_new_in_head_not_in_tail >> simp[]) >>
  qpat_x_assum `switch_BoolV _ _ _ _ = _` mp_tac >>
  rw[switch_BoolV_def, raise_def]
QED

(* ===== Code containment for the parts of a fragment ===== *)

(* The start of a fragment is in fn too. *)
Theorem fn_has_code_start:
  !st st' fn.
    cs_extends st st' /\ fn_has_code st st' fn ==>
    ?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX st.cs_current_insts bb.bb_instructions
Proof
  rw[cs_extends_def] >> Cases_on `new = []` >> gvs[]
  >- (fs[fn_has_code_def] >> metis_tac[isPREFIX_TRANS]) >>
  `emitted_blocks st st' = new` by (irule emitted_blocks_append >> simp[]) >>
  fs[fn_has_code_def] >>
  qexists_tac `LAST new` >>
  metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]
QED

(* fn contains the code of any part of a fragment it contains. *)
Theorem fn_has_code_mid:
  !st0 sa sb st' fn.
    cs_extends st0 sa /\ cs_extends sa sb /\ cs_extends sb st' /\
    fn_has_code st0 st' fn ==>
    fn_has_code sa sb fn
Proof
  rpt strip_tac >>
  `cs_extends st0 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code st0 sb fn` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

(* A block finished by new_block is in fn as it was finished. *)
Theorem fn_has_code_new_block:
  !sa lbl x sb fn.
    new_block lbl sa = (x, sb) /\ fn_has_code sa sb fn ==>
    lookup_block sa.cs_current_bb fn.fn_blocks =
      SOME <| bb_label := sa.cs_current_bb;
              bb_instructions := sa.cs_current_insts |>
Proof
  rw[new_block_def] >>
  `emitted_blocks sa (sa with <| cs_blocks :=
       <| bb_label := sa.cs_current_bb;
          bb_instructions := sa.cs_current_insts |> :: sa.cs_blocks;
       cs_current_bb := lbl; cs_current_insts := [] |>) =
   [<| bb_label := sa.cs_current_bb;
       bb_instructions := sa.cs_current_insts |>]` by
    (irule emitted_blocks_append >> simp[]) >>
  fs[fn_has_code_def] >>
  first_x_assum (qspec_then `<| bb_label := sa.cs_current_bb;
                               bb_instructions := sa.cs_current_insts |>`
                   mp_tac) >> simp[]
QED

(* Jumping out of the last instruction of a block fn holds. *)
Theorem run_from_jump_last:
  !fuel ctx fn s lbl insts j tgt bb'.
    lookup_block s.vs_current_bb fn.fn_blocks =
      SOME <| bb_label := lbl; bb_instructions := insts ++ [j] |> /\
    s.vs_inst_idx = LENGTH insts /\
    is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
    step_inst_base j s = OK (jump_to tgt s) /\ ~s.vs_halted /\
    lookup_block tgt fn.fn_blocks = SOME bb' /\
    phi_prefix_length bb'.bb_instructions = 0 ==>
    run_from (SUC fuel) ctx fn s = run_from fuel ctx fn (jump_to tgt s)
Proof
  rpt strip_tac >> match_mp_tac run_from_jump >>
  qexistsl_tac [`<| bb_label := lbl; bb_instructions := insts ++ [j] |>`,
                `j`, `bb'`] >>
  simp[get_instruction_def, EL_LENGTH_APPEND]
QED

(* ===== Compile-state effects of the primitives ===== *)

Theorem fresh_label_state:
  !sfx s l s'.
    fresh_label sfx s = (l, s') ==>
    s'.cs_current_bb = s.cs_current_bb /\
    s'.cs_current_insts = s.cs_current_insts /\
    s'.cs_next_var = s.cs_next_var /\ cs_extends s s'
Proof
  rpt gen_tac >> strip_tac >> imp_res_tac cs_extends_fresh_label >>
  gvs[fresh_label_def]
QED

Theorem emit_inst_state:
  !opc ops outs s x s'.
    emit_inst opc ops outs s = (x, s') ==>
    s'.cs_current_bb = s.cs_current_bb /\
    s'.cs_current_insts =
      s.cs_current_insts ++ [mk_inst s.cs_next_id opc ops outs] /\
    s'.cs_next_var = s.cs_next_var /\ cs_extends s s'
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends s s'` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def]
QED

Theorem new_block_state:
  !l s x s'.
    new_block l s = (x, s') ==>
    s'.cs_current_bb = l /\ s'.cs_current_insts = [] /\
    s'.cs_next_var = s.cs_next_var /\ cs_extends s s'
Proof
  rpt gen_tac >> strip_tac >> imp_res_tac cs_extends_new_block >>
  gvs[new_block_def]
QED

Theorem step_jnz:
  !id op t e s w.
    eval_operand op s = SOME w ==>
    step_inst_base (mk_inst id JNZ [op; Label t; Label e] []) s =
      OK (jump_to (if w <> 0w then t else e) s)
Proof
  rw[step_inst_base_def, venomInstTheory.mk_inst_def]
QED

Theorem step_jmp:
  !id l s.
    step_inst_base (mk_inst id JMP [Label l] []) s = OK (jump_to l s)
Proof
  rw[step_inst_base_def, venomInstTheory.mk_inst_def]
QED

Theorem compile_if_frag:
  !ctx func cenv cx lctx ty c ss1 ss2 st st' es es' R.
    compile_stmt cenv lctx ty (If c ss1 ss2) st = ((), st') /\
    eval_stmt cx (If c ss1 ss2) es = (INL (), es') /\
    (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    (!sa sb op esa esb v.
       lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) /\
       eval_expr cx c esa = (INL (Value v), esb) ==>
       cs_extends sa sb /\
       frag_exec_in ctx func sa sb (frag_rel func cenv cx sa esa)
         (\s. frag_rel func cenv cx sb esb s /\
              eval_operand op s = SOME (val_to_w256 v)) R) /\
    (!sa sb u. compile_stmts cenv lctx ty ss1 sa = (u, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       ~block_is_terminated sb) /\
    (!sa sb u. compile_stmts cenv lctx ty ss2 sa = (u, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       ~block_is_terminated sb) /\
    (!sa sb u esa esb.
       compile_stmts cenv lctx ty ss1 sa = (u, sb) /\
       eval_stmts cx ss1 esa = (INL (), esb) ==>
       frag_exec_in ctx func sa sb (frag_rel func cenv cx sa esa)
         (frag_rel func cenv cx sb esb) R) /\
    (!sa sb u esa esb.
       compile_stmts cenv lctx ty ss2 sa = (u, sb) /\
       eval_stmts cx ss2 esa = (INL (), esb) ==>
       frag_exec_in ctx func sa sb (frag_rel func cenv cx sa esa)
         (frag_rel func cenv cx sb esb) R) ==>
    frag_exec_in ctx func st st' (frag_rel func cenv cx st es)
      (frag_rel func cenv cx st' es') R
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_stmt_if_success >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_get_def,
       emit_jmp_if_not_terminated_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  rename1 `lower_value _ _ _ c st = (cond_op, s1)` >>
  rename1 `fresh_label "then" s1 = (then_lbl, s2)` >>
  rename1 `fresh_label "else" s2 = (else_lbl, s3)` >>
  rename1 `fresh_label "if_exit" s3 = (exit_lbl, s4)` >>
  rename1 `emit_inst JNZ _ _ s4 = (_, s5)` >>
  rename1 `new_block then_lbl s5 = (_, s6)` >>
  rename1 `compile_stmts _ _ _ ss1 s6 = (_, s7)` >>
  rename1 `new_block else_lbl s8 = (_, s9)` >>
  rename1 `compile_stmts _ _ _ ss2 s9 = (_, s10)` >>
  `cs_extends s6 s7 /\ s6.cs_next_var <= s7.cs_next_var /\
   ~block_is_terminated s7` by metis_tac[] >>
  `cs_extends s9 s10 /\ s9.cs_next_var <= s10.cs_next_var /\
   ~block_is_terminated s10` by metis_tac[] >>
  qpat_x_assum `(if block_is_terminated s7 then _ else _) _ = _` mp_tac >>
  qpat_x_assum `(if block_is_terminated s10 then _ else _) _ = _` mp_tac >>
  asm_simp_tac std_ss [] >> ntac 2 strip_tac >>
  rename1 `emit_inst JMP _ _ s7 = (_, s8)` >>
  rename1 `emit_inst JMP _ _ s10 = (_, s11)` >>
  simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `new_block exit_lbl s11 = (_, s12)` >>
  qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >>
  imp_res_tac fresh_label_state >> imp_res_tac new_block_state >>
  imp_res_tac emit_inst_state >>
  (* the fragment parts only append *)
  qpat_x_assum `!sa sb op esa esb v. P sa sb op esa esb v ==>
                                     Q sa sb op esa esb v`
    (qspecl_then [`st`, `s1`, `cond_op`, `es`, `es1`, `BoolV b`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  `cs_extends s4 s5 /\ cs_extends s7 s8 /\ cs_extends s10 s11` by simp[] >>
  `cs_extends st s2` by (irule cs_extends_trans >> qexists_tac `s1` >> simp[]) >>
  `cs_extends st s3` by (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  `cs_extends st s4` by (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends st s5` by (irule cs_extends_trans >> qexists_tac `s4` >> simp[]) >>
  `cs_extends st s6` by (irule cs_extends_trans >> qexists_tac `s5` >> simp[]) >>
  `cs_extends st s7` by (irule cs_extends_trans >> qexists_tac `s6` >> simp[]) >>
  `cs_extends st s8` by (irule cs_extends_trans >> qexists_tac `s7` >> simp[]) >>
  `cs_extends st s9` by (irule cs_extends_trans >> qexists_tac `s8` >> simp[]) >>
  `cs_extends st s10` by (irule cs_extends_trans >> qexists_tac `s9` >> simp[]) >>
  `cs_extends st s11` by (irule cs_extends_trans >> qexists_tac `s10` >> simp[]) >>
  `cs_extends st s12` by (irule cs_extends_trans >> qexists_tac `s11` >> simp[]) >>
  `cs_extends s10 s12` by (irule cs_extends_trans >> qexists_tac `s11` >> simp[]) >>
  `cs_extends s9 s12` by (irule cs_extends_trans >> qexists_tac `s10` >> simp[]) >>
  `cs_extends s8 s12` by (irule cs_extends_trans >> qexists_tac `s9` >> simp[]) >>
  `cs_extends s7 s12` by (irule cs_extends_trans >> qexists_tac `s8` >> simp[]) >>
  `cs_extends s6 s12` by (irule cs_extends_trans >> qexists_tac `s7` >> simp[]) >>
  `cs_extends s5 s12` by (irule cs_extends_trans >> qexists_tac `s6` >> simp[]) >>
  `cs_extends s4 s12` by (irule cs_extends_trans >> qexists_tac `s5` >> simp[]) >>
  `cs_extends s3 s12` by (irule cs_extends_trans >> qexists_tac `s4` >> simp[]) >>
  `cs_extends s2 s12` by (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends s1 s12` by (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  simp[frag_exec_in_def] >> rpt strip_tac >>
  (* the condition *)
  `fn_has_code st s1 func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  qpat_x_assum `frag_exec_in ctx func st s1 _ _ _`
    (mp_tac o SIMP_RULE std_ss [frag_exec_in_def]) >>
  asm_rewrite_tac[] >> disch_then (qspec_then `s` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac
  >- (rename1 `frag_rel func cenv cx s1 es1 t1` >>
      (* the JNZ ending the condition's block *)
      `fn_has_code s5 s6 func` by
        metis_tac[fn_has_code_mid, cs_extends_refl] >>
      `lookup_block s5.cs_current_bb func.fn_blocks =
         SOME <| bb_label := s5.cs_current_bb;
                 bb_instructions := s5.cs_current_insts |>` by
        metis_tac[fn_has_code_new_block] >>
      qpat_x_assum `lookup_block s5.cs_current_bb _ = _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      Cases_on `b` >> fs[]
      >- (
  (* enter the then_lbl branch *)
  `?bt. lookup_block then_lbl func.fn_blocks = SOME bt /\
        phi_prefix_length bt.bb_instructions = 0` by
    (`fn_has_code s6 s7 func` by
       metis_tac[fn_has_code_mid, cs_extends_refl] >>
     qspecl_then [`s6`, `s7`, `func`] mp_tac fn_has_code_start >>
     asm_rewrite_tac[] >> strip_tac >> qexists_tac `bb` >> simp[] >>
     metis_tac[lookup_block_MEM]) >>
  `!f. run_from (SUC f) ctx func t1 = run_from f ctx func (jump_to then_lbl t1)` by
    (gen_tac >>
     qspecl_then [`f`, `ctx`, `func`, `t1`, `s1.cs_current_bb`,
       `s1.cs_current_insts`,
       `mk_inst s4.cs_next_id JNZ [cond_op; Label then_lbl; Label else_lbl] []`,
       `then_lbl`, `bt`] mp_tac run_from_jump_last >>
     impl_tac >- (
       `eval_operand cond_op t1 = SOME (val_to_w256 (BoolV T))` by simp[] >>
       drule step_jnz >>
       disch_then (qspecl_then [`s4.cs_next_id`, `then_lbl`, `else_lbl`]
                     assume_tac) >>
       fs[frag_rel_def, val_to_w256_def, venomInstTheory.mk_inst_def,
          is_terminator_def]) >>
     simp[]) >>
  (* the branch body *)
  `fn_has_code s6 s7 func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `frag_exec_in ctx func s6 s7
     (frag_rel func cenv cx s6 (es1 with scopes := FEMPTY :: es1.scopes))
     (frag_rel func cenv cx s7 es2) R` by
    (qpat_x_assum `!sa sb esa esb.
        compile_stmts cenv lctx ty ss1 sa = ((), sb) /\ P sa sb esa esb ==>
        Q sa sb esa esb` irule >> metis_tac[oneTheory.one]) >>
  qpat_x_assum `frag_exec_in ctx func s6 s7 _ _ _`
    (mp_tac o SIMP_RULE std_ss [frag_exec_in_def]) >>
  asm_rewrite_tac[] >>
  disch_then (qspec_then `jump_to then_lbl t1` mp_tac) >>
  `frag_rel func cenv cx s6 (es1 with scopes := FEMPTY :: es1.scopes)
     (jump_to then_lbl t1)` by
    (simp[frag_rel_jump_to] >>
     `s1.cs_next_var <= s6.cs_next_var` by fs[] >>
     irule frag_rel_next_var_le >> qexists_tac `s1` >>
     fs[frag_rel_def, state_rel_push_scope]) >>
  simp[jump_to_def] >> strip_tac
  >- (rename1 `frag_rel func cenv cx s7 es2 t2` >>
      (* jump to the exit *)
      `fn_has_code s8 s9 func` by
        metis_tac[fn_has_code_mid, cs_extends_refl] >>
      `lookup_block s8.cs_current_bb func.fn_blocks =
         SOME <| bb_label := s8.cs_current_bb;
                 bb_instructions := s8.cs_current_insts |>` by
        metis_tac[fn_has_code_new_block] >>
      qpat_x_assum `lookup_block s8.cs_current_bb _ = _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      `?be. lookup_block exit_lbl func.fn_blocks = SOME be /\
            phi_prefix_length be.bb_instructions = 0` by
        (qpat_x_assum `fn_has_code st s12 func` mp_tac >>
         simp[fn_has_code_def] >> strip_tac >> gvs[] >>
         metis_tac[lookup_block_MEM]) >>
      `!f. run_from (SUC f) ctx func t2 =
           run_from f ctx func (jump_to exit_lbl t2)` by
        (gen_tac >>
         qspecl_then [`f`, `ctx`, `func`, `t2`, `s7.cs_current_bb`,
           `s7.cs_current_insts`,
           `mk_inst s7.cs_next_id JMP [Label exit_lbl] []`, `exit_lbl`, `be`]
           mp_tac run_from_jump_last >>
         impl_tac >- fs[frag_rel_def, step_jmp, venomInstTheory.mk_inst_def,
                        is_terminator_def] >>
         simp[]) >>
      disj1_tac >> qexists_tac `jump_to exit_lbl t2` >>
      `s7.cs_next_var <= s12.cs_next_var` by fs[] >>
      `frag_rel func cenv cx s7 (es2 with scopes := rest)
         (jump_to exit_lbl t2)` by
        (fs[frag_rel_jump_to, frag_rel_def] >>
         irule state_rel_pop_scope >> metis_tac[]) >>
      `frag_rel func cenv cx s12 (es2 with scopes := rest)
         (jump_to exit_lbl t2)` by metis_tac[frag_rel_next_var_le] >>
      `(jump_to exit_lbl t2).vs_current_bb = s12.cs_current_bb /\
       (jump_to exit_lbl t2).vs_inst_idx = LENGTH s12.cs_current_insts` by
        simp[jump_to_def] >>
      asm_rewrite_tac[LENGTH] >> gen_tac >> strip_tac >>
      `jump_to then_lbl t1 =
       t1 with <| vs_prev_bb := SOME s1.cs_current_bb;
                  vs_current_bb := then_lbl; vs_inst_idx := 0 |>` by
        simp[jump_to_def] >>
      `run_from (SUC fuel) ctx func t2 =
       run_from fuel ctx func (jump_to exit_lbl t2)` by simp[] >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func t2 <> Error e) ==>
                           Q fuel` (qspec_then `SUC fuel` mp_tac) >>
      asm_rewrite_tac[] >> strip_tac >>
      `run_from (SUC fuel') ctx func t1 =
       run_from fuel ctx func (jump_to exit_lbl t2)` by asm_rewrite_tac[] >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func t1 <> Error e) ==>
                           Q fuel` (qspec_then `SUC fuel'` mp_tac) >>
      asm_rewrite_tac[] >> strip_tac >> metis_tac[]) >>
  (* the branch exits *)
  disj2_tac >>
  `jump_to then_lbl t1 =
   t1 with <| vs_prev_bb := SOME s1.cs_current_bb;
              vs_current_bb := then_lbl; vs_inst_idx := 0 |>` by
    simp[jump_to_def] >>
  `run_from (SUC fuel) ctx func t1 =
   run_from fuel ctx func
     (t1 with <| vs_prev_bb := SOME s1.cs_current_bb;
                 vs_current_bb := then_lbl; vs_inst_idx := 0 |>)` by
    asm_rewrite_tac[] >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx func t1 <> Error e) ==>
                       Q fuel` (qspec_then `SUC fuel` mp_tac) >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[exit_result_not_error]) >>
  strip_tac >> qexists_tac `fuel'` >> asm_rewrite_tac[]
)
      >> 
  (* enter the else_lbl branch *)
  `?bt. lookup_block else_lbl func.fn_blocks = SOME bt /\
        phi_prefix_length bt.bb_instructions = 0` by
    (`fn_has_code s9 s10 func` by
       metis_tac[fn_has_code_mid, cs_extends_refl] >>
     qspecl_then [`s9`, `s10`, `func`] mp_tac fn_has_code_start >>
     asm_rewrite_tac[] >> strip_tac >> qexists_tac `bb` >> simp[] >>
     metis_tac[lookup_block_MEM]) >>
  `!f. run_from (SUC f) ctx func t1 = run_from f ctx func (jump_to else_lbl t1)` by
    (gen_tac >>
     qspecl_then [`f`, `ctx`, `func`, `t1`, `s1.cs_current_bb`,
       `s1.cs_current_insts`,
       `mk_inst s4.cs_next_id JNZ [cond_op; Label then_lbl; Label else_lbl] []`,
       `else_lbl`, `bt`] mp_tac run_from_jump_last >>
     impl_tac >- (
       `eval_operand cond_op t1 = SOME (val_to_w256 (BoolV F))` by simp[] >>
       drule step_jnz >>
       disch_then (qspecl_then [`s4.cs_next_id`, `then_lbl`, `else_lbl`]
                     assume_tac) >>
       fs[frag_rel_def, val_to_w256_def, venomInstTheory.mk_inst_def,
          is_terminator_def]) >>
     simp[]) >>
  (* the branch body *)
  `fn_has_code s9 s10 func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `frag_exec_in ctx func s9 s10
     (frag_rel func cenv cx s9 (es1 with scopes := FEMPTY :: es1.scopes))
     (frag_rel func cenv cx s10 es2) R` by
    (qpat_x_assum `!sa sb esa esb.
        compile_stmts cenv lctx ty ss2 sa = ((), sb) /\ P sa sb esa esb ==>
        Q sa sb esa esb` irule >> metis_tac[oneTheory.one]) >>
  qpat_x_assum `frag_exec_in ctx func s9 s10 _ _ _`
    (mp_tac o SIMP_RULE std_ss [frag_exec_in_def]) >>
  asm_rewrite_tac[] >>
  disch_then (qspec_then `jump_to else_lbl t1` mp_tac) >>
  `frag_rel func cenv cx s9 (es1 with scopes := FEMPTY :: es1.scopes)
     (jump_to else_lbl t1)` by
    (simp[frag_rel_jump_to] >>
     `s1.cs_next_var <= s9.cs_next_var` by fs[] >>
     irule frag_rel_next_var_le >> qexists_tac `s1` >>
     fs[frag_rel_def, state_rel_push_scope]) >>
  simp[jump_to_def] >> strip_tac
  >- (rename1 `frag_rel func cenv cx s10 es2 t2` >>
      (* jump to the exit *)
      `fn_has_code s11 s12 func` by
        metis_tac[fn_has_code_mid, cs_extends_refl] >>
      `lookup_block s11.cs_current_bb func.fn_blocks =
         SOME <| bb_label := s11.cs_current_bb;
                 bb_instructions := s11.cs_current_insts |>` by
        metis_tac[fn_has_code_new_block] >>
      qpat_x_assum `lookup_block s11.cs_current_bb _ = _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      `?be. lookup_block exit_lbl func.fn_blocks = SOME be /\
            phi_prefix_length be.bb_instructions = 0` by
        (qpat_x_assum `fn_has_code st s12 func` mp_tac >>
         simp[fn_has_code_def] >> strip_tac >> gvs[] >>
         metis_tac[lookup_block_MEM]) >>
      `!f. run_from (SUC f) ctx func t2 =
           run_from f ctx func (jump_to exit_lbl t2)` by
        (gen_tac >>
         qspecl_then [`f`, `ctx`, `func`, `t2`, `s10.cs_current_bb`,
           `s10.cs_current_insts`,
           `mk_inst s10.cs_next_id JMP [Label exit_lbl] []`, `exit_lbl`, `be`]
           mp_tac run_from_jump_last >>
         impl_tac >- fs[frag_rel_def, step_jmp, venomInstTheory.mk_inst_def,
                        is_terminator_def] >>
         simp[]) >>
      disj1_tac >> qexists_tac `jump_to exit_lbl t2` >>
      `s10.cs_next_var <= s12.cs_next_var` by fs[] >>
      `frag_rel func cenv cx s10 (es2 with scopes := rest)
         (jump_to exit_lbl t2)` by
        (fs[frag_rel_jump_to, frag_rel_def] >>
         irule state_rel_pop_scope >> metis_tac[]) >>
      `frag_rel func cenv cx s12 (es2 with scopes := rest)
         (jump_to exit_lbl t2)` by metis_tac[frag_rel_next_var_le] >>
      `(jump_to exit_lbl t2).vs_current_bb = s12.cs_current_bb /\
       (jump_to exit_lbl t2).vs_inst_idx = LENGTH s12.cs_current_insts` by
        simp[jump_to_def] >>
      asm_rewrite_tac[LENGTH] >> gen_tac >> strip_tac >>
      `jump_to else_lbl t1 =
       t1 with <| vs_prev_bb := SOME s1.cs_current_bb;
                  vs_current_bb := else_lbl; vs_inst_idx := 0 |>` by
        simp[jump_to_def] >>
      `run_from (SUC fuel) ctx func t2 =
       run_from fuel ctx func (jump_to exit_lbl t2)` by simp[] >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func t2 <> Error e) ==>
                           Q fuel` (qspec_then `SUC fuel` mp_tac) >>
      asm_rewrite_tac[] >> strip_tac >>
      `run_from (SUC fuel') ctx func t1 =
       run_from fuel ctx func (jump_to exit_lbl t2)` by asm_rewrite_tac[] >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func t1 <> Error e) ==>
                           Q fuel` (qspec_then `SUC fuel'` mp_tac) >>
      asm_rewrite_tac[] >> strip_tac >> metis_tac[]) >>
  (* the branch exits *)
  disj2_tac >>
  `jump_to else_lbl t1 =
   t1 with <| vs_prev_bb := SOME s1.cs_current_bb;
              vs_current_bb := else_lbl; vs_inst_idx := 0 |>` by
    simp[jump_to_def] >>
  `run_from (SUC fuel) ctx func t1 =
   run_from fuel ctx func
     (t1 with <| vs_prev_bb := SOME s1.cs_current_bb;
                 vs_current_bb := else_lbl; vs_inst_idx := 0 |>)` by
    asm_rewrite_tac[] >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx func t1 <> Error e) ==>
                       Q fuel` (qspec_then `SUC fuel` mp_tac) >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[exit_result_not_error]) >>
  strip_tac >> qexists_tac `fuel'` >> asm_rewrite_tac[]
) >>
  disj2_tac >> metis_tac[]
QED

(* ===== Checked addition that overflows ===== *)

Theorem w2n_add_overflow:
  !a b : bytes32.
    dimword (:256) <= w2n a + w2n b ==> w2n (a + b) < w2n a
Proof
  rpt strip_tac >>
  `w2n a < dimword (:256) /\ w2n b < dimword (:256)` by simp[wordsTheory.w2n_lt] >>
  `w2n (a + b) = (w2n a + w2n b) MOD dimword (:256)` by
    simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >>
  `(w2n a + w2n b) MOD dimword (:256) =
   (w2n a + w2n b - dimword (:256)) MOD dimword (:256)` by
    (irule (GSYM arithmeticTheory.SUB_MOD) >> simp[]) >>
  `(w2n a + w2n b - dimword (:256)) MOD dimword (:256) =
   w2n a + w2n b - dimword (:256)` by
    (irule arithmeticTheory.LESS_MOD >> simp[]) >>
  simp[]
QED

(* The source's unsigned 256-bit addition fails exactly when the words
   overflow. *)
Theorem bounded_int_op_add_overflow:
  !i1 i2 err.
    within_int_bound (Unsigned 256) i1 /\ within_int_bound (Unsigned 256) i2 /\
    bounded_int_op (Unsigned 256) (i1 + i2) = INR err ==>
    dimword (:256) <=
      w2n (val_to_w256 (IntV i1)) + w2n (val_to_w256 (IntV i2))
Proof
  rw[bounded_int_op_def, within_int_bound_def] >>
  `?n1 n2. i1 = &n1 /\ i2 = &n2` by
    metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
  gvs[val_to_w256_def, integer_wordTheory.i2w_def, wordsTheory.w2n_n2w,
      wordsTheory.dimword_def, integerTheory.INT_ADD]
QED

(* compile_safe_add on unsigned 256-bit operands whose sum overflows: the
   ASSERT fails, so the fragment aborts with Revert_abort. *)
Theorem compile_safe_add_overflow_frag:
  !ctx fn x y ty st op st' P Q R.
    compile_safe_add x y ty st = (op, st') /\
    type_bits ty = 256 /\ ~is_signed_type ty /\
    (!s. P s ==> fresh_vars_wrt st s /\
         ?a b. eval_operand x s = SOME a /\ eval_operand y s = SOME b /\
               dimword (:256) <= w2n a + w2n b) /\
    (!s. R (Abort Revert_abort s)) ==>
    frag_exec_in ctx fn st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_safe_add_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op ADD [x; y] st = (op, st1)` >>
  rename1 `emit_op LT [op; x] st1 = (lt, st2)` >>
  rename1 `emit_op ISZERO [lt] st2 = (ok, st3)` >>
  rename1 `emit_void ASSERT [ok] st3 = ((), st4)` >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `emitted_insts st3 st4 = [mk_inst st3.cs_next_id ASSERT [ok] []]` by
    (qpat_x_assum `emit_void ASSERT _ _ = _` mp_tac >>
     simp[emit_void_assert_inst] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `emitted_insts st st4 =
   emitted_insts st st1 ++ emitted_insts st1 st2 ++ emitted_insts st2 st3 ++
   emitted_insts st3 st4 /\
   st4.cs_current_insts = st.cs_current_insts ++ emitted_insts st st4` by
    (`emitted_insts st2 st4 = emitted_insts st2 st3 ++ emitted_insts st3 st4`
       by (irule emitted_insts_append >> simp[]) >>
     `st4.cs_current_insts = st2.cs_current_insts ++ emitted_insts st2 st4`
       by simp[] >>
     `emitted_insts st1 st4 = emitted_insts st1 st2 ++ emitted_insts st2 st4`
       by (irule emitted_insts_append >> simp[]) >>
     `st4.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st4`
       by simp[] >>
     `emitted_insts st st4 = emitted_insts st st1 ++ emitted_insts st1 st4`
       by (irule emitted_insts_append >> simp[]) >>
     simp[]) >>
  `st4.cs_blocks = st.cs_blocks /\ st4.cs_current_bb = st.cs_current_bb` by
    fs[same_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st4)` by
    (imp_res_tac emitted_insts_emit_op >>
     asm_rewrite_tac[] >>
     simp[venomInstTheory.mk_inst_def, is_terminator_def]) >>
  irule frag_exec_in_run_inst_seq >>
  asm_rewrite_tac[IS_PREFIX_APPEND3] >>
  rpt strip_tac >> disj2_tac >>
  `fresh_vars_wrt st s /\
   ?a b. eval_operand x s = SOME a /\ eval_operand y s = SOME b /\
         dimword (:256) <= w2n a + w2n b` by metis_tac[] >>
  qspecl_then [`x`, `y`, `a`, `b`, `st`, `op`, `st1`, `s`] mp_tac
    emit_op_ADD_correct >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st1) s = OK ss1` >>
  qspecl_then [`op`, `x`, `a + b`, `a`, `st1`, `lt`, `st2`, `ss1`] mp_tac
    emit_op_LT_correct >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) ss1 = OK ss2` >>
  qspecl_then [`lt`, `bool_to_word (w2n (a + b) < w2n a)`, `st2`, `ok`,
               `st3`, `ss2`] mp_tac emit_op_ISZERO_correct >>
  simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st2 st3) ss2 = OK ss3` >>
  `w2n (a + b) < w2n a` by (irule w2n_add_overflow >> simp[]) >>
  `eval_operand ok ss3 = SOME 0w` by fs[bool_to_word_def] >>
  `run_inst_seq (emitted_insts st3 st4) ss3 =
   Abort Revert_abort (revert_state (set_returndata [] ss3))` by
    simp[run_inst_seq_def, assert_false_correct] >>
  qexistsl_tac [`Revert_abort`,
                `revert_state (set_returndata [] ss3)`] >>
  conj_tac >- (
    asm_rewrite_tac[GSYM APPEND_ASSOC] >>
    qpat_x_assum `run_inst_seq (emitted_insts st st1) s = OK ss1`
      (fn th => rewrite_tac [MATCH_MP run_inst_seq_append th]) >>
    qpat_x_assum `run_inst_seq (emitted_insts st1 st2) ss1 = OK ss2`
      (fn th => rewrite_tac [MATCH_MP run_inst_seq_append th]) >>
    qpat_x_assum `run_inst_seq (emitted_insts st2 st3) ss2 = OK ss3`
      (fn th => rewrite_tac [MATCH_MP run_inst_seq_append th]) >>
    simp[run_inst_seq_def, assert_false_correct]) >>
  simp[]
QED

(* Slice lemma 3: a checked unsigned 256-bit addition whose source result is
   a RuntimeError aborts in the lowered code, which result_rel relates to the
   source error. *)
Theorem compile_safe_add_runtime_error:
  !ctx fn func ret_tv cenv cx tv x y ty st op st' P Q es' i1 i2 err.
    compile_safe_add x y ty st = (op, st') /\
    type_bits ty = 256 /\ ~is_signed_type ty /\
    within_int_bound (Unsigned 256) i1 /\ within_int_bound (Unsigned 256) i2 /\
    evaluate_binop (Unsigned 256) tv Add (IntV i1) (IntV i2) = INR err /\
    (!s. P s ==> fresh_vars_wrt st s /\
         eval_operand x s = SOME (val_to_w256 (IntV i1)) /\
         eval_operand y s = SOME (val_to_w256 (IntV i2))) ==>
    err = RuntimeError "bounded_int_op bound" /\
    frag_exec_in ctx fn st st' P Q
      (result_rel func ret_tv cenv cx (INR (Error err), es'))
Proof
  rpt gen_tac >> strip_tac >>
  `bounded_int_op (Unsigned 256) (i1 + i2) = INR err` by
    fs[evaluate_binop_def] >>
  conj_tac >- (qpat_x_assum `bounded_int_op _ _ = _` mp_tac >>
               rw[bounded_int_op_def]) >>
  `dimword (:256) <=
   w2n (val_to_w256 (IntV i1)) + w2n (val_to_w256 (IntV i2))` by
    (irule bounded_int_op_add_overflow >> metis_tac[]) >>
  qspecl_then [`ctx`, `fn`, `x`, `y`, `ty`, `st`, `op`, `st'`, `P`, `Q`,
               `result_rel func ret_tv cenv cx (INR (Error err), es')`]
    mp_tac compile_safe_add_overflow_frag >>
  impl_tac >- (simp[result_rel_def] >> metis_tac[]) >>
  simp[]
QED

(* ===== Declaring and reading a word local ===== *)

(* A straight-line instruction steps run_from to the next index. *)
Theorem run_from_step:
  !fuel ctx fn s bb inst s1.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s1 ==>
    run_from fuel ctx fn s =
    run_from fuel ctx fn (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  simp[run_from_def, Once exec_block_def, step_inst_non_invoke]
QED

Theorem lookup_block_fn_insts:
  !lbl fn bb i.
    lookup_block lbl fn.fn_blocks = SOME bb /\ MEM i bb.bb_instructions ==>
    MEM i (fn_insts fn)
Proof
  rw[fn_insts_def] >> drule lookup_block_MEM >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> rw[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem eval_stmt_annassign_value:
  !cx id typ e es es'.
    eval_stmt cx (AnnAssign id typ e) es = (INL (), es') ==>
    ?tyv tv es1 v es2 sc rest.
      evaluate_type (get_tenv cx) typ = SOME tyv /\
      eval_expr cx e es = (INL tv, es1) /\
      materialise cx tv es1 = (INL v, es2) /\
      lookup_scopes id es2.scopes = NONE /\ es2.scopes = sc :: rest /\
      es' = es2 with scopes :=
              (sc |+ (id, <| assignable := T; type := tyv; value := v |>))
              :: rest
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       LET_THM] >>
  strip_tac >>
  gvs[AllCaseEqs(), lift_option_type_def, raise_def, return_def] >>
  qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
  simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, set_scopes_def, return_def, raise_def] >>
  rw[AllCaseEqs()] >> gvs[] >>
  rename1 `materialise cx tv es1 = (INL v, es2)` >>
  qpat_x_assum `(case evaluate_type _ _ of NONE => _ | SOME _ => _) _ = _`
    mp_tac >>
  Cases_on `evaluate_type (get_tenv cx) typ` >>
  simp[raise_def, return_def] >> strip_tac >>
  qpat_x_assum `(case es2.scopes of [] => _ | _ => _) _ = _` mp_tac >>
  Cases_on `es2.scopes` >> simp[raise_def, set_scopes_def, return_def] >>
  strip_tac >> gvs[] >>
  qexistsl_tac [`tv`, `es1`, `v`, `es2`, `h`, `t`] >>
  simp[evaluation_state_component_equality]
QED

(* A value held in one memory word under its plain encoding val_to_w256. *)
Definition word_value_def:
  word_value v <=>
    (?b. v = BoolV b) \/ (?n. v = IntV n) \/ (?k. v = FlagV k) \/
    (?n. v = DecimalV n)
End

Theorem word_value_in_memory:
  !ty v off s.
    word_value v ==>
    val_in_memory ty v off (mstore off (val_to_w256 v) s).vs_memory
Proof
  rw[word_value_def] >> simp[mstore_establishes_val_in_memory_prim]
QED

Theorem word_value_wf:
  !ty v. word_value v /\ type_memory_size ty = 32 ==> val_wf ty v
Proof
  rw[word_value_def] >> simp[val_wf_def]
QED

(* state_rel reads the Venom state only through the locals' memory and
   the fields below. *)
Theorem state_rel_frame:
  !func cenv cx es es' s s'.
    state_rel func cenv cx es s /\ local_ptrs_rel func cenv es'.scopes s' /\
    es' = es with scopes := es'.scopes /\
    s'.vs_accounts = s.vs_accounts /\ s'.vs_transient = s.vs_transient /\
    s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\ s'.vs_logs = s.vs_logs /\
    s'.vs_outcomes = s.vs_outcomes /\ s'.vs_requests = s.vs_requests /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_data_section = s.vs_data_section ==>
    state_rel func cenv cx es' s'
Proof
  rpt strip_tac >>
  qpat_x_assum `es' = _` SUBST1_TAC >>
  fs[state_rel_def, storage_rel_def, transient_rel_def, immutables_rel_def,
     logs_rel_def, call_ctx_rel_def, contract_storage_def,
     contract_transient_def]
QED

Theorem local_ptrs_rel_inst_idx:
  !func cenv sc s n.
    local_ptrs_rel func cenv sc (s with vs_inst_idx := n) <=>
    local_ptrs_rel func cenv sc s
Proof
  simp[local_ptrs_rel_def, local_region_def, local_backed_def, lookup_var_def]
QED

Theorem alloca_inv_fields:
  !s s'.
    alloca_inv s /\ s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next ==> alloca_inv s'
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Theorem compile_annassign_word_frag:
  !ctx func cenv cx lctx ty id vtyp e st st' es es' R p sz.
    compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((), st') /\
    eval_stmt cx (AnnAssign id vtyp e) es = (INL (), es') /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    is_word_type vtyp /\ ~has_length_word vtyp /\
    32 <= sz /\ sz < dimword (:256) /\ fn_inst_ids_distinct func /\
    (!n sz'. n <> id ==> FLOOKUP cenv.ce_vars n <> SOME (PtrVar (Var p) sz')) /\
    (!n. st.cs_next_var <= n ==> p <> STRING #"%" (toString n)) /\
    (!tyv. evaluate_type (get_tenv cx) vtyp = SOME tyv ==>
           type_memory_size tyv = 32) /\
    (!esa tv esb. eval_expr cx e esa = (INL tv, esb) ==>
       ?v. tv = Value v /\ word_value v) /\
    (!sa sb op esa esb v w aid b.
       lower_value compile_expr cenv (expr_type e) e sa = (op, sb) /\
       eval_expr cx e esa = (INL (Value v), esb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       frag_exec_in ctx func sa sb
         (\s. frag_rel func cenv cx sa esa s /\ lookup_var p s = SOME w /\
              FLOOKUP s.vs_allocas aid = SOME b)
         (\s. frag_rel func cenv cx sb esb s /\
              eval_operand op s = SOME (val_to_w256 v) /\
              lookup_var p s = SOME w /\ FLOOKUP s.vs_allocas aid = SOME b)
         R) ==>
    frag_exec_in ctx func st st'
      (\s. frag_rel func cenv cx st es s /\
           FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
           s.vs_alloca_next + sz < dimword (:256))
      (frag_rel func cenv cx st' es') R
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_stmt_annassign_value >> strip_tac >>
  qpat_x_assum `!esa tv esb. eval_expr cx e esa = (INL tv, esb) ==> Q esa tv esb`
    (qspecl_then [`es`, `tv`, `es1`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  gvs[materialise_def, return_def] >>
  `type_memory_size tyv = 32` by fs[] >>
  `lookup_scopes id es.scopes = NONE` by
    (irule lookup_scopes_none_map_fdom >> qexists_tac `es1.scopes` >>
     qpat_x_assum `eval_expr cx e es = _`
       (strip_assume_tac o MATCH_MP eval_expr_preserves_scopes_dom) >>
     simp[]) >>
  `not_local_ptr cenv es.scopes p /\ not_local_ptr cenv es1.scopes p` by
    (rw[not_local_ptr_def] >> Cases_on `name = id` >> gvs[]) >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_local_alloca_def, compile_assign_value_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `emit_inst ALLOCA _ _ st = (_, st1)` >>
  rename1 `compile_expr cenv (expr_type e) e st1 = (src_vv, st2)` >>
  rename1 `unwrap_value cenv src_vv st2 = (val_op, st3)` >>
  `lower_value compile_expr cenv (expr_type e) e st1 = (val_op, st3)` by
    simp[lower_value_def, comp_bind_def] >>
  imp_res_tac emit_inst_state >>
  imp_res_tac emitted_insts_emit_void >> imp_res_tac emit_void_extends >>
  qpat_x_assum `!sa sb op esa esb v w aid b. P sa sb op esa esb v w aid b ==>
                                         Q sa sb op esa esb v w aid b`
    (fn th => drule_all_then strip_assume_tac
                (Q.SPECL [`st1`, `st3`, `val_op`, `es`, `es1`] th)) >>
  `cs_extends st3 st'` by
    (irule cs_extends_same_block >> fs[same_blocks_def]) >>
  `cs_extends st st3` by
    (irule cs_extends_trans >> qexists_tac `st1` >> asm_rewrite_tac[]) >>
  `cs_extends st1 st'` by
    (irule cs_extends_trans >> qexists_tac `st3` >> asm_rewrite_tac[]) >>
  `cs_extends st1 st3` by metis_tac[] >>
  simp[frag_exec_in_def] >> rpt strip_tac >>
  `fn_has_code st1 st' func /\ fn_has_code st1 st3 func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  (* the ALLOCA *)
  qspecl_then [`st1`, `st'`, `func`] mp_tac fn_has_code_start >>
  asm_rewrite_tac[] >> strip_tac >>
  qabbrev_tac `A = mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `get_instruction bb s.vs_inst_idx = SOME A /\ MEM A bb.bb_instructions` by
    (qpat_x_assum `isPREFIX _ bb.bb_instructions` mp_tac >>
     asm_rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
     asm_rewrite_tac[get_instruction_def] >>
     PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[EL_LENGTH_APPEND]) >>
  `MEM A (fn_insts func)` by metis_tac[lookup_block_fn_insts] >>
  `w2n (n2w sz : bytes32) = sz` by
    (rewrite_tac[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >>
     first_assum ACCEPT_TAC) >>
  `s.vs_alloca_next < dimword (:256)` by DECIDE_TAC >>
  `A.inst_id = st.cs_next_id /\ A.inst_opcode = ALLOCA /\
   A.inst_outputs = [p] /\ A.inst_operands = [Lit (n2w sz)]` by
    simp[Abbr `A`, venomInstTheory.mk_inst_def] >>
  `step_inst_base A s = exec_alloca A s (n2w sz : bytes32)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> asm_rewrite_tac[] >>
     simp[]) >>
  `?s1. exec_alloca A s (n2w sz : bytes32) = OK s1` by simp[exec_alloca_def] >>
  qspecl_then [`func`, `cenv`, `es.scopes`, `s`, `s1`, `A`, `p`, `n2w sz : bytes32`]
    mp_tac local_ptrs_rel_exec_alloca_fresh >>
  impl_tac >- fs[frag_rel_def, state_rel_def] >> strip_tac >>
  rename1 `lookup_var p s1 = SOME w1` >>
  `s1.vs_memory = s.vs_memory /\ s1.vs_accounts = s.vs_accounts /\
   s1.vs_transient = s.vs_transient /\ s1.vs_call_ctx = s.vs_call_ctx /\
   s1.vs_tx_ctx = s.vs_tx_ctx /\ s1.vs_block_ctx = s.vs_block_ctx /\
   s1.vs_logs = s.vs_logs /\ s1.vs_outcomes = s.vs_outcomes /\
   s1.vs_requests = s.vs_requests /\ s1.vs_immutables = s.vs_immutables /\
   s1.vs_data_section = s.vs_data_section /\ s1.vs_halted = s.vs_halted /\
   s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_vars = s.vs_vars |+ (p, n2w s.vs_alloca_next)` by
    (qpat_x_assum `exec_alloca _ _ _ = OK s1` mp_tac >>
     simp[exec_alloca_def, update_var_def] >> strip_tac >> gvs[]) >>
  qabbrev_tac `s1' = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!f. run_from f ctx func s = run_from f ctx func s1'` by
    (gen_tac >>
     qspecl_then [`f`, `ctx`, `func`, `s`, `bb`, `A`, `s1`] mp_tac
       run_from_step >>
     impl_tac >- fs[is_terminator_def] >> simp[Abbr `s1'`]) >>
  `state_rel func cenv cx es s1'` by
    (qspecl_then [`func`, `cenv`, `cx`, `es`, `es`, `s`, `s1'`] mp_tac
       state_rel_frame >>
     impl_tac >- (
       simp[Abbr `s1'`, local_ptrs_rel_inst_idx,
            vyperStateTheory.evaluation_state_component_equality] >>
       fs[frag_rel_def]) >>
     simp[]) >>
  `fresh_vars_wrt st1 s1'` by
    (simp[fresh_vars_wrt_def, Abbr `s1'`] >> rpt strip_tac >>
     fs[frag_rel_def, fresh_vars_wrt_def] >> metis_tac[]) >>
  `alloca_inv s1'` by
    (irule alloca_inv_fields >> qexists_tac `s1` >> simp[Abbr `s1'`] >>
     fs[frag_rel_def] >> metis_tac[alloca_inv_exec_alloca]) >>
  `frag_rel func cenv cx st1 es s1'` by
    fs[frag_rel_def, Abbr `s1'`] >>
  (* the right-hand side *)
  `lookup_var p s1' = SOME w1 /\
   FLOOKUP s1'.vs_allocas st.cs_next_id = SOME (w2n w1, sz) /\
   s1'.vs_current_bb = st1.cs_current_bb /\
   s1'.vs_inst_idx = LENGTH st1.cs_current_insts` by
    gvs[Abbr `s1'`, lookup_var_def] >>
  qpat_x_assum `!w aid b. P w aid b /\ Q w aid b`
    (qspecl_then [`w1`, `st.cs_next_id`, `(w2n w1, sz)`] strip_assume_tac) >>
  qpat_x_assum `frag_exec_in ctx func st1 st3 _ _ _`
    (mp_tac o SIMP_RULE std_ss [frag_exec_in_def]) >>
  asm_rewrite_tac[] >> disch_then (qspec_then `s1'` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac
  >- (rename1 `frag_rel func cenv cx st3 es1 s2` >>
      (* the MSTORE *)
      qabbrev_tac `M = mk_inst st3.cs_next_id MSTORE [Var p; val_op] []` >>
      `?bm. lookup_block st3.cs_current_bb func.fn_blocks = SOME bm /\
            isPREFIX st'.cs_current_insts bm.bb_instructions` by
        (qpat_x_assum `fn_has_code st st' func` mp_tac >>
         simp[fn_has_code_def] >> fs[same_blocks_def] >> metis_tac[]) >>
      `get_instruction bm s2.vs_inst_idx = SOME M` by
        (qpat_x_assum `isPREFIX _ bm.bb_instructions` mp_tac >>
         asm_rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
         asm_rewrite_tac[get_instruction_def] >>
         PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[EL_LENGTH_APPEND, Abbr `M`]) >>
      `step_inst_base M s2 = OK (mstore (w2n w1) (val_to_w256 v) s2)` by
        (qunabbrev_tac `M` >> irule step_MSTORE >>
         fs[eval_operand_def]) >>
      qabbrev_tac `s3m = mstore (w2n w1) (val_to_w256 v) s2` >>
      qabbrev_tac `s3 = s3m with vs_inst_idx := SUC s2.vs_inst_idx` >>
      `!f. run_from f ctx func s2 = run_from f ctx func s3` by
        (gen_tac >>
         qspecl_then [`f`, `ctx`, `func`, `s2`, `bm`, `M`, `s3m`] mp_tac
           run_from_step >>
         impl_tac >- fs[Abbr `M`, venomInstTheory.mk_inst_def,
                        is_terminator_def] >>
         simp[Abbr `s3`]) >>
      `s3m.vs_vars = s2.vs_vars /\ s3m.vs_allocas = s2.vs_allocas /\
       s3m.vs_alloca_next = s2.vs_alloca_next /\
       s3m.vs_halted = s2.vs_halted /\
       s3m.vs_current_bb = s2.vs_current_bb /\
       s3m.vs_accounts = s2.vs_accounts /\ s3m.vs_transient = s2.vs_transient /\
       s3m.vs_call_ctx = s2.vs_call_ctx /\ s3m.vs_tx_ctx = s2.vs_tx_ctx /\
       s3m.vs_block_ctx = s2.vs_block_ctx /\ s3m.vs_logs = s2.vs_logs /\
       s3m.vs_outcomes = s2.vs_outcomes /\ s3m.vs_requests = s2.vs_requests /\
       s3m.vs_immutables = s2.vs_immutables /\
       s3m.vs_data_section = s2.vs_data_section` by
        simp[Abbr `s3m`, mstore_def, LET_THM] >>
      (* the new local is held at its region *)
      `!n b sz'. n <> id /\ local_region cenv es1.scopes s2 n b sz' ==>
                 regions_disjoint (w2n w1) sz b sz'` by
        (rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
         qexistsl_tac [`cenv`, `func`, `A`, `n`, `p`, `es1.scopes`, `s2`] >>
         fs[frag_rel_def, state_rel_def]) >>
      `w2n w1 + sz <= s2.vs_alloca_next` by
        (fs[frag_rel_def, alloca_inv_def, alloca_next_valid_def] >>
         res_tac >> fs[]) >>
      `local_backed func p s2 (w2n w1) sz` by
        (simp[local_backed_def] >> disj1_tac >> qexists_tac `A` >> simp[]) >>
      `val_in_memory tyv v (w2n w1) s3m.vs_memory` by
        simp[Abbr `s3m`, word_value_in_memory] >>
      `val_wf tyv v` by (irule word_value_wf >> simp[]) >>
      `!n b sz'. n <> id /\ local_region cenv es1.scopes s2 n b sz' ==>
                 mem_bytes_at b sz' s2.vs_memory =
                 mem_bytes_at b sz' s3m.vs_memory` by
        (rpt strip_tac >>
         `regions_disjoint (w2n w1) sz b sz'` by metis_tac[] >>
         `b + sz' <= w2n w1 \/ w2n w1 + 32 <= b` by
           (fs[regions_disjoint_def] >> DECIDE_TAC) >>
         simp[Abbr `s3m`] >> irule EQ_SYM >>
         irule mstore_mem_bytes_at_disjoint >> simp[]) >>
      `lookup_scopes id
         (sc |+ (id, <| assignable := T; type := tyv; value := v |>) :: rest) =
         SOME <| assignable := T; type := tyv; value := v |> /\
       !n. n <> id ==>
           lookup_scopes n
             (sc |+ (id, <| assignable := T; type := tyv; value := v |>)
              :: rest) = lookup_scopes n es1.scopes` by
        simp[lookup_scopes_def, FLOOKUP_UPDATE] >>
      `local_ptrs_rel func cenv
         (sc |+ (id, <| assignable := T; type := tyv; value := v |>) :: rest)
         s3m` by
        (irule local_ptrs_rel_write_local >>
         qexistsl_tac [`<| assignable := T; type := tyv; value := v |>`,
                       `id`, `p`, `es1.scopes`, `s2`, `sz`, `w1`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         fs[frag_rel_def, state_rel_def, lookup_var_def] >> rw[] >> gvs[]) >>
      `state_rel func cenv cx
         (es1 with scopes :=
            sc |+ (id, <| assignable := T; type := tyv; value := v |>) :: rest)
         s3` by
        (qspecl_then [`func`, `cenv`, `cx`, `es1`,
           `es1 with scopes :=
              sc |+ (id, <| assignable := T; type := tyv; value := v |>)
              :: rest`, `s2`, `s3`] mp_tac state_rel_frame >>
         impl_tac >- (
           simp[Abbr `s3`, local_ptrs_rel_inst_idx,
                vyperStateTheory.evaluation_state_component_equality] >>
           fs[frag_rel_def]) >>
         simp[]) >>
      disj1_tac >> qexists_tac `s3` >>
      `s3.vs_current_bb = st'.cs_current_bb /\
       s3.vs_inst_idx = LENGTH st3.cs_current_insts + 1` by
        fs[Abbr `s3`, same_blocks_def] >>
      `frag_rel func cenv cx st'
         (es1 with scopes :=
            sc |+ (id, <| assignable := T; type := tyv; value := v |>) :: rest)
         s3` by
        (fs[frag_rel_def, Abbr `s3`, fresh_vars_wrt_def] >>
         irule alloca_inv_fields >> qexists_tac `s2` >> simp[]) >>
      asm_rewrite_tac[] >> gen_tac >> strip_tac >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func s2 <> Error e) ==>
                           Q fuel` (qspec_then `fuel` mp_tac) >>
      asm_rewrite_tac[]) >>
  disj2_tac >> metis_tac[]
QED

(* Slice lemma 1, the read: a word local held through its pointer loads
   with one MLOAD of the pointer, and the source reads the same value. *)
Theorem compile_name_word_frag:
  !ctx func cenv cx ty ann id st op st' es R p sz entry.
    lower_value compile_expr cenv ty (Name ann id) st = (op, st') /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    is_word_type ann /\
    lookup_scopes id es.scopes = SOME entry /\ word_value entry.value ==>
    eval_expr cx (Name ann id) es = (INL (Value entry.value), es) /\
    frag_exec_in ctx func st st' (frag_rel func cenv cx st es)
      (\s. frag_rel func cenv cx st' es s /\
           eval_operand op s = SOME (val_to_w256 entry.value)) R
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
           lift_option_type_def] >>
      `lookup_scopes_val id es.scopes = SOME entry.value` by
        (qpat_x_assum `lookup_scopes _ _ = _` mp_tac >>
         qspec_tac (`es.scopes`, `scs`) >>
         Induct >> simp[lookup_scopes_def, lookup_scopes_val_def] >>
         rpt strip_tac >> Cases_on `FLOOKUP h id` >> gvs[]) >>
      simp[return_def]) >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, compile_expr_def, comp_bind_def, compile_name_vv_def,
       unwrap_value_def, contextTheory.compile_ptr_load_def,
       contextTheory.mk_ptr_def, comp_return_def,
       vyperASTTheory.expr_type_def] >>
  strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  qabbrev_tac `out = STRING #"%" (toString st.cs_next_var)` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by
    simp[venomInstTheory.mk_inst_def, is_terminator_def] >>
  irule frag_exec_in_run_inst_seq >>
  fs[same_blocks_def, IS_PREFIX_APPEND3] >>
  rpt strip_tac >> disj1_tac >>
  `?w. lookup_var p s = SOME w /\
       val_in_memory entry.type entry.value (w2n w) s.vs_memory` by
    (fs[frag_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> metis_tac[]) >>
  `mload (w2n w) s = val_to_w256 entry.value` by
    (fs[word_value_def] >> gvs[val_in_memory_prim, mem_word_at_eq_mload]) >>
  qabbrev_tac `u = update_var out (mload (w2n w) s) s` >>
  `step_inst_base (mk_inst st.cs_next_id MLOAD [Var p] [out]) s = OK u` by
    (qunabbrev_tac `u` >> irule step_MLOAD >> simp[eval_operand_def]) >>
  qexists_tac `u` >> simp[run_inst_seq_def] >>
  `not_local_ptr cenv es.scopes out` by
    (qunabbrev_tac `out` >>
     qspecl_then [`func`, `cenv`, `es.scopes`, `st`, `s`, `st.cs_next_var`]
       mp_tac local_ptrs_rel_fresh_not_local_ptr >>
     fs[frag_rel_def, state_rel_def]) >>
  `state_rel func cenv cx es u` by
    (simp[Abbr `u`] >> irule state_rel_update_var >> fs[frag_rel_def]) >>
  `fresh_vars_wrt st' u` by
    (rw[fresh_vars_wrt_def] >>
     fs[Abbr `u`, Abbr `out`, update_var_def, frag_rel_def,
        fresh_vars_wrt_def]) >>
  `state_rel func cenv cx es (u with vs_inst_idx := LENGTH st.cs_current_insts + 1)` by
    (qspecl_then [`func`, `cenv`, `cx`, `es`, `es`, `u`,
                  `u with vs_inst_idx := LENGTH st.cs_current_insts + 1`]
       mp_tac state_rel_frame >>
     impl_tac >- (
       fs[state_rel_def, local_ptrs_rel_inst_idx,
          vyperStateTheory.evaluation_state_component_equality]) >>
     simp[]) >>
  `alloca_inv u` by
    (irule alloca_inv_fields >> qexists_tac `s` >>
     fs[Abbr `u`, update_var_def, frag_rel_def]) >>
  `~u.vs_halted` by fs[Abbr `u`, update_var_def, frag_rel_def] >>
  `frag_rel func cenv cx st' es
     (u with vs_inst_idx := LENGTH st.cs_current_insts + 1)` by
    (fs[frag_rel_def, fresh_vars_wrt_def] >>
     irule alloca_inv_fields >> qexists_tac `u` >> simp[]) >>
  asm_rewrite_tac[] >>
  simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE]
QED
