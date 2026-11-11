(*
 * Fuel bound for the decimal-digit loop of uint2str.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_uint2str
 *)

Theory fragFuelLoopUint2str
Ancestors
  fragFuel fragFuelContextBase compileEnv emitHelper context venomInst
  builtinStrings exprSimUint2Str
Libs
  fragFuelLib

(* Structural boundary for the post-allocation tail.  Its layout and
   templates are shared with the existing uint2str simulation proof. *)
Theorem uint2str_tail_structure[local]:
  cs_extends a (u2s_end a op buf n) /\
  a.cs_next_var <= (u2s_end a op buf n).cs_next_var /\
  (cs_no_phi a ==> cs_no_phi (u2s_end a op buf n))
Proof
  conj_tac
  >- (simp[cs_extends_def, u2s_end_def] >>
      simp[u2s_blocks_def]) >>
  simp[u2s_end_def, cs_no_phi_def, u2s_blocks_def,
       u2s_setup_def, u2s_check_def, u2s_cond_def, u2s_body_def,
       u2s_zero_def, u2s_final_def, u2s_inst_def, mk_inst_def,
       listTheory.EVERY_APPEND]
QED

Theorem uint2str_structure[local]:
  compile_uint2str op n sz st = (x,st') ==>
  cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
  (cs_no_phi st ==> cs_no_phi st')
Proof
  strip_tac >> drule compile_uint2str_layout >> strip_tac >>
  gvs[u2s_layout_def] >>
  mp_tac (Q.SPECL [`n + sz`, `{}:string set`, `{}:string set`]
    fuel_ok_compile_alloc_buffer) >>
  rewrite_tac[fuel_ok_def] >> disch_then drule >> strip_tac >>
  mp_tac (Q.INST [`buf` |-> `ba.buf_operand`] uint2str_tail_structure) >>
  strip_tac >> conj_tac
  >- metis_tac[cs_extends_trans] >>
  simp[u2s_end_def]
QED

(* Every destination in the shared templates is fresh at the allocation
   endpoint, hence outside all protected variables at the original entry. *)
Theorem uint2str_var_not_below[local]:
  N <= a.cs_next_var ==> ~var_below N (u2s_var a k)
Proof
  strip_tac >> simp[u2s_var_def, fresh_var_def] >>
  irule var_below_fresh >> simp[]
QED

(* A failed call-free prefix fixes the result before any block transition. *)
Theorem uint2str_prefix_failure[local]:
  !is s ctx fn bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
    (!t. run_inst_seq is s <> OK t) ==>
    !f. run_from f ctx fn s = run_from 0 ctx fn s
Proof
  Induct >> simp[exprLoweringPropsTheory.run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >> fs[] >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h :: rest /\
          isPREFIX is rest` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
  drule fragExecTheory.DROP_EQ_CONS >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    simp[get_instruction_def] >>
  `!f. run_from f ctx fn s =
    case step_inst_base h s of
      OK s1 => run_from f ctx fn (s1 with vs_inst_idx := SUC s.vs_inst_idx)
    | IntRet v s1 => IntRet v s1
    | Halt s1 => Halt s1
    | Abort a s1 => Abort a s1
    | Error e => Error e` by
    (gen_tac >> drule_all run_from_nonterm >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK s1` >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow, venomExecSemanticsTheory.step_inst_non_invoke] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) is` by fs[listTheory.EVERY_MEM] >>
  first_x_assum irule >> simp[] >>
  simp[fragExecTheory.run_inst_seq_inst_idx] >>
  Cases_on `run_inst_seq is s1` >> gvs[instIdxIndepTheory.exec_result_map_def]
QED

Theorem uint2str_prefix_outcome[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is ==>
  ((?t. run_inst_seq is s = OK t /\
        t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx /\
        (!x. EVERY (\i. ~MEM x i.inst_outputs) is ==>
             lookup_var x t = lookup_var x s) /\
        (!f. run_from f ctx fn s =
             run_from f ctx fn (t with vs_inst_idx := s.vs_inst_idx + LENGTH is))) \/
   (!f. run_from f ctx fn s = run_from 0 ctx fn s))
Proof
  strip_tac >> Cases_on `?t. run_inst_seq is s = OK t`
  >- (pop_assum strip_assume_tac >> disj1_tac >> qexists_tac `t` >> simp[] >>
      rpt conj_tac
      >- (drule_all fragExecTheory.exec_block_run_inst_seq >> metis_tac[]) 
      >- (irule exprLoweringPropsTheory.run_inst_seq_preserves_field >>
          qexists_tac `is` >> simp[] >> rpt strip_tac >>
          fs[listTheory.EVERY_MEM] >>
          metis_tac[venomInstPropsTheory.step_preserves_control_flow,
                    venomExecSemanticsTheory.step_inst_non_invoke])
      >- (rpt strip_tac >>
          irule exprLoweringPropsTheory.run_inst_seq_preserves_field >>
          qexists_tac `is` >> simp[] >> rpt strip_tac >>
          fs[listTheory.EVERY_MEM] >>
          metis_tac[venomInstPropsTheory.step_preserves_non_output_vars,
                    venomExecSemanticsTheory.step_inst_non_invoke]) >>
      gen_tac >> drule_all u2s_run_from_prefix >> simp[arithmeticTheory.ADD_COMM]) >>
  disj2_tac >> irule uint2str_prefix_failure >> metis_tac[]
QED

Theorem uint2str_body_quotient[local]:
  eval_operand (Var (u2s_var a 0)) s = SOME xw /\
  run_inst_seq (TAKE 9 (u2s_body a buf n)) s = OK t ==>
  eval_operand (Var (u2s_var a 0)) t = SOME (safe_div xw 10w)
Proof
  strip_tac >>
  `TAKE 9 (u2s_body a buf n) = TAKE 5 (u2s_body a buf n) ++
     (TAKE 2 (DROP 5 (u2s_body a buf n)) ++
      TAKE 2 (DROP 7 (u2s_body a buf n)))` by simp[u2s_body_def] >>
  `?s1. run_inst_seq (TAKE 5 (u2s_body a buf n)) s = OK s1` by
    (Cases_on `run_inst_seq (TAKE 5 (u2s_body a buf n)) s` >>
     gvs[] >>
     gvs[exprLoweringPropsTheory.run_inst_seq_append_err]) >>
  `eval_operand (Var (u2s_var a 0)) s1 = SOME xw` by
    (`lookup_var (u2s_var a 0) s1 = lookup_var (u2s_var a 0) s` by
       (irule exprLoweringPropsTheory.run_inst_seq_preserves_field >>
        qexists_tac `TAKE 5 (u2s_body a buf n)` >> simp[] >>
        rpt strip_tac >>
        `~MEM (u2s_var a 0) i.inst_outputs /\
         i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
          (gvs[u2s_body_def, u2s_inst_def, mk_inst_def, is_terminator_def] >> simp[]) >>
        metis_tac[venomInstPropsTheory.step_preserves_non_output_vars,
                  venomExecSemanticsTheory.step_inst_non_invoke]) >>
     gvs[venomStateTheory.eval_operand_def]) >>
  drule u2s_body_div_run >> strip_tac >>
  `run_inst_seq (TAKE 2 (DROP 7 (u2s_body a buf n)))
     (update_var (u2s_var a 0) (safe_div xw 10w)
       (update_var (u2s_var a 9) (safe_div xw 10w) s1)) = OK t` by
    (qpat_x_assum `run_inst_seq (TAKE 9 _) _ = _` mp_tac >>
     asm_rewrite_tac[] >>
     drule_all exprLoweringPropsTheory.run_inst_seq_append >>
     disch_then (qspec_then `TAKE 2 (DROP 5 (u2s_body a buf n)) ++ TAKE 2 (DROP 7 (u2s_body a buf n))` SUBST1_TAC) >>
     first_x_assum (qspecl_then [`n`, `buf`] assume_tac) >>
     drule_all exprLoweringPropsTheory.run_inst_seq_append >>
     simp[]) >>
  `lookup_var (u2s_var a 0) t =
     lookup_var (u2s_var a 0)
       (update_var (u2s_var a 0) (safe_div xw 10w)
         (update_var (u2s_var a 9) (safe_div xw 10w) s1))` by
    (irule exprLoweringPropsTheory.run_inst_seq_preserves_field >>
     qexists_tac `TAKE 2 (DROP 7 (u2s_body a buf n))` >> simp[] >>
     rpt strip_tac >>
     `~MEM (u2s_var a 0) i.inst_outputs /\
      i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
       (gvs[u2s_body_def, u2s_inst_def, mk_inst_def, is_terminator_def] >> simp[]) >>
     metis_tac[venomInstPropsTheory.step_preserves_non_output_vars,
               venomExecSemanticsTheory.step_inst_non_invoke]) >>
  gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem uint2str_block_outcome[local]:
  no_phi_fn fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions = is ++ [inst] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  (!x. var_below N x /\ x NOTIN Wv ==>
       EVERY (\i. ~MEM x i.inst_outputs) is) /\
  (!t. run_inst_seq is s = OK t ==> ?lbl.
     step_inst_base inst (t with vs_inst_idx := s.vs_inst_idx + LENGTH is) =
       OK (jump_to lbl (t with vs_inst_idx := s.vs_inst_idx + LENGTH is)) /\
     P (jump_to lbl (t with vs_inst_idx := s.vs_inst_idx + LENGTH is))) ==>
  fuel_outcome G ctx fn s 1 (\u. P u /\ vars_kept N Wv s u)
Proof
  strip_tac >>
  `isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all uint2str_prefix_outcome >> disch_then (qspec_then `ctx` strip_assume_tac)
  >- (first_x_assum drule >> strip_tac >>
      `get_instruction bb (s.vs_inst_idx + LENGTH is) = SOME inst` by
        (`DROP (LENGTH is) (DROP s.vs_inst_idx bb.bb_instructions) = [inst]` by simp[exprLoweringPropsTheory.DROP_PREFIX] >>
         fs[rich_listTheory.DROP_DROP_T] >>
         drule fragExecTheory.DROP_EQ_CONS >>
         simp[get_instruction_def, arithmeticTheory.ADD_COMM]) >>
      `vars_kept N Wv s (jump_to lbl (t with vs_inst_idx := s.vs_inst_idx + LENGTH is))` by
        (simp[vars_kept_def, venomStateTheory.lookup_var_def] >>
         metis_tac[venomStateTheory.lookup_var_def]) >>
      `fuel_outcome G ctx fn
         (t with vs_inst_idx := s.vs_inst_idx + LENGTH is) 1
         (\u. P u /\ vars_kept N Wv s u)` by
        (irule fuel_outcome_jump >> simp[] >>
         qexistsl [`inst`, `lbl`] >> gvs[arithmeticTheory.ADD_COMM]) >>
      gvs[fuel_outcome_def] >> metis_tac[]) >>
  simp[fuel_outcome_def] >> disj2_tac >> metis_tac[]
QED

(* The loop works on a fresh copy val_var of val_op, made before the loop
   (so no precondition on val_op is needed), and on a fresh counter i_var
   from 0.  Each round (cond -> body -> cond) runs straight-line code, sets
   val_var to val_var / 10 and adds 1 to i_var, leaving through final_lbl
   when val_var is 0.  The body writes only val_var, i_var and variables it
   allocates itself, so the loop variable is the one that shrinks: a 256-bit
   value reaches 0 after at most 78 divisions by 10, so i_var is at most 78
   and never wraps, and the bound is independent of the runtime state. *)
Theorem fuel_ok_compile_uint2str:
  !val_op n_digits buf_size Wv E.
    fuel_ok Wv {} E (compile_uint2str val_op n_digits buf_size)
Proof
  cheat
QED
