(*
 * Straight-line code that writes only fresh variables (#636)
 *
 * The run-level lemmas of the lowering (emitHelperProps, arithmeticProps)
 * say what an emitted sequence computes from a state where the fresh
 * variables are unbound (fresh_vars_wrt), and nothing of what it leaves
 * alone.  writes_fresh is the syntactic side: every instruction is a pure
 * operation or an assertion, and writes only variables fresh at the start.
 * Such a sequence changes nothing but those variables, and
 * frag_exec_writes_fresh turns a run-level lemma into a fragment over
 * stmt_state_rel, from a state with the last iteration's temporaries
 * still bound.
 *
 * TOP-LEVEL:
 *   fresh_write_op, writes_fresh
 *   run_inst_seq_writes_fresh — the run changes only fresh variables
 *   writes_fresh_emit_op, writes_fresh_mono, writes_fresh_append
 *   frag_exec_run_frame       — semantic-frame lifting, including read opcodes
 *   frag_exec_writes_fresh    — the pure/fresh specialization
 *   straight_fresh            — a compile action that emits such code in
 *                               the current block, with its combinators
 *                               (_return, _emit_op, _emit_void, _bind,
 *                               _ignore_bind)
 *   frag_exec_straight_fresh  — the fragment of a straight_fresh action
 *   frag_exec_writes_fresh_abort, frag_exec_straight_fresh_abort
 *                             — the same for code that always aborts
 *
 * Helpers: exec_pure_ok_update, step_fresh_write_op, fresh_write_op_simple,
 *   not_fresh_at_mono, eval_operand_drop_fresh
 *)

Theory freshWrites
Ancestors
  exprSimProps
  list rich_list finite_map pred_set
  fragExec varsExt
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  venomExecSemantics venomInst venomState

(* ===== The instructions ===== *)

(* The opcodes whose step writes at most their output: the pure
   operations and the assertions. *)
Definition fresh_write_op_def:
  fresh_write_op opc <=>
    MEM opc [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
             EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT;
             SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSERT; ASSERT_UNREACHABLE]
End

Definition writes_fresh_def:
  writes_fresh st is <=>
    EVERY (\i. fresh_write_op i.inst_opcode /\
               EVERY (\x. ~not_fresh_at st x) i.inst_outputs) is
End

Theorem fresh_write_op_simple:
  !opc. fresh_write_op opc ==>
        opc <> INVOKE /\ ~is_terminator opc /\ ~is_ext_call_op opc
Proof
  rw[fresh_write_op_def] >> simp[is_terminator_def, is_ext_call_op_def]
QED


Theorem step_fresh_write_op:
  !inst ss tt.
    fresh_write_op inst.inst_opcode /\ step_inst_base inst ss = OK tt ==>
    tt = ss with vs_vars := tt.vs_vars /\
    !x. ~MEM x inst.inst_outputs ==>
        FLOOKUP tt.vs_vars x = FLOOKUP ss.vs_vars x
Proof
  rewrite_tac[fresh_write_op_def] >>
  MATCH_ACCEPT_TAC step_pure_opcode_frame
QED

(* ===== The run ===== *)

Theorem run_inst_seq_writes_fresh:
  !is st ss tt.
    writes_fresh st is /\ run_inst_seq is ss = OK tt ==>
    tt = ss with vs_vars := tt.vs_vars /\
    !x. not_fresh_at st x ==> FLOOKUP tt.vs_vars x = FLOOKUP ss.vs_vars x
Proof
  Induct >- simp[run_inst_seq_def, venom_state_component_equality] >>
  qx_gen_tac `inst` >> rpt gen_tac >>
  simp[writes_fresh_def, run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base inst ss` >> gvs[] >>
  rename1 `step_inst_base inst ss = OK s1` >>
  drule_all step_fresh_write_op >> strip_tac >>
  first_x_assum (qspecl_then [`st`, `s1`, `tt`] mp_tac) >>
  simp[writes_fresh_def] >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
      fs[venom_state_component_equality]) >>
  rpt strip_tac >> fs[EVERY_MEM] >> metis_tac[]
QED

(* ===== The emitted code ===== *)

Theorem not_fresh_at_mono:
  !st st' z.
    not_fresh_at st z /\ st.cs_next_var <= st'.cs_next_var ==>
    not_fresh_at st' z
Proof
  rw[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem writes_fresh_emit_op:
  !opc args st op st'.
    emit_op opc args st = (op, st') /\ fresh_write_op opc ==>
    writes_fresh st (emitted_insts st st')
Proof
  rpt strip_tac >> imp_res_tac emitted_insts_emit_op >>
  simp[writes_fresh_def, venomInstTheory.mk_inst_def, not_fresh_at_def]
QED

Theorem writes_fresh_mono:
  !st st' is.
    writes_fresh st' is /\ st.cs_next_var <= st'.cs_next_var ==>
    writes_fresh st is
Proof
  rw[writes_fresh_def, EVERY_MEM] >> res_tac >> fs[EVERY_MEM] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem writes_fresh_append:
  !st is1 is2.
    writes_fresh st (is1 ++ is2) <=> writes_fresh st is1 /\ writes_fresh st is2
Proof
  rw[writes_fresh_def]
QED

(* An operand handed out before st reads the same once the variables fresh
   at st are dropped. *)
Theorem eval_operand_drop_fresh:
  !x st ss.
    (!z. x = Var z ==> not_fresh_at st z) ==>
    eval_operand x (drop_fresh st ss) = eval_operand x ss
Proof
  Cases >> rw[eval_operand_def, lookup_var_drop_fresh] >> simp[drop_fresh_def]
QED

(* ===== The fragment ===== *)

(* A run-level lemma for code that writes only fresh variables, from a
   state where they are unbound, gives a fragment from any state related
   at es that satisfies P: on success it ends related at es with op
   holding w, the earlier variables, the allocations and the memory kept;
   on an abort allowed by A it exits as R allows.  P must survive dropping
   the fresh variables, as facts about earlier operands do. *)
Theorem frag_exec_run_frame:
  !ctx func cenv cx es sa sb op w P A R s0.
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb) /\
    (!ss tt. run_inst_seq (emitted_insts sa sb) ss = OK tt ==>
       tt = ss with vs_vars := tt.vs_vars /\
       (!x. not_fresh_at sa x ==>
            FLOOKUP tt.vs_vars x = FLOOKUP ss.vs_vars x)) /\
    local_ptrs_reserved cenv sa /\
    (!ss. P ss ==> P (drop_fresh sa ss)) /\
    (!ss. fresh_vars_wrt sa ss /\ P ss ==>
       (?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
              eval_operand op ss' = SOME w) \/
       (?a ss'. run_inst_seq (emitted_insts sa sb) ss = Abort a ss' /\ A a)) /\
    (!a ss. A a ==> R (Abort a ss)) ==>
    frag_exec ctx sa sb
      (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\ P ss)
      (\ss. stmt_state_rel ctx func cenv cx es ss /\ eval_operand op ss = SOME w /\
            (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
                    lookup_var x ss = SOME w') /\
            (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                     FLOOKUP ss.vs_allocas aid = SOME b) /\
            ss.vs_memory = s0.vs_memory) R
Proof
  rpt strip_tac >>
  irule frag_exec_run_inst_seq_drop_fresh >> simp[] >> rpt strip_tac >>
  `P (drop_fresh sa s0)` by res_tac >>
  assume_tac (Q.SPECL [`sa`, `s0`] fresh_vars_wrt_drop_fresh) >>
  qpat_x_assum `!ss. fresh_vars_wrt _ _ /\ _ ==> _`
    (qspec_then `drop_fresh sa s0` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac
  >- (disj1_tac >> qexists_tac `ss'` >> asm_rewrite_tac[] >> rpt gen_tac >>
      strip_tac >>
      qpat_x_assum `!ss tt. run_inst_seq _ ss = OK tt ==> _`
        drule >> strip_tac >>
      (* the variables of s0 that the code does not write are kept *)
      `!x v. not_fresh_at sa x /\ FLOOKUP s0.vs_vars x = SOME v ==>
             FLOOKUP t.vs_vars x = SOME v` by
        (rpt strip_tac >>
         `FLOOKUP (drop_fresh sa s0).vs_vars x = SOME v` by
           simp[drop_fresh_def, FLOOKUP_DRESTRICT, IN_DEF] >>
         fs[vars_ext_def] >> metis_tac[FLOOKUP_SUBMAP]) >>
      `t with vs_inst_idx := LENGTH sb.cs_current_insts =
       (s0 with vs_vars := t.vs_vars) with
         vs_inst_idx := LENGTH sb.cs_current_insts` by
        (fs[vars_ext_def, drop_fresh_def] >>
         qpat_x_assum `t = _` (fn th => ONCE_REWRITE_TAC [th]) >>
         qpat_x_assum `ss' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
         simp[venom_state_component_equality]) >>
      pop_assum SUBST1_TAC >>
      simp[stmt_state_rel_inst_idx] >>
      conj_tac
      >- (irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac
          >~ [`cenv.ce_imm_alloca = SOME (Var p)`]
          >- (`not_fresh_at sa p` by
                (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
              `FLOOKUP s0.vs_vars p = SOME 0w` by
                fs[stmt_state_rel_def, immutable_base_zero_def,
                   eval_operand_def, lookup_var_def] >>
              qpat_x_assum `!x v. not_fresh_at sa x /\ _ ==> _`
                (qspecl_then [`p`, `0w`] mp_tac) >>
              fs[lookup_var_def]) >>
          fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
          first_x_assum drule_all >> strip_tac >>
          `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> res_tac) >>
          fs[lookup_var_def] >>
          qpat_x_assum `!x v. not_fresh_at sa x /\ _ ==> _` drule >> simp[]) >>
      conj_tac
      >- (`eval_operand op t = SOME w` by
            (fs[vars_ext_def] >>
             qpat_x_assum `t = _` (fn th => ONCE_REWRITE_TAC [th]) >>
             simp[eval_operand_vars_ext]) >>
          `t.vs_labels = s0.vs_labels` by
            (fs[vars_ext_def] >>
             qpat_x_assum `t = _` (fn th => ONCE_REWRITE_TAC [th]) >>
             qpat_x_assum `ss' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
             simp[drop_fresh_def]) >>
          Cases_on `op` >> fs[eval_operand_def, lookup_var_def]) >>
      conj_tac >- (rw[lookup_var_def] >> fs[lookup_var_def]) >>
      fs[vars_ext_def] >>
      qpat_x_assum `t = _` (fn th => ONCE_REWRITE_TAC [th]) >>
      qpat_x_assum `ss' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
      simp[drop_fresh_def]) >>
  disj2_tac >> qexistsl_tac [`a`, `ss'`] >> simp[]
QED

Theorem frag_exec_writes_fresh:
  !ctx func cenv cx es sa sb op w P A R s0.
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    writes_fresh sa (emitted_insts sa sb) /\ local_ptrs_reserved cenv sa /\
    (!ss. P ss ==> P (drop_fresh sa ss)) /\
    (!ss. fresh_vars_wrt sa ss /\ P ss ==>
       (?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
              eval_operand op ss' = SOME w) \/
       (?a ss'. run_inst_seq (emitted_insts sa sb) ss = Abort a ss' /\ A a)) /\
    (!a ss. A a ==> R (Abort a ss)) ==>
    frag_exec ctx sa sb
      (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\ P ss)
      (\ss. stmt_state_rel ctx func cenv cx es ss /\ eval_operand op ss = SOME w /\
            (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
                    lookup_var x ss = SOME w') /\
            (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                     FLOOKUP ss.vs_allocas aid = SOME b) /\
            ss.vs_memory = s0.vs_memory) R
Proof
  rpt strip_tac >> irule frag_exec_run_frame >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all run_inst_seq_writes_fresh >> simp[]) >>
  conj_tac >- (qexists_tac `A` >> simp[]) >>
  fs[writes_fresh_def, EVERY_MEM] >> rpt strip_tac >>
  res_tac >> imp_res_tac fresh_write_op_simple >> simp[]
QED

(* A run-level lemma by which the code always aborts, as A allows, gives a
   fragment that exits as R allows and never reaches its end. *)
Theorem frag_exec_run_abort:
  !ctx func cenv cx es sa sb P A Q R s0.
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb) /\
    (!ss. P ss ==> P (drop_fresh sa ss)) /\
    (!ss. fresh_vars_wrt sa ss /\ P ss ==>
       ?a ss'. run_inst_seq (emitted_insts sa sb) ss = Abort a ss' /\ A a) /\
    (!a ss. A a ==> R (Abort a ss)) ==>
    frag_exec ctx sa sb
      (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\ P ss) Q R
Proof
  rpt strip_tac >>
  irule frag_exec_run_inst_seq_drop_fresh >> simp[] >> rpt strip_tac >>
  `P (drop_fresh sa s0)` by res_tac >>
  assume_tac (Q.SPECL [`sa`, `s0`] fresh_vars_wrt_drop_fresh) >>
  qpat_x_assum `!ss. fresh_vars_wrt _ _ /\ _ ==> _`
    (qspec_then `drop_fresh sa s0` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  disj2_tac >> qexistsl_tac [`a`, `ss'`] >> simp[]
QED

Theorem frag_exec_writes_fresh_abort:
  !ctx func cenv cx es sa sb P A Q R s0.
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    writes_fresh sa (emitted_insts sa sb) /\
    (!ss. P ss ==> P (drop_fresh sa ss)) /\
    (!ss. fresh_vars_wrt sa ss /\ P ss ==>
       ?a ss'. run_inst_seq (emitted_insts sa sb) ss = Abort a ss' /\ A a) /\
    (!a ss. A a ==> R (Abort a ss)) ==>
    frag_exec ctx sa sb
      (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\ P ss) Q R
Proof
  rpt strip_tac >> irule frag_exec_run_abort >> simp[] >>
  conj_tac >- (qexists_tac `A` >> simp[]) >>
  fs[writes_fresh_def, EVERY_MEM] >> rpt gen_tac >> strip_tac >>
  res_tac >> imp_res_tac fresh_write_op_simple >> simp[]
QED

(* ===== Compile actions ===== *)

(* m emits, in the current block, code that writes only fresh variables. *)
Definition straight_fresh_def:
  straight_fresh (m : 'a compiler) <=>
    !st x st'. m st = (x, st') ==>
      st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
      st.cs_next_var <= st'.cs_next_var /\
      writes_fresh st (emitted_insts st st')
End

Theorem straight_fresh_return:
  !x. straight_fresh (comp_return x)
Proof
  rw[straight_fresh_def, comp_return_def, emitted_insts_refl, writes_fresh_def]
QED

Theorem straight_fresh_emit_op:
  !opc ops. fresh_write_op opc ==> straight_fresh (emit_op opc ops)
Proof
  rw[straight_fresh_def] >> imp_res_tac emit_op_extends >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac writes_fresh_emit_op >>
  fs[same_blocks_def]
QED

Theorem straight_fresh_emit_void:
  !opc ops. fresh_write_op opc ==> straight_fresh (emit_void opc ops)
Proof
  rw[straight_fresh_def] >> imp_res_tac emit_void_extends >>
  imp_res_tac emitted_insts_emit_void >>
  fs[same_blocks_def, writes_fresh_def, venomInstTheory.mk_inst_def]
QED

Theorem straight_fresh_bind:
  !mm ff. straight_fresh mm /\ (!a. straight_fresh (ff a)) ==>
          straight_fresh (comp_bind mm ff)
Proof
  rewrite_tac[straight_fresh_def, comp_bind_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> Cases_on `mm st` >> simp[] >> strip_tac >>
  rename1 `mm st = (a, mid)` >>
  qpat_x_assum `!st x st'. mm st = _ ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!a st x st'. ff a st = _ ==> _` (drule_then strip_assume_tac) >>
  `emitted_insts st st' = emitted_insts st mid ++ emitted_insts mid st'` by
    (irule emitted_insts_append >> simp[]) >>
  `writes_fresh st (emitted_insts mid st')` by
    (irule writes_fresh_mono >> qexists_tac `mid` >> simp[]) >>
  asm_rewrite_tac[writes_fresh_append] >> simp[]
QED

Theorem straight_fresh_ignore_bind:
  !mm ff. straight_fresh mm /\ straight_fresh ff ==>
          straight_fresh (comp_ignore_bind mm ff)
Proof
  rw[comp_ignore_bind_def] >> irule straight_fresh_bind >> simp[]
QED

(* frag_exec_writes_fresh for the code of a straight_fresh action. *)
Theorem frag_exec_straight_fresh:
  !ctx func cenv cx es m sa sb op w P A R s0.
    straight_fresh m /\ m sa = (op, sb) /\ local_ptrs_reserved cenv sa /\
    (!ss. P ss ==> P (drop_fresh sa ss)) /\
    (!ss. fresh_vars_wrt sa ss /\ P ss ==>
       (?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
              eval_operand op ss' = SOME w) \/
       (?a ss'. run_inst_seq (emitted_insts sa sb) ss = Abort a ss' /\ A a)) /\
    (!a ss. A a ==> R (Abort a ss)) ==>
    frag_exec ctx sa sb
      (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\ P ss)
      (\ss. stmt_state_rel ctx func cenv cx es ss /\ eval_operand op ss = SOME w /\
            (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
                    lookup_var x ss = SOME w') /\
            (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                     FLOOKUP ss.vs_allocas aid = SOME b) /\
            ss.vs_memory = s0.vs_memory) R
Proof
  rpt strip_tac >> irule frag_exec_writes_fresh >>
  qpat_x_assum `straight_fresh _` (mp_tac o REWRITE_RULE [straight_fresh_def]) >>
  disch_then drule >> strip_tac >> asm_rewrite_tac[] >>
  conj_tac >- (qexists_tac `A` >> asm_rewrite_tac[]) >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

(* frag_exec_writes_fresh_abort for the code of a straight_fresh action. *)
Theorem frag_exec_straight_fresh_abort:
  !ctx func cenv cx es m sa sb op P A Q R s0.
    straight_fresh m /\ m sa = (op, sb) /\
    (!ss. P ss ==> P (drop_fresh sa ss)) /\
    (!ss. fresh_vars_wrt sa ss /\ P ss ==>
       ?a ss'. run_inst_seq (emitted_insts sa sb) ss = Abort a ss' /\ A a) /\
    (!a ss. A a ==> R (Abort a ss)) ==>
    frag_exec ctx sa sb
      (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\ P ss) Q R
Proof
  rpt strip_tac >> irule frag_exec_writes_fresh_abort >>
  qpat_x_assum `straight_fresh _` (mp_tac o REWRITE_RULE [straight_fresh_def]) >>
  disch_then drule >> strip_tac >> asm_rewrite_tac[] >>
  conj_tac >- (qexists_tac `A` >> asm_rewrite_tac[]) >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED
