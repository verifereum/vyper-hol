(*
 * Module Lowering Properties
 *
 * TOP-LEVEL:
 *   compile_selector_dispatch_linear_correct — linear dispatch reaches the
 *     block linear_dispatch_target picks for the calldata (run_from)
 *   compile_entry_checks_correct — nonpayable/calldatasize checks (single-block)
 *   compile_entry_checks_nonpayable_revert — nonpayable revert (derived)
 *   compile_constructor_epilogue_correct — runtime code copy + RETURN (single-block)
 *
 * Helper (no standalone correctness — always composed):
 *   compile_decode_args_nil   — empty arg list is no-op
 *   compile_init_kwargs_nil   — empty kwargs list is no-op
 *
 * Source: module.py (VenomModuleCompiler)
 * Lowering: moduleLoweringScript.sml
 *
 * NOTE on execution models:
 *   - Linear selector dispatch jumps to labels it does not emit (fn
 *     bodies, fallback), so it is stated with run_from in any function
 *     containing its code (fn_has_code): runs_through.
 *   - Entry checks and constructor epilogue stay within a single block,
 *     so they use the simpler run_inst_seq/emitted_insts pattern.
 *   - compile_decode_args and compile_init_kwargs are fragments (no terminator)
 *     always composed within a larger compilation. No standalone theorem;
 *     theorems here cover only their empty-input cases.
 *)

Theory moduleLoweringProps
Ancestors
  stmtLoweringProps
  emitHelperProps
  exprLoweringProps
  moduleLowering compileEnv context
  venomExecSemantics venomState venomInst venomExecProofs
  stateEquiv
  abiEncoder
  fragExec selectorDispatch byte vyperMisc list rich_list finite_map words
Libs
  wordsLib

(* ===== Selector Dispatch =====

   Linear dispatch ends in jumps to labels it does not emit: the function
   bodies and the fallback.  The fragment judgment frag_exec ends at the
   point where the code leaves off, so the dispatch is stated with run_from
   directly: execution reaches the start of the block the source picks for
   the calldata, and every result from there is a result from the start. *)

(* Every non-Error result of running fn from tt is a result from ss. *)
Definition runs_through_def:
  runs_through ctx fn ss tt <=>
    !fuel r. run_from fuel ctx fn tt = r /\ (!e. r <> Error e) ==>
             ?fuel'. run_from fuel' ctx fn ss = r
End

(* tt differs from ss only in its variables and its position. *)
Definition vars_pc_only_def:
  vars_pc_only ss tt <=>
    tt with <| vs_vars := ss.vs_vars; vs_prev_bb := ss.vs_prev_bb;
               vs_current_bb := ss.vs_current_bb;
               vs_inst_idx := ss.vs_inst_idx |> = ss
End

(* The label of the first selector that the method id m equals. *)
Definition selector_hit_def:
  selector_hit (m : bytes32) [] = NONE /\
  selector_hit m ((sel : num, lbl : string)::rest) =
    if m = n2w sel then SOME lbl else selector_hit m rest
End

(* The block linear dispatch picks for calldata cd: the label of the first
   selector the calldata hits, else the fallback. *)
Definition linear_dispatch_target_def:
  linear_dispatch_target cd [] fb = fb /\
  linear_dispatch_target cd ((sel : num, lbl : string)::rest) fb =
    if calldata_hits_selector cd sel then lbl
    else linear_dispatch_target cd rest fb
End

Theorem runs_through_refl:
  !ctx fn ss. runs_through ctx fn ss ss
Proof
  rw[runs_through_def] >> metis_tac[]
QED

Theorem runs_through_trans:
  !ctx fn ss tt uu.
    runs_through ctx fn ss tt /\ runs_through ctx fn tt uu ==>
    runs_through ctx fn ss uu
Proof
  rw[runs_through_def] >> metis_tac[]
QED

Theorem vars_pc_only_refl:
  !ss. vars_pc_only ss ss
Proof
  rw[vars_pc_only_def, venom_state_component_equality]
QED

Theorem vars_pc_only_trans:
  !ss tt uu. vars_pc_only ss tt /\ vars_pc_only tt uu ==> vars_pc_only ss uu
Proof
  rw[vars_pc_only_def, venom_state_component_equality] >> gvs[]
QED

Theorem vars_pc_only_update_var:
  !ss tt x w. vars_pc_only ss tt ==> vars_pc_only ss (update_var x w tt)
Proof
  rw[vars_pc_only_def, venom_state_component_equality, update_var_def] >>
  gvs[]
QED

Theorem vars_pc_only_jump_to:
  !ss tt l. vars_pc_only ss tt ==> vars_pc_only ss (jump_to l tt)
Proof
  rw[vars_pc_only_def, venom_state_component_equality, jump_to_def] >> gvs[]
QED

Theorem vars_pc_only_inst_idx:
  !ss tt n. vars_pc_only ss tt ==> vars_pc_only ss (tt with vs_inst_idx := n)
Proof
  rw[vars_pc_only_def, venom_state_component_equality] >> gvs[]
QED

Theorem vars_pc_only_fields:
  !ss tt. vars_pc_only ss tt ==>
    tt.vs_call_ctx = ss.vs_call_ctx /\ tt.vs_halted = ss.vs_halted /\
    tt.vs_labels = ss.vs_labels
Proof
  rw[vars_pc_only_def] >> pop_assum (SUBST1_TAC o SYM) >> simp[]
QED

(* A jump or a move of the instruction index reads and writes no variable. *)
Theorem control_moves_keep_vars:
  !l n ss st op x.
    eval_operand op (jump_to l ss) = eval_operand op ss /\
    eval_operand op (ss with vs_inst_idx := n) = eval_operand op ss /\
    lookup_var x (jump_to l ss) = lookup_var x ss /\
    lookup_var x (ss with vs_inst_idx := n) = lookup_var x ss /\
    (fresh_vars_wrt st (jump_to l ss) <=> fresh_vars_wrt st ss) /\
    (fresh_vars_wrt st (ss with vs_inst_idx := n) <=> fresh_vars_wrt st ss) /\
    (jump_to l ss).vs_halted = ss.vs_halted
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, jump_to_def, fresh_vars_wrt_def]
QED

Theorem lookup_var_update_not_fresh:
  !st x n w ss.
    not_fresh_at st x /\ st.cs_next_var <= n ==>
    lookup_var x (update_var (STRING #"%" (toString n)) w ss) =
    lookup_var x ss
Proof
  rw[lookup_var_def, update_var_def, FLOOKUP_UPDATE, not_fresh_at_def] >>
  metis_tac[]
QED

Theorem run_from_step_runs_through:
  !ctx fn ss bb inst s1 n.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb ss.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    step_inst_base inst ss = OK s1 /\ n = SUC ss.vs_inst_idx ==>
    runs_through ctx fn ss (s1 with vs_inst_idx := n)
Proof
  rw[runs_through_def] >> metis_tac[run_from_step]
QED

Theorem run_from_jump_runs_through:
  !ctx fn ss bb inst lbl.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb ss.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst ss = OK (jump_to lbl ss) /\ ~ss.vs_halted ==>
    runs_through ctx fn ss (jump_to lbl ss)
Proof
  rw[runs_through_def] >> metis_tac[run_from_jump_result]
QED

Theorem step_CALLDATASIZE:
  !id out ss.
    step_inst_base (mk_inst id CALLDATASIZE [] [out]) ss =
    OK (update_var out (n2w (LENGTH ss.vs_call_ctx.cc_calldata)) ss)
Proof
  rw[step_inst_base_def, exec_read0_def, mk_inst_def]
QED

Theorem compile_selector_checks_appends:
  !mid sels. cs_appends (compile_selector_checks mid sels)
Proof
  gen_tac >> Induct >- simp[compile_selector_checks_def, cs_appends_return] >>
  Cases >> simp[compile_selector_checks_def] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[cs_appends_prims, cs_appends_emit_helpers]) >>
  rw[cs_appends_prims, cs_appends_emit_helpers]
QED

Theorem compile_selector_checks_next_var:
  !mid sels st x st'.
    compile_selector_checks mid sels st = (x, st') ==>
    st.cs_next_var <= st'.cs_next_var
Proof
  gen_tac >> Induct >- simp[compile_selector_checks_def, comp_return_def] >>
  Cases >> simp[compile_selector_checks_def, comp_bind_def,
    comp_ignore_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_inst_extends >>
  imp_res_tac fresh_label_props >>
  gvs[new_block_def] >> first_x_assum drule >> simp[]
QED

(* ----- The method id: CALLDATALOAD 0 shifted right by 224 ----- *)

Theorem num_of_bytes_lt:
  !bs:word8 list. num_of_bytes bs < 256 ** LENGTH bs
Proof
  Induct >> simp[num_of_bytes_def, arithmeticTheory.EXP] >> rpt strip_tac >>
  `w2n h < 256` by (assume_tac (INST_TYPE [alpha |-> ``:8``] w2n_lt) >> fs[]) >>
  `num_of_bytes bs + 1 <= 256 ** LENGTH bs` by simp[] >>
  `256 * (num_of_bytes bs + 1) <= 256 * 256 ** LENGTH bs` by simp[] >> fs[]
QED

Theorem n2w_shr_224:
  !N q. N < 2 ** 224 /\ q < 2 ** 32 ==>
        (n2w (N + 2 ** 224 * q) : bytes32) >>> 224 = n2w q
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC[GSYM w2n_11] >>
  REWRITE_TAC[w2n_lsr, w2n_n2w] >> simp[dimword_def] >>
  `2 ** 224 * q <= 2 ** 224 * (2 ** 32 - 1)` by fs[] >>
  `N + 2 ** 224 * q < 2 ** 256` by fs[] >>
  `q < 2 ** 256` by fs[] >> fs[arithmeticTheory.LESS_MOD] >>
  irule arithmeticTheory.DIV_UNIQUE >> qexists_tac `N` >> fs[]
QED

(* The word CALLDATALOAD 0 reads, shifted right by 224, is the method id. *)
Theorem calldataload_0_shr_224:
  !cd:word8 list. 4 <= LENGTH cd ==>
    word_of_bytes T (0w:bytes32) (TAKE 32 (cd ++ REPLICATE 32 0w)) >>> 224 =
    calldata_method_id cd
Proof
  Cases >- simp[] >> rename1 `a::t1` >> Cases_on `t1` >- simp[] >>
  rename1 `a::b::t2` >> Cases_on `t2` >- simp[] >>
  rename1 `a::b::c::t3` >> Cases_on `t3` >- simp[] >>
  rename1 `a::b::c::d::rest` >> strip_tac >>
  `LENGTH (TAKE 28 (rest ++ REPLICATE 32 (0w:word8))) = 28` by
    simp[LENGTH_TAKE_EQ] >>
  simp[word_of_bytes_T_0w_256, be_bytes_thm, calldata_method_id_def,
       TAKE_APPEND1, TAKE_TAKE, num_of_bytes_APPEND, num_of_bytes_def] >>
  qspecl_then [`num_of_bytes (REVERSE (TAKE 28 (rest ++ REPLICATE 32 0w)))`,
               `16777216 * w2n a + (65536 * w2n b + (256 * w2n c + w2n d))`]
    mp_tac n2w_shr_224 >>
  simp[arithmeticTheory.LEFT_ADD_DISTRIB] >> disch_then irule >>
  `!x:word8. w2n x < 256` by
    (gen_tac >> assume_tac (INST_TYPE [alpha |-> ``:8``] w2n_lt) >> fs[]) >>
  qspec_then `REVERSE (TAKE 28 (rest ++ REPLICATE 32 0w))` mp_tac
    num_of_bytes_lt >>
  asm_simp_tac std_ss [LENGTH_REVERSE] >> simp[] >> disch_then kall_tac >>
  first_assum (qspec_then `a` assume_tac) >>
  first_assum (qspec_then `b` assume_tac) >>
  first_assum (qspec_then `c` assume_tac) >>
  first_x_assum (qspec_then `d` assume_tac) >> fs[]
QED

(* Calldata shorter than a selector hits none. *)
Theorem linear_dispatch_target_short:
  !sels cd fb. LENGTH cd < 4 ==> linear_dispatch_target cd sels fb = fb
Proof
  Induct >- simp[linear_dispatch_target_def] >> Cases >>
  simp[linear_dispatch_target_def, calldata_hits_selector_def]
QED

(* For 4-byte selectors, hitting one is the method id equal to it. *)
Theorem linear_dispatch_target_selector_hit:
  !sels cd fb.
    4 <= LENGTH cd /\ EVERY (\(sel, lbl). sel < 2 ** 32) sels ==>
    linear_dispatch_target cd sels fb =
    case selector_hit (calldata_method_id cd) sels of
      SOME l => l
    | NONE => fb
Proof
  Induct >- simp[linear_dispatch_target_def, selector_hit_def] >> Cases >>
  rename1 `(sel, lbl)` >>
  rw[linear_dispatch_target_def, selector_hit_def,
     calldata_hits_selector_def] >>
  gvs[] >> `sel < dimword (:256)` by fs[dimword_def] >> gvs[] >>
  metis_tac[n2w_w2n]
QED

(* ----- The selector checks ----- *)

(* From the start of the checks with the method id m in mid, execution
   reaches the label of the first selector equal to m, or else the end of
   the checks. *)
Theorem compile_selector_checks_correct:
  !sels mid st st'. compile_selector_checks mid sels st = ((), st') ==>
     !ctx fn ss m.
       fn_has_code st st' fn /\ eval_operand mid ss = SOME m /\
       fresh_vars_wrt st ss /\ ~ss.vs_halted /\
       ss.vs_current_bb = st.cs_current_bb /\
       ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
       ?tt. runs_through ctx fn ss tt /\ vars_pc_only ss tt /\ fresh_vars_wrt
         st' tt /\
           (!x. not_fresh_at st x ==> lookup_var x tt = lookup_var x ss) /\
           case selector_hit m sels of
             SOME lbl => tt.vs_current_bb = lbl /\ tt.vs_inst_idx = 0
           | NONE => tt.vs_current_bb = st'.cs_current_bb /\
                     tt.vs_inst_idx = LENGTH st'.cs_current_insts
Proof
  (Induct >- (simp[compile_selector_checks_def, comp_return_def,
    selector_hit_def] >> rpt strip_tac >> qexists_tac `ss`
    >> simp[runs_through_refl, vars_pc_only_refl])) >>
    (Cases >> rename1 `(sel, lbl)` >> rpt gen_tac
      >> simp[compile_selector_checks_def, comp_bind_def, comp_ignore_bind_def]
      >> rpt (pairarg_tac >> fs[]) >> strip_tac >> rpt gen_tac >> strip_tac) >>
    (rename1 `new_block next_lbl s6 = (_, s7)`
      >> rename1 `emit_inst JMP _ _ s5 = (_, s6)`
      >> rename1 `new_block match_lbl s4 = (_, s5)`
      >> rename1 `emit_inst JNZ _ _ s3 = (_, s4)`
      >> rename1 `fresh_label "next" s2 = (_, s3)`
      >> rename1 `fresh_label "match" s1 = (_, s2)`
      >> rename1 `emit_op EQ _ st = (_, s1)`) >>
    (`cs_extends st s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\ cs_extends s3
      s4 /\ cs_extends s4 s5 /\ cs_extends s5 s6 /\ cs_extends s6 s7 /\
      cs_extends s7 st'` by (rpt conj_tac
      >> metis_tac[cs_appends_def, cs_appends_emit_helpers, cs_appends_prims,
      compile_selector_checks_appends])) >>
    (`fn_has_code s4 s5 fn /\ fn_has_code s6 s7 fn /\ fn_has_code s7 st' fn` by
      (rpt conj_tac
      >> metis_tac[fn_has_code_mid, fn_has_code_split, cs_extends_trans])) >>
    (`lookup_block s4.cs_current_bb fn.fn_blocks = SOME <| bb_label :=
      s4.cs_current_bb; bb_instructions := s4.cs_current_insts |> /\
      lookup_block s6.cs_current_bb fn.fn_blocks = SOME <| bb_label :=
      s6.cs_current_bb; bb_instructions := s6.cs_current_insts |>` by
      metis_tac[fn_has_code_new_block]) >>
    (qpat_x_assum `new_block match_lbl _ = _` (strip_assume_tac o SIMP_RULE
      (srw_ss()) [new_block_def, LET_THM])
      >> qpat_x_assum `new_block next_lbl _ = _` (strip_assume_tac o SIMP_RULE
      (srw_ss()) [new_block_def, LET_THM]) >> qpat_x_assum `_ = _0` kall_tac
      >> qpat_x_assum `_ = _0'` kall_tac
      >> qpat_x_assum `_ = s5` (SUBST_ALL_TAC o SYM)
      >> `s7.cs_current_bb = next_lbl /\ s7.cs_current_insts = [] /\
      s7.cs_next_var = s6.cs_next_var /\ s7.cs_blocks = <| bb_label :=
      s6.cs_current_bb; bb_instructions := s6.cs_current_insts |> ::
      s6.cs_blocks` by (qpat_x_assum `_ = s7` (SUBST1_TAC o SYM) >> simp[])
      >> qpat_x_assum `_ = s7` kall_tac) >>
    (imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends
      >> imp_res_tac emit_inst_extends >> imp_res_tac fresh_label_props
      >> fs[same_blocks_def]) >>
    (`st.cs_next_var + 1 <= st'.cs_next_var` by (imp_res_tac
      compile_selector_checks_next_var >> gvs[])) >>
    (qmatch_asmsub_abbrev_tac `lookup_block st.cs_current_bb fn.fn_blocks = SOME
      blk`) >>
    (`get_instruction blk (LENGTH st.cs_current_insts) = SOME (mk_inst
      st.cs_next_id EQ [mid; Lit (n2w sel)] [STRING #"%" (toString
      st.cs_next_var)]) /\ get_instruction blk (SUC (LENGTH
      st.cs_current_insts)) = SOME (mk_inst (st.cs_next_id + 1) JNZ [Var (STRING
      #"%" (toString st.cs_next_var)); Label match_lbl; Label next_lbl] [])` by
      simp[Abbr `blk`, get_instruction_def, EL_APPEND_EQN,
      arithmeticTheory.ADD1]) >>
    (`runs_through ctx fn ss (update_var (STRING #"%" (toString st.cs_next_var))
      (bool_to_word (m = n2w sel)) ss with vs_inst_idx := SUC ss.vs_inst_idx)`
      by (irule run_from_step_runs_through >> conj_tac >- simp[]
      >> qexists_tac `blk` >> fs[mk_inst_def, is_terminator_def]
      >> irule (SIMP_RULE std_ss [mk_inst_def] step_EQ)
      >> simp[eval_operand_def])) >>
    (qabbrev_tac `u1 = update_var (STRING #"%" (toString st.cs_next_var))
      (bool_to_word (m = n2w sel)) ss with vs_inst_idx := SUC ss.vs_inst_idx`)
      >>
    (`step_inst_base (mk_inst (st.cs_next_id + 1) JNZ [Var (STRING #"%"
      (toString st.cs_next_var)); Label match_lbl; Label next_lbl] []) u1 = if m
      = n2w sel then OK (jump_to match_lbl u1) else OK (jump_to next_lbl u1)` by
      (`eval_operand (Var (STRING #"%" (toString st.cs_next_var))) u1 = SOME
      (bool_to_word (m = n2w sel))` by simp[Abbr `u1`, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> drule step_jnz_behavior
      >> simp[mk_inst_def] >> Cases_on `m = n2w sel` >> simp[bool_to_word_def]))
      >>
    (`u1.vs_current_bb = st.cs_current_bb /\ u1.vs_inst_idx = SUC (LENGTH
      st.cs_current_insts) /\ ~u1.vs_halted /\ vars_pc_only ss u1 /\
      fresh_vars_wrt s7 u1 /\ (!x. not_fresh_at st x ==> lookup_var x u1 =
      lookup_var x ss) /\ eval_operand mid u1 = SOME m` by (simp[Abbr `u1`,
      control_moves_keep_vars] >> rpt conj_tac >> TRY (fs[update_var_def]
      >> NO_TAC) >> TRY (metis_tac[vars_pc_only_inst_idx,
      vars_pc_only_update_var, vars_pc_only_refl] >> NO_TAC)
      >> TRY (irule fresh_vars_wrt_advance
      >> qexistsl_tac [`st.cs_next_var`, `st`] >> fs[] >> NO_TAC)
      >> TRY (rw[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
      >> fs[not_fresh_at_def] >> NO_TAC) >> irule eval_operand_update_fresh
      >> conj_tac >- first_assum ACCEPT_TAC
      >> qexistsl_tac [`st.cs_next_var`, `st`] >> fs[])) >>
    (`runs_through ctx fn u1 (jump_to (if m = n2w sel then match_lbl else
      next_lbl) u1)` by (irule run_from_jump_runs_through >> fs[]
      >> rw[is_terminator_def])) >>
    (`s7.cs_next_var <= st'.cs_next_var` by (imp_res_tac
      compile_selector_checks_next_var >> fs[])) >>
    (Cases_on `m = n2w sel` >> fs[selector_hit_def])
    >- (`runs_through ctx fn (jump_to match_lbl u1) (jump_to lbl (jump_to
      match_lbl u1))` by (irule run_from_jump_runs_through
      >> simp[control_moves_keep_vars] >> fs[]
      >> simp[jump_to_def, get_instruction_def, mk_inst_def, is_terminator_def,
      step_jmp_behavior]) >>
        qexists_tac `jump_to lbl (jump_to match_lbl u1)`
          >> simp[control_moves_keep_vars] >> rpt conj_tac
        >- (metis_tac[runs_through_trans])
        >- (metis_tac[vars_pc_only_jump_to])
        >- (irule fresh_vars_wrt_mono >> qexists_tac `s7` >> fs[])
        >- (simp[jump_to_def])
        >> simp[jump_to_def])
    >> (first_x_assum (drule_then (qspecl_then [`ctx`, `fn`, `jump_to next_lbl
      u1`, `m`] mp_tac)) >> impl_tac >- (simp[control_moves_keep_vars]
      >> simp[jump_to_def])) >>
    (strip_tac >> qexists_tac `tt` >> rpt conj_tac)
    >- (metis_tac[runs_through_trans])
    >- (metis_tac[vars_pc_only_trans, vars_pc_only_jump_to])
    >- (fs[])
    >- (rpt strip_tac >> `not_fresh_at s7 x` by fs[not_fresh_at_def]
      >> fs[control_moves_keep_vars])
    >> fs[]
QED

(* Linear dispatch: from the start of the dispatch code, execution reaches
   the start of the block linear_dispatch_target picks for the calldata,
   changing only fresh variables.  Every non-Error result from there is a
   result from the start. *)
Theorem compile_selector_dispatch_linear_correct:
  !selectors fallback_lbl st st' ctx fn ss.
      compile_selector_dispatch_linear selectors fallback_lbl st = ((), st') /\
      fn_has_code st st' fn /\
      EVERY (\(sel, lbl). sel < 2 ** 32) selectors /\
      LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256) /\
      fresh_vars_wrt st ss /\ ~ss.vs_halted /\
      ss.vs_current_bb = st.cs_current_bb /\
      ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
      ?tt. runs_through ctx fn ss tt /\ vars_pc_only ss tt /\
           fresh_vars_wrt st' tt /\
           (!x. not_fresh_at st x ==> lookup_var x tt = lookup_var x ss) /\
           tt.vs_current_bb =
             linear_dispatch_target ss.vs_call_ctx.cc_calldata selectors
               fallback_lbl /\
           tt.vs_inst_idx = 0
Proof
  (rpt gen_tac >> strip_tac
    >> qpat_x_assum `compile_selector_dispatch_linear _ _ _ = _` mp_tac
    >> simp[compile_selector_dispatch_linear_def, comp_bind_def,
    comp_ignore_bind_def] >> rpt (pairarg_tac >> fs[]) >> strip_tac) >>
    (rename1 `emit_inst JMP _ _ a9 = (_, st')`
      >> rename1 `compile_selector_checks _ _ a8 = (_, a9)`
      >> rename1 `emit_op SHR _ a7 = (_, a8)`
      >> rename1 `emit_op CALLDATALOAD _ a6 = (_, a7)`
      >> rename1 `new_block dispatch_lbl a5 = (_, a6)`
      >> rename1 `emit_inst JNZ _ _ a4 = (_, a5)`
      >> rename1 `fresh_label "dispatch" a3 = (_, a4)`
      >> rename1 `emit_op ISZERO _ a2 = (_, a3)`
      >> rename1 `emit_op LT _ a1 = (_, a2)`
      >> rename1 `emit_op CALLDATASIZE _ st = (_, a1)`) >>
    (`cs_extends st a1 /\ cs_extends a1 a2 /\ cs_extends a2 a3 /\ cs_extends a3
      a4 /\ cs_extends a4 a5 /\ cs_extends a5 a6 /\ cs_extends a6 a7 /\
      cs_extends a7 a8 /\ cs_extends a8 a9 /\ cs_extends a9 st'` by (rpt
      conj_tac >> metis_tac[cs_appends_def, cs_appends_emit_helpers,
      cs_appends_prims, compile_selector_checks_appends])) >>
    (`fn_has_code a5 a6 fn /\ fn_has_code a6 a8 fn /\ fn_has_code a8 a9 fn /\
      fn_has_code a9 st' fn` by (rpt conj_tac
      >> metis_tac[fn_has_code_mid, fn_has_code_split, cs_extends_trans])) >>
    (`lookup_block a5.cs_current_bb fn.fn_blocks = SOME <| bb_label :=
      a5.cs_current_bb; bb_instructions := a5.cs_current_insts |>` by
      metis_tac[fn_has_code_new_block]) >>
    (qpat_x_assum `new_block dispatch_lbl _ = _` (strip_assume_tac o SIMP_RULE
      (srw_ss()) [new_block_def, LET_THM]) >> qpat_x_assum `_ = _0` kall_tac
      >> `a6.cs_current_bb = dispatch_lbl /\ a6.cs_current_insts = [] /\
      a6.cs_next_var = a5.cs_next_var /\ a6.cs_next_id = a5.cs_next_id` by
      (qpat_x_assum `_ = a6` (SUBST1_TAC o SYM) >> simp[])
      >> qpat_x_assum `_ = a6` kall_tac) >>
    (`a8.cs_next_var <= a9.cs_next_var` by
      metis_tac[compile_selector_checks_next_var]) >>
    (imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends
      >> imp_res_tac emit_inst_extends >> imp_res_tac fresh_label_props
      >> fs[same_blocks_def]) >>
    (qspecl_then [`a6`, `a8`, `fn`, `emitted_insts a6 a7 ++ emitted_insts a7
      a8`] mp_tac fn_has_code_same_block >> impl_tac >- fs[] >> strip_tac
      >> rename1 `lookup_block a6.cs_current_bb fn.fn_blocks = SOME bb2`
      >> first_assum (qspec_then `0` mp_tac)
      >> first_x_assum (qspec_then `1` mp_tac) >> simp[]) >>
    (rpt strip_tac) >>
    (qspecl_then [`a9`, `st'`, `fn`, `[mk_inst a9.cs_next_id JMP [Label
      fallback_lbl] []]`] mp_tac fn_has_code_same_block >> impl_tac >- fs[]
      >> strip_tac
      >> rename1 `lookup_block a9.cs_current_bb fn.fn_blocks = SOME bb3`
      >> first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac) >>
    (qmatch_asmsub_abbrev_tac `lookup_block st.cs_current_bb fn.fn_blocks = SOME
      blk`) >>
    (`get_instruction blk (LENGTH st.cs_current_insts) = SOME (mk_inst
      st.cs_next_id CALLDATASIZE [] [STRING #"%" (toString st.cs_next_var)]) /\
          get_instruction blk (SUC (LENGTH st.cs_current_insts)) = SOME (mk_inst
            (st.cs_next_id + 1) LT [Var (STRING #"%" (toString st.cs_next_var));
            Lit 4w] [STRING #"%" (toString (st.cs_next_var + 1))]) /\
          get_instruction blk (SUC (SUC (LENGTH st.cs_current_insts))) = SOME
            (mk_inst (st.cs_next_id + 2) ISZERO [Var (STRING #"%" (toString
            (st.cs_next_var + 1)))] [STRING #"%" (toString (st.cs_next_var +
            2))]) /\
          get_instruction blk (SUC (SUC (SUC (LENGTH st.cs_current_insts)))) =
            SOME (mk_inst (st.cs_next_id + 3) JNZ [Var (STRING #"%" (toString
            (st.cs_next_var + 2))); Label dispatch_lbl; Label fallback_lbl] [])`
            by simp[Abbr `blk`, get_instruction_def, EL_APPEND_EQN,
            arithmeticTheory.ADD1]) >>
    (qabbrev_tac `cd = ss.vs_call_ctx.cc_calldata`) >>
    (qabbrev_tac `u1 = update_var (STRING #"%" (toString st.cs_next_var)) (n2w
      (LENGTH cd)) ss with vs_inst_idx := SUC ss.vs_inst_idx`) >>
    (`runs_through ctx fn ss u1` by (simp[Abbr `u1`]
      >> irule run_from_step_runs_through >> fs[]
      >> fs[step_CALLDATASIZE, Abbr `cd`]
      >> simp[mk_inst_def, is_terminator_def])) >>
    (`u1.vs_current_bb = st.cs_current_bb /\ u1.vs_inst_idx = SUC (LENGTH
      st.cs_current_insts) /\ eval_operand (Var (STRING #"%" (toString
      st.cs_next_var))) u1 = SOME (n2w (LENGTH cd)) /\ vars_pc_only ss u1 /\
      fresh_vars_wrt (st with cs_next_var := st.cs_next_var + 1) u1 /\ (!x.
      not_fresh_at st x ==> lookup_var x u1 = lookup_var x ss) /\ ~u1.vs_halted`
      by (simp[Abbr `u1`, control_moves_keep_vars] >> rpt conj_tac
      >> TRY (fs[update_var_def] >> NO_TAC)
      >> TRY (simp[eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE] >> NO_TAC)
      >> TRY (metis_tac[vars_pc_only_inst_idx, vars_pc_only_update_var,
      vars_pc_only_refl] >> NO_TAC) >> TRY (irule fresh_vars_wrt_advance
      >> qexistsl_tac [`st.cs_next_var`, `st`] >> fs[] >> NO_TAC)
      >> rw[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
      >> fs[not_fresh_at_def])) >>
    (qabbrev_tac `u2 = update_var (STRING #"%" (toString (st.cs_next_var + 1)))
      (bool_to_word (LENGTH cd < 4)) u1 with vs_inst_idx := SUC u1.vs_inst_idx`)
      >>
    (`runs_through ctx fn u1 u2` by (simp[Abbr `u2`]
      >> irule run_from_step_runs_through >> fs[is_terminator_def]
      >> `bool_to_word (LENGTH cd < 4) = bool_to_word (w2n (n2w (LENGTH cd) :
      bytes32) < w2n (4w : bytes32))` by fs[Abbr `cd`] >> pop_assum SUBST1_TAC
      >> irule step_LT >> fs[eval_operand_def])) >>
    (`u2.vs_current_bb = st.cs_current_bb /\ u2.vs_inst_idx = SUC (SUC (LENGTH
      st.cs_current_insts)) /\ eval_operand (Var (STRING #"%" (toString
      (st.cs_next_var + 1)))) u2 = SOME (bool_to_word (LENGTH cd < 4)) /\
      vars_pc_only ss u2 /\ fresh_vars_wrt (st with cs_next_var :=
      st.cs_next_var + 2) u2 /\ (!x. not_fresh_at st x ==> lookup_var x u2 =
      lookup_var x ss) /\ ~u2.vs_halted` by (simp[Abbr `u2`,
      control_moves_keep_vars] >> rpt conj_tac >> TRY (fs[update_var_def]
      >> NO_TAC) >> TRY (simp[eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE] >> NO_TAC) >> TRY (irule vars_pc_only_inst_idx
      >> irule vars_pc_only_update_var >> fs[] >> NO_TAC)
      >> TRY (irule fresh_vars_wrt_advance
      >> qexistsl_tac [`st.cs_next_var + 1`, `st with cs_next_var :=
      st.cs_next_var + 1`] >> simp[] >> NO_TAC) >> rpt strip_tac
      >> `lookup_var x (update_var (STRING #"%" (toString (st.cs_next_var + 1)))
      (bool_to_word (LENGTH cd < 4)) u1) = lookup_var x u1` by (irule
      lookup_var_update_not_fresh >> qexists_tac `st` >> simp[]) >> fs[])) >>
    (qabbrev_tac `u3 = update_var (STRING #"%" (toString (st.cs_next_var + 2)))
      (bool_to_word (4 <= LENGTH cd)) u2 with vs_inst_idx := SUC
      u2.vs_inst_idx`) >>
    (`runs_through ctx fn u2 u3` by (simp[Abbr `u3`]
      >> irule run_from_step_runs_through >> fs[is_terminator_def]
      >> `bool_to_word (4 <= LENGTH cd) = bool_to_word (bool_to_word (LENGTH cd
      < 4) = 0w)` by (Cases_on `LENGTH cd < 4` >> simp[bool_to_word_def])
      >> pop_assum SUBST1_TAC >> irule step_ISZERO >> fs[])) >>
    (`u3.vs_current_bb = st.cs_current_bb /\ u3.vs_inst_idx = SUC (SUC (SUC
      (LENGTH st.cs_current_insts))) /\ eval_operand (Var (STRING #"%" (toString
      (st.cs_next_var + 2)))) u3 = SOME (bool_to_word (4 <= LENGTH cd)) /\
      vars_pc_only ss u3 /\ fresh_vars_wrt (st with cs_next_var :=
      st.cs_next_var + 3) u3 /\ (!x. not_fresh_at st x ==> lookup_var x u3 =
      lookup_var x ss) /\ ~u3.vs_halted` by (simp[Abbr `u3`,
      control_moves_keep_vars] >> rpt conj_tac >> TRY (fs[update_var_def]
      >> NO_TAC) >> TRY (simp[eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE] >> NO_TAC) >> TRY (irule vars_pc_only_inst_idx
      >> irule vars_pc_only_update_var >> fs[] >> NO_TAC)
      >> TRY (irule fresh_vars_wrt_advance
      >> qexistsl_tac [`st.cs_next_var + 2`, `st with cs_next_var :=
      st.cs_next_var + 2`] >> simp[] >> NO_TAC) >> rpt strip_tac
      >> `lookup_var x (update_var (STRING #"%" (toString (st.cs_next_var + 2)))
      (bool_to_word (4 <= LENGTH cd)) u2) = lookup_var x u2` by (irule
      lookup_var_update_not_fresh >> qexists_tac `st` >> simp[]) >> fs[])) >>
    (`step_inst_base (mk_inst (st.cs_next_id + 3) JNZ [Var (STRING #"%"
      (toString (st.cs_next_var + 2))); Label dispatch_lbl; Label fallback_lbl]
      []) u3 = if 4 <= LENGTH cd then OK (jump_to dispatch_lbl u3) else OK
      (jump_to fallback_lbl u3)` by (qspecl_then [`u3`, `Var (STRING #"%"
      (toString (st.cs_next_var + 2)))`, `dispatch_lbl`, `fallback_lbl`,
      `st.cs_next_id + 3`, `bool_to_word (4 <= LENGTH cd)`] mp_tac
      step_jnz_behavior >> impl_tac >- fs[] >> simp[mk_inst_def]
      >> Cases_on `4 <= LENGTH cd` >> simp[bool_to_word_def])) >>
    (`runs_through ctx fn u3 (jump_to (if 4 <= LENGTH cd then dispatch_lbl else
      fallback_lbl) u3)` by (irule run_from_jump_runs_through >> fs[]
      >> rw[is_terminator_def])) >>
    (`st.cs_next_var + 5 <= st'.cs_next_var` by fs[]) >>
    (Cases_on `4 <= LENGTH cd` >> fs[])
    >- ((`u3.vs_call_ctx.cc_calldata = cd /\ (jump_to dispatch_lbl
      u3).vs_current_bb = a6.cs_current_bb /\ (jump_to dispatch_lbl
      u3).vs_inst_idx = 0` by (imp_res_tac vars_pc_only_fields
      >> fs[Abbr `cd`, jump_to_def])) >>
    (qabbrev_tac `u5 = update_var (STRING #"%" (toString (st.cs_next_var + 3)))
      (word_of_bytes T (0w:bytes32) (TAKE 32 (DROP 0 cd ++ REPLICATE 32 0w)))
      (jump_to dispatch_lbl u3) with vs_inst_idx := 1`) >>
    (`runs_through ctx fn (jump_to dispatch_lbl u3) u5` by (simp[Abbr `u5`]
      >> irule run_from_step_runs_through >> conj_tac >- fs[]
      >> qexistsl_tac [`bb2`, `mk_inst (st.cs_next_id + 4) CALLDATALOAD [Lit 0w]
      [STRING #"%" (toString (st.cs_next_var + 3))]`] >> fs[] >> rpt conj_tac
      >- simp[is_terminator_def]
      >- (simp[step_inst_base_def, mk_inst_def, exec_read1_def,
      eval_operand_def] >> fs[jump_to_def]) >> metis_tac[])) >>
    (`u5.vs_current_bb = a6.cs_current_bb /\ u5.vs_inst_idx = 1 /\ eval_operand
      (Var (STRING #"%" (toString (st.cs_next_var + 3)))) u5 = SOME
      (word_of_bytes T (0w:bytes32) (TAKE 32 (DROP 0 cd ++ REPLICATE 32 0w))) /\
      vars_pc_only ss u5 /\ fresh_vars_wrt (st with cs_next_var :=
      st.cs_next_var + 4) u5 /\ (!x. not_fresh_at st x ==> lookup_var x u5 =
      lookup_var x ss) /\ ~u5.vs_halted` by (simp[Abbr `u5`,
      control_moves_keep_vars] >> rpt conj_tac
      >> TRY (fs[update_var_def, jump_to_def] >> NO_TAC)
      >> TRY (simp[eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE] >> NO_TAC) >> TRY (irule vars_pc_only_inst_idx
      >> irule vars_pc_only_update_var >> irule vars_pc_only_jump_to >> fs[]
      >> NO_TAC) >> TRY (irule fresh_vars_wrt_advance
      >> qexistsl_tac [`st.cs_next_var + 3`, `st with cs_next_var :=
      st.cs_next_var + 3`] >> simp[control_moves_keep_vars] >> NO_TAC)
      >> rpt strip_tac
      >> `lookup_var x (update_var (STRING #"%" (toString (st.cs_next_var + 3)))
      (word_of_bytes T (0w:bytes32) (TAKE 32 (DROP 0 cd ++ REPLICATE 32 0w)))
      (jump_to dispatch_lbl u3)) = lookup_var x (jump_to dispatch_lbl u3)` by
      (irule lookup_var_update_not_fresh >> qexists_tac `st` >> simp[])
      >> fs[control_moves_keep_vars])) >>
    (qabbrev_tac `u6 = update_var (STRING #"%" (toString (st.cs_next_var + 4)))
      (calldata_method_id cd) u5 with vs_inst_idx := 2`) >>
    (`runs_through ctx fn u5 u6` by (simp[Abbr `u6`]
      >> irule run_from_step_runs_through >> conj_tac >- fs[]
      >> qexistsl_tac [`bb2`, `mk_inst (st.cs_next_id + 5) SHR [Lit 224w; Var
      (STRING #"%" (toString (st.cs_next_var + 3)))] [STRING #"%" (toString
      (st.cs_next_var + 4))]`] >> fs[is_terminator_def] >> conj_tac
      >- (`calldata_method_id cd = word_lsr (word_of_bytes T (0w:bytes32) (TAKE
      32 (DROP 0 cd ++ REPLICATE 32 0w))) (w2n (224w:bytes32))` by (simp[]
      >> fs[calldataload_0_shr_224]) >> pop_assum SUBST1_TAC >> irule step_SHR
      >> fs[eval_operand_def]) >> metis_tac[])) >>
    (`u6.vs_current_bb = a6.cs_current_bb /\ u6.vs_inst_idx = 2 /\ eval_operand
      (Var (STRING #"%" (toString (st.cs_next_var + 4)))) u6 = SOME
      (calldata_method_id cd) /\ vars_pc_only ss u6 /\ fresh_vars_wrt (st with
      cs_next_var := st.cs_next_var + 5) u6 /\ (!x. not_fresh_at st x ==>
      lookup_var x u6 = lookup_var x ss) /\ ~u6.vs_halted` by (simp[Abbr `u6`,
      control_moves_keep_vars] >> rpt conj_tac
      >> TRY (fs[update_var_def, jump_to_def] >> NO_TAC)
      >> TRY (simp[eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE] >> NO_TAC) >> TRY (irule vars_pc_only_inst_idx
      >> irule vars_pc_only_update_var >> fs[] >> NO_TAC)
      >> TRY (irule fresh_vars_wrt_advance
      >> qexistsl_tac [`st.cs_next_var + 4`, `st with cs_next_var :=
      st.cs_next_var + 4`] >> simp[control_moves_keep_vars] >> NO_TAC)
      >> rpt strip_tac
      >> `lookup_var x (update_var (STRING #"%" (toString (st.cs_next_var + 4)))
      (calldata_method_id cd) u5) = lookup_var x u5` by (irule
      lookup_var_update_not_fresh >> qexists_tac `st` >> simp[])
      >> fs[control_moves_keep_vars])) >>
    (qspecl_then [`selectors`, `Var (STRING #"%" (toString (st.cs_next_var +
      4)))`, `a8`, `a9`] mp_tac compile_selector_checks_correct >> impl_tac
      >- fs[] >> disch_then (qspecl_then [`ctx`, `fn`, `u6`, `calldata_method_id
      cd`] mp_tac) >> impl_tac >- (fs[] >> irule fresh_vars_wrt_mono
      >> qexists_tac `st with cs_next_var := st.cs_next_var + 5` >> fs[])
      >> strip_tac) >>
    (`runs_through ctx fn ss u6` by metis_tac[runs_through_trans]) >>
    (`!x. not_fresh_at st x ==> not_fresh_at a8 x` by fs[not_fresh_at_def]) >>
    (`linear_dispatch_target cd selectors fallback_lbl = case selector_hit
      (calldata_method_id cd) selectors of SOME l => l | NONE => fallback_lbl`
      by (irule linear_dispatch_target_selector_hit >> fs[])) >>
    (Cases_on `selector_hit (calldata_method_id cd) selectors` >> fs[])
        >- ((`runs_through ctx fn tt (jump_to fallback_lbl tt)` by (irule
          run_from_jump_runs_through
          >> `~tt.vs_halted` by metis_tac[vars_pc_only_fields] >> conj_tac
          >- fs[] >> qexistsl_tac [`bb3`, `mk_inst a9.cs_next_id JMP [Label
          fallback_lbl] []`] >> fs[]
          >> simp[is_terminator_def, mk_inst_def, step_jmp_behavior])) >>
            (qexists_tac `jump_to fallback_lbl tt`
              >> simp[control_moves_keep_vars] >> rpt conj_tac)
            >- (metis_tac[runs_through_trans])
            >- (metis_tac[vars_pc_only_trans, vars_pc_only_jump_to])
            >- (irule fresh_vars_wrt_mono >> qexists_tac `a9` >> fs[])
            >- (simp[jump_to_def])
            >> simp[jump_to_def])
        >> (qexists_tac `tt` >> rpt conj_tac)
        >- (metis_tac[runs_through_trans])
        >- (metis_tac[vars_pc_only_trans])
        >- (irule fresh_vars_wrt_mono >> qexists_tac `a9` >> fs[])
        >- (fs[])
        >- (fs[])
        >> fs[])
    >> (qexists_tac `jump_to fallback_lbl u3` >> simp[control_moves_keep_vars]
      >> rpt conj_tac)
    >- (metis_tac[runs_through_trans])
    >- (irule vars_pc_only_jump_to >> fs[])
    >- (irule fresh_vars_wrt_mono
      >> qexists_tac `st with cs_next_var := st.cs_next_var + 3` >> fs[])
    >- (`LENGTH cd < 4` by fs[]
      >> simp[jump_to_def, linear_dispatch_target_short])
    >> simp[jump_to_def]
QED

(* Needed for Holmake: mark incomplete theorems *)
val _ = Feedback.set_trace "Theory.allow_rebinds" 1;

(* ===== Argument Decoding (helpers only) ===== *)

Theorem compile_decode_args_nil:
  ∀ cenv offset load_opc hi_op base_adj st.
    compile_decode_args cenv [] offset load_opc hi_op base_adj st = ((), st)
Proof
  simp[compile_decode_args_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

Theorem compile_init_kwargs_nil:
  ∀ cenv offset from_cd hi_op st.
    compile_init_kwargs cenv [] offset from_cd hi_op st = ((), st)
Proof
  simp[compile_init_kwargs_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* ===== Entry Checks ===== *)

(* Helper: the calldatasize sub-check (4 instructions: CDS, LT, ISZERO, ASSERT)
   Either succeeds (OK) or reverts. Used in both entry_checks_correct cases. *)
Theorem compile_cds_check_ok_or_revert:
  ∀ min_cds st0 st1 st2 st3 st4 cds_v lt_v ok_v ss0.
    emit_op CALLDATASIZE [] st0 = (cds_v, st1) ∧
    emit_op LT [cds_v; Lit (n2w min_cds)] st1 = (lt_v, st2) ∧
    emit_op ISZERO [lt_v] st2 = (ok_v, st3) ∧
    emit_void ASSERT [ok_v] st3 = ((), st4) ∧
    fresh_vars_wrt st0 ss0
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st0 st4) ss0 = OK ss') ∨
      (run_inst_seq (emitted_insts st0 st4) ss0 = Abort Revert_abort ss')
Proof
  rpt strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  (* Step 1: CALLDATASIZE → OK ss1 *)
  drule_all emit_op_CALLDATASIZE_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st0 st1) ss0 = OK ss1` >>
  (* Step 2: LT → OK ss2 *)
  drule emit_op_LT_correct >> disch_then drule >>
  disch_then (qspec_then `n2w min_cds` mp_tac) >>
  (impl_tac >- gvs[eval_operand_lit]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) ss1 = OK ss2` >>
  (* Extend: st0→st2 *)
  `run_inst_seq (emitted_insts st0 st2) ss0 = OK ss2`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  (* Step 3: ISZERO → OK ss3 *)
  drule emit_op_ISZERO_correct >> disch_then drule >>
  (impl_tac >- gvs[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st2 st3) ss2 = OK ss3` >>
  (* Extend: st0→st3 *)
  `run_inst_seq (emitted_insts st0 st3) ss0 = OK ss3`
    by (`inst_extends st0 st2` by metis_tac[inst_extends_trans] >>
        imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  (* Step 4: ASSERT → OK or Abort *)
  drule emit_void_ASSERT_ok_or_revert >> disch_then drule >>
  (impl_tac >- gvs[]) >> strip_tac >> gvs[]
  (* OK case *)
  >- (`inst_extends st0 st3` by metis_tac[inst_extends_trans] >>
      imp_res_tac run_inst_seq_emit_extend >> gvs[] >> metis_tac[])
  (* Abort case *)
  >> (`inst_extends st0 st3` by metis_tac[inst_extends_trans] >>
      imp_res_tac run_inst_seq_emit_extend >> gvs[])
QED

(* Helper: the payable sub-check (3 instructions: CALLVALUE, ISZERO, ASSERT).
   OK branch: callvalue = 0w, fresh_vars preserved.
   Abort branch: callvalue ≠ 0w. *)
Theorem compile_payable_check_ok_or_revert:
  ∀ st0 st1 st2 st3 cv_v nv_v ss0.
    emit_op CALLVALUE [] st0 = (cv_v, st1) ∧
    emit_op ISZERO [cv_v] st1 = (nv_v, st2) ∧
    emit_void ASSERT [nv_v] st2 = ((), st3) ∧
    fresh_vars_wrt st0 ss0
    ⇒
    (∃ ss'. run_inst_seq (emitted_insts st0 st3) ss0 = OK ss' ∧
     fresh_vars_wrt st3 ss' ∧ same_blocks st0 st3 ∧
     ss0.vs_call_ctx.cc_callvalue = 0w) ∨
    (∃ ss'.
       run_inst_seq (emitted_insts st0 st3) ss0 = Abort Revert_abort ss' ∧
       ss0.vs_call_ctx.cc_callvalue ≠ 0w)
Proof
  rpt strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  (* Step 1: CALLVALUE → OK ss1 *)
  drule_all emit_op_CALLVALUE_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st0 st1) ss0 = OK ss1` >>
  (* Step 2: ISZERO → OK ss2 *)
  drule emit_op_ISZERO_correct >> disch_then drule >>
  (impl_tac >- gvs[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) ss1 = OK ss2` >>
  (* Extend: st0→st2 *)
  `run_inst_seq (emitted_insts st0 st2) ss0 = OK ss2`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  (* Step 3: ASSERT → OK or Abort *)
  drule emit_void_ASSERT_ok_or_revert >> disch_then drule >>
  (impl_tac >- gvs[]) >> strip_tac >> gvs[]
  (* OK case: ASSERT succeeds, callvalue = 0w *)
  >- suspend "ok_case"
  (* Abort case: callvalue ≠ 0w *)
  >> suspend "abort_case"
QED

Resume compile_payable_check_ok_or_revert[ok_case]:
  `inst_extends st0 st2` by metis_tac[inst_extends_trans] >>
  imp_res_tac run_inst_seq_emit_extend >> gvs[] >>
  conj_tac >- metis_tac[same_blocks_trans] >>
  Cases_on `ss0.vs_call_ctx.cc_callvalue = 0w` >>
  gvs[bool_to_word_def]
QED

Resume compile_payable_check_ok_or_revert[abort_case]:
  `inst_extends st0 st2` by metis_tac[inst_extends_trans] >>
  imp_res_tac run_inst_seq_emit_extend >> gvs[] >>
  Cases_on `ss0.vs_call_ctx.cc_callvalue = 0w` >>
  gvs[bool_to_word_def]
QED

Finalise compile_payable_check_ok_or_revert

Theorem compile_entry_checks_correct:
  ∀ min_cds is_payable ss st st'.
    compile_entry_checks min_cds is_payable st = ((), st') ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       (is_payable ∨ ss.vs_call_ctx.cc_callvalue = 0w)) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  gvs[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, LET_THM] >>
  Cases_on `is_payable` >> gvs[] >>
  rpt (pairarg_tac >> gvs[])
  >- suspend "payable_case"
  >> suspend "nonpayable_case"
QED

Resume compile_entry_checks_correct[payable_case]:
  gvs[comp_return_def] >>
  Cases_on `min_cds > 4` >> gvs[comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM]
  >- (
    rpt (pairarg_tac >> gvs[]) >>
    drule_all compile_cds_check_ok_or_revert >>
    strip_tac >> metis_tac[]
  ) >>
  qexists `ss` >> DISJ1_TAC >>
  simp[emitted_insts_def, run_inst_seq_def]
QED

Resume compile_entry_checks_correct[nonpayable_case]:
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      LET_THM, pairTheory.PAIR] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all compile_payable_check_ok_or_revert >> strip_tac
  >- suspend "nonpayable_ok"
  >> suspend "nonpayable_abort"
QED

(* Payable OK: callvalue = 0w, payable prefix gives OK ss' *)
Resume compile_entry_checks_correct[nonpayable_ok]:
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  qpat_x_assum `emit_op CALLVALUE _ _ = _` kall_tac >>
  qpat_x_assum `emit_op ISZERO _ _ = _` kall_tac >>
  qpat_x_assum `emit_void ASSERT _ _ = _` kall_tac >>
  Cases_on `min_cds > 4` >> gvs[comp_return_def] >>
  gvs[comp_bind_def, comp_ignore_bind_def, LET_THM, pairTheory.PAIR] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all compile_cds_check_ok_or_revert >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  irule run_inst_seq_compose_ok_or_abort >>
  qexistsl [`ss'`, `cs'`] >> gvs[] >>
  metis_tac[inst_extends_trans]
QED

(* Payable Abort: callvalue ≠ 0w *)
Resume compile_entry_checks_correct[nonpayable_abort]:
  qexists `ss'` >> disj2_tac >>
  irule run_inst_seq_abort_extends >>
  qexists `cs'` >> rpt conj_tac
  (* abort assumption *)
  >- first_assum ACCEPT_TAC
  (* inst_extends st cs' from payable emit chain *)
  >- (qmatch_asmsub_rename_tac
        `emit_op CALLVALUE [] st = (cv, pay_st1)` >>
      qmatch_asmsub_rename_tac
        `emit_op ISZERO [cv] pay_st1 = (no_value, pay_st2)` >>
      imp_res_tac inst_extends_emit_op >>
      imp_res_tac inst_extends_emit_void >>
      irule inst_extends_trans >> qexists_tac `pay_st1` >> simp[] >>
      irule inst_extends_trans >> qexists_tac `pay_st2` >> simp[])
  (* inst_extends cs' st' from CDS conditional *)
  >> (qpat_x_assum `emit_op CALLVALUE _ _ = _` kall_tac >>
      qpat_x_assum `emit_op ISZERO [cv] _ = _` kall_tac >>
      qpat_x_assum `emit_void ASSERT [no_value] _ = _` kall_tac >>
      Cases_on `min_cds > 4` >> gvs[comp_return_def, inst_extends_refl] >>
      gvs[comp_bind_def, comp_ignore_bind_def, LET_THM, pairTheory.PAIR] >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac inst_extends_emit_op >>
      imp_res_tac inst_extends_emit_void >>
      metis_tac[inst_extends_trans])
QED

Finalise compile_entry_checks_correct

(* Derive nonpayable revert from the general theorem *)
Theorem compile_entry_checks_nonpayable_revert:
  ∀ min_cds ss st st'.
    compile_entry_checks min_cds F st = ((), st') ∧
    fresh_vars_wrt st ss ∧
    ss.vs_call_ctx.cc_callvalue ≠ 0w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  drule_all compile_entry_checks_correct >> strip_tac >> gvs[]
QED

(* ===== Constructor Epilogue ===== *)

(* Both branches use Label "runtime_begin" via OFFSET, needing vs_labels.
   The immutables_len > 0 branch also uses immutables_buf in MCOPY.
   fresh_vars_wrt only constrains vs_vars, not vs_labels. *)
Theorem compile_constructor_epilogue_correct:
  ∀ runtime_size immutables_len immutables_buf ss st st'.
    compile_constructor_epilogue runtime_size immutables_len immutables_buf st =
      ((), st') ∧
    fresh_vars_wrt st ss ∧
    (∃ v. FLOOKUP ss.vs_labels "runtime_begin" = SOME v) ∧
    (immutables_len > 0 ⇒ ∃ v. eval_operand immutables_buf ss = SOME v)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Halt ss'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_constructor_epilogue _ _ _ _ = _` mp_tac >>
  simp[compile_constructor_epilogue_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  Cases_on `immutables_len > 0` >> gvs[]
  (* immutables_len > 0 branch *)
  >- suspend "imm_pos"
  (* immutables_len = 0 branch *)
  >> suspend "imm_zero"
QED

Resume compile_constructor_epilogue_correct[imm_pos]:
  strip_tac >> gvs[comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  (* Step 1: ALLOCA *)
  drule_all emit_op_ALLOCA_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st cs1) ss = OK ss1` >>
  (* Step 2: ADD — deploy_buf evaluable in ss1, Lit always evaluable *)
  drule emit_op_ADD_correct >>
  disch_then drule >>
  disch_then (qspec_then `n2w runtime_size` mp_tac) >>
  (impl_tac >- gvs[eval_operand_lit]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs1 cs2) ss1 = OK ss2` >>
  (* Step 3: MCOPY — imm_dst from ADD, immutables_buf from hypothesis (preserved), Lit *)
  drule emit_void_MCOPY_correct >>
  disch_then drule >>
  disch_then (qspecl_then [`v'`, `n2w immutables_len`] mp_tac) >>
  (impl_tac >- gvs[eval_operand_lit]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs2 cs3) ss2 = OK ss3` >>
  (* Step 4: CODECOPY — the runtime label is used directly. *)
  `eval_operand (Label "runtime_begin") ss3 = SOME v`
    by (gvs[eval_operand_def] >>
        `FLOOKUP ss1.vs_labels "runtime_begin" = SOME v`
          by gvs[] >>
        `FLOOKUP ss2.vs_labels "runtime_begin" = SOME v`
          by (Cases_on `Label "runtime_begin"` >>
              gvs[eval_operand_def] >>
              first_x_assum (qspecl_then [`Label "runtime_begin"`, `v`] mp_tac) >>
              simp[eval_operand_def]) >>
        gvs[mcopy_def, write_memory_with_expansion_def, LET_THM]) >>
  `eval_operand deploy_buf ss3 = SOME (n2w offset)` by metis_tac[] >>
  `eval_operand (Lit (n2w runtime_size)) ss3 = SOME (n2w runtime_size)`
    by simp[eval_operand_def] >>
  drule_all emit_void_CODECOPY_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs3 cs4) ss3 = OK ss4` >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  imp_res_tac inst_extends_emit_inst >>
  (* Compose all OK segments: st→cs1→cs2→cs3→cs4. *)
  `run_inst_seq (emitted_insts st cs2) ss = OK ss2`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st cs3) ss = OK ss3`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs3` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st cs4) ss = OK ss4`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs4` by metis_tac[inst_extends_trans] >>
  (* Final: RETURN → Halt *)
  `eval_operand deploy_buf ss4 = SOME (n2w offset)` by metis_tac[] >>
  `eval_operand (Lit (n2w (immutables_len + runtime_size))) ss4 =
     SOME (n2w (immutables_len + runtime_size))`
    by simp[eval_operand_def] >>
  drule_all emit_inst_RETURN_halt >> strip_tac >>
  `inst_extends cs4 st'` by metis_tac[inst_extends_emit_inst] >>
  drule_all run_inst_seq_emit_extend >> gvs[]
QED

Resume compile_constructor_epilogue_correct[imm_zero]:
  strip_tac >>
  gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  (* Step 1: ALLOCA *)
  drule_all emit_op_ALLOCA_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st cs1) ss = OK ss1` >>
  (* Step 2: CODECOPY — the runtime label is used directly. *)
  `eval_operand (Label "runtime_begin") ss1 = SOME v`
    by gvs[eval_operand_def] >>
  `eval_operand (Lit (n2w runtime_size)) ss1 = SOME (n2w runtime_size)`
    by simp[eval_operand_def] >>
  drule_all emit_void_CODECOPY_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs1 cs2) ss1 = OK ss2` >>
  (* Step 3: RETURN → Halt *)
  `eval_operand op ss2 = SOME (n2w offset)` by metis_tac[] >>
  `eval_operand (Lit (n2w runtime_size)) ss2 = SOME (n2w runtime_size)`
    by simp[eval_operand_def] >>
  drule_all emit_inst_RETURN_halt >> strip_tac >>
  (* Compose *)
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  imp_res_tac inst_extends_emit_inst >>
  `run_inst_seq (emitted_insts st cs2) ss = OK ss2`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs2` by metis_tac[inst_extends_trans] >>
  `inst_extends cs2 st'` by metis_tac[inst_extends_emit_inst] >>
  drule_all run_inst_seq_emit_extend >> gvs[]
QED

Finalise compile_constructor_epilogue_correct

Theorem run_inst_seq_ok_not_halted:
  ∀ is ss ss'.
    run_inst_seq is ss = OK ss' ∧
    (∀i ss1 ss2. MEM i is ∧ step_inst_base i ss1 = OK ss2 ⇒ (ss2.vs_halted ⇔ ss1.vs_halted)) ∧
    ¬ss.vs_halted
    ⇒
    ¬ss'.vs_halted
Proof
  rpt strip_tac >>
  drule_at (Pos hd) (Q.ISPEC `\s. s.vs_halted` run_inst_seq_preserves_field) >>
  (impl_tac >- (rpt strip_tac >> res_tac >> fs[])) >>
  simp[]
QED
