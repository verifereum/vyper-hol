(*
 * Expression simulation: ecrecover (#636, Builtins row 8)
 *
 * ecrecover(hash, v, r, s) lowers its four word operands with lower_value,
 * then compile_ecrecover: an ALLOCA'd 128-byte input buffer holding the four
 * words, an ALLOCA'd 32-byte output buffer zeroed, a STATICCALL to
 * precompile 1, an ASSERT of its success word and an MLOAD of the output.
 * Both buffers are fresh ALLOCAs of the function, so alloca_room keeps
 * them, and the ADDs into the input buffer, below 2 ** 256.  take_outcome
 * answers the call with precompile_result (extCallOracle), which always
 * succeeds for address 1: a valid signature's address padded to 32 bytes,
 * or no bytes for an invalid one, leaving the zeroed output buffer as the
 * source's AddressV 0w.
 *
 * TOP-LEVEL:
 *   compile_ecrecover_call_case — expr_vv_case of ECRecover from its
 *                            operands' exprs_case
 *
 * Exported for the other precompiles (ecadd, ecmul in exprSimECArith):
 *   - computed STATICCALLs: computed_static_consume_eq, computed_static_exec,
 *     computed_static_exec_success, computed_static_exec_failure,
 *     computed_static_exec_state_rel,
 *     computed_static_exec_wb_frame, write_memory_stmt_state_rel,
 *     wb_frame_readonly_input
 *   - counted composition: eval_exprs_suffix (operands, then a
 *     continuation), run_inst_seq_gas_path (a straight-line run as a
 *     counted path)
 *   - the GAS/STATICCALL/ASSERT suffix: computed_suffix_shape,
 *     computed_suffix_success, computed_suffix_failure,
 *     computed_suffix_output, computed_suffix_preserves
 *   - ALLOCA'd buffers around a payload: allocated_payload_shape,
 *     allocated_payload_run, alloc_buffer_finish, state_allocations_disjoint,
 *     precompile_alloca_immutable_disjoint
 *   - stack operands under their typed encoding (a bytes32 is not a
 *     word_value): typed_args_ready, typed_args_post, typed_args_ready_head,
 *     typed_args_ready_tail, typed_args_cons_cases, typed_args_post_cons,
 *     lower_typed_args_nil_sim, lower_typed_args_sim,
 *     typed_args_ready_of_case, typed_stack_args_ready,
 *     stack_args_values_typed, stack_args_values_typed_body,
 *     typed_builtin_stack_args_values, expr_body_pre_stack_result,
 *     expr_sim_pre_stack_result,
 *     expr_post_typed_stack_operand, expr_post_typed_stack_intro
 *   - scratch buffers: scratch_mstore_frame, mem_bytes_at_store_append,
 *     scratch_three_word_stores, scratch_four_word_stores,
 *     scratch_memory_frame
 *   - big-endian words: num_of_bytes_l2n, num_of_be_bytes_word32,
 *     padded_num_to_be_bytes, padded_num_to_be_bytes_word32,
 *     take_pad_word_prefix, drop_word_prefix
 * The ecrecover-specific helpers are local.
 *)

Theory exprSimPrecompiles
Ancestors
  exprBopSimProps
  exprSimSource
  exprSimProps
  exprSimHypsDefs
  exprSimDefs exprSimStack
  loweringPosts
  exprSimAlloc
  list fragExec loweringSlice  exprSimHyps exprSimWordBuiltins
  exprSimLiteralBuffer abiDecodeStaticProps dftCommutation loweringHalt
  exprSimWordArgs exprSimOperators exprSimHash exprBopLowering exprLowering
  exprLoweringProps builtinMisc compileEnv
  valueEncoding valueEncodingProps valueEncodingProofs valueCopy extCallOracle
  venomMemDefs venomExecSemantics venomInst venomState
  venomCallOracleDefs exprSimOps vyperEvalExprPreservesScopesDom
  byte words rich_list vyperTyping integer_word vfmTypes vfmBuffer numposrep cv_std[ignore_grammar]
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
Libs
  monadsyntax

open gasContextTheory gasOutcomeTheory gasSummaryTheory gasSummaryComposeTheory
     gasExemptCertTheory fragGasModeTheory fragGasPathTheory;

Theorem padded_num_bytes_aux[local]:
  !k n. n < 256 ** k ==>
    PAD_RIGHT (0w:word8) k (if n = 0 then [] else MAP n2w (n2l 256 n)) =
    bytes_of_num k n
Proof
  Induct_on `k`
  >- simp[bytes_of_num_def, PAD_RIGHT] >>
  rpt strip_tac >>
  Cases_on `n = 0`
  >- (gvs[bytes_of_num_def, PAD_RIGHT, GENLIST_CONS] >>
      first_x_assum (qspec_then `0` mp_tac) >>
      simp[PAD_RIGHT, arithmeticTheory.EXP_POS]) >>
  `n DIV 256 < 256 ** k` by
    (gvs[arithmeticTheory.EXP, arithmeticTheory.DIV_LT_X]) >>
  first_x_assum (qspec_then `n DIV 256` mp_tac) >> simp[] >>
  Cases_on `n < 256`
  >- (`n DIV 256 = 0` by simp[arithmeticTheory.DIV_EQ_0] >>
      simp[] >> strip_tac >>
      simp[Once n2l_def, bytes_of_num_def, PAD_RIGHT_CONS]) >>
  `n DIV 256 <> 0` by simp[arithmeticTheory.DIV_EQ_0] >>
  simp[] >> strip_tac >>
  simp[Once n2l_def, bytes_of_num_def, PAD_RIGHT_CONS,
       dimword_def, fcpLib.INDEX_CONV ``dimindex(:8)``]
QED

Theorem padded_num_to_be_bytes:
  !k n. n < 256 ** k ==>
    PAD_LEFT 0w k (num_to_be_bytes n) = REVERSE (bytes_of_num k n)
Proof
  rpt strip_tac >> drule padded_num_bytes_aux >>
  disch_then (mp_tac o AP_TERM ``REVERSE:word8 list -> word8 list``) >>
  Cases_on `n = 0` >>
  simp[num_to_be_bytes_def, PAD_LEFT, PAD_RIGHT, REVERSE_APPEND,
       REVERSE_GENLIST, combinTheory.K_DEF, MAP_REVERSE] >>
  disch_then (SUBST1_TAC o SYM) >>
  simp[REVERSE_APPEND, REVERSE_GENLIST]
QED

Theorem padded_num_to_be_bytes_word32:
  n < 2 ** 256 ==>
  PAD_LEFT 0w 32 (num_to_be_bytes n) = word_to_bytes (n2w n:bytes32) T
Proof
  strip_tac >>
  `256 ** 32 = 2 ** 256` by EVAL_TAC >>
  `n < 256 ** 32` by (asm_rewrite_tac[]) >>
  `w2n (n2w n:bytes32) = n` by
    (pure_rewrite_tac[w2n_n2w] >> irule arithmeticTheory.LESS_MOD >>
     rewrite_tac[dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
     first_assum ACCEPT_TAC) >>
  drule (Q.SPEC `32` padded_num_to_be_bytes) >>
  simp[GSYM word_to_bytes_be_def, cv_stdTheory.word_to_bytes_be_eq_bytes_of_num,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem write_memory_stmt_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b + sz <= dst \/ dst + LENGTH data <= b) /\
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
    (write_memory_with_expansion dst data s) ==>
  stmt_state_rel ctx func cenv cx es (write_memory_with_expansion dst data s)
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes (write_memory_with_expansion dst data s)` by
    (irule localPtrsPropsTheory.local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     rpt conj_tac
     >~ [`local_ptrs_rel _ _ _ _`]
     >- gvs[stmt_state_rel_def, state_rel_def]
     >~ [`mem_bytes_at _ _ _ = mem_bytes_at _ _ _`]
     >- (rpt strip_tac >> sym_tac >> irule mem_bytes_at_write_disjoint >>
         metis_tac[]) >>
     simp[write_memory_with_expansion_def, lookup_var_def] >>
     rpt strip_tac >> gvs[]) >>
  `immutable_base_zero cenv (write_memory_with_expansion dst data s)` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     gvs[stmt_state_rel_def, write_memory_with_expansion_def, lookup_var_def]) >>
  qpat_x_assum `stmt_state_rel ctx _ _ _ _ _` mp_tac >>
  rewrite_tac[Once stmt_state_rel_def] >> strip_tac >>
  rewrite_tac[stmt_state_rel_def] >> conj_tac
  >- (irule state_rel_frame >> simp[] >> qexistsl_tac [`es`, `s`] >>
      simp[write_memory_with_expansion_def]) >>
  conj_tac
  >- (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `s` >>
      simp[write_memory_with_expansion_def]) >>
  conj_tac
  >- (irule alloca_room_fields >> qexists_tac `s` >>
      simp[write_memory_with_expansion_def]) >>
  conj_tac
  >- (irule fmp_room_fields >> qexists_tac `s` >>
      simp[write_memory_with_expansion_def]) >>
  gvs[write_memory_with_expansion_def, immutable_alloca_sep_def,
      local_region_def, lookup_var_def] >> metis_tac[]
QED

Theorem computed_static_consume_eq:
  rq = venom_call_request s addr 0w ai an T /\ computed_precompile rq ==>
  consume_call_outcome rq ro rs s =
    (if (FST (take_outcome rq s.vs_outcomes)).co_success then 1w else 0w,
     (write_memory_with_expansion ro
       (TAKE rs (FST (take_outcome rq s.vs_outcomes)).co_returnData) s)
       with <|vs_returndata := (FST (take_outcome rq s.vs_outcomes)).co_returnData;
              vs_outcomes := DROP 1 s.vs_outcomes|>)
Proof
  strip_tac >> drule computed_precompile_no_request >>
  disch_then (qspec_then `s.vs_requests` assume_tac) >>
  `rq.cr_static` by simp[venom_call_request_def] >>
  simp[consume_call_outcome_eq, take_outcome_rest, adopt_outcome_def,
       adopt_outcome_deletions_def,
       write_memory_with_expansion_def, venom_state_component_equality]
QED

Theorem computed_static_exec:
  rq = venom_call_request s addr 0w ai an T /\ computed_precompile rq /\
  inst.inst_outputs = [out] ==>
  exec_ext_call inst s gas addr 0w ai an ro rs T =
    OK (update_var out
      (if (FST (take_outcome rq s.vs_outcomes)).co_success then 1w else 0w)
      ((write_memory_with_expansion (w2n ro)
        (TAKE (w2n rs) (FST (take_outcome rq s.vs_outcomes)).co_returnData) s)
       with <|vs_returndata := (FST (take_outcome rq s.vs_outcomes)).co_returnData;
              vs_outcomes := DROP 1 s.vs_outcomes|>))
Proof
  strip_tac >> drule_all computed_static_consume_eq >>
  disch_then (qspecl_then [`w2n rs`, `w2n ro`] assume_tac) >>
  gvs[exec_ext_call_def, Excl "consume_call_outcome_eq"]
QED

Theorem computed_static_exec_state_rel:
  rq = venom_call_request s addr 0w ai an T /\ computed_precompile rq /\
  inst.inst_outputs = [out] /\
  stmt_state_rel ctx func cenv cx es s /\ not_local_ptr cenv es.scopes out /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b + sz <= w2n ro \/
     w2n ro + LENGTH (TAKE (w2n rs)
       (FST (take_outcome rq s.vs_outcomes)).co_returnData) <= b) /\
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
    (write_memory_with_expansion (w2n ro)
      (TAKE (w2n rs) (FST (take_outcome rq s.vs_outcomes)).co_returnData) s) ==>
  ?t. exec_ext_call inst s gas addr 0w ai an ro rs T = OK t /\
      stmt_state_rel ctx func cenv cx
        (es with outcomes := SOME (DROP 1 s.vs_outcomes)) t
Proof
  strip_tac >> drule_all computed_static_consume_eq >>
  disch_then (qspecl_then [`w2n rs`, `w2n ro`] assume_tac) >>
  gvs[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  irule stmt_state_rel_update_var >> simp[hash_returndata_state_rel] >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel _ _ _ _ _ (m with vs_outcomes := _)` >>
  `m.vs_outcomes = s.vs_outcomes` by simp[Abbr `m`, write_memory_with_expansion_def] >>
  `stmt_state_rel ctx func cenv cx es m` by
    (qunabbrev_tac `m` >> irule write_memory_stmt_state_rel >> simp[] >> metis_tac[]) >>
  drule hash_outcomes_state_rel >> simp[]
QED

Theorem computed_static_exec_wb_frame:
  rq = venom_call_request s addr 0w ai an T /\ computed_precompile rq /\
  inst.inst_outputs = [out] /\ ~not_fresh_at sa out /\
  (!aid b sz.
     FLOOKUP s.vs_allocas aid = SOME (b, sz) /\ aid < sa.cs_next_id /\
     (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
         b + sz <= lb \/ lb + lsz <= b) ==>
     b + sz <= w2n ro \/ w2n ro + LENGTH (TAKE (w2n rs)
       (FST (take_outcome rq s.vs_outcomes)).co_returnData) <= b) /\
  (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
     regions_disjoint (w2n ro) (w2n rs) lb lsz) ==>
  ?t. exec_ext_call inst s gas addr 0w ai an ro rs T = OK t /\
      wb_frame cenv es sa s t
Proof
  strip_tac >> drule_all computed_static_consume_eq >>
  disch_then (qspecl_then [`w2n rs`, `w2n ro`] assume_tac) >>
  gvs[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  simp[wb_frame_def, update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac
  >- (rpt strip_tac >> IF_CASES_TAC >> gvs[write_memory_with_expansion_def]) >>
  conj_tac
  >- (rpt strip_tac >> irule mem_bytes_at_write_disjoint >>
      first_x_assum (drule_all_then mp_tac) >> decide_tac) >>
  (* the locals: the returned bytes land outside their regions *)
  rw[locals_kept_def] >> irule mem_bytes_at_write_disjoint >>
  first_x_assum (drule_then mp_tac) >>
  qmatch_goalsub_abbrev_tac `LENGTH bs` >>
  `LENGTH bs <= w2n rs` by simp[Abbr `bs`, listTheory.LENGTH_TAKE_EQ] >>
  simp[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem computed_static_empty_probe[local]:
  rq = venom_call_request s addr 0w ai an T /\ computed_precompile rq /\
  inst.inst_outputs = [out] /\ s.vs_outcomes = [] ==>
  exec_ext_call inst s gas addr 0w ai an ro rs T =
    OK (update_var out 0w
      ((write_memory_with_expansion (w2n ro) [] s)
        with <|vs_returndata := []; vs_outcomes := []|>))
Proof
  strip_tac >> drule_all computed_static_exec >>
  simp[take_outcome_def, write_memory_with_expansion_def]
QED

Theorem computed_static_false_probe[local]:
  rq = venom_call_request s addr 0w ai an T /\ computed_precompile rq /\
  inst.inst_outputs = [out] /\ s.vs_outcomes = head::rest /\ ~head.co_success ==>
  exec_ext_call inst s gas addr 0w ai an ro rs T =
    OK (update_var out 0w
      ((write_memory_with_expansion (w2n ro) [] s)
        with <|vs_returndata := []; vs_outcomes := rest|>))
Proof
  strip_tac >>
  Cases_on `precompile_result rq.cr_target rq.cr_data`
  >- (drule_all computed_static_exec >> simp[take_outcome_def]) >>
  rename1 `SOME result` >> Cases_on `result` >>
  drule_all computed_static_exec >> simp[take_outcome_def]
QED

Theorem computed_static_true_probe[local]:
  rq = venom_call_request s addr 0w ai an T /\ computed_precompile rq /\
  inst.inst_outputs = [out] /\ s.vs_outcomes = head::rest /\ head.co_success /\
  precompile_result rq.cr_target rq.cr_data = SOME (SOME data) ==>
  exec_ext_call inst s gas addr 0w ai an ro rs T =
    OK (update_var out 1w
      ((write_memory_with_expansion (w2n ro) (TAKE (w2n rs) data) s)
        with <|vs_returndata := data; vs_outcomes := rest|>))
Proof
  strip_tac >> drule_all computed_static_exec >> simp[take_outcome_def]
QED

Theorem ecrecover_typing[local]:
  well_typed_builtin_app ty ECRecover ts ==>
  LENGTH ts = 4 /\ ty = BaseT AddressT /\
  HD ts = BaseT (BytesT (Fixed 32)) /\
  (EL 1 ts = BaseT (UintT 8) \/ EL 1 ts = BaseT (UintT 256) \/
   EL 1 ts = BaseT (BytesT (Fixed 32))) /\
  EVERY (\t. t = BaseT (UintT 256) \/ t = BaseT (BytesT (Fixed 32))) (TL (TL ts))
Proof
  simp[well_typed_builtin_app_def]
QED

Theorem expr_post_typed_stack_operand:
  expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  eval_operand op s = SOME (typed_val_to_w256 tv v)
Proof
  simp[expr_post_def, expr_val_rel_def] >> metis_tac[]
QED

Theorem expr_post_typed_stack_intro:
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  stmt_state_rel ctx func cenv cx es' s /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  wb_frame cenv es sa s0 s ==>
  expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, wb_frame_def] >>
  metis_tac[]
QED

(* The word-only argument predicates cannot encode bytes32.  Keep the
   same compiler and frame, but use the type-directed stack encoding.  As
   wb_args_ready, a later operand's facts only if the ones before it can
   evaluate. *)
Definition typed_args_ready_def:
  typed_args_ready ctx func cenv cx arg_ty Inv [] = T /\
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) =
    ((!es. Inv es ==>
       expr_sim ctx func cenv cx (arg_ty e) e es /\
       is_word_type (expr_type e) /\
       IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
       (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==> expr_res_ok res) /\
       (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
         Inv es')) /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      typed_args_ready ctx func cenv cx arg_ty Inv args))
End

Definition typed_args_post_def:
  typed_args_post ctx func cenv cx es sa s0 es' args xs vs s <=>
    stmt_state_rel ctx func cenv cx es' s /\
    LENGTH args = LENGTH vs /\
    LIST_REL (\x ev. eval_operand x s = SOME
      (typed_val_to_w256
        (THE (evaluate_type (get_tenv cx) (expr_type (FST ev))))
        (SND ev))) xs (ZIP (args,vs)) /\
    wb_frame cenv es sa s0 s
End

Theorem typed_args_ready_head:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es ==>
    expr_sim ctx func cenv cx (arg_ty e) e es /\
    is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==> expr_res_ok res) /\
    (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
      Inv es')
Proof
  simp[typed_args_ready_def] >> metis_tac[]
QED

Theorem typed_args_ready_tail:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) ==>
  typed_args_ready ctx func cenv cx arg_ty Inv args
Proof
  simp[typed_args_ready_def] >> rpt strip_tac >> first_x_assum irule >>
  drule eval_expr_read_INL >> metis_tac[]
QED

Theorem typed_args_cons_cases:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  eval_exprs cx (e::args) es = (res, es') ==>
  (?exc. (do r <- eval_expr cx e; read_result cx r od) es = (INR exc, es') /\ res = INR exc) \/
  ?v es1 rr. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) /\
    Inv es1 /\ eval_exprs cx args es1 = (rr, es') /\
    res = (case rr of INL vs => INL (v::vs) | INR exc => INR exc)
Proof
  rpt strip_tac >> drule_all typed_args_ready_head >> strip_tac >>
  drule eval_exprs_cons_cases >> strip_tac >> metis_tac[]
QED

Theorem lower_typed_args_nil_sim:
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx, func) (eval_exprs cx []) (es, s0)
    (\rr ee t. ?vs. rr = INL vs /\
       typed_args_post ctx func cenv cx es sa s0 ee [] [] vs t /\
       t.vs_current_bb = sa.cs_current_bb /\
       t.vs_inst_idx = LENGTH sa.cs_current_insts)
    (\rr ee r. wb_args_exit rr r)
Proof
  strip_tac >> rewrite_tac[fragGasModeTheory.gas_marked_path_def, gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def, gasSummaryTheory.gas_marked_exec_def,
       fragGasModeTheory.gas_marked_path_def, eval_exprs_nil,
       gasSummaryTheory.gas_explicit_def] >>
  qexistsl_tac [`INL []`, `es`, `OK s0`] >>
  simp[typed_args_post_def, wb_frame_refl] >>
  irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]
QED

Theorem typed_args_post_cons:
  expr_post ctx func cenv cx e es sa s1 s0 es1 v x t /\
  typed_args_post ctx func cenv cx es1 s1 t es' args xs vs u /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) ==>
  typed_args_post ctx func cenv cx es sa s0 es' (e::args) (x::xs) (v::vs) u
Proof
  rpt strip_tac >>
  `eval_operand x t = SOME (typed_val_to_w256 tv v)` by
    (drule_all expr_post_typed_stack_operand >> simp[]) >>
  `wb_frame cenv es sa s0 t` by metis_tac[expr_post_frame] >>
  gvs[typed_args_post_def] >> conj_tac
  >- (irule eval_operand_frame >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[wb_frame_vars]) >>
  irule wb_frame_trans >> simp[] >> conj_tac
  >- (qexistsl_tac [`es1`, `s1`, `t`] >> simp[]) >>
  qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]
QED

Theorem typed_args_head_admissible[local]:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
  `Inv (es with gas_obs := gs)` by metis_tac[] >>
  drule_all typed_args_ready_head >> strip_tac >>
  first_x_assum irule >> qexists_tac `ee` >> gvs[bind_def]
QED

Theorem typed_args_head_marked_facts[local]:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
  gas_marked_exec F (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0) marks (INL v) mid r ==>
  Inv (mid with gas_obs := []) /\
  typed_args_ready ctx func cenv cx arg_ty Inv args /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  fs[] >> rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  `Inv (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) typed_args_ready_head) >>
  strip_tac >>
  `Inv (mid with gas_obs := [])` by metis_tac[] >>
  `typed_args_ready ctx func cenv cx arg_ty Inv args` by
    (irule (CONV_RULE (DEPTH_CONV ETA_CONV) typed_args_ready_tail) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  drule (CONV_RULE (DEPTH_CONV ETA_CONV)
           forced_eval_expr_preserves_scopes_dom) >> simp[]
QED

Theorem lower_typed_args_sim:
  !args ctx func cenv cx arg_ty Inv es sa xs sb s0.
    typed_args_ready ctx func cenv cx arg_ty Inv args /\ Inv es /\
    (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
    wb_args_shape cenv arg_ty args /\
    lower_word_args cenv arg_ty args sa = (xs,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func) (eval_exprs cx args) (es, s0)
      (\rr ee t. ?vs. rr = INL vs /\
         typed_args_post ctx func cenv cx es sa s0 ee args xs vs t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\rr ee r. wb_args_exit rr r)
Proof
  Induct
  >- (simp[lower_word_args_nil, eval_exprs_nil] >> rpt strip_tac >>
      irule lower_typed_args_nil_sim >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `typed_args_ready ctx func cenv cx arg_ty Inv (e::args)` >>
  `wb_args_shape cenv arg_ty args` by metis_tac[wb_args_shape_tail] >>
  gvs[lower_word_args_cons] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   sa.cs_next_id <= s1.cs_next_id /\
   (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
    (qpat_x_assum `wb_args_shape _ _ (_::_)` mp_tac >>
     rewrite_tac[wb_args_shape_def] >>
     disch_then (qspec_then `e` mp_tac) >> simp[] >>
     disch_then drule >> simp[]) >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv s1` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[typed_args_head_admissible] >>
  drule_all typed_args_ready_head >> strip_tac >>
  drule_all expr_sim_apply >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "head_normal"
      >> suspend "head_exit") >>
  suspend "head_exempt"
QED

Resume lower_typed_args_sim[head_normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  drule_all typed_args_head_marked_facts >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    metis_tac[expr_post_state] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `!ctx func cenv cx arg_ty Inv es sa xs sb s0. _`
    (drule_all_then mp_tac) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "tail_normal"
      >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED
Resume lower_typed_args_sim[head_exit]:
  Cases_on `res` >- gvs[expr_exit_def] >>
  qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED
Resume lower_typed_args_sim[head_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  irule_at Any wb_args_head_exempt_cert >> goal_assum (drule_at Any)
QED
Resume lower_typed_args_sim[tail_normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (v::vs)`, `es_end'`, `OK t'`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v) _ _` (irule_at Any) >>
      BETA_TAC >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL vs) _ _`
        (mp_tac o MATCH_MP gas_marked_exec_cons_values) >> simp[]) >>
  disj1_tac >> simp[] >>
  irule typed_args_post_cons >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `evaluate_type (get_tenv cx) (expr_type e)` >> gvs[]
QED
Resume lower_typed_args_sim[tail_exit]:
  Cases_on `res` >- gvs[wb_args_exit_def] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end'`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v) _ _` (irule_at Any) >>
      BETA_TAC >> irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED
Resume lower_typed_args_sim[tail_exempt]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  irule_at Any wb_args_tail_exempt_cert >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED
Finalise lower_typed_args_sim

Theorem num_of_bytes_l2n:
  !bs. num_of_bytes bs = l2n 256 (MAP w2n bs)
Proof
  Induct >> simp[num_of_bytes_def, l2n_def] >>
  qx_gen_tac `b` >> qspec_then `b` mp_tac w2n_lt >> simp[dimword_def, fcpLib.INDEX_CONV ``dimindex(:8)``]
QED

Theorem num_of_be_bytes_word32:
  LENGTH bs = 32 ==>
  num_of_be_bytes bs = w2n (word_of_bytes_be bs : bytes32)
Proof
  strip_tac >>
  `8 <= dimindex(:256) /\ divides 8 (dimindex(:256))` by
    (simp[fcpLib.INDEX_CONV ``dimindex(:256)``] >> EVAL_TAC) >>
  `TAKE 32 (bs ++ REPLICATE 32 0w) = bs` by
    (qpat_x_assum `LENGTH bs = 32` (fn th => rewrite_tac[GSYM th]) >>
     simp[TAKE_APPEND1]) >>
  `num_of_bytes (REVERSE bs) < dimword(:256)` by
    (qspec_then `REVERSE bs` mp_tac num_of_bytes_lt >>
     simp[dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
  simp[word_of_bytes_be_eq_num_of_bytes, be_bytes_thm,
       fcpLib.INDEX_CONV ``dimindex(:256)``,
       GSYM num_of_bytes_l2n, num_of_be_bytes_def]
QED

(* A serialized word can be decoded independently of the remaining words.
   Repeated use covers either three- or four-word precompile inputs. *)
Theorem take_pad_word_prefix:
  take_pad_0 32 (word_to_bytes (w:bytes32) T ++ bs) =
    word_to_bytes w T
Proof
  simp[take_pad_0_def, LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, TAKE_APPEND1, PAD_RIGHT]
QED

Theorem drop_word_prefix:
  DROP (32 + n) (word_to_bytes (w:bytes32) T ++ bs) = DROP n bs
Proof
  simp[DROP_APPEND, LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, DROP_LENGTH_TOO_LONG]
QED

Theorem precompile_result_four_words[local]:
  !(h:bytes32) (v:bytes32) (r:bytes32) (s:bytes32).
  precompile_result 1w
    (word_to_bytes h T ++ word_to_bytes v T ++
     word_to_bytes r T ++ word_to_bytes s T) =
  SOME (SOME (case vfmExecution$ecrecover h (w2n v) (w2n r) (w2n s) of
    NONE => [] | SOME addr => PAD_LEFT 0w 32 (word_to_bytes addr T)))
Proof
  rpt gen_tac >>
  rewrite_tac[precompile_result_def, take_pad_word_prefix] >>
  simp[take_pad_0_def,
       LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``,
       listTheory.TAKE_APPEND1, listTheory.DROP_APPEND,
       TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG, PAD_RIGHT,
       num_of_be_bytes_word32, word_to_bytes_word_of_bytes_32,
       word_of_bytes_be_def]
QED

Theorem ecrecover_arg_typed_encoding[local]:
  ((?k. tv = BaseTV (UintT k) /\ k <= 256) \/
   tv = BaseTV (BytesT (Fixed 32))) /\ value_has_type tv x ==>
  ecrecover_arg_to_num x = SOME (w2n (typed_val_to_w256 tv x))
Proof
  strip_tac
  >- (Cases_on `x` >>
      gvs[value_has_type_def, ecrecover_arg_to_num_def,
          typed_val_to_w256_def, val_to_w256_def] >>
      `Num i < 2 ** 256` by
        (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** k` >>
         simp[]) >>
      `~(i < 0)` by intLib.ARITH_TAC >>
      gvs[i2w_def, dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
  Cases_on `x` >>
  gvs[value_has_type_def, ecrecover_arg_to_num_def,
      typed_val_to_w256_def, PAD_LEFT, PAD_RIGHT]
QED

Theorem ecrecover_output_encoding[local]:
  ((data = [] /\ (addr:address) = 0w) \/
   data = PAD_LEFT 0w 32 (word_to_bytes addr T)) ==>
  (word_of_bytes_be (TAKE 32 (data ++ REPLICATE 32 0w)) : bytes32) =
  typed_val_to_w256 (BaseTV AddressT) (AddressV addr)
Proof
  strip_tac
  >- (gvs[] >> simp[typed_val_to_w256_def, val_to_w256_address,
        GSYM word_to_bytes_w2w_address, word_of_bytes_be_def,
        word_to_bytes_word_of_bytes_256, TAKE_LENGTH_TOO_LONG,
        word_of_bytes_replicate_zero, wordsTheory.w2w_0]) >>
  gvs[typed_val_to_w256_def] >>
  AP_TERM_TAC >>
  `LENGTH (PAD_LEFT 0w 32 (word_to_bytes addr T)) = 32` by
    simp[PAD_LEFT, LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  metis_tac[rich_listTheory.TAKE_LENGTH_APPEND]
QED

(* The operands are words (bytes32, and uint8, uint256 or bytes32), lowered
   to stack values in order as the source evaluates them; the fragment after
   them only writes its own two fresh buffers, so the operands' variables
   and every live allocation are kept. *)
Theorem ecrecover_code_shape[local]:
  compile_ecrecover h v r s sa = (op,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  simp[compile_ecrecover_def, contextTheory.compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       same_blocks_def, mk_inst_def, is_terminator_def]
QED

Theorem ecrecover_run_frag[local]:
  compile_ecrecover h v r sig sa = (op,sb) /\
  (!s. P s ==> ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       Q (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
  frag_exec ctx sa sb P Q R
Proof
  strip_tac >> drule ecrecover_code_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]
QED

(* A scratch write frames every earlier allocation, including reused ones. *)
Theorem scratch_mstore_frame:
  (!aid b sz. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     a + 32 <= b \/ b + sz <= a) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint a 32 b sz) ==>
  wb_frame cenv es sa s (mstore a w s)
Proof
  strip_tac >> rewrite_tac[wb_frame_def] >>
  conj_tac >- simp[mstore_def] >>
  conj_tac >- simp[mstore_def] >>
  conj_tac
  >- (rpt strip_tac >>
      irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
      first_x_assum drule >> simp[]) >>
  (* the locals: the word lands outside their regions *)
  irule locals_kept_regions >> rpt strip_tac >>
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  first_x_assum drule >> simp[compileEnvTheory.regions_disjoint_def]
QED

(* Appending a word by MSTORE does not disturb the serialized prefix. *)
Theorem mem_bytes_at_store_append:
  mem_bytes_at a n s.vs_memory = bs ==>
  mem_bytes_at a (n + 32) (mstore (a+n) w s).vs_memory =
    bs ++ word_to_bytes w T
Proof
  strip_tac >>
  rewrite_tac[valueEncodingProofsTheory.mem_bytes_at_split_padded,
              mem_bytes_at_mstore_same] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  simp[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint]
QED

(* Shared three-word prefix: ECMul uses exactly this input layout, while
   ECAdd and ecrecover append a fourth word. *)
Theorem scratch_three_word_stores:
  mem_bytes_at a 96
    (mstore (a+64) r (mstore (a+32) v (mstore a h s))).vs_memory =
    word_to_bytes h T ++ word_to_bytes v T ++ word_to_bytes r T
Proof
  `mem_bytes_at a 32 (mstore a h s).vs_memory = word_to_bytes h T`
    by simp[mem_bytes_at_mstore_same] >>
  drule mem_bytes_at_store_append >>
  disch_then (qspec_then `v` assume_tac) >>
  gvs[] >>
  drule mem_bytes_at_store_append >>
  disch_then (qspec_then `r` mp_tac) >>
  simp[APPEND_ASSOC]
QED

Theorem scratch_four_word_stores:
  mem_bytes_at a 128
    (mstore (a+96) sig
      (mstore (a+64) r (mstore (a+32) v (mstore a h s)))).vs_memory =
    word_to_bytes h T ++ word_to_bytes v T ++
    word_to_bytes r T ++ word_to_bytes sig T
Proof
  assume_tac scratch_three_word_stores >>
  drule mem_bytes_at_store_append >>
  disch_then (qspec_then `sig` mp_tac) >>
  simp[APPEND_ASSOC]
QED

(* Frozen baseline instance of the shared four-word serialization. *)
Theorem ecrecover_input_stores[local]:
  mem_bytes_at a 128
    (mstore (a+96) sig
      (mstore (a+64) r (mstore (a+32) v (mstore a h s)))).vs_memory =
    word_to_bytes h T ++ word_to_bytes v T ++
    word_to_bytes r T ++ word_to_bytes sig T
Proof
  simp[scratch_four_word_stores]
QED

Theorem ecrecover_input_stores_shape[local]:
  (do emit_void MSTORE [base_op; h];
      p1 <- emit_op ADD [base_op; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [base_op; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [base_op; Lit 96w];
      emit_void MSTORE [p3; sig]
   od) sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\ sb.cs_next_id = sa.cs_next_id + 7
Proof
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

Theorem ecrecover_lookup_generated_update[local]:
  not_fresh_at sa x /\ sa.cs_next_var <= k ==>
  lookup_var x (update_var (STRING #"%" (toString k)) z t) = lookup_var x t
Proof
  simp[not_fresh_at_def, emitHelperPropsTheory.lookup_var_update_var] >>
  metis_tac[]
QED

Theorem ecrecover_operand_generated_update[local]:
  (!x. q = Var x ==> not_fresh_at sa x) /\ sa.cs_next_var <= k ==>
  eval_operand q (update_var (STRING #"%" (toString k)) z t) = eval_operand q t
Proof
  Cases_on `q` >> simp[eval_operand_def] >>
  metis_tac[ecrecover_lookup_generated_update]
QED

Theorem ecrecover_operand_mstore[local]:
  eval_operand q (mstore a z t) = eval_operand q t
Proof
  Cases_on `q` >> simp[eval_operand_def, mstore_def, lookup_var_def]
QED

Theorem ecrecover_input_stores_run[local]:
  (do emit_void MSTORE [base_op; h];
      p1 <- emit_op ADD [base_op; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [base_op; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [base_op; Lit 96w];
      emit_void MSTORE [p3; sig]
   od) sa = ((),sb) /\
  eval_operand base_op s = SOME p /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [base_op;h;v;r;sig] ==> not_fresh_at sa x) /\
  w2n p + 128 < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n p+96) ws (mstore (w2n p+64) wr
        (mstore (w2n p+32) wv (mstore (w2n p) wh s)))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >>
  `!q k z t. MEM q [base_op;h;v;r;sig] /\ sa.cs_next_var <= k ==>
     eval_operand q (update_var (STRING #"%" (toString k)) z t) =
     eval_operand q t` by
    (rpt strip_tac >> irule ecrecover_operand_generated_update >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
       exec_write2_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
       exec_pure2_def, bind_outputs_def, eval_operand_def,
       ecrecover_operand_mstore] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_write2_def,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_pure2_def,
       bind_outputs_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_write2_def,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_pure2_def,
       bind_outputs_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_write2_def,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  simp[run_inst_seq_def] >>
  `w2n (p+32w) = w2n p + 32 /\
   w2n (p+64w) = w2n p + 64 /\
   w2n (p+96w) = w2n p + 96` by
    (rpt conj_tac >> irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >>
     decide_tac) >>
  qpat_x_assum `!q k z t. _` kall_tac >>
  simp[GSYM dftCommutationTheory.update_var_mstore_commute] >>
  `!a z t m vs. (mstore a z t) with <|vs_memory := m; vs_vars := vs|> =
     t with <|vs_memory := m; vs_vars := vs|>` by simp[mstore_def] >>
  conj_tac >- simp[update_var_def] >>
  rpt strip_tac >> simp[emitHelperPropsTheory.lookup_var_update_var] >>
  gvs[not_fresh_at_def]
QED

Theorem scratch_memory_frame:
  stmt_state_rel ctx func cenv cx es s /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!b sz. compileEnv$regions_disjoint scratch_base scratch_len b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    compileEnv$regions_disjoint scratch_base scratch_len b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    compileEnv$regions_disjoint scratch_base scratch_len b sz) /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
      SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name =
      SOME (tv,iv) ==>
    regions_disjoint scratch_base scratch_len off (type_memory_size tv)) ==>
  stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sc s t
Proof
  strip_tac >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
      (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
  conj_tac
  >- (irule literal_state_memory_frame >> qexists_tac `s` >> simp[] >>
      conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
      conj_tac
      >- (rpt strip_tac >> first_x_assum irule >>
          gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
      conj_tac
      >- (rpt strip_tac >>
          drule_all local_ptrs_reserved_imm_base >> strip_tac >>
          qpat_x_assum `!x. not_fresh_at sa x ==> _` irule >>
          first_assum ACCEPT_TAC) >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  `locals_kept cenv es s t` by
    (irule locals_kept_regions >> rpt strip_tac >>
     first_x_assum irule >> metis_tac[]) >>
  simp[wb_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sa x` by
        (gvs[not_fresh_at_def] >>
         metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem ecrecover_input_stores_sim[local]:
  (do emit_void MSTORE [base_op; h];
      p1 <- emit_op ADD [base_op; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [base_op; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [base_op; Lit 96w];
      emit_void MSTORE [p3; sig]
   od) sa = ((),sb) /\
  eval_operand base_op s = SOME p /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [base_op;h;v;r;sig] ==> not_fresh_at sa x) /\
  w2n p + 128 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint (w2n p) 128 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n p) 128 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,iv) ==>
     regions_disjoint (w2n p) 128 off (type_memory_size tv)) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n p+96) ws (mstore (w2n p+64) wr
        (mstore (w2n p+32) wv (mstore (w2n p) wh s)))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sc s t /\
    mem_bytes_at (w2n p) 128 t.vs_memory =
      word_to_bytes wh T ++ word_to_bytes wv T ++
      word_to_bytes wr T ++ word_to_bytes ws T
Proof
  rpt strip_tac >> drule_all ecrecover_input_stores_run >> strip_tac >>
  `!b len. regions_disjoint (w2n p) 128 b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     `b + len <= w2n p \/ w2n p + 128 <= b` by
       gvs[compileEnvTheory.regions_disjoint_def] >>
     simp[mstore_mem_bytes_at_disjoint]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (simp[immutableMemoryFrameTheory.immutable_mstore_capacity] >> decide_tac) >>
  drule_all scratch_memory_frame >> strip_tac >>
  qexists_tac `t` >> simp[scratch_four_word_stores]
QED

Theorem allocated_payload_shape:
  (do ib <- context$compile_alloc_buffer ni;
      payload ib;
      ob <- context$compile_alloc_buffer no;
      return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sc) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sc) ==> MEM i (fn_insts func)) /\
  (!ib sa sb. payload ib sa = ((),sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id) ==>
  ?ib sa sb ob.
    context$compile_alloc_buffer ni sf = (ib,sa) /\
    payload ib sa = ((),sb) /\
    context$compile_alloc_buffer no sb = (ob,sc) /\
    ip = ib.buf_operand /\ op = ob.buf_operand /\
    emitted_insts sf sc = emitted_insts sf sa ++ emitted_insts sa sb ++
      emitted_insts sb sc /\ same_blocks sf sc /\
    sc.cs_current_insts = sf.cs_current_insts ++ emitted_insts sf sc /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit (n2w ni)]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w no)]
      [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
    local_ptrs_reserved cenv sc /\
    sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_next_var <= sc.cs_next_var /\
    sf.cs_next_id < sa.cs_next_id /\ sa.cs_next_id <= sb.cs_next_id /\
    sb.cs_next_id < sc.cs_next_id /\
    (?x. ip = Var x /\ not_fresh_at sa x /\ not_fresh_at sc x) /\
    (?x. op = Var x /\ not_fresh_at sc x)
Proof
  strip_tac >>
  qpat_x_assum `_ sf = ((ip,op),sc)` mp_tac >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >>
  rename1 `context$compile_alloc_buffer ni sf = (ib,sa)` >>
  simp[Once comp_ignore_bind_def, Once comp_bind_def] >>
  pairarg_tac >> simp[] >> rename1 `payload ib sa = (u,sb)` >>
  Cases_on `u` >> simp[Once comp_bind_def] >> pairarg_tac >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `context$compile_alloc_buffer no sb = (ob,sc)` >>
  first_x_assum drule >> strip_tac >>
  qpat_assum `context$compile_alloc_buffer ni _ = _`
    (strip_assume_tac o MATCH_MP compile_alloc_buffer_insts) >>
  qpat_assum `context$compile_alloc_buffer no _ = _`
    (strip_assume_tac o MATCH_MP compile_alloc_buffer_insts) >>
  `emitted_insts sf sc = emitted_insts sf sa ++
     emitted_insts sa sb ++ emitted_insts sb sc` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1] >>
     simp[emitted_insts_def, NoAsms] >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  `MEM (mk_inst sf.cs_next_id ALLOCA [Lit (n2w ni)]
       [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func)` by
    (first_x_assum irule >>
     qpat_x_assum `emitted_insts sf sc = _` SUBST1_TAC >>
     simp[] >> disj1_tac >> disj1_tac >>
     simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w no)]
       [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func)` by
    (first_x_assum irule >>
     qpat_x_assum `emitted_insts sf sc = _` SUBST1_TAC >>
     simp[] >> disj2_tac >> once_rewrite_tac[emitted_insts_def] >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  qpat_assum `context$compile_alloc_buffer ni _ = _`
    (strip_assume_tac o MATCH_MP compile_alloc_buffer_parts) >>
  qpat_assum `context$compile_alloc_buffer no _ = _`
    (strip_assume_tac o MATCH_MP compile_alloc_buffer_parts) >>
  `emitted_insts sf sa =
     [mk_inst sf.cs_next_id ALLOCA [Lit (n2w ni)]
       [STRING #"%" (toString sf.cs_next_var)]] /\
   emitted_insts sb sc =
     [mk_inst sb.cs_next_id ALLOCA [Lit (n2w no)]
       [STRING #"%" (toString sb.cs_next_var)]]` by
    (conj_tac >> once_rewrite_tac[emitted_insts_def] >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  fs[same_blocks_def] >>
  rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[])
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[])
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[]) >>
  simp[not_fresh_at_def] >> decide_tac
QED

Theorem ecrecover_buffers_prefix_shape[local]:
  (do ib <- context$compile_alloc_buffer 128;
      emit_void MSTORE [ib.buf_operand; h];
      p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
      emit_void MSTORE [p3; sig];
      ob <- context$compile_alloc_buffer 32;
      emit_void MSTORE [ob.buf_operand; Lit 0w];
      return (ib.buf_operand,ob.buf_operand)
   od) sf = ((ip,op),sm) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)) ==>
  ?ib ob sa sb sc.
    ip = ib.buf_operand /\ op = ob.buf_operand /\
    context$compile_alloc_buffer 128 sf = (ib,sa) /\
    (do emit_void MSTORE [ib.buf_operand; h];
        p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [p1; v];
        p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [p2; r];
        p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
        emit_void MSTORE [p3; sig] od) sa = ((),sb) /\
    context$compile_alloc_buffer 32 sb = (ob,sc) /\
    emit_void MSTORE [ob.buf_operand; Lit 0w] sc = ((),sm) /\
    emitted_insts sf sc = emitted_insts sf sa ++ emitted_insts sa sb ++
      emitted_insts sb sc /\
    emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sb ++
      emitted_insts sb sc ++ emitted_insts sc sm /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sb.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
    local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sm /\
    sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= sm.cs_next_var /\
    sf.cs_next_id < sa.cs_next_id /\ sa.cs_next_id < sb.cs_next_id /\
    sb.cs_next_id < sc.cs_next_id /\ sc.cs_next_id < sm.cs_next_id /\
    (?x. ip = Var x /\ not_fresh_at sm x) /\
    (?x. op = Var x /\ not_fresh_at sm x)
Proof
  rpt strip_tac >>
  ` (do ib <- context$compile_alloc_buffer 128;
        (do emit_void MSTORE [ib.buf_operand; h];
            p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
            emit_void MSTORE [p1; v];
            p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
            emit_void MSTORE [p2; r];
            p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
            emit_void MSTORE [p3; sig] od);
        ob <- context$compile_alloc_buffer 32;
        emit_void MSTORE [ob.buf_operand; Lit 0w];
        return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm)` by
    (simp[comp_ignore_bind_def, comp_bind_assoc] >>
     simp[GSYM comp_ignore_bind_def]) >>
  pop_assum mp_tac >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >>
  rename1 `context$compile_alloc_buffer 128 sf = (ib,sa)` >>
  simp[Once comp_ignore_bind_def, Once comp_bind_def] >>
  pairarg_tac >> simp[] >>
  rename1 `_ sa = (u,sb)` >> Cases_on `u` >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >>
  rename1 `context$compile_alloc_buffer 32 sb = (ob,sc)` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_void MSTORE _ sc = (u0,_)` >> Cases_on `u0` >> gvs[] >>
  rename1 `emit_void MSTORE _ sc = ((),sm)` >>
  ` (do ib <- context$compile_alloc_buffer 128;
        (do emit_void MSTORE [ib.buf_operand; h];
            p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
            emit_void MSTORE [p1; v];
            p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
            emit_void MSTORE [p2; r];
            p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
            emit_void MSTORE [p3; sig] od);
        ob <- context$compile_alloc_buffer 32;
        return (ib.buf_operand,ob.buf_operand) od) sf =
      ((ib.buf_operand,ob.buf_operand),sc)` by
    (simp[Once comp_bind_def] >>
     simp[Once comp_ignore_bind_def, Once comp_bind_def] >>
     simp[comp_bind_def, comp_return_def]) >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  `sc.cs_current_insts = sf.cs_current_insts ++ emitted_insts sf sc` by
    (drule ecrecover_input_stores_shape >> strip_tac >>
     qpat_assum `context$compile_alloc_buffer 128 _ = _`
       (strip_assume_tac o MATCH_MP compile_alloc_buffer_insts) >>
     qpat_assum `context$compile_alloc_buffer 32 _ = _`
       (strip_assume_tac o MATCH_MP compile_alloc_buffer_insts) >>
     once_rewrite_tac[emitted_insts_def] >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  `emitted_insts sf sm = emitted_insts sf sc ++ emitted_insts sc sm` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  drule (BETA_RULE (Q.INST [`payload` |->
    `\ib. do emit_void MSTORE [ib.buf_operand; h];
             p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
             emit_void MSTORE [p1; v];
             p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
             emit_void MSTORE [p2; r];
             p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
             emit_void MSTORE [p3; sig] od`] (SPEC_ALL allocated_payload_shape))) >>
  disch_then (qspecl_then [`func`, `cenv`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> drule ecrecover_input_stores_shape >> simp[]) >>
  strip_tac >> gvs[] >>
  drule ecrecover_input_stores_shape >> strip_tac >> simp[] >>
  rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sc` >> simp[]) >>
  gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Preserve the baseline interface; execution also uses the prefix split. *)
Theorem ecrecover_buffers_shape[local]:
  (do ib <- context$compile_alloc_buffer 128;
      emit_void MSTORE [ib.buf_operand; h];
      p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
      emit_void MSTORE [p3; sig];
      ob <- context$compile_alloc_buffer 32;
      emit_void MSTORE [ob.buf_operand; Lit 0w];
      return (ib.buf_operand,ob.buf_operand)
   od) sf = ((ip,op),sm) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)) ==>
  ?ib ob sa sb sc.
    ip = ib.buf_operand /\ op = ob.buf_operand /\
    context$compile_alloc_buffer 128 sf = (ib,sa) /\
    (do emit_void MSTORE [ib.buf_operand; h];
        p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [p1; v];
        p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [p2; r];
        p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
        emit_void MSTORE [p3; sig] od) sa = ((),sb) /\
    context$compile_alloc_buffer 32 sb = (ob,sc) /\
    emit_void MSTORE [ob.buf_operand; Lit 0w] sc = ((),sm) /\
    emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sb ++
      emitted_insts sb sc ++ emitted_insts sc sm /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sb.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
    local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sm /\
    sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= sm.cs_next_var /\
    sf.cs_next_id < sa.cs_next_id /\ sa.cs_next_id < sb.cs_next_id /\
    sb.cs_next_id < sc.cs_next_id /\ sc.cs_next_id < sm.cs_next_id /\
    (?x. ip = Var x /\ not_fresh_at sm x) /\
    (?x. op = Var x /\ not_fresh_at sm x)
Proof
  strip_tac >> drule_all ecrecover_buffers_prefix_shape >> strip_tac >>
  qexistsl_tac [`ib`, `ob`, `sa`, `sb`, `sc`] >> simp[] >> metis_tac[]
QED

Theorem state_allocations_disjoint:
  stmt_state_rel ctx func cenv cx es t /\
  FLOOKUP t.vs_allocas a = SOME (p,n) /\
  FLOOKUP t.vs_allocas b = SOME (q,m) /\ a <> b ==>
  regions_disjoint p n q m
Proof
  simp[stmt_state_rel_def, alloca_inv_def, allocas_non_overlapping_def,
       compileEnvTheory.regions_disjoint_def] >>
  strip_tac >> first_x_assum drule >>
  disch_then drule >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem alloc_buffer_finish:
  context$compile_alloc_buffer outsz sb = (ob,sm) /\
  stmt_state_rel ctx func cenv cx es u /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sb /\ outsz < dimword (:256) /\
  MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w outsz)]
    [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func) /\
  sf.cs_next_id <= sb.cs_next_id /\ sf.cs_next_var <= sb.cs_next_var /\
  local_ptrs_reserved cenv sf /\ stmt_state_rel ctx func cenv cx es s /\
  wb_frame cenv es sf s u /\
  (!x. not_fresh_at sf x ==> lookup_var x u = lookup_var x s) /\
  eval_operand ip u = SOME input_word /\
  (!x. ip = Var x ==> not_fresh_at sb x) ==>
  ?t po. run_inst_seq (emitted_insts sb sm) u = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sf s t /\
    eval_operand ip t = SOME input_word /\ eval_operand ob.buf_operand t = SOME po /\
    t.vs_memory = u.vs_memory /\
    (!aid entry. FLOOKUP u.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    FLOOKUP t.vs_allocas sb.cs_next_id = SOME (w2n po,outsz) /\
    w2n po + outsz < dimword (:256) /\
    (!old b sz. old < sf.cs_next_id /\ FLOOKUP t.vs_allocas old = SOME (b,sz) ==>
      regions_disjoint (w2n po) outsz b sz) /\
    (!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n po) outsz b sz) /\
    (!x. not_fresh_at sf x ==> lookup_var x t = lookup_var x s) /\
    sb.cs_next_id < sm.cs_next_id /\
    (?x. ob.buf_operand = Var x /\ not_fresh_at sm x) /\
    (!x. ip = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >>
  qpat_x_assum `stmt_state_rel ctx func cenv cx es s` mp_tac >>
  drule_all alloc_buffer_frame_run >> strip_tac >> disch_tac >>
  `wb_frame cenv es sf s t` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`es`,`sb`,`u`] >> simp[]) >>
     qexistsl_tac [`ctx`,`cx`,`func`] >> simp[]) >>
  `!old b sz. old < sf.cs_next_id /\ FLOOKUP t.vs_allocas old = SOME (b,sz) ==>
    regions_disjoint (w2n w) outsz b sz` by
    (rpt strip_tac >> irule state_allocations_disjoint >>
     qexistsl_tac [`sb.cs_next_id`, `old`, `cenv`,`ctx`,`cx`,`es`,`func`, `t`] >>
     simp[] >> decide_tac) >>
  `!z. not_fresh_at sf z ==> lookup_var z t = lookup_var z s` by
    (qx_gen_tac `z` >> strip_tac >>
     `not_fresh_at sb z` by
       (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >> simp[]) >>
  `eval_operand ip t = SOME input_word` by
    (Cases_on `ip` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `sb.cs_next_var <= sm.cs_next_var` by
    (qpat_x_assum `context$compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, emitHelperTheory.emit_op_def,
          fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[]) >>
  qexistsl_tac [`t`,`w`] >> simp[] >> rpt strip_tac >>
  gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Shared input allocation, payload execution and output allocation. *)
Theorem allocated_payload_run:
  context$compile_alloc_buffer insz sf = (ib,sa) /\
  context$compile_alloc_buffer outsz sb = (ob,sm) /\
  emitted_insts sf sm = emitted_insts sf sa ++ code ++ emitted_insts sb sm /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sb /\
  insz < dimword (:256) /\ outsz < dimword (:256) /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit (n2w insz)]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w outsz)]
    [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func) /\
  sa.cs_next_id <= sb.cs_next_id /\
  sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
  (!s1 wi.
    run_inst_seq (emitted_insts sf sa) s = OK s1 /\
    stmt_state_rel ctx func cenv cx es s1 /\
    eval_operand ib.buf_operand s1 = SOME wi /\
    FLOOKUP s1.vs_allocas sf.cs_next_id = SOME (w2n wi,insz) /\
    w2n wi + insz < dimword (:256) /\ s1.vs_memory = s.vs_memory /\
    wb_frame cenv es sf s s1 /\ s1.vs_labels = s.vs_labels /\
    (!name b len. local_region cenv es.scopes s1 name b len ==>
      regions_disjoint (w2n wi) insz b len) /\
    (!aid b len. aid < sf.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n wi) insz b len) /\
    (!aid b len. aid < sf.cs_next_id /\
      FLOOKUP s1.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n wi) insz b len) /\
    (!x. not_fresh_at sf x ==> lookup_var x s1 = lookup_var x s) ==>
    ?u. run_inst_seq code s1 = OK u /\ stmt_state_rel ctx func cenv cx es u /\
      wb_frame cenv es sf s1 u /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s1) /\
      FLOOKUP u.vs_allocas sf.cs_next_id = SOME (w2n wi,insz) /\
      eval_operand ib.buf_operand u = SOME wi /\
      mem_bytes_at (w2n wi) insz u.vs_memory = bytes) ==>
  ?t pi po. run_inst_seq (emitted_insts sf sm) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sf s t /\
    eval_operand ib.buf_operand t = SOME pi /\
    eval_operand ob.buf_operand t = SOME po /\
    w2n pi + insz < dimword (:256) /\ w2n po + outsz < dimword (:256) /\
    mem_bytes_at (w2n pi) insz t.vs_memory = bytes /\
    FLOOKUP t.vs_allocas sb.cs_next_id = SOME (w2n po,outsz) /\
    sf.cs_next_id <= sb.cs_next_id /\ sb.cs_next_id < sm.cs_next_id /\
    regions_disjoint (w2n po) outsz (w2n pi) insz /\
    (!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n po) outsz b sz) /\
    (!old b sz. old < sf.cs_next_id /\
      FLOOKUP t.vs_allocas old = SOME (b,sz) ==>
      regions_disjoint (w2n po) outsz b sz) /\
    (!x. not_fresh_at sf x ==> lookup_var x t = lookup_var x s) /\
    (?x. ib.buf_operand = Var x /\ not_fresh_at sm x) /\
    (?x. ob.buf_operand = Var x /\ not_fresh_at sm x)
Proof
  strip_tac >>
  `?s1 wi. run_inst_seq (emitted_insts sf sa) s = OK s1 /\
    stmt_state_rel ctx func cenv cx es s1 /\
    eval_operand ib.buf_operand s1 = SOME wi /\
    FLOOKUP s1.vs_allocas sf.cs_next_id = SOME (w2n wi,insz) /\
    w2n wi + insz < dimword (:256) /\ s1.vs_memory = s.vs_memory /\
    sf.cs_next_id < sa.cs_next_id /\
    (!x. not_fresh_at sf x ==> lookup_var x s1 = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP s1.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sf.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n wi) insz b len) /\
    (!name b len. local_region cenv es.scopes s1 name b len ==>
      regions_disjoint (w2n wi) insz b len) /\
    (?p. ib.buf_operand = Var p /\ not_fresh_at sa p) /\
    s1.vs_labels = s.vs_labels /\ wb_frame cenv es sf s s1` by
    (irule alloc_buffer_frame_run >> simp[]) >>
  `!aid b len. aid < sf.cs_next_id /\
    FLOOKUP s1.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n wi) insz b len` by
    (rpt strip_tac >> irule state_allocations_disjoint >>
     qexistsl_tac [`sf.cs_next_id`,`aid`,`cenv`,`ctx`,`cx`,`es`,`func`,`s1`] >>
     simp[] >> decide_tac) >>
  qpat_x_assum `!s1 wi. _` (qspecl_then [`s1`,`wi`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `sf.cs_next_id <= sb.cs_next_id` by decide_tac >>
  `sf.cs_next_var <= sb.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sf x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by (gvs[not_fresh_at_def] >> decide_tac) >>
     simp[]) >>
  `wb_frame cenv es sf s u` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`es`,`sf`,`s1`] >> simp[]) >>
     qexistsl_tac [`ctx`,`cx`,`func`] >> simp[]) >>
  `!x. ib.buf_operand = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >> decide_tac) >>
  qpat_x_assum `wb_frame cenv es sf s s1` kall_tac >>
  qpat_x_assum `stmt_state_rel ctx func cenv cx es s1` kall_tac >>
  qpat_x_assum `wb_frame cenv es sf s1 u` kall_tac >>
  `eval_operand ib.buf_operand u = SOME wi` by simp[] >>
  drule_all alloc_buffer_finish >> strip_tac >>
  `FLOOKUP t.vs_allocas sf.cs_next_id = SOME (w2n wi,insz)` by
    metis_tac[] >>
  `regions_disjoint (w2n po) outsz (w2n wi) insz` by
    (irule state_allocations_disjoint >>
     qexistsl_tac [`sb.cs_next_id`,`sf.cs_next_id`,`cenv`,`ctx`,`cx`,`es`,`func`,`t`] >>
     simp[] >> decide_tac) >>
  qexistsl_tac [`t`,`wi`,`po`] >>
  conj_tac
  >- (asm_rewrite_tac[] >>
      qpat_x_assum `run_inst_seq (emitted_insts sf sa) s = OK s1` mp_tac >>
      qpat_x_assum `run_inst_seq code s1 = OK u` mp_tac >>
      qpat_x_assum `run_inst_seq (emitted_insts sb sm) u = OK t` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[run_inst_seq_append]) >>
  gvs[arithmeticTheory.ADD_COMM] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem precompile_alloca_immutable_disjoint:
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,iv) ==>
     regions_disjoint b sz off (type_memory_size tv))
Proof
  strip_tac >>
  qpat_x_assum `stmt_state_rel ctx _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >>
  strip_tac >> rpt strip_tac >>
  qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _` drule_all >>
  simp[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem ecrecover_buffers_run[local]:
  (do ib <- context$compile_alloc_buffer 128;
      emit_void MSTORE [ib.buf_operand; h];
      p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
      emit_void MSTORE [p3; sig];
      ob <- context$compile_alloc_buffer 32;
      emit_void MSTORE [ob.buf_operand; Lit 0w];
      return (ib.buf_operand,ob.buf_operand)
   od) sf = ((ip,op),sm) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sf x) ==>
  ?t pi po. run_inst_seq (emitted_insts sf sm) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sf s t /\
    eval_operand ip t = SOME pi /\ eval_operand op t = SOME po /\
    w2n pi + 128 < dimword (:256) /\ w2n po + 32 < dimword (:256) /\
    mem_bytes_at (w2n pi) 128 t.vs_memory =
      word_to_bytes wh T ++ word_to_bytes wv T ++
      word_to_bytes wr T ++ word_to_bytes ws T /\
    mem_word_at (w2n po) t.vs_memory = 0w /\
    (!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n po) 32 b sz) /\
    (!aid b sz. aid < sf.cs_next_id /\
      FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint (w2n po) 32 b sz) /\
    (cenv.ce_is_ctor ==> !name tv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name =
         SOME (tv,iv) ==>
       regions_disjoint (w2n po) 32 off (type_memory_size tv)) /\
    (!x. not_fresh_at sf x ==> lookup_var x t = lookup_var x s) /\
    (?x. ip = Var x /\ not_fresh_at sm x) /\
    (?x. op = Var x /\ not_fresh_at sm x)
Proof
  rpt strip_tac >> drule_all ecrecover_buffers_prefix_shape >> strip_tac >>
  qpat_x_assum `_ sf = ((ip,op),sm)` kall_tac >>
  `128 < dimword (:256) /\ 32 < dimword (:256)` by
    simp[wordsTheory.dimword_def] >>
  mp_tac (Q.INST [`insz` |-> `128`, `outsz` |-> `32`,
    `sm` |-> `sc`, `code` |-> `emitted_insts sa sb`,
    `bytes` |-> `word_to_bytes (wh:256 word) T ++ word_to_bytes (wv:256 word) T ++
                word_to_bytes (wr:256 word) T ++ word_to_bytes (ws:256 word) T`]
    (SPEC_ALL allocated_payload_run)) >>
  (impl_tac >- (
    simp[] >> rpt strip_tac >>
    `!z. MEM z [h;v;r;sig] ==> eval_operand z s1 = eval_operand z s` by
      (rpt strip_tac >> Cases_on `z` >>
       simp[eval_operand_def] >> metis_tac[]) >>
    `eval_operand h s1 = SOME wh /\ eval_operand v s1 = SOME wv /\
     eval_operand r s1 = SOME wr /\ eval_operand sig s1 = SOME ws` by
      metis_tac[listTheory.MEM] >>
    `!x. MEM (Var x) [ib.buf_operand;h;v;r;sig] ==> not_fresh_at sa x` by
      (qpat_x_assum `!x. MEM (Var x) [h;v;r;sig] ==> _` mp_tac >>
       qpat_x_assum `context$compile_alloc_buffer 128 sf = (ib,sa)`
         (mp_tac o MATCH_MP compile_alloc_buffer_parts) >>
       POP_ASSUM_LIST (K all_tac) >> simp[listTheory.MEM] >> metis_tac[]) >>
    `sf.cs_next_id <= sa.cs_next_id` by decide_tac >>
    `cenv.ce_is_ctor ==> !name tv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name =
         SOME (tv,iv) ==>
       regions_disjoint (w2n wi) 128 off (type_memory_size tv)` by
      (match_mp_tac (Q.INST
         [`s` |-> `s1`, `inst` |-> `mk_inst sf.cs_next_id ALLOCA [Lit 128w]
           [STRING #"%" (toString sf.cs_next_var)]`]
         precompile_alloca_immutable_disjoint) >>
       simp[mk_inst_def]) >>
    drule_all ecrecover_input_stores_sim >> strip_tac >>
    `t.vs_allocas = s1.vs_allocas` by
      (qpat_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
        (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
    `eval_operand ib.buf_operand t = SOME wi` by
      (Cases_on `ib.buf_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
    qexists_tac `t` >> simp[])) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sf sc) s = OK s3` >>
  rename1 `eval_operand ib.buf_operand s3 = SOME wi` >>
  rename1 `eval_operand ob.buf_operand s3 = SOME wo` >>
  `eval_operand (Lit 0w) s3 = SOME 0w` by simp[eval_operand_def] >>
  drule_all literal_emit_mstore_run >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es (mstore (w2n wo) 0w s3)` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`w2n wo`,
       `mk_inst sb.cs_next_id ALLOCA [Lit 32w]
         [STRING #"%" (toString sb.cs_next_var)]`, `32`] >> simp[mk_inst_def] >>
     gvs[compileEnvTheory.regions_disjoint_def]) >>
  `!aid b sz. aid < sf.cs_next_id /\
     FLOOKUP s3.vs_allocas aid = SOME (b,sz) ==>
     w2n wo + 32 <= b \/ b + sz <= w2n wo` by
    (gvs[compileEnvTheory.regions_disjoint_def]) >>
  `wb_frame cenv es sf s3 (mstore (w2n wo) 0w s3)` by
    (irule scratch_mstore_frame >> conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es sf s (mstore (w2n wo) 0w s3)` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`es`,`sf`,`s3`] >> simp[]) >>
     qexistsl_tac [`ctx`,`cx`,`func`] >> simp[]) >>
  qexistsl_tac [`mstore (w2n wo) 0w s3`,`wi`,`wo`] >>
  conj_tac
  >- (`emitted_insts sf sm = emitted_insts sf sc ++ emitted_insts sc sm` by
        metis_tac[APPEND_ASSOC] >>
      qpat_x_assum `emitted_insts sf sm = emitted_insts sf sc ++ _` SUBST1_TAC >>
      qpat_x_assum `run_inst_seq (emitted_insts sf sc) s = OK s3` mp_tac >>
      qpat_x_assum `run_inst_seq (emitted_insts sc sm) s3 = _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[run_inst_seq_append]) >>
  simp[] >>
  conj_tac
  >- (gvs[eval_operand_def, mstore_def] >>
      `not_fresh_at sb p` by
        (gvs[not_fresh_at_def] >>
         metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
      metis_tac[]) >>
  conj_tac >- gvs[eval_operand_def, mstore_def] >>
  conj_tac
  >- (`mem_bytes_at (w2n wi) 128 (mstore (w2n wo) 0w s3).vs_memory =
         mem_bytes_at (w2n wi) 128 s3.vs_memory` by
        (irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
         gvs[compileEnvTheory.regions_disjoint_def]) >> simp[]) >>
  simp[valueEncodingPropsTheory.mstore_mem_word_at_same] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name b len. local_region _ _ s3 _ _ _ ==> _` irule >>
      qexists_tac `name` >>
      gvs[local_region_def, mstore_def]) >>
  simp[mstore_def] >> conj_tac >- first_assum ACCEPT_TAC >>
  match_mp_tac (Q.INST
    [`s` |-> `s3`, `inst` |-> `mk_inst sb.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sb.cs_next_var)]`]
    precompile_alloca_immutable_disjoint) >>
  simp[mk_inst_def]
QED

(* Specialize the computed-call boundary to a successful concrete response. *)
Theorem computed_static_exec_success:
  rq = venom_call_request s addr 0w ai an T /\
  precompile_result rq.cr_target rq.cr_data = SOME (SOME data) /\
  inst.inst_outputs = [out] /\
  (?co rest. s.vs_outcomes = co::rest /\ co.co_success) ==>
  exec_ext_call inst s gas addr 0w ai an ro rs T =
    OK (update_var out 1w
      ((write_memory_with_expansion (w2n ro) (TAKE (w2n rs) data) s)
       with <|vs_returndata := data; vs_outcomes := DROP 1 s.vs_outcomes|>))
Proof
  strip_tac >>
  `computed_precompile rq` by
    simp[computed_precompile_def, venom_call_request_def] >>
  irule computed_static_true_probe >> simp[] >> metis_tac[]
QED

Theorem computed_static_exec_failure:
  rq = venom_call_request s addr 0w ai an T /\
  precompile_result rq.cr_target rq.cr_data = SOME NONE /\
  inst.inst_outputs = [out] ==>
  exec_ext_call inst s gas addr 0w ai an ro rs T =
    OK (update_var out 0w
      ((write_memory_with_expansion (w2n ro) [] s)
       with <|vs_returndata := []; vs_outcomes := DROP 1 s.vs_outcomes|>))
Proof
  strip_tac >>
  `computed_precompile rq` by
    simp[computed_precompile_def, venom_call_request_def] >>
  drule_all computed_static_exec >>
  Cases_on `s.vs_outcomes` >> simp[take_outcome_def]
QED

Theorem ecrecover_output_write[local]:
  mem_word_at off s.vs_memory = 0w /\
  ((data = [] /\ (addr:address) = 0w) \/
    data = PAD_LEFT 0w 32 (word_to_bytes addr T)) ==>
  mem_word_at off
    (write_memory_with_expansion off (TAKE 32 data) s).vs_memory =
    typed_val_to_w256 (BaseTV AddressT) (AddressV addr)
Proof
  strip_tac
  >- (`mem_bytes_at off 32
        (write_memory_with_expansion off [] s).vs_memory =
        mem_bytes_at off 32 s.vs_memory` by
        (irule mem_bytes_at_write_disjoint >> simp[]) >>
      gvs[mem_word_at_def, mem_bytes_at_def] >>
      simp[typed_val_to_w256_def, val_to_w256_address,
           GSYM word_to_bytes_w2w_address, word_of_bytes_be_def,
           word_to_bytes_word_of_bytes_256, TAKE_LENGTH_TOO_LONG,
           word_of_bytes_replicate_zero, wordsTheory.w2w_0]) >>
  `LENGTH data = 32` by
    gvs[PAD_LEFT, LENGTH_word_to_bytes,
        fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  `TAKE 32 data = data` by simp[GSYM LENGTH_NIL, TAKE_LENGTH_TOO_LONG] >>
  `mem_bytes_at off 32
      (write_memory_with_expansion off data s).vs_memory = data` by
    metis_tac[hash_write_memory_read_self] >>
  mp_tac ecrecover_output_encoding >>
  (impl_tac >- simp[]) >>
  gvs[mem_word_at_def, GSYM mem_bytes_at_def, word_of_bytes_be_def,
      TAKE_LENGTH_TOO_LONG] >>
  metis_tac[rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem ecrecover_request_result[local]:
  mem_bytes_at (w2n ai) 128 s.vs_memory =
    word_to_bytes (h:bytes32) T ++ word_to_bytes (v:bytes32) T ++
    word_to_bytes (r:bytes32) T ++ word_to_bytes (sig:bytes32) T ==>
  precompile_result (venom_call_request s 1w 0w ai 128w T).cr_target
    (venom_call_request s 1w 0w ai 128w T).cr_data =
    SOME (SOME (case vfmExecution$ecrecover h (w2n v) (w2n r) (w2n sig) of
      NONE => [] | SOME addr => PAD_LEFT 0w 32 (word_to_bytes addr T)))
Proof
  strip_tac >>
  simp[venom_call_request_def, read_memory_def, GSYM mem_bytes_at_def,
       wordsTheory.dimword_def, wordsTheory.w2w_n2w,
       fcpLib.INDEX_CONV ``dimindex(:160)``, precompile_result_four_words]
QED

Theorem compile_ecrecover_prefix[local]:
  compile_ecrecover h v r sig =
    do bufs <-
         (do ib <- context$compile_alloc_buffer 128;
             emit_void MSTORE [ib.buf_operand; h];
             p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
             emit_void MSTORE [p1; v];
             p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
             emit_void MSTORE [p2; r];
             p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
             emit_void MSTORE [p3; sig];
             ob <- context$compile_alloc_buffer 32;
             emit_void MSTORE [ob.buf_operand; Lit 0w];
             return (ib.buf_operand,ob.buf_operand) od);
       gas <- emit_op GAS [];
       success <- emit_op STATICCALL
         [gas; Lit 1w; FST bufs; Lit 128w; SND bufs; Lit 32w];
       emit_void ASSERT [success];
       emit_op MLOAD [SND bufs]
    od
Proof
  simp[compile_ecrecover_def, comp_ignore_bind_def, comp_bind_assoc] >>
  simp[comp_bind_def, comp_return_def, FUN_EQ_THM]
QED

Theorem computed_suffix_shape:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) ==>
  res = op /\ sb.cs_next_var = sm.cs_next_var + 2 /\
  sb.cs_next_id = sm.cs_next_id + 3 /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  emitted_insts sm sb =
    [mk_inst sm.cs_next_id GAS [] [STRING #"%" (toString sm.cs_next_var)];
     mk_inst (sm.cs_next_id+1) STATICCALL
       [Var (STRING #"%" (toString sm.cs_next_var)); Lit target; ip; Lit insz; op; Lit outsz]
       [STRING #"%" (toString (sm.cs_next_var+1))];
     mk_inst (sm.cs_next_id+2) ASSERT
       [Var (STRING #"%" (toString (sm.cs_next_var+1)))] []]
Proof
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

Theorem computed_suffix_staticcall_dispatch[local]:
  eval_operand gp s = SOME gas /\ eval_operand ap s = SOME addr /\
  eval_operand ip s = SOME ai /\ eval_operand np s = SOME an /\
  eval_operand op s = SOME ro /\ eval_operand zp s = SOME rs ==>
  step_inst_base (mk_inst id STATICCALL [gp; ap; ip; np; op; zp] outs) s =
  exec_ext_call (mk_inst id STATICCALL [gp; ap; ip; np; op; zp] outs)
    s gas addr 0w ai an ro rs T
Proof
  strip_tac >> simp[step_inst_base_def, mk_inst_def]
QED

Theorem computed_suffix_success:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME (SOME data) /\
  (?co rest. s.vs_outcomes = co::rest /\ co.co_success) ==>
  run_inst_seq (emitted_insts sm sb) s =
    OK (update_var (STRING #"%" (toString (sm.cs_next_var+1))) 1w
      ((write_memory_with_expansion (w2n wo) (TAKE (w2n outsz) data)
         (update_var (STRING #"%" (toString sm.cs_next_var))
            (HD (s.vs_gas_readings ++ [0w]))
            (s with vs_gas_readings := DROP 1 s.vs_gas_readings))) with
         <|vs_returndata := data; vs_outcomes := DROP 1 s.vs_outcomes|>))
Proof
  strip_tac >> drule computed_suffix_shape >> strip_tac >>
  qabbrev_tac `g = HD (s.vs_gas_readings ++ [0w:bytes32])` >>
  qabbrev_tac `s0 = s with vs_gas_readings := DROP 1 s.vs_gas_readings` >>
  `!x. eval_operand x s0 = eval_operand x s` by
    (Cases >> simp[Abbr `s0`, eval_operand_def, lookup_var_def]) >>
  qabbrev_tac `sg = update_var (STRING #"%" (toString sm.cs_next_var)) g s0` >>
  `step_inst_base (mk_inst sm.cs_next_id GAS [] [STRING #"%" (toString sm.cs_next_var)]) s =
   OK sg` by simp[Abbr `sg`, Abbr `g`, Abbr `s0`, step_GAS] >>
  `eval_operand ip sg = SOME wi /\ eval_operand op sg = SOME wo` by
    (simp[Abbr `sg`] >>
     metis_tac[eval_operand_update_not_fresh, arithmeticTheory.LESS_EQ_REFL]) >>
  `venom_call_request sg target 0w wi insz T =
   venom_call_request s target 0w wi insz T` by
    simp[Abbr `sg`, Abbr `s0`, venom_call_request_def, update_var_def, read_memory_def] >>
  qabbrev_tac `ci = mk_inst (sm.cs_next_id+1) STATICCALL
    [Var (STRING #"%" (toString sm.cs_next_var)); Lit target; ip; Lit insz; op; Lit outsz]
    [STRING #"%" (toString (sm.cs_next_var+1))]` >>
  qabbrev_tac `sc = update_var (STRING #"%" (toString (sm.cs_next_var+1))) 1w
    ((write_memory_with_expansion (w2n wo) (TAKE (w2n outsz) data) sg)
      with <|vs_returndata := data; vs_outcomes := DROP 1 sg.vs_outcomes|>)` >>
  `exec_ext_call ci sg (g:bytes32) target 0w wi insz wo outsz T =
    OK sc` by
    (qunabbrev_tac `sc` >> irule computed_static_exec_success >>
     simp[Abbr `ci`, mk_inst_def, Abbr `sg`, Abbr `s0`, update_var_def] >> metis_tac[]) >>
  `eval_operand (Var (STRING #"%" (toString sm.cs_next_var))) sg = SOME g` by
    simp[Abbr `sg`, eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `step_inst_base ci sg =
   exec_ext_call ci sg (g:bytes32) target 0w wi insz wo outsz T` by
    (qunabbrev_tac `ci` >>
     irule computed_suffix_staticcall_dispatch >> simp[eval_operand_def]) >>
  `step_inst_base ci sg = OK sc` by simp[] >>
  `step_inst_base (mk_inst (sm.cs_next_id+2) ASSERT
     [Var (STRING #"%" (toString (sm.cs_next_var+1)))] []) sc = OK sc` by
    (irule emitHelperPropsTheory.step_ASSERT_ok >> qexists_tac `1w` >>
     simp[Abbr `sc`, eval_operand_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[Once run_inst_seq_def] >>
  simp[Once run_inst_seq_def] >>
  gvs[mk_inst_def] >>
  simp[run_inst_seq_def, Abbr `sc`, Abbr `sg`, Abbr `s0`]
QED

Theorem computed_suffix_failure:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME NONE ==>
  ?u. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort u
Proof
  strip_tac >> drule computed_suffix_shape >> strip_tac >>
  qabbrev_tac `g = HD (s.vs_gas_readings ++ [0w:bytes32])` >>
  qabbrev_tac `s0 = s with vs_gas_readings := DROP 1 s.vs_gas_readings` >>
  `!x. eval_operand x s0 = eval_operand x s` by
    (Cases >> simp[Abbr `s0`, eval_operand_def, lookup_var_def]) >>
  qabbrev_tac `sg = update_var (STRING #"%" (toString sm.cs_next_var)) g s0` >>
  `step_inst_base (mk_inst sm.cs_next_id GAS [] [STRING #"%" (toString sm.cs_next_var)]) s =
   OK sg` by simp[Abbr `sg`, Abbr `g`, Abbr `s0`, step_GAS] >>
  `eval_operand ip sg = SOME wi /\ eval_operand op sg = SOME wo` by
    (simp[Abbr `sg`] >>
     metis_tac[eval_operand_update_not_fresh, arithmeticTheory.LESS_EQ_REFL]) >>
  `venom_call_request sg target 0w wi insz T =
   venom_call_request s target 0w wi insz T` by
    simp[Abbr `sg`, Abbr `s0`, venom_call_request_def, update_var_def, read_memory_def] >>
  `precompile_result (venom_call_request sg target 0w wi insz T).cr_target
     (venom_call_request sg target 0w wi insz T).cr_data = SOME NONE` by
    metis_tac[] >>
  `computed_precompile (venom_call_request sg target 0w wi insz T)` by
    simp[computed_precompile_def, venom_call_request_def] >>
  `(mk_inst (sm.cs_next_id+1) STATICCALL
     [Var (STRING #"%" (toString sm.cs_next_var)); Lit target; ip; Lit insz; op; Lit outsz]
     [STRING #"%" (toString (sm.cs_next_var+1))]).inst_outputs =
     [STRING #"%" (toString (sm.cs_next_var+1))]` by simp[mk_inst_def] >>
  `exec_ext_call (mk_inst (sm.cs_next_id+1) STATICCALL
     [Var (STRING #"%" (toString sm.cs_next_var)); Lit target; ip; Lit insz; op; Lit outsz]
     [STRING #"%" (toString (sm.cs_next_var+1))]) sg (g:bytes32) target 0w wi insz wo outsz T =
   OK (update_var (STRING #"%" (toString (sm.cs_next_var+1))) 0w
     ((write_memory_with_expansion (w2n wo) [] sg)
       with <|vs_returndata := []; vs_outcomes := DROP 1 sg.vs_outcomes|>))` by
    (qpat_x_assum `venom_call_request _ _ _ _ _ _ = _` kall_tac >>
     irule computed_static_exec_failure >> simp[] >> metis_tac[]) >>
  `eval_operand (Var (STRING #"%" (toString sm.cs_next_var))) sg = SOME g` by
    simp[Abbr `sg`, eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (sm.cs_next_id+1) STATICCALL
     [Var (STRING #"%" (toString sm.cs_next_var)); Lit target; ip; Lit insz; op; Lit outsz]
     [STRING #"%" (toString (sm.cs_next_var+1))]) sg =
   OK (update_var (STRING #"%" (toString (sm.cs_next_var+1))) 0w
     ((write_memory_with_expansion (w2n wo) [] sg)
       with <|vs_returndata := []; vs_outcomes := DROP 1 sg.vs_outcomes|>))` by
    (fs[mk_inst_def] >> simp[step_inst_base_def, eval_operand_def] >>
     first_assum ACCEPT_TAC) >>
  simp[Once run_inst_seq_def] >>
  simp[Once run_inst_seq_def] >> fs[mk_inst_def] >>
  rpt (pop_assum kall_tac) >>
  simp[run_inst_seq_def, step_inst_base_def, eval_operand_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem computed_suffix_oracle_failure:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  computed_precompile (venom_call_request s target 0w wi insz T) /\
  (s.vs_outcomes = [] \/ ?co rest. s.vs_outcomes = co::rest /\ ~co.co_success) ==>
  ?u. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort u
Proof
  strip_tac >> drule computed_suffix_shape >> strip_tac >>
  qabbrev_tac `g = HD (s.vs_gas_readings ++ [0w:bytes32])` >>
  qabbrev_tac `s0 = s with vs_gas_readings := DROP 1 s.vs_gas_readings` >>
  `!x. eval_operand x s0 = eval_operand x s` by
    (Cases >> simp[Abbr `s0`, eval_operand_def, lookup_var_def]) >>
  qabbrev_tac `sg = update_var (STRING #"%" (toString sm.cs_next_var)) g s0` >>
  `step_inst_base (mk_inst sm.cs_next_id GAS [] [STRING #"%" (toString sm.cs_next_var)]) s =
   OK sg` by simp[Abbr `sg`, Abbr `g`, Abbr `s0`, step_GAS] >>
  `eval_operand ip sg = SOME wi /\ eval_operand op sg = SOME wo` by
    (simp[Abbr `sg`] >>
     metis_tac[eval_operand_update_not_fresh, arithmeticTheory.LESS_EQ_REFL]) >>
  `venom_call_request sg target 0w wi insz T =
   venom_call_request s target 0w wi insz T` by
    simp[Abbr `sg`, Abbr `s0`, venom_call_request_def, update_var_def, read_memory_def] >>
  qabbrev_tac `ci = mk_inst (sm.cs_next_id+1) STATICCALL
    [Var (STRING #"%" (toString sm.cs_next_var)); Lit target; ip; Lit insz; op; Lit outsz]
    [STRING #"%" (toString (sm.cs_next_var+1))]` >>
  qabbrev_tac `sc = update_var (STRING #"%" (toString (sm.cs_next_var+1))) 0w
    ((write_memory_with_expansion (w2n wo) [] sg)
      with <|vs_returndata := []; vs_outcomes := DROP 1 sg.vs_outcomes|>)` >>
  `exec_ext_call ci sg (g:bytes32) target 0w wi insz wo outsz T =
    OK sc` by
    (qunabbrev_tac `sc` >>
     Cases_on `s.vs_outcomes = []`
     >- (`sg.vs_outcomes = []` by simp[Abbr `sg`, Abbr `s0`, update_var_def] >>
         simp[] >> irule computed_static_empty_probe >>
         simp[Abbr `ci`, mk_inst_def] >> metis_tac[]) >>
     fs[] >>
     `sg.vs_outcomes = co::rest` by simp[Abbr `sg`, Abbr `s0`, update_var_def] >>
     simp[] >> irule computed_static_false_probe >>
     simp[Abbr `ci`, mk_inst_def] >> metis_tac[]) >>
  `eval_operand (Var (STRING #"%" (toString sm.cs_next_var))) sg =
    SOME g` by
    simp[Abbr `sg`, eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `step_inst_base ci sg = OK sc` by
    (fs[Abbr `ci`, mk_inst_def] >>
     simp[step_inst_base_def, eval_operand_def]) >>
  simp[Once run_inst_seq_def] >>
  simp[Once run_inst_seq_def] >> gvs[mk_inst_def] >>
  `eval_operand (Var (STRING #"%" (toString (sm.cs_next_var+1)))) sc = SOME 0w` by
    simp[NoAsms, Abbr `sc`, eval_operand_def, lookup_var_def,
         update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  qexists_tac `revert_state (set_returndata [] sc)` >>
  simp[run_inst_seq_def, step_inst_base_def]
QED

Theorem computed_suffix_ok_outcomes[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  computed_precompile (venom_call_request s target 0w wi insz T) /\
  run_inst_seq (emitted_insts sm sb) s = OK t ==>
  ?co rest. s.vs_outcomes = co::rest /\ co.co_success
Proof
  strip_tac >> spose_not_then assume_tac >>
  qsuff_tac `s.vs_outcomes = [] \/
    ?co rest. s.vs_outcomes = co::rest /\ ~co.co_success`
  >- (disch_tac >> drule_all computed_suffix_oracle_failure >> simp[]) >>
  Cases_on `s.vs_outcomes` >> gvs[]
QED

Theorem computed_suffix_output:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME (SOME data) /\
  run_inst_seq (emitted_insts sm sb) s = OK t ==>
  eval_operand res t = SOME wo /\
  t.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE (w2n outsz) data) s).vs_memory /\
  t.vs_allocas = s.vs_allocas /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `computed_precompile (venom_call_request s target 0w wi insz T)` by
    simp[computed_precompile_def, venom_call_request_def] >>
  drule_all computed_suffix_ok_outcomes >> disch_tac >>
  drule_all computed_suffix_success >> strip_tac >>
  drule computed_suffix_shape >> strip_tac >> gvs[] >>
  conj_tac
  >- (Cases_on `op` >>
      gvs[eval_operand_def, lookup_var_def, update_var_def,
          write_memory_with_expansion_def, finite_mapTheory.FLOOKUP_UPDATE,
          not_fresh_at_def]) >>
  simp[update_var_def, write_memory_with_expansion_def] >>
  rpt strip_tac >> simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt IF_CASES_TAC >> gvs[not_fresh_at_def]
QED

Theorem ecrecover_suffix_core[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
      emit_void ASSERT [success]; emit_op MLOAD [op] od) sm = (res,sb) ==>
  ?sc. (do gas <- emit_op GAS [];
           success <- emit_op STATICCALL
             [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
           emit_void ASSERT [success]; comp_return op od) sm = (op,sc) /\
       emit_op MLOAD [op] sc = (res,sb) /\
       emitted_insts sm sb = emitted_insts sm sc ++
         [mk_inst (sm.cs_next_id + 3) MLOAD [op]
           [STRING #"%" (toString (sm.cs_next_var + 2))]] /\
       res = Var (STRING #"%" (toString (sm.cs_next_var + 2)))
Proof
  simp[comp_bind_def, comp_ignore_bind_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

Theorem ecrecover_suffix_shape[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
      emit_void ASSERT [success];
      emit_op MLOAD [op] od) sm = (res,sb) ==>
  res = Var (STRING #"%" (toString (sm.cs_next_var + 2))) /\
  sb.cs_next_var = sm.cs_next_var + 3 /\
  sb.cs_next_id = sm.cs_next_id + 4 /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  emitted_insts sm sb =
    [mk_inst sm.cs_next_id GAS []
       [STRING #"%" (toString sm.cs_next_var)];
     mk_inst (sm.cs_next_id + 1) STATICCALL
       [Var (STRING #"%" (toString sm.cs_next_var)); Lit 1w;
        ip; Lit 128w; op; Lit 32w]
       [STRING #"%" (toString (sm.cs_next_var + 1))];
     mk_inst (sm.cs_next_id + 2) ASSERT
       [Var (STRING #"%" (toString (sm.cs_next_var + 1)))] [];
     mk_inst (sm.cs_next_id + 3) MLOAD [op]
       [STRING #"%" (toString (sm.cs_next_var + 2))]]
Proof
  strip_tac >> drule ecrecover_suffix_core >> strip_tac >>
  drule computed_suffix_shape >> strip_tac >>
  qpat_x_assum `emit_op MLOAD [op] sc = _` mp_tac >>
  simp[emitHelperTheory.emit_op_def, fresh_id_def, fresh_var_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[]
QED

Theorem wb_frame_readonly_input:
  wb_frame cenv es sa t u /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
     lookup_var x t = SOME w) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
  (!name b sz. local_region cenv es.scopes t name b sz ==>
     local_region cenv es.scopes s name b sz) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     local_region cenv es.scopes t name b sz) ==>
  wb_frame cenv es sa s u
Proof
  simp[wb_frame_def, locals_kept_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem precompile_write_immutables[local]:
  stmt_state_rel ctx func cenv cx es s /\ LENGTH data <= cap /\
  (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,iv) ==>
     regions_disjoint dst cap off (type_memory_size tv)) ==>
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
    (write_memory_with_expansion dst data s)
Proof
  strip_tac >> irule immutables_rel_mem_agree >> qexists_tac `s` >>
  conj_tac
  >- simp[immutableMemoryFrameTheory.immutable_write_memory_capacity,
          arithmeticTheory.MAX_DEF] >>
  conj_tac >- simp[write_memory_with_expansion_def] >>
  reverse conj_tac >- gvs[stmt_state_rel_def, state_rel_def] >>
  rpt strip_tac >> irule hash_write_memory_disjoint >>
  qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
  disch_then drule_all >>
  simp[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem computed_suffix_preserves:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME (SOME data) /\
  run_inst_seq (emitted_insts sm sb) s = OK t /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint (w2n wo) (w2n outsz) b sz) /\
  (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n wo) (w2n outsz) b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,iv) ==>
     regions_disjoint (w2n wo) (w2n outsz) off (type_memory_size tv)) ==>
  stmt_state_rel ctx func cenv cx
    (es with outcomes := SOME (DROP 1 s.vs_outcomes)) t /\ wb_frame cenv es sf s t
Proof
  strip_tac >>
  `computed_precompile (venom_call_request s target 0w wi insz T)` by
    simp[computed_precompile_def, venom_call_request_def] >>
  drule_all computed_suffix_ok_outcomes >> disch_tac >>
  drule_all computed_suffix_success >> strip_tac >>
  qabbrev_tac `g = HD (s.vs_gas_readings ++ [0w:bytes32])` >>
  qabbrev_tac `s0 = s with vs_gas_readings := DROP 1 s.vs_gas_readings` >>
  qabbrev_tac `sg = update_var (STRING #"%" (toString sm.cs_next_var)) g s0` >>
  `venom_call_request sg target 0w wi insz T =
   venom_call_request s target 0w wi insz T` by
    simp[Abbr `sg`, Abbr `s0`, venom_call_request_def, update_var_def, read_memory_def] >>
  `!n. sm.cs_next_var <= n ==>
     not_local_ptr cenv es.scopes (STRING #"%" (toString n))` by
    metis_tac[local_ptrs_reserved_fresh] >>
  `stmt_state_rel ctx func cenv cx es sg` by
    (simp[Abbr `sg`] >> irule stmt_state_rel_update_var >>
     simp[Abbr `s0`, hash_gas_readings_state_rel]) >>
  `!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
     lookup_var x sg = SOME w` by
    (simp[Abbr `sg`, Abbr `s0`, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     rpt strip_tac >> IF_CASES_TAC >> gvs[not_fresh_at_def]) >>
  `!name b sz. local_region cenv es.scopes sg name b sz ==>
     local_region cenv es.scopes s name b sz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >>
       gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sm`, `es.scopes`, `sg`] >> simp[]) >>
  `computed_precompile (venom_call_request sg target 0w wi insz T)` by
    (simp[computed_precompile_def] >> simp[venom_call_request_def]) >>
  `!name b sz. local_region cenv es.scopes sg name b sz ==>
     regions_disjoint (w2n wo) (w2n outsz) b sz` by metis_tac[] >>
  qabbrev_tac `ci = mk_inst (sm.cs_next_id+1) STATICCALL
    [Var (STRING #"%" (toString sm.cs_next_var)); Lit target; ip; Lit insz; op; Lit outsz]
    [STRING #"%" (toString (sm.cs_next_var+1))]` >>
  `sg.vs_outcomes = s.vs_outcomes` by simp[Abbr `sg`, Abbr `s0`, update_var_def] >>
  `exec_ext_call ci sg (g:bytes32)
     target 0w wi insz wo outsz T = OK t` by
    (irule EQ_TRANS >>
     irule_at Any computed_static_exec_success >> simp[Abbr `ci`, mk_inst_def] >>
     gvs[]) >>
  `?u. exec_ext_call ci sg (g:bytes32)
      target 0w wi insz wo outsz T = OK u /\ stmt_state_rel ctx func cenv cx
        (es with outcomes := SOME (DROP 1 sg.vs_outcomes)) u` by
    (irule computed_static_exec_state_rel >>
     simp[Abbr `ci`, mk_inst_def] >> conj_tac
     >- (rpt strip_tac >>
         `regions_disjoint (w2n wo) (w2n outsz) b sz` by metis_tac[] >>
         gvs[compileEnvTheory.regions_disjoint_def, listTheory.LENGTH_TAKE_EQ] >>
         decide_tac) >>
     irule precompile_write_immutables >>
     reverse conj_tac >- (qexistsl_tac [`ctx`,`func`] >> simp[]) >>
     qexists_tac `w2n outsz` >> simp[listTheory.LENGTH_TAKE_EQ] >>
     first_assum ACCEPT_TAC) >>
  conj_tac >- gvs[] >>
  `?u. exec_ext_call ci sg (g:bytes32)
      target 0w wi insz wo outsz T = OK u /\ wb_frame cenv es sf sg u` by
    (irule computed_static_exec_wb_frame >>
     simp[Abbr `ci`, mk_inst_def, not_fresh_at_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     `FLOOKUP s.vs_allocas aid = SOME (b,sz)` by
       gvs[Abbr `sg`, Abbr `s0`, update_var_def] >>
     `regions_disjoint (w2n wo) (w2n outsz) b sz` by metis_tac[] >>
     gvs[compileEnvTheory.regions_disjoint_def, listTheory.LENGTH_TAKE_EQ] >>
     decide_tac) >>
  `wb_frame cenv es sf sg t` by gvs[] >>
  irule wb_frame_readonly_input >> qexists_tac `sg` >>
  simp[Abbr `sg`, Abbr `s0`, update_var_def] >>
  conj_tac
  >- (simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt strip_tac >> IF_CASES_TAC >> gvs[not_fresh_at_def]) >>
  rpt strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >>
  qexistsl_tac [`s`, `sm`, `es.scopes`] >> simp[update_var_def] >>
  simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[not_fresh_at_def]
QED

Theorem expr_body_pre_stack_result:
  expr_body_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') ==>
  expr_sim_inv cenv cx env es' /\ expr_res_ok res /\
  !v. res = INL v ==> ?tv.
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v
Proof
  strip_tac >> drule_all expr_body_pre_word_type_result >> strip_tac >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (drule_then irule expr_body_pre_res_ok >> simp[] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem expr_sim_pre_stack_result:
  expr_sim_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') ==>
  expr_sim_inv cenv cx env es' /\ expr_res_ok res /\
  !v. res = INL v ==> ?tv.
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v
Proof
  metis_tac[expr_body_pre_stack_result, expr_sim_pre_body_pre]
QED

Theorem typed_args_ready_of_ok[local]:
  !args ctx func cenv cx env arg_ty.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
           expr_sim_pre cenv cx env e s) /\
    EVERY (\e. is_word_type (expr_type e) /\ expr_sim_ok cenv e) args ==>
    typed_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args
Proof
  Induct >> simp[typed_args_ready_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env h es` by metis_tac[] >>
  rpt conj_tac
  >~ [`expr_sim _ _ _ _ _ _ _`] >- metis_tac[expr_sim_ok_def]
  >~ [`IS_SOME _`] >- metis_tac[well_typed_expr_type_evaluates]
  >~ [`expr_res_ok _`]
  >- (rpt strip_tac >> drule_all expr_sim_pre_stack_result >> simp[]) >>
  rpt strip_tac >> drule_all expr_sim_pre_stack_result >> simp[]
QED

(* typed_args_ready from the operands' shared case judgments. *)
Theorem typed_args_ready_of_case:
  !args nocalls ctx func cenv cx env arg_ty.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
       expr_body_pre cenv cx env e s /\ (nocalls ==> int_calls_expr e = []) /\
       is_word_type (expr_type e)) /\
    exprs_case nocalls ctx func cenv cx args ==>
    typed_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args
Proof
  Induct >> simp[typed_args_ready_def, exprs_case_def] >> rpt gen_tac >>
  strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `expr_body_pre cenv cx env h es /\ (nocalls ==> int_calls_expr h = []) /\
       is_word_type (expr_type h)` by metis_tac[] >>
      rpt conj_tac
      >- metis_tac[expr_sim_case_def]
      >- first_assum ACCEPT_TAC
      >- metis_tac[expr_body_pre_type_evaluates]
      >- (rpt strip_tac >> drule_all expr_body_pre_stack_result >> simp[]) >>
      rpt strip_tac >> drule_all expr_body_pre_stack_result >> simp[]) >>
  disch_tac >>
  qpat_x_assum `!nocalls ctx func cenv cx env arg_ty. _` irule >>
  qexists_tac `nocalls` >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!e s. _` irule >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem typed_stack_args_shape:
  !args cenv cx env arg_ty es.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
           expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)) /\
    expr_sim_inv cenv cx env es ==>
    wb_args_shape cenv arg_ty args
Proof
  rpt strip_tac >> simp[wb_args_shape_def] >> rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e es /\ is_word_type (expr_type e)` by
    metis_tac[] >>
  drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[]
QED

(* typed_args_ready and wb_args_shape of word operands that each meet
   expr_sim_pre wherever expr_sim_inv holds. *)
Theorem typed_stack_args_ready:
  (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
         expr_sim_pre cenv cx env e s) /\
  expr_sim_inv cenv cx env es /\
  EVERY (\e. is_word_type (expr_type e) /\ expr_sim_ok cenv e) args ==>
  typed_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args /\
  wb_args_shape cenv arg_ty args
Proof
  strip_tac >> conj_tac >- metis_tac[typed_args_ready_of_ok] >>
  irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >> simp[] >>
  rpt strip_tac >- metis_tac[expr_sim_pre_body_pre] >>
  gvs[EVERY_MEM] >> first_x_assum drule >> simp[]
QED

Theorem stack_args_values_typed_body:
  !args vs cenv cx env es es'.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
       expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)) /\
    expr_sim_inv cenv cx env es /\ eval_exprs cx args es = (INL vs,es') ==>
    LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                         value_has_type tv v) args vs
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[eval_exprs_nil] >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env h es /\ is_word_type (expr_type h)` by
    (first_x_assum irule >> simp[]) >>
  drule_all expr_body_pre_stack_result >> strip_tac >> gvs[] >>
  Cases_on `rr` >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[listTheory.MEM]
QED

Theorem stack_args_values_typed:
  !args vs cenv cx env es es'.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
       expr_sim_pre cenv cx env e s /\ is_word_type (expr_type e)) /\
    expr_sim_inv cenv cx env es /\ eval_exprs cx args es = (INL vs,es') ==>
    LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                         value_has_type tv v) args vs
Proof
  metis_tac[stack_args_values_typed_body, expr_sim_pre_body_pre]
QED

Theorem typed_builtin_stack_args_values:
  expr_sim_pre cenv cx env (Builtin ann bt args) es /\
  EVERY (\e. is_word_type (expr_type e) /\ expr_sim_ok cenv e) args /\
  eval_exprs cx args es = (INL vs,es') ==>
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                       value_has_type tv v) args vs
Proof
  strip_tac >> irule stack_args_values_typed >> goal_assum (drule_at Any) >>
  qexistsl_tac [`cenv`, `env`] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (irule expr_sim_pre_builtin_typed_arg >> simp[] >>
          conj_tac
          >- (strip_tac >> gvs[EVERY_MEM] >> first_x_assum drule >>
              simp[is_word_type_def]) >>
          qexistsl_tac [`ann`, `args`, `bt`, `es`] >> simp[]) >>
      gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  gvs[expr_sim_pre_def]
QED

Theorem eval_expr_ecrecover_cases[local]:
  LENGTH args = 4 /\
  eval_expr cx (Builtin ann ECRecover args) es = (res,es') ==>
  (?exc. eval_exprs cx args es = (INR exc,es') /\ res = INR exc) \/
  ?vs es1. eval_exprs cx args es = (INL vs,es1) /\
    (case builtin_result cx es1.accounts ann ECRecover (MAP expr_type args) vs of
       INR exc => res = INR exc /\ es' = es1
     | INL w => (do precompile_call_success ECRecover; return (Value w) od) es1 = (res,es'))
Proof
  strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, builtin_args_length_ok_def] >>
  Cases_on `eval_exprs cx args es` >>
  rename1 `eval_exprs cx args es = (rr, es1)` >>
  Cases_on `rr` >>
  simp[bind_def, return_def, get_accounts_def, lift_sum_def,
       builtin_result_def, AllCaseEqs(), ignore_bind_def] >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs()] >>
  Cases_on `evaluate_builtin cx es1.accounts ann ECRecover (MAP expr_type args) x` >>
  gvs[return_def, raise_def, ignore_bind_def, bind_def] >> metis_tac[]
QED

Theorem ecrecover_source_outcome_step[local]:
  precompile_call_success ECRecover es =
    case es.outcomes of
      NONE => (INL (),es)
    | SOME [] => (INR (Error (RuntimeError "precompile failed")),es)
    | SOME (outcome::rest) =>
        (if call_outcome_success outcome then INL ()
         else INR (Error (RuntimeError "precompile failed")),
         es with outcomes := SOME rest)
Proof
  Cases_on `es.outcomes` >> simp[precompile_call_success_def, return_def] >>
  rename1 `SOME os` >> Cases_on `os` >>
  simp[check_def, assert_def, return_def, raise_def] >>
  Cases_on `call_outcome_success h` >> simp[return_def, raise_def]
QED

Theorem ecrecover_suffix_run[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
      emit_void ASSERT [success];
      emit_op MLOAD [op] od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s 1w 0w wi 128w T).cr_target
    (venom_call_request s 1w 0w wi 128w T).cr_data = SOME (SOME data) /\
  s.vs_outcomes = co::rest /\ co.co_success /\
  mem_word_at (w2n wo)
    (write_memory_with_expansion (w2n wo) (TAKE 32 data) s).vs_memory = w ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    eval_operand res t = SOME w
Proof
  strip_tac >> drule ecrecover_suffix_core >> strip_tac >>
  drule computed_suffix_success >> simp[] >>
  disch_then (qspecl_then [`wo`, `wi`, `s`, `data`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s = OK st` >> strip_tac >>
  drule_all computed_suffix_output >> strip_tac >>
  `mem_word_at (w2n wo) st.vs_memory = w` by
    gvs[wordsTheory.dimword_def] >>
  qexists_tac `update_var (STRING #"%" (toString (sm.cs_next_var + 2))) w st` >>
  conj_tac
  >- (drule run_inst_seq_append >> disch_then (qspec_then
        `[mk_inst (sm.cs_next_id + 3) MLOAD [op]
           [STRING #"%" (toString (sm.cs_next_var + 2))]]` mp_tac) >>
      asm_rewrite_tac[] >> disch_then SUBST1_TAC >>
      simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_read1_def,
           mload_def, mem_word_at_def, eval_operand_def] >>
      gvs[mem_word_at_def, word_of_bytes_be_def, wordsTheory.dimword_def]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem ecrecover_suffix_oracle_failure[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
      emit_void ASSERT [success];
      emit_op MLOAD [op] od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  ~( ?co rest. s.vs_outcomes = co::rest /\ co.co_success) ==>
  ?u. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort u
Proof
  strip_tac >> drule ecrecover_suffix_core >> strip_tac >>
  `computed_precompile (venom_call_request s 1w 0w wi 128w T)` by
    simp[computed_precompile_def, venom_call_request_def, precompile_result_def,
         wordsTheory.w2w_n2w, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  `?u. run_inst_seq (emitted_insts sm sc) s = Abort Revert_abort u` by
    (irule computed_suffix_oracle_failure >> simp[] >>
     Cases_on `s.vs_outcomes` >> gvs[] >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >>
  `!v. run_inst_seq (emitted_insts sm sc) s <> OK v` by simp[] >>
  drule run_inst_seq_append_err >> simp[]
QED

Theorem ecrecover_suffix_preserves[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
      emit_void ASSERT [success];
      emit_op MLOAD [op] od) sm = (res,sb) /\
  run_inst_seq (emitted_insts sm sb) s = OK t /\
  s.vs_outcomes = co::rest /\ co.co_success /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s 1w 0w wi 128w T).cr_target
    (venom_call_request s 1w 0w wi 128w T).cr_data = SOME (SOME data) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n wo) 32 b sz) /\
  (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n wo) 32 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,iv) ==>
     regions_disjoint (w2n wo) 32 off (type_memory_size tv)) ==>
  stmt_state_rel ctx func cenv cx
    (es with outcomes := SOME (DROP 1 s.vs_outcomes)) t /\ wb_frame cenv es sf s t
Proof
  strip_tac >> drule ecrecover_suffix_core >> strip_tac >>
  drule computed_suffix_success >> simp[] >>
  disch_then (qspecl_then [`wo`, `wi`, `s`, `data`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s = OK st` >> strip_tac >>
  drule computed_suffix_preserves >>
  simp[wordsTheory.dimword_def] >>
  disch_then drule >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  drule_all computed_suffix_output >> strip_tac >>
  drule run_inst_seq_append >> disch_then (qspec_then
    `[mk_inst (sm.cs_next_id + 3) MLOAD [op]
       [STRING #"%" (toString (sm.cs_next_var + 2))]]` assume_tac) >>
  qpat_x_assum `run_inst_seq (emitted_insts sm sb) s = OK t` mp_tac >>
  asm_rewrite_tac[] >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_read1_def,
       AllCaseEqs()] >> strip_tac >> gvs[] >>
  `!n. sm.cs_next_var <= n ==>
     not_local_ptr cenv es.scopes (STRING #"%" (toString n))` by
    metis_tac[local_ptrs_reserved_fresh] >>
  conj_tac >- (irule stmt_state_rel_update_var >> simp[]) >>
  irule wb_frame_readonly_tail >> qexistsl_tac [`sm`, `st`] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[not_fresh_at_def]
QED

Theorem compile_ecrecover_run[local]:
  compile_ecrecover h v r sig sf = (res,sb) /\
  s.vs_outcomes = co::rest /\ co.co_success /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sf x) ==>
  ?t. run_inst_seq (emitted_insts sf sb) s = OK t /\
    stmt_state_rel ctx func cenv cx (es with outcomes := SOME rest) t /\
    wb_frame cenv es sf s t /\
    eval_operand res t = SOME
      (typed_val_to_w256 (BaseTV AddressT)
        (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws) of
          NONE => 0w | SOME addr => addr)))
Proof
  strip_tac >>
  qpat_x_assum `compile_ecrecover _ _ _ _ sf = _` mp_tac >>
  rewrite_tac[compile_ecrecover_prefix] >>
  pure_once_rewrite_tac[comp_bind_def] >>
  pure_rewrite_tac[LET_THM] >> pairarg_tac >> strip_tac >>
  rename1 `_ sf = (ipop,sm)` >> PairCases_on `ipop` >> fs[] >>
  rename1 `_ sf = ((ip,op),sm)` >>
  qpat_x_assum `(\(x,y). _) _ = _` mp_tac >>
  asm_rewrite_tac[] >> simp[pairTheory.UNCURRY_DEF] >> strip_tac >>
  `LENGTH sf.cs_current_insts <= LENGTH sm.cs_current_insts` by
    (qpat_x_assum `_ sf = ((ip,op),sm)` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, emitHelperTheory.emit_op_def,
          emitHelperTheory.emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[]) >>
  drule ecrecover_suffix_shape >> strip_tac >>
  `!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[emitted_insts_def, rich_listTheory.DROP_APPEND] >>
     simp[]) >>
  `!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sf x` by
    (pure_rewrite_tac [MEM] >> metis_tac[]) >>
  drule_all ecrecover_buffers_run >> strip_tac >>
  rename1 `eval_operand ip t = SOME wi` >>
  `local_ptrs_reserved cenv sm /\
   sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id` by
    (drule_all ecrecover_buffers_prefix_shape >> strip_tac >> simp[] >> decide_tac) >>
  `(!y. ip = Var y ==> not_fresh_at sm y) /\
   (!y. op = Var y ==> not_fresh_at sm y)` by simp[] >>
  drule ecrecover_request_result >> strip_tac >>
  `?data. precompile_result (venom_call_request t 1w 0w wi 128w T).cr_target
      (venom_call_request t 1w 0w wi 128w T).cr_data = SOME (SOME data) /\
    mem_word_at (w2n po)
      (write_memory_with_expansion (w2n po) (TAKE 32 data) t).vs_memory =
      typed_val_to_w256 (BaseTV AddressT)
        (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws) of
          NONE => 0w | SOME addr => addr))` by
    (Cases_on `vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws)`
     >- (gvs[] >> drule ecrecover_output_write >>
         disch_then (qspecl_then [`[]`, `0w:address`] mp_tac) >> simp[]) >>
     rename1 `_ = SOME addr` >> gvs[] >> drule ecrecover_output_write >>
     disch_then (qspecl_then [`PAD_LEFT 0w 32 (word_to_bytes addr T)`, `addr`] mp_tac) >>
     simp[]) >>
  `t.vs_outcomes = co::rest` by
    (gvs[stmt_state_rel_def, state_rel_def]) >>
  drule_all ecrecover_suffix_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sb) t = OK tf` >>
  drule_all ecrecover_suffix_preserves >> strip_tac >>
  `LENGTH sf.cs_current_insts - LENGTH sm.cs_current_insts = 0` by decide_tac >>
  qexists_tac `tf` >> simp[] >>
  conj_tac
  >- (`emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb` by
        simp[emitted_insts_def, rich_listTheory.DROP_APPEND,
             arithmeticTheory.SUB_EQ_0] >>
      metis_tac[run_inst_seq_append]) >>
  conj_tac
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ (_ with outcomes := _) tf` mp_tac >> simp[]) >>
  irule wb_frame_trans >>
  conj_tac >- simp[] >>
  conj_tac >- (qexistsl_tac [`es`, `sf`, `t`] >> simp[]) >>
  qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]
QED

Theorem compile_ecrecover_oracle_failure[local]:
  compile_ecrecover h v r sig sf = (res,sb) /\
  ~(?co rest. s.vs_outcomes = co::rest /\ co.co_success) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sf x) ==>
  ?u. run_inst_seq (emitted_insts sf sb) s = Abort Revert_abort u
Proof
  strip_tac >>
  qpat_x_assum `compile_ecrecover _ _ _ _ sf = _` mp_tac >>
  rewrite_tac[compile_ecrecover_prefix] >>
  pure_once_rewrite_tac[comp_bind_def] >>
  pure_rewrite_tac[LET_THM] >> pairarg_tac >> strip_tac >>
  rename1 `_ sf = (ipop,sm)` >> PairCases_on `ipop` >> fs[] >>
  rename1 `_ sf = ((ip,op),sm)` >>
  qpat_x_assum `(\(x,y). _) _ = _` mp_tac >>
  asm_rewrite_tac[] >> simp[pairTheory.UNCURRY_DEF] >> strip_tac >>
  `LENGTH sf.cs_current_insts <= LENGTH sm.cs_current_insts` by
    (qpat_x_assum `_ sf = ((ip,op),sm)` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, emitHelperTheory.emit_op_def,
          emitHelperTheory.emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[]) >>
  drule ecrecover_suffix_shape >> strip_tac >>
  `!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[emitted_insts_def, rich_listTheory.DROP_APPEND] >> simp[]) >>
  `!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sf x` by
    (pure_rewrite_tac [MEM] >> metis_tac[]) >>
  drule_all ecrecover_buffers_run >> strip_tac >>
  rename1 `eval_operand ip t = SOME wi` >>
  `~(?co rest. t.vs_outcomes = co::rest /\ co.co_success)` by
    (gvs[stmt_state_rel_def, state_rel_def]) >>
  `(!y. ip = Var y ==> not_fresh_at sm y) /\
   (!y. op = Var y ==> not_fresh_at sm y)` by simp[] >>
  drule_all ecrecover_suffix_oracle_failure >> strip_tac >>
  `LENGTH sf.cs_current_insts - LENGTH sm.cs_current_insts = 0` by decide_tac >>
  `emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb` by
    simp[emitted_insts_def, rich_listTheory.DROP_APPEND, arithmeticTheory.SUB_EQ_0] >>
  drule run_inst_seq_append >>
  disch_then (qspec_then `emitted_insts sm sb` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem ecrecover_oracle_failure_frag[local]:
  compile_ecrecover h v r sig sa = (op,sb) /\
  ~(?co rest. s.vs_outcomes = co::rest /\ co.co_success) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!i. MEM i (emitted_insts sa sb) ==> MEM i (fn_insts func)) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sa x) ==>
  frag_exec ctx sa sb (\t. t = s) Q
    (expr_exit (INR (Error (RuntimeError "precompile failed"))))
Proof
  strip_tac >> drule ecrecover_code_shape >> strip_tac >>
  irule hash_abort_frag >> simp[] >>
  gvs[MEM] >> drule_all (SRULE [MEM] compile_ecrecover_oracle_failure) >> simp[]
QED

Theorem lower_value_ecrecover[local]:
  lower_value compile_expr cenv ty (Builtin ann ECRecover [a;b;c;d]) sa = (op,sb) ==>
  ?h v r sig sm. lower_word_args cenv (\e. ty) [a;b;c;d] sa = ([h;v;r;sig],sm) /\
    compile_ecrecover h v r sig sm = (op,sb)
Proof
  strip_tac >>
  `compile_expr cenv ty (Builtin ann ECRecover [a;b;c;d]) sa =
    compile_builtin_dispatch cenv ann ty ECRecover [a;b;c;d] sa` by
    (irule compile_expr_builtin_dispatch >>
     Cases_on `a` >> simp[names_builtin_def] >>
     Cases_on `b` >> simp[names_builtin_def] >>
     Cases_on `c` >> simp[names_builtin_def]) >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def] >>
  goal_assum (drule_at Any) >>
  simp[lower_word_args_def, comp_bind_def, comp_return_def]
QED

Theorem lower_value_ecrecover_args[local]:
  LENGTH args = 4 /\
  lower_value compile_expr cenv ty (Builtin ann ECRecover args) sa = (op,sb) ==>
  ?h v r sig sm. lower_word_args cenv (\e. ty) args sa = ([h;v;r;sig],sm) /\
    compile_ecrecover h v r sig sm = (op,sb)
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  drule lower_value_ecrecover >> simp[]
QED

Theorem compile_ecrecover_stack[local]:
  LENGTH args = 4 /\
  compile_expr cenv ty (Builtin ann ECRecover args) sa = (vv,sb) ==>
  ?op. vv = StackValue ann op
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `Builtin ann ECRecover [a;b;c;d]` >>
  `compile_expr cenv ty (Builtin ann ECRecover [a;b;c;d]) sa =
    compile_builtin_dispatch cenv ann ty ECRecover [a;b;c;d] sa` by
    (irule compile_expr_builtin_dispatch >>
     Cases_on `a` >> simp[names_builtin_def] >>
     Cases_on `b` >> simp[names_builtin_def] >>
     Cases_on `c` >> simp[names_builtin_def]) >>
  gvs[] >>
  qpat_x_assum `compile_builtin_dispatch _ _ _ _ _ _ = _` mp_tac >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >> rw[] >> gvs[as_stack_val_pair]
QED

Theorem compile_ecrecover_extends[local]:
  compile_ecrecover h v r sig sa = (op,sb) ==>
  cs_extends sa sb
Proof
  strip_tac >> drule ecrecover_code_shape >>
  simp[same_blocks_def, cs_extends_def] >> strip_tac >>
  qexists_tac `[]` >> simp[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem ecrecover_pre_types[local]:
  expr_body_pre cenv cx env (Builtin ann ECRecover args) es ==>
  ann = BaseT AddressT /\ LENGTH args = 4 /\
  EVERY (\e. is_word_type (expr_type e)) args
Proof
  simp[expr_body_pre_def, well_typed_expr_def] >> strip_tac >>
  drule ecrecover_typing >> simp[] >> strip_tac >>
  `LENGTH args = 4` by simp[] >>
  gvs[LENGTH_EQ_NUM_compute] >> gvs[is_word_type_def]
QED

Theorem evaluate_ecrecover_encoded[local]:
  LENGTH bs = 32 /\
  ecrecover_arg_to_num va = SOME v /\
  ecrecover_arg_to_num ra = SOME r /\
  ecrecover_arg_to_num sa = SOME s ==>
  evaluate_ecrecover [BytesV bs;va;ra;sa] =
    INL (AddressV (case vfmExecution$ecrecover
      (word_of_bytes_be bs) v r s of NONE => 0w | SOME addr => addr))
Proof
  strip_tac >>
  Cases_on `vfmExecution$ecrecover (word_of_bytes_be bs) v r s` >>
  simp[evaluate_ecrecover_def]
QED

Theorem evaluate_ecrecover_typed[local]:
  value_has_type (BaseTV (BytesT (Fixed 32))) vh /\
  EVERY (\tv. (?k. tv = BaseTV (UintT k) /\ k <= 256) \/
                tv = BaseTV (BytesT (Fixed 32))) [tv;tr;ts] /\
  value_has_type tv va /\ value_has_type tr ra /\ value_has_type ts sa ==>
  evaluate_ecrecover [vh;va;ra;sa] =
    INL (AddressV (case vfmExecution$ecrecover
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) vh)
      (w2n (typed_val_to_w256 tv va))
      (w2n (typed_val_to_w256 tr ra))
      (w2n (typed_val_to_w256 ts sa)) of NONE => 0w | SOME addr => addr))
Proof
  strip_tac >>
  `ecrecover_arg_to_num va = SOME (w2n (typed_val_to_w256 tv va))` by
    (irule ecrecover_arg_typed_encoding >> gvs[]) >>
  `ecrecover_arg_to_num ra = SOME (w2n (typed_val_to_w256 tr ra))` by
    (irule ecrecover_arg_typed_encoding >> gvs[]) >>
  `ecrecover_arg_to_num sa = SOME (w2n (typed_val_to_w256 ts sa))` by
    (irule ecrecover_arg_typed_encoding >> gvs[]) >>
  qpat_x_assum `value_has_type (BaseTV (BytesT (Fixed 32))) vh` mp_tac >>
  Cases_on `vh` >> simp[value_has_type_def] >> strip_tac >>
  simp[typed_val_to_w256_def, PAD_LEFT, PAD_RIGHT] >>
  irule evaluate_ecrecover_encoded >> simp[]
QED

Theorem ecrecover_typed_result[local]:
  well_typed_builtin_app ann ECRecover (MAP expr_type args) /\
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) args vs ==>
  ?ah av ar asig vh va ra sa tv tr ts.
    args = [ah;av;ar;asig] /\ vs = [vh;va;ra;sa] /\
    evaluate_type (get_tenv cx) (expr_type ah) = SOME (BaseTV (BytesT (Fixed 32))) /\
    evaluate_type (get_tenv cx) (expr_type av) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type ar) = SOME tr /\
    evaluate_type (get_tenv cx) (expr_type asig) = SOME ts /\
    builtin_result cx acc ann ECRecover (MAP expr_type args) vs =
      INL (AddressV (case vfmExecution$ecrecover
        (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) vh)
        (w2n (typed_val_to_w256 tv va))
        (w2n (typed_val_to_w256 tr ra))
        (w2n (typed_val_to_w256 ts sa)) of NONE => 0w | SOME addr => addr))
Proof
  strip_tac >> drule ecrecover_typing >> simp[] >> strip_tac >>
  `LENGTH args = 4` by simp[] >>
  `LENGTH vs = 4` by metis_tac[LIST_REL_LENGTH] >>
  gvs[LENGTH_EQ_NUM_compute] >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  simp[builtin_result_def, evaluate_builtin_def] >>
  qmatch_goalsub_rename_tac `evaluate_ecrecover [vh;va;ra;sa]` >>
  qmatch_goalsub_abbrev_tac `AddressV addr` >>
  `evaluate_ecrecover [vh;va;ra;sa] = INL (AddressV addr)` suffices_by simp[] >>
  simp[Abbr `addr`] >> irule evaluate_ecrecover_typed >> simp[]
QED

Theorem ecrecover_expr_tail[local]:
  compile_ecrecover h v r sig sm = (op,sb) /\
  t.vs_outcomes = co::rest /\ co.co_success /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  (!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts func)) /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sm x) /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel ctx func cenv cx es' t /\ wb_frame cenv es sa s0 t /\
  eval_operand h t = SOME wh /\ eval_operand v t = SOME wv /\
  eval_operand r t = SOME wr /\ eval_operand sig t = SOME ws /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV AddressT) ==>
  frag_exec ctx sm sb (\s. s = t)
    (\u. expr_post ctx func cenv cx e es sa sb s0 (es' with outcomes := SOME rest)
      (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws) of
        NONE => 0w | SOME a => a)) op u) R
Proof
  strip_tac >> irule ecrecover_run_frag >> reverse conj_tac
  >- (goal_assum (drule_at Any)) >>
  rpt strip_tac >> gvs[] >> drule_all (SRULE [MEM] compile_ecrecover_run) >>
  strip_tac >> rename1 `run_inst_seq _ input = OK output` >>
  goal_assum (drule_at Any) >>
  irule expr_post_typed_stack_intro >> simp[stmt_state_rel_inst_idx] >>
  irule wb_frame_trans >> conj_tac >- simp[] >>
  conj_tac
  >- (qexistsl_tac [`es'`, `sm`, `input`] >>
      gvs[wb_frame_def, lookup_var_def] >> metis_tac[]) >>
  qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]
QED

Theorem ecrecover_read_cases[local]:
  LENGTH args = 4 /\
  (do r <- eval_expr cx (Builtin ann ECRecover args); read_result cx r od) es = (res,es') ==>
  (?exc. eval_exprs cx args es = (INR exc,es') /\ res = INR exc) \/
  ?vs es1. eval_exprs cx args es = (INL vs,es1) /\
    (case builtin_result cx es1.accounts ann ECRecover (MAP expr_type args) vs of
       INR exc => res = INR exc /\ es' = es1
     | INL w => (do precompile_call_success ECRecover; return w od) es1 = (res,es'))
Proof
  strip_tac >> qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, builtin_args_length_ok_def] >>
  Cases_on `eval_exprs cx args es` >>
  rename1 `eval_exprs cx args es = (rr,es1)` >> Cases_on `rr` >>
  simp[get_accounts_def, bind_def, return_def, lift_sum_def, builtin_result_def] >>
  rename1 `evaluate_builtin cx _ ann ECRecover _ vs` >>
  Cases_on `evaluate_builtin cx es1.accounts ann ECRecover (MAP expr_type args) vs` >>
  simp[bind_def, return_def, raise_def, read_result_def, ignore_bind_def] >>
  Cases_on `precompile_call_success ECRecover es1` >>
  rename1 `precompile_call_success ECRecover es1 = (out,es2)` >> Cases_on `out` >>
  simp[bind_def, return_def, read_result_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* An argument list's gas outcome, then a continuation on its values. *)
Theorem eval_exprs_suffix:
  gas_outcome F tops (ctx,func) (eval_exprs cx args) (es,s0)
    (\rr ee t. ?vs. rr = INL vs /\ P vs ee t) (\rr ee r. wb_args_exit rr r) /\
  (!exc ee r. wb_args_exit (INR exc) r ==> R (INR exc) ee r) /\
  (!gs vs ee t.
     eval_exprs cx args (es with gas_obs := gs) = (INL vs, ee) /\
     ee.gas_obs = [] /\ P vs ee t /\ ~t.vs_halted ==>
     ?marks. gas_summary_at F (ctx,func) marks (k vs) (ee,t) Q R) ==>
  gas_outcome F tops (ctx,func) (bind (eval_exprs cx args) k) (es,s0) Q R
Proof
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      gvs[]
      >- (`eval_exprs cx args
             (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL vs, es_end with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          qpat_x_assum `!gs vs ee t. _`
            (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `vs`,
                          `es_end with gas_obs := []`, `t`] mp_tac) >>
          (impl_tac >- simp[]) >> strip_tac >>
          rename1 `gas_summary_at F _ right _ _ _ _` >>
          qexists_tac `marks ++ right` >> disj1_tac >>
          qpat_x_assum `gas_summary_at F _ right _ _ _ _`
            (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
          disch_then (qx_choosel_then [`fres`, `fin`, `fr`]
            (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
          drule_all gas_marked_exec_bind_normal >> strip_tac >>
          rewrite_tac[gas_summary_at_def] >>
          qexistsl_tac [`fres`, `fin`, `fr`] >> asm_rewrite_tac[]) >>
      Cases_on `res` >> gvs[wb_args_exit_def] >>
      rename1 `expr_exit (INR exc) r` >>
      qexists_tac `marks` >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
      disj2_tac >> simp[] >> first_x_assum irule >> simp[wb_args_exit_def]) >>
  qexists_tac `marks` >> disj2_tac >>
  qabbrev_tac `a = eval_exprs cx args` >>
  `ignore_bind (bind a k) (return ()) =
   bind a (\v. ignore_bind (k v) (return ()))` by
    simp[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  pop_assum SUBST1_TAC >>
  metis_tac[gas_exempt_cert_error_values]
QED

(* frag_exec_run_inst_seq's premise, concluding a counted target path. *)
Theorem run_inst_seq_gas_path:
  !ctx func st st' s Q R.
  fn_has_code st st' func /\
  st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ((?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
         Q (s' with vs_inst_idx := LENGTH st'.cs_current_insts)) \/
   (?a s'. run_inst_seq (emitted_insts st st') s = Abort a s' /\
           !n. R (Abort a (s' with vs_inst_idx := n)))) ==>
  ?n r. gas_marked_path F ctx func s n r /\
    ((?u. r = OK u /\ Q u /\ u.vs_current_bb = st'.cs_current_bb /\
          u.vs_inst_idx = LENGTH st'.cs_current_insts) \/
     (exit_result r /\ R r))
Proof
  rpt gen_tac >> strip_tac >>
  `st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'` by
    gvs[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def,
        rich_listTheory.DROP_LENGTH_APPEND]
  >- (drule_all hash_run_path >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      qexistsl_tac [`LENGTH (FILTER (\i. i.inst_opcode = GAS)
                               (emitted_insts st st'))`,
                    `OK (s' with vs_inst_idx := LENGTH st'.cs_current_insts)`] >>
      gvs[]) >>
  drule_all hash_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum drule >> asm_simp_tac (srw_ss()) [exit_result_def]
QED

Theorem eval_expr_ecrecover_read_action[local]:
  LENGTH args = 4 ==>
  bind (eval_expr cx (Builtin ann ECRecover args)) (read_result cx) =
  bind (eval_exprs cx args)
    (\vs ee. case builtin_result cx ee.accounts ann ECRecover (MAP expr_type args) vs of
       INR exc => (INR exc, ee)
     | INL w => (do precompile_call_success ECRecover; return w od) ee)
Proof
  strip_tac >> pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  Cases_on `bind (eval_expr cx (Builtin ann ECRecover args)) (read_result cx) x` >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) ecrecover_read_cases) >>
  strip_tac >> gvs[bind_def] >>
  Cases_on `builtin_result cx es1.accounts ann ECRecover (MAP expr_type args) vs` >>
  gvs[]
QED

Theorem ecrecover_success_path[local]:
  compile_ecrecover h v r sig sm = (op,sb) /\ fn_has_code sm sb func /\
  t.vs_outcomes = co::rest /\ co.co_success /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sm x) /\
  wb_frame cenv es sa s0 t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel ctx func cenv cx es' t /\
  eval_operand h t = SOME wh /\ eval_operand v t = SOME wv /\
  eval_operand r t = SOME wr /\ eval_operand sig t = SOME ws /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?n u. gas_marked_path F ctx func t n (OK u) /\
    expr_post ctx func cenv cx (Builtin (BaseT AddressT) ECRecover args)
      es sa sb s0 (es' with outcomes := SOME rest)
      (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws) of
        NONE => 0w | SOME a => a)) op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts func)` by
    metis_tac[hash_emitted_inst_mem] >>
  drule_all compile_ecrecover_run >> strip_tac >>
  rename1 `run_inst_seq _ t = OK output` >>
  drule ecrecover_code_shape >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by gvs[same_blocks_def] >>
  drule_all hash_run_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum drule >> simp[] >>
  irule expr_post_typed_stack_intro >>
  simp[stmt_state_rel_inst_idx, expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def] >>
  irule wb_frame_trans >> conj_tac >- simp[] >>
  conj_tac
  >- (qexistsl_tac [`es'`, `sm`, `t`] >>
      gvs[wb_frame_def, lookup_var_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]
QED

Theorem ecrecover_failure_path[local]:
  compile_ecrecover h v r sig sm = (op,sb) /\
  eval_operand h t = SOME wh /\ eval_operand v t = SOME wv /\
  eval_operand r t = SOME wr /\ eval_operand sig t = SOME ws /\
  stmt_state_rel ctx func cenv cx es t /\ fn_inst_ids_distinct func /\
  fn_has_code sm sb func /\
  ~(?co rest. t.vs_outcomes = co::rest /\ co.co_success) /\
  local_ptrs_reserved cenv sm /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sm x) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?n a u. gas_marked_path F ctx func t n (Abort a u)
Proof
  strip_tac >>
  `!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts func)` by
    metis_tac[hash_emitted_inst_mem] >>
  drule_all compile_ecrecover_oracle_failure >> strip_tac >>
  drule ecrecover_code_shape >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by gvs[same_blocks_def] >>
  drule_all hash_abort_path >> metis_tac[]
QED

Theorem ecrecover_expr_sim[local]:
  expr_body_pre cenv cx env (Builtin ann ECRecover args) es /\
  (!arg_ty. typed_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args) ==>
  expr_sim ctx func cenv cx ty (Builtin ann ECRecover args) es
Proof
  strip_tac >> drule ecrecover_pre_types >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
         expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)` by
    (rpt strip_tac
     >- (qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
           (mp_then Any mp_tac expr_body_pre_builtin_arg) >>
         simp[] >> disch_then irule >> simp[]) >>
     gvs[EVERY_MEM]) >>
  `typed_args_ready ctx func cenv cx (\e. ty) (expr_sim_inv cenv cx env) args /\
   wb_args_shape cenv (\e. ty) args` by metis_tac[typed_stack_args_shape] >>
  `well_typed_builtin_app ann ECRecover (MAP expr_type args)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  rewrite_tac[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  drule_all lower_value_ecrecover_args >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sb` by metis_tac[compile_ecrecover_extends] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!es gs. expr_sim_inv cenv cx env es ==>
           expr_sim_inv cenv cx env (es with gas_obs := gs)` by simp[] >>
  drule_all lower_typed_args_sim >> strip_tac >>
  drule_then (fn th => rewrite_tac[th]) eval_expr_ecrecover_read_action >>
  irule eval_exprs_suffix >>
  conj_tac >- simp[wb_args_exit_def] >>
  qexists_tac `\vs ee t. typed_args_post ctx func cenv cx es sa s0 ee args
                 [h;v;r;sig] vs t /\ t.vs_current_bb = sm.cs_current_bb /\
                 t.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  BETA_TAC >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) args vs` by
    (irule stack_args_values_typed_body >>
     qexistsl_tac [`cenv`, `env`, `es with gas_obs := gs`, `ee`] >>
     simp[] >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  drule_all ecrecover_typed_result >>
  disch_then (qspec_then `ee.accounts` strip_assume_tac) >>
  gvs[typed_args_post_def] >>
  `ee.outcomes = SOME t.vs_outcomes` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sm x` by
    (gvs[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `builtin_result _ _ _ _ _ _ = INL (AddressV addr)` >>
  Cases_on `t.vs_outcomes`
  >- (`~(?co rest. t.vs_outcomes = co::rest /\ co.co_success)` by gvs[] >>
      drule_all ecrecover_failure_path >> strip_tac >>
      qexists_tac `REPLICATE n F` >> rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR (Error (RuntimeError "precompile failed"))`, `ee`,
                    `Abort a u`] >>
      asm_simp_tac (srw_ss()) [gas_marked_exec_def, exit_result_def,
        expr_exit_def, ignore_bind_def, bind_def, ecrecover_source_outcome_step]) >>
  rename1 `t.vs_outcomes = co::rest` >> Cases_on `co.co_success`
  >- (drule_all ecrecover_success_path >>
      disch_then (qspec_then `[ah;av;ar;asig]` strip_assume_tac) >>
      qabbrev_tac `es2 = ee with outcomes := SOME rest` >>
      `es2 with gas_obs := [] = es2` by
        gvs[Abbr `es2`, evaluation_state_component_equality] >>
      qexists_tac `REPLICATE n F` >> rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INL (AddressV addr)`, `es2`, `OK u`] >>
      rewrite_tac[gas_marked_exec_def, LENGTH_REPLICATE,
                  gas_explicit_replicate_false, APPEND] >>
      BETA_TAC >> pop_assum SUBST1_TAC >> conj_tac
      >- (asm_simp_tac (srw_ss()) [Abbr `es2`, ignore_bind_def, bind_def,
            ecrecover_source_outcome_step, return_def]) >>
      disj1_tac >> qexists_tac `u` >> simp[] >> gvs[Abbr `addr`]) >>
  `~(?co rest. t.vs_outcomes = co::rest /\ co.co_success)` by gvs[] >>
  drule_all ecrecover_failure_path >> strip_tac >>
  qexists_tac `REPLICATE n F` >> rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "precompile failed"))`,
                `ee with outcomes := SOME rest`, `Abort a u`] >>
  asm_simp_tac (srw_ss()) [gas_marked_exec_def, exit_result_def,
    expr_exit_def, ignore_bind_def, bind_def, ecrecover_source_outcome_step]
QED

Theorem compile_ecrecover_call_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann ECRecover args)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_vv_case_def] >>
  rpt strip_tac >> drule ecrecover_pre_types >> strip_tac >>
  irule expr_vv_sim_stack >> simp[] >> conj_tac
  >- (gen_tac >> Cases_on `compile_expr cenv ty (Builtin ann ECRecover args) sa` >>
      drule_all compile_ecrecover_stack >> simp[] >> metis_tac[]) >>
  conj_tac
  >- metis_tac[eval_expr_builtin_value] >>
  irule ecrecover_expr_sim >> qexists_tac `env` >> gvs[] >> gen_tac >>
  irule typed_args_ready_of_case >> qexists_tac `nocalls` >> simp[] >>
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
        (mp_then Any mp_tac expr_body_pre_builtin_arg) >>
      simp[] >> disch_then irule >> simp[])
  >- metis_tac[int_calls_builtin_arg] >>
  gvs[EVERY_MEM]
QED

