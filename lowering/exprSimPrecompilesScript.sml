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
 *   compile_ecrecover_call_sim — expr_vv_ok of ECRecover
 *
 * Exported for the other precompiles:
 *   - computed STATICCALLs: computed_static_consume_eq, computed_static_exec,
 *     computed_static_exec_success, computed_static_exec_state_rel,
 *     computed_static_exec_wb_frame, write_memory_stmt_state_rel,
 *     wb_frame_readonly_input
 *   - stack operands under their typed encoding (a bytes32 is not a
 *     word_value): typed_args_ready, typed_args_post, typed_args_ready_head,
 *     typed_args_ready_tail, typed_args_cons_cases, typed_args_post_cons,
 *     lower_typed_args_nil_sim, lower_typed_args_sim,
 *     typed_stack_args_ready, stack_args_values_typed,
 *     typed_builtin_stack_args_values, expr_sim_pre_stack_result,
 *     expr_post_typed_stack_operand, expr_post_typed_stack_intro
 *   - scratch buffers: scratch_mstore_frame, mem_bytes_at_store_append
 *   - big-endian words: num_of_bytes_l2n, num_of_be_bytes_word32
 * The ecrecover-specific helpers are local.
 *)

Theory exprSimPrecompiles
Ancestors
  list fragExec loweringSlice exprSim exprSimHyps exprSimWordBuiltins
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

Theorem write_memory_stmt_state_rel:
  stmt_state_rel func cenv cx es s /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b + sz <= dst \/ dst + LENGTH data <= b) ==>
  stmt_state_rel func cenv cx es (write_memory_with_expansion dst data s)
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
  qpat_x_assum `stmt_state_rel _ _ _ _ _` mp_tac >>
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
  simp[write_memory_with_expansion_def] >> metis_tac[]
QED

Theorem computed_static_consume_eq:
  rq = venom_call_request s addr 0w ai an T /\ computed_precompile rq ==>
  consume_call_outcome rq ro rs s =
    (if (FST (take_outcome rq s.vs_outcomes)).co_success then 1w else 0w,
     (write_memory_with_expansion ro
       (TAKE rs (FST (take_outcome rq s.vs_outcomes)).co_returnData) s)
       with vs_returndata := (FST (take_outcome rq s.vs_outcomes)).co_returnData)
Proof
  strip_tac >> drule computed_precompile_no_observation >>
  disch_then (qspecl_then [`s.vs_requests`, `s.vs_outcomes`] strip_assume_tac) >>
  `rq.cr_static` by simp[venom_call_request_def] >>
  simp[consume_call_outcome_eq, adopt_outcome_def,
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
       with vs_returndata := (FST (take_outcome rq s.vs_outcomes)).co_returnData))
Proof
  strip_tac >> drule_all computed_static_consume_eq >>
  disch_then (qspecl_then [`w2n rs`, `w2n ro`] assume_tac) >>
  gvs[exec_ext_call_def, Excl "consume_call_outcome_eq"]
QED

Theorem computed_static_exec_state_rel:
  rq = venom_call_request s addr 0w ai an T /\ computed_precompile rq /\
  inst.inst_outputs = [out] /\
  stmt_state_rel func cenv cx es s /\ not_local_ptr cenv es.scopes out /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b + sz <= w2n ro \/
     w2n ro + LENGTH (TAKE (w2n rs)
       (FST (take_outcome rq s.vs_outcomes)).co_returnData) <= b) ==>
  ?t. exec_ext_call inst s gas addr 0w ai an ro rs T = OK t /\
      stmt_state_rel func cenv cx es t
Proof
  strip_tac >> drule_all computed_static_consume_eq >>
  disch_then (qspecl_then [`w2n rs`, `w2n ro`] assume_tac) >>
  gvs[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  irule stmt_state_rel_update_var >> simp[hash_returndata_state_rel] >>
  irule write_memory_stmt_state_rel >> simp[] >> metis_tac[]
QED

Theorem computed_static_exec_wb_frame:
  rq = venom_call_request s addr 0w ai an T /\ computed_precompile rq /\
  inst.inst_outputs = [out] /\ ~not_fresh_at sa out /\
  (!aid b sz.
     FLOOKUP s.vs_allocas aid = SOME (b, sz) /\ aid < sa.cs_next_id /\
     (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
         b + sz <= lb \/ lb + lsz <= b) ==>
     b + sz <= w2n ro \/ w2n ro + LENGTH (TAKE (w2n rs)
       (FST (take_outcome rq s.vs_outcomes)).co_returnData) <= b) ==>
  ?t. exec_ext_call inst s gas addr 0w ai an ro rs T = OK t /\
      wb_frame cenv es sa s t
Proof
  strip_tac >> drule_all computed_static_consume_eq >>
  disch_then (qspecl_then [`w2n rs`, `w2n ro`] assume_tac) >>
  gvs[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  simp[wb_frame_def, update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac
  >- (rpt strip_tac >> IF_CASES_TAC >> gvs[write_memory_with_expansion_def]) >>
  rpt strip_tac >> irule mem_bytes_at_write_disjoint >>
  first_x_assum (drule_all_then mp_tac) >> decide_tac
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
  expr_post func cenv cx e es sa sb s0 es' v op s /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  eval_operand op s = SOME (typed_val_to_w256 tv v)
Proof
  simp[expr_post_def, expr_val_rel_def] >> metis_tac[]
QED

Theorem expr_post_typed_stack_intro:
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  stmt_state_rel func cenv cx es' s /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  wb_frame cenv es sa s0 s ==>
  expr_post func cenv cx e es sa sb s0 es' v op s
Proof
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, wb_frame_def] >>
  metis_tac[]
QED

(* The word-only argument predicates cannot encode bytes32.  Keep the
   same compiler and frame, but use the type-directed stack encoding. *)
Definition typed_args_ready_def:
  typed_args_ready ctx func cenv cx arg_ty Inv args <=>
    !e es. MEM e args /\ Inv es ==>
      expr_sim ctx func cenv cx (arg_ty e) e es /\
      is_word_type (expr_type e) /\
      IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
      (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==> expr_res_ok res) /\
      (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
        Inv es')
End

Definition typed_args_post_def:
  typed_args_post func cenv cx es sa s0 es' args xs vs s <=>
    stmt_state_rel func cenv cx es' s /\
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
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) ==>
  typed_args_ready ctx func cenv cx arg_ty Inv args
Proof
  simp[typed_args_ready_def] >> metis_tac[]
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
  frag_exec ctx sa sa (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
    (\s. typed_args_post func cenv cx es sa s0 es [] [] [] s)
    (wb_args_exit (INL []))
Proof
  irule frag_exec_refl >>
  simp[typed_args_post_def, wb_frame_refl] >> metis_tac[]
QED

Theorem typed_args_post_cons:
  expr_post func cenv cx e es sa s1 s0 es1 v x t /\
  typed_args_post func cenv cx es1 s1 t es' args xs vs u /\
  stmt_state_rel func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) ==>
  typed_args_post func cenv cx es sa s0 es' (e::args) (x::xs) (v::vs) u
Proof
  rpt strip_tac >>
  `eval_operand x t = SOME (typed_val_to_w256 tv v)` by
    (drule_all expr_post_typed_stack_operand >> simp[]) >>
  `wb_frame cenv es sa s0 t` by metis_tac[expr_post_frame] >>
  gvs[typed_args_post_def] >> conj_tac
  >- (irule eval_operand_frame >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[wb_frame_vars]) >>
  irule wb_frame_trans >> simp[] >> conj_tac
  >- (qexistsl_tac [`cx`, `func`] >> simp[]) >>
  qexistsl_tac [`es1`, `s1`, `t`] >> simp[]
QED

Theorem lower_typed_args_sim:
  !args ctx func cenv cx arg_ty Inv es sa xs sb rr es' s0.
    typed_args_ready ctx func cenv cx arg_ty Inv args /\ Inv es /\
    wb_args_shape cenv arg_ty args /\
    lower_word_args cenv arg_ty args sa = (xs,sb) /\
    eval_exprs cx args es = (rr,es') /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
      (\s. ?vs. rr = INL vs /\ typed_args_post func cenv cx es sa s0 es' args xs vs s)
      (wb_args_exit rr)
Proof
  Induct
  >- (simp[lower_word_args_nil, eval_exprs_nil] >> rpt strip_tac >>
      irule lower_typed_args_nil_sim) >>
  rpt gen_tac >> strip_tac >>
  rename1 `typed_args_ready ctx func cenv cx arg_ty Inv (e::args)` >>
  reverse (Cases_on `stmt_state_rel func cenv cx es s0`)
  >- (`(\s. s = s0 /\ stmt_state_rel func cenv cx es s) = (\s. F)` by
        (simp[FUN_EQ_THM] >> metis_tac[]) >>
      simp[] >> irule frag_exec_false_pre) >>
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
  drule_all typed_args_ready_head >> strip_tac >>
  drule_all typed_args_cons_cases >> strip_tac
  >- (gvs[wb_args_exit_def] >>
      drule_all expr_sim_apply >>
      disch_then (qspec_then `s0` mp_tac) >> simp[] >> strip_tac >>
      irule frag_exec_exit_prefix >> goal_assum (drule_at Any) >> simp[]) >>
  rename1 `eval_exprs cx args es1 = (rr1, _)` >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `typed_args_ready ctx func cenv cx arg_ty Inv args` by
    metis_tac[typed_args_ready_tail] >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    (qpat_x_assum `bind _ _ es = (INL v,es1)` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `expr_exit (INL v) = (\r. F)` by simp[FUN_EQ_THM] >>
  `expr_res_ok (INL v)` by simp[expr_res_ok_def] >>
  drule_all expr_sim_apply >> disch_then (qspec_then `s0` mp_tac) >>
  simp[expr_exit_def] >> disch_then (mp_then Any irule wb_frag_then) >> simp[] >>
  qx_gen_tac `t` >> strip_tac >>
  first_x_assum (drule_all_then (qspec_then `t` mp_tac)) >>
  disch_then (mp_then Any irule frag_exec_weaken) >>
  conj_tac >- (Cases_on `rr1` >> simp[wb_args_exit_def]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[expr_post_state]) >>
  rpt strip_tac >> gvs[] >>
  irule typed_args_post_cons >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac
  >- (Cases_on `evaluate_type (get_tenv cx) (expr_type e)` >> gvs[]) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

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

Theorem precompile_result_four_words[local]:
  !(h:bytes32) (v:bytes32) (r:bytes32) (s:bytes32).
  precompile_result 1w
    (word_to_bytes h T ++ word_to_bytes v T ++
     word_to_bytes r T ++ word_to_bytes s T) =
  SOME (SOME (case vfmExecution$ecrecover h (w2n v) (w2n r) (w2n s) of
    NONE => [] | SOME addr => PAD_LEFT 0w 32 (word_to_bytes addr T)))
Proof
  rpt gen_tac >>
  simp[precompile_result_def, take_pad_0_def,
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
     a + 32 <= b \/ b + sz <= a) ==>
  wb_frame cenv es sa s (mstore a w s)
Proof
  strip_tac >> rewrite_tac[wb_frame_def] >>
  conj_tac >- simp[mstore_def] >>
  conj_tac >- simp[mstore_def] >>
  rpt strip_tac >>
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  first_x_assum drule >> simp[]
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

Theorem ecrecover_input_stores[local]:
  mem_bytes_at a 128
    (mstore (a+96) sig
      (mstore (a+64) r (mstore (a+32) v (mstore a h s)))).vs_memory =
    word_to_bytes h T ++ word_to_bytes v T ++
    word_to_bytes r T ++ word_to_bytes sig T
Proof
  `mem_bytes_at a 32 (mstore a h s).vs_memory = word_to_bytes h T`
    by simp[mem_bytes_at_mstore_same] >>
  drule mem_bytes_at_store_append >>
  disch_then (qspec_then `v` assume_tac) >>
  gvs[] >>
  drule mem_bytes_at_store_append >>
  disch_then (qspec_then `r` assume_tac) >>
  gvs[] >>
  drule mem_bytes_at_store_append >>
  disch_then (qspec_then `sig` mp_tac) >>
  simp[APPEND_ASSOC]
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
    (rpt gen_tac >> strip_tac >> Cases_on `q` >>
     simp[eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
     IF_CASES_TAC >> gvs[] >>
     qpat_x_assum `!x. _ ==> not_fresh_at sa x`
       (qspec_then `STRING #"%" (toString k)` mp_tac) >>
     simp[not_fresh_at_def]) >>
  `!q a z t. eval_operand q (mstore a z t) = eval_operand q t` by
    (Cases >> simp[eval_operand_def, mstore_def, lookup_var_def]) >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
       exec_write2_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
       exec_pure2_def, bind_outputs_def, eval_operand_def,
       emitHelperPropsTheory.eval_operand_mstore] >>
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
  qpat_x_assum `!q a z t. _` kall_tac >>
  simp[GSYM dftCommutationTheory.update_var_mstore_commute] >>
  `!a z t m vs. (mstore a z t) with <|vs_memory := m; vs_vars := vs|> =
     t with <|vs_memory := m; vs_vars := vs|>` by simp[mstore_def] >>
  conj_tac >- simp[update_var_def] >>
  rpt strip_tac >> simp[emitHelperPropsTheory.lookup_var_update_var] >>
  gvs[not_fresh_at_def]
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
  stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint (w2n p) 128 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n p) 128 b sz) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n p+96) ws (mstore (w2n p+64) wr
        (mstore (w2n p+32) wv (mstore (w2n p) wh s)))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    stmt_state_rel func cenv cx es t /\ wb_frame cenv es sc s t /\
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
  `t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
      (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
  qexists_tac `t` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (irule literal_state_memory_frame >> qexists_tac `s` >>
      simp[IgnAsm `t.vs_memory = _`] >>
      conj_tac >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
      rpt strip_tac >> first_x_assum irule >>
      gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac
  >- (simp[wb_frame_def, IgnAsm `t.vs_memory = _`] >> conj_tac
      >- (rpt strip_tac >>
          `not_fresh_at sa x` by
            (gvs[not_fresh_at_def] >>
             metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
          metis_tac[]) >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  simp[ecrecover_input_stores]
QED

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
  drule ecrecover_input_stores_shape >> strip_tac >>
  qpat_assum `context$compile_alloc_buffer 128 _ = _`
    (strip_assume_tac o MATCH_MP compile_alloc_buffer_insts) >>
  qpat_assum `context$compile_alloc_buffer 32 _ = _`
    (strip_assume_tac o MATCH_MP compile_alloc_buffer_insts) >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  `emitted_insts sf sm = emitted_insts sf sa ++
     emitted_insts sa sb ++ emitted_insts sb sc ++ emitted_insts sc sm` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1] >>
     simp[emitted_insts_def, NoAsms] >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  `MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
       [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func)` by
    (first_x_assum irule >>
     qpat_x_assum `emitted_insts sf sm = _` SUBST1_TAC >>
     simp[] >> disj1_tac >> disj1_tac >> disj1_tac >>
     simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func)` by
    (first_x_assum irule >>
     qpat_x_assum `emitted_insts sf sm = _` SUBST1_TAC >>
     simp[] >> disj1_tac >> disj2_tac >>
     once_rewrite_tac [emitted_insts_def] >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  qpat_assum `context$compile_alloc_buffer 128 _ = _`
    (strip_assume_tac o MATCH_MP compile_alloc_buffer_parts) >>
  qpat_assum `context$compile_alloc_buffer 32 _ = _`
    (strip_assume_tac o MATCH_MP compile_alloc_buffer_parts) >>
  simp[] >>
  `sf.cs_next_var <= sa.cs_next_var /\
   sf.cs_next_var <= sb.cs_next_var /\
   sf.cs_next_var <= sc.cs_next_var /\
   sf.cs_next_var <= sm.cs_next_var` by simp[] >>
  rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[])
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[])
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[])
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[]) >>
  gvs[not_fresh_at_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
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
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sf x) ==>
  ?t pi po. run_inst_seq (emitted_insts sf sm) s = OK t /\
    stmt_state_rel func cenv cx es t /\ wb_frame cenv es sf s t /\
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
    (!x. not_fresh_at sf x ==> lookup_var x t = lookup_var x s) /\
    (?x. ip = Var x /\ not_fresh_at sm x) /\
    (?x. op = Var x /\ not_fresh_at sm x)
Proof
  rpt strip_tac >> drule_all ecrecover_buffers_shape >> strip_tac >>
  qpat_x_assum `_ sf = ((ip,op),sm)` kall_tac >>
  `128 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sf sa) s = OK s1` >>
  rename1 `FLOOKUP s1.vs_allocas sf.cs_next_id = SOME (w2n wi,128)` >>
  `s1.vs_labels = s.vs_labels` by
    (qpat_assum `context$compile_alloc_buffer 128 _ = _`
       (strip_assume_tac o MATCH_MP compile_alloc_buffer_insts) >>
     qspecl_then [`sf.cs_next_id`,`128w`,
       `STRING #"%" (toString sf.cs_next_var)`,`s`] strip_assume_tac
       step_alloca_frame >>
     gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1, run_inst_seq_def]) >>
  `!z. MEM z [h;v;r;sig] ==> eval_operand z s1 = eval_operand z s` by
    (rpt strip_tac >> Cases_on `z` >>
     simp[eval_operand_def] >> metis_tac[]) >>
  `eval_operand h s1 = SOME wh /\ eval_operand v s1 = SOME wv /\
   eval_operand r s1 = SOME wr /\ eval_operand sig s1 = SOME ws` by
    metis_tac[listTheory.MEM] >>
  `!aid b sz. aid < sf.cs_next_id /\
     FLOOKUP s1.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n wi) 128 b sz` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ s1`
       (strip_assume_tac o REWRITE_RULE
         [stmt_state_rel_def, alloca_inv_def, allocas_non_overlapping_def]) >>
     simp[compileEnvTheory.regions_disjoint_def] >>
     first_x_assum irule >>
     qexistsl_tac [`sf.cs_next_id`,`aid`] >> simp[] >> decide_tac) >>
  `sf.cs_next_id <= sa.cs_next_id` by decide_tac >>
  `!x. MEM (Var x) [ib.buf_operand;h;v;r;sig] ==> not_fresh_at sa x` by
    (simp[] >> rpt strip_tac >> gvs[] >>
     gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  drule_all ecrecover_input_stores_sim >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s1 = OK s2` >>
  `wb_frame cenv es sf s s1` by
    (simp[wb_frame_def] >> metis_tac[]) >>
  `wb_frame cenv es sf s s2` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`cx`,`func`] >> simp[]) >>
     qexistsl_tac [`es`,`sf`,`s1`] >> simp[]) >>
  `FLOOKUP s2.vs_allocas sf.cs_next_id = SOME (w2n wi,128)` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
       (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `do emit_void _ _; _ od sa = _` kall_tac >>
  qpat_x_assum `s2.vs_memory = _` kall_tac >>
  qpat_x_assum `context$compile_alloc_buffer 128 _ = _` kall_tac >>
  qpat_x_assum `!z. MEM z _ ==> eval_operand _ _ = _` kall_tac >>
  qpat_x_assum `!x. MEM (Var x) [ib.buf_operand;h;v;r;sig] ==> _` kall_tac >>
  qpat_x_assum `!x. MEM (Var x) [h;v;r;sig] ==> _` kall_tac >>
  map_every (fn z => qpat_x_assum z kall_tac)
    [`eval_operand h s = _`, `eval_operand v s = _`,
     `eval_operand r s = _`, `eval_operand sig s = _`,
     `eval_operand h s1 = _`, `eval_operand v s1 = _`,
     `eval_operand r s1 = _`, `eval_operand sig s1 = _`] >>
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sb sc) s2 = OK s3` >>
  rename1 `FLOOKUP s3.vs_allocas sb.cs_next_id = SOME (w2n wo,32)` >>
  `regions_disjoint (w2n wo) 32 (w2n wi) 128` by
    (qpat_x_assum `!aid b len. aid < sb.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `sf.cs_next_id` >> simp[] >> decide_tac) >>
  `eval_operand (Lit 0w) s3 = SOME 0w` by simp[eval_operand_def] >>
  drule_all literal_emit_mstore_run >> strip_tac >>
  `stmt_state_rel func cenv cx es (mstore (w2n wo) 0w s3)` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`w2n wo`,`32`] >> simp[] >>
     gvs[compileEnvTheory.regions_disjoint_def]) >>
  `wb_frame cenv es sb s2 s3` by
    (simp[wb_frame_def] >> metis_tac[]) >>
  `wb_frame cenv es sf s s3` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`cx`,`func`] >> simp[]) >>
     qexistsl_tac [`es`,`sb`,`s2`] >> simp[] >> decide_tac) >>
  `!aid b sz. aid < sf.cs_next_id /\
     FLOOKUP s3.vs_allocas aid = SOME (b,sz) ==>
     w2n wo + 32 <= b \/ b + sz <= w2n wo` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ s3`
       (strip_assume_tac o REWRITE_RULE
         [stmt_state_rel_def, alloca_inv_def, allocas_non_overlapping_def]) >>
     first_x_assum irule >>
     qexistsl_tac [`sb.cs_next_id`,`aid`] >> simp[] >> decide_tac) >>
  `wb_frame cenv es sf s3 (mstore (w2n wo) 0w s3)` by
    (irule scratch_mstore_frame >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es sf s (mstore (w2n wo) 0w s3)` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`cx`,`func`] >> simp[]) >>
     qexistsl_tac [`es`,`sf`,`s3`] >> simp[]) >>
  qexistsl_tac [`mstore (w2n wo) 0w s3`,`wi`,`wo`] >>
  conj_tac
  >- (asm_rewrite_tac[] >> rewrite_tac[GSYM APPEND_ASSOC] >>
      qpat_assum `run_inst_seq (emitted_insts sf sa) s = _`
        (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
      qpat_assum `run_inst_seq (emitted_insts sa sb) s1 = _`
        (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
      qpat_assum `run_inst_seq (emitted_insts sb sc) s2 = _`
        (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
      first_assum ACCEPT_TAC) >>
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
  conj_tac
  >- (simp[mstore_def, compileEnvTheory.regions_disjoint_def] >>
      first_assum ACCEPT_TAC) >>
  qx_gen_tac `y` >> strip_tac >>
  `not_fresh_at sa y /\ not_fresh_at sb y` by
    (gvs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  metis_tac[]
QED

(* Specialize the computed-call boundary to a successful concrete response. *)
Theorem computed_static_exec_success:
  rq = venom_call_request s addr 0w ai an T /\
  precompile_result rq.cr_target rq.cr_data = SOME (SOME data) /\
  inst.inst_outputs = [out] ==>
  exec_ext_call inst s gas addr 0w ai an ro rs T =
    OK (update_var out 1w
      ((write_memory_with_expansion (w2n ro) (TAKE (w2n rs) data) s)
       with vs_returndata := data))
Proof
  strip_tac >>
  `computed_precompile rq` by
    simp[computed_precompile_def, venom_call_request_def] >>
  drule_all computed_static_exec >>
  simp[take_outcome_def, failed_outcome_def]
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
  simp[comp_bind_def, comp_ignore_bind_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]
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
  mem_word_at (w2n wo)
    (write_memory_with_expansion (w2n wo) (TAKE 32 data) s).vs_memory = w ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    eval_operand res t = SOME w
Proof
  strip_tac >> drule ecrecover_suffix_shape >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts sm sb = code` >>
  qabbrev_tac `sg = update_var (STRING #"%" (toString sm.cs_next_var))
    (n2w s.vs_call_ctx.cc_gas) s` >>
  `eval_operand ip sg = SOME wi /\ eval_operand op sg = SOME wo` by
    (simp[Abbr `sg`] >>
     metis_tac[eval_operand_update_not_fresh, arithmeticTheory.LESS_EQ_REFL]) >>
  `venom_call_request sg 1w 0w wi 128w T =
   venom_call_request s 1w 0w wi 128w T` by
    simp[Abbr `sg`, venom_call_request_def, update_var_def, read_memory_def] >>
  qabbrev_tac `ci = mk_inst (sm.cs_next_id + 1) STATICCALL
    [Var (STRING #"%" (toString sm.cs_next_var)); Lit 1w;
     ip; Lit 128w; op; Lit 32w]
    [STRING #"%" (toString (sm.cs_next_var + 1))]` >>
  qabbrev_tac `sc = update_var (STRING #"%" (toString (sm.cs_next_var + 1))) 1w
    ((write_memory_with_expansion (w2n wo) (TAKE (w2n (32w:bytes32)) data) sg)
      with vs_returndata := data)` >>
  `exec_ext_call ci sg (n2w s.vs_call_ctx.cc_gas:bytes32)
     (1w:bytes32) 0w wi (128w:bytes32) wo (32w:bytes32) T =
     OK sc` by
    (qunabbrev_tac `sc` >> irule computed_static_exec_success >>
     simp[Abbr `ci`, mk_inst_def, wordsTheory.dimword_def]) >>
  `eval_operand op sc = SOME wo` by
    (Cases_on `op` >>
     gvs[Abbr `sc`, eval_operand_def, lookup_var_def, update_var_def,
         write_memory_with_expansion_def, not_fresh_at_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  `mem_word_at (w2n wo) sc.vs_memory = w` by
    gvs[Abbr `sc`, Abbr `sg`, update_var_def,
        write_memory_with_expansion_def, wordsTheory.dimword_def] >>
  `eval_operand (Var (STRING #"%" (toString sm.cs_next_var))) sg =
     SOME (n2w s.vs_call_ctx.cc_gas:bytes32)` by
    simp[Abbr `sg`, eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `step_inst_base ci sg = OK sc` by
    (gvs[Abbr `ci`, mk_inst_def] >>
     simp[step_inst_base_def, eval_operand_def]) >>
  `eval_operand (Var (STRING #"%" (toString (sm.cs_next_var + 1)))) sc = SOME 1w` by
    simp[Abbr `sc`, eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  qexists_tac `update_var (STRING #"%" (toString (sm.cs_next_var + 2))) w sc` >>
  conj_tac
  >- (simp[Abbr `code`, Once run_inst_seq_def, step_inst_base_def,
           mk_inst_def, exec_read0_def] >>
      simp[Once run_inst_seq_def] >>
      simp[Once run_inst_seq_def, step_inst_base_def] >>
      simp[run_inst_seq_def, step_inst_base_def, exec_read1_def,
           mload_def, mem_word_at_def, eval_operand_def] >>
      gvs[mem_word_at_def, word_of_bytes_be_def]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]

QED

Theorem wb_frame_readonly_input:
  wb_frame cenv es sa t u /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
     lookup_var x t = SOME w) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
  (!name b sz. local_region cenv es.scopes t name b sz ==>
     local_region cenv es.scopes s name b sz) ==>
  wb_frame cenv es sa s u
Proof
  simp[wb_frame_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem ecrecover_suffix_preserves[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
      emit_void ASSERT [success];
      emit_op MLOAD [op] od) sm = (res,sb) /\
  run_inst_seq (emitted_insts sm sb) s = OK t /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s 1w 0w wi 128w T).cr_target
    (venom_call_request s 1w 0w wi 128w T).cr_data = SOME (SOME data) /\
  stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n wo) 32 b sz) /\
  (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n wo) 32 b sz) ==>
  stmt_state_rel func cenv cx es t /\ wb_frame cenv es sf s t
Proof
  strip_tac >> drule ecrecover_suffix_shape >> strip_tac >>
  qpat_x_assum `_ sm = (res,sb)` kall_tac >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_read0_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ sg` >>
  `eval_operand ip sg = SOME wi /\ eval_operand op sg = SOME wo` by
    (simp[Abbr `sg`] >>
     metis_tac[eval_operand_update_not_fresh, arithmeticTheory.LESS_EQ_REFL]) >>
  `eval_operand (Var (STRING #"%" (toString sm.cs_next_var))) sg =
     SOME (n2w s.vs_call_ctx.cc_gas:bytes32)` by
    simp[Abbr `sg`, eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[Once run_inst_seq_def, step_inst_base_def, eval_operand_def] >>
  qmatch_goalsub_abbrev_tac `exec_ext_call ci sg _ _ _ _ _ _ _ T` >>
  simp[AllCaseEqs()] >> strip_tac >>
  rename1 `exec_ext_call ci sg _ _ _ _ _ _ _ T = OK sc` >>
  `!n. sm.cs_next_var <= n ==>
     not_local_ptr cenv es.scopes (STRING #"%" (toString n))` by
    metis_tac[local_ptrs_reserved_fresh] >>
  `stmt_state_rel func cenv cx es sg` by
    (simp[Abbr `sg`] >> irule stmt_state_rel_update_var >> simp[]) >>
  `!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
     lookup_var x sg = SOME w` by
    (simp[Abbr `sg`, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     rpt strip_tac >> IF_CASES_TAC >> gvs[not_fresh_at_def]) >>
  `!name b sz. local_region cenv es.scopes sg name b sz ==>
     local_region cenv es.scopes s name b sz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`sm`, `es.scopes`, `sg`] >> simp[]) >>
  `!name b sz. local_region cenv es.scopes sg name b sz ==>
      regions_disjoint (w2n wo) 32 b sz` by metis_tac[] >>
  `?u. exec_ext_call ci sg (n2w s.vs_call_ctx.cc_gas:bytes32)
        (1w:bytes32) 0w wi (128w:bytes32) wo (32w:bytes32) T = OK u /\
       stmt_state_rel func cenv cx es u` by
    (irule computed_static_exec_state_rel >>
     simp[Abbr `ci`, computed_precompile_def, venom_call_request_def,
          wordsTheory.dimword_def, wordsTheory.w2w_n2w,
          fcpLib.INDEX_CONV ``dimindex(:160)``] >>
     conj_tac >-
       (rpt strip_tac >>
        `regions_disjoint (w2n wo) 32 b sz` by metis_tac[] >>
        gvs[compileEnvTheory.regions_disjoint_def, listTheory.LENGTH_TAKE_EQ] >>
        decide_tac) >>
     qpat_x_assum `precompile_result _ _ = _` mp_tac >>
     simp[venom_call_request_def, Abbr `sg`, update_var_def, read_memory_def,
          wordsTheory.w2w_n2w, wordsTheory.dimword_def,
          fcpLib.INDEX_CONV ``dimindex(:160)``]) >>
  `stmt_state_rel func cenv cx es sc` by gvs[] >>
  `?u. exec_ext_call ci sg (n2w s.vs_call_ctx.cc_gas:bytes32)
        (1w:bytes32) 0w wi (128w:bytes32) wo (32w:bytes32) T = OK u /\
       wb_frame cenv es sf sg u` by
    (irule computed_static_exec_wb_frame >>
     simp[Abbr `ci`, computed_precompile_def, venom_call_request_def,
          wordsTheory.dimword_def, wordsTheory.w2w_n2w,
          fcpLib.INDEX_CONV ``dimindex(:160)``] >>
     reverse conj_tac >- (simp[not_fresh_at_def] >> decide_tac) >>
     conj_tac >-
       (rpt strip_tac >>
        `regions_disjoint (w2n wo) 32 b sz` by
          (qpat_x_assum `!aid b sz. aid < _ /\ _ ==> _`
             (qspecl_then [`aid`, `b`, `sz`] mp_tac) >>
           gvs[Abbr `sg`, update_var_def]) >>
        gvs[compileEnvTheory.regions_disjoint_def, listTheory.LENGTH_TAKE_EQ] >>
        decide_tac) >>
     qpat_x_assum `precompile_result _ _ = _` mp_tac >>
     simp[venom_call_request_def, Abbr `sg`, update_var_def, read_memory_def,
          wordsTheory.w2w_n2w, wordsTheory.dimword_def,
          fcpLib.INDEX_CONV ``dimindex(:160)``]) >>
  `wb_frame cenv es sf sg sc` by gvs[] >>
  qpat_x_assum `run_inst_seq _ sc = OK t` mp_tac >>
  simp[Once run_inst_seq_def, step_inst_base_def,
       eval_operand_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `sc = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `run_inst_seq _ sc = OK t` mp_tac >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_read1_def,
       AllCaseEqs()] >> strip_tac >>
  gvs[run_inst_seq_def] >>
  conj_tac >- (irule stmt_state_rel_update_var >> simp[]) >>
  `wb_frame cenv es sf s sc` by
    (irule wb_frame_readonly_input >> qexists_tac `sg` >>
     simp[Abbr `sg`, update_var_def] >>
     simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     rpt strip_tac >> IF_CASES_TAC >> gvs[not_fresh_at_def] >> decide_tac) >>
  irule wb_frame_readonly_tail >>
  qexistsl_tac [`sm`, `sc`] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[not_fresh_at_def]

QED

Theorem compile_ecrecover_run[local]:
  compile_ecrecover h v r sig sf = (res,sb) /\
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sf x) ==>
  ?t. run_inst_seq (emitted_insts sf sb) s = OK t /\
    stmt_state_rel func cenv cx es t /\ wb_frame cenv es sf s t /\
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
    (drule_all ecrecover_buffers_shape >> strip_tac >> simp[] >> decide_tac) >>
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
  irule wb_frame_trans >>
  conj_tac >- simp[] >>
  conj_tac >- (qexistsl_tac [`cx`, `func`] >> simp[]) >>
  qexistsl_tac [`es`, `sf`, `t`] >> simp[]
QED

Theorem expr_sim_pre_stack_result:
  expr_sim_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') ==>
  expr_sim_inv cenv cx env es' /\ expr_res_ok res /\
  !v. res = INL v ==> ?tv.
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v
Proof
  strip_tac >> drule_all expr_sim_pre_word_type_result >> strip_tac >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (drule_then irule expr_sim_pre_res_ok >> simp[] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem typed_stack_args_ready:
  expr_sim_pre cenv cx env (Builtin ann bt args) es /\
  EVERY (\e. is_word_type (expr_type e) /\ expr_sim_ok cenv e) args ==>
  typed_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args /\
  wb_args_shape cenv arg_ty args
Proof
  strip_tac >> conj_tac
  >- (pure_rewrite_tac[typed_args_ready_def] >> rpt gen_tac >>
      disch_then strip_assume_tac >>
      rename1 `expr_sim_inv cenv cx env es_arg` >>
      `is_word_type (expr_type e) /\ expr_sim_ok cenv e` by
        (gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
      `expr_sim_pre cenv cx env e es_arg` by
        (drule_all expr_sim_pre_builtin_arg >> simp[]) >>
      simp[] >> rpt conj_tac
      >- metis_tac[expr_sim_ok_def]
      >- metis_tac[well_typed_expr_type_evaluates]
      >- (rpt strip_tac >> drule_all expr_sim_pre_stack_result >> simp[]) >>
      rpt strip_tac >> drule_all expr_sim_pre_stack_result >>
      simp[] >> metis_tac[]) >>
  simp[wb_args_shape_def] >> rpt gen_tac >> strip_tac >>
  `is_word_type (expr_type e)` by
    (gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  `expr_sim_pre cenv cx env e es` by
    (drule expr_sim_pre_builtin_arg >> disch_then irule >>
     gvs[expr_sim_pre_def]) >>
  drule expr_sim_pre_lower_value_word_shape >> disch_then drule >> simp[]
QED

Theorem stack_args_values_typed:
  !args vs cenv cx env es es'.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
       expr_sim_pre cenv cx env e s /\ is_word_type (expr_type e)) /\
    expr_sim_inv cenv cx env es /\ eval_exprs cx args es = (INL vs,es') ==>
    LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                         value_has_type tv v) args vs
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[eval_exprs_nil] >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[] >>
  `expr_sim_pre cenv cx env h es /\ is_word_type (expr_type h)` by
    (first_x_assum irule >> simp[]) >>
  drule_all expr_sim_pre_stack_result >> strip_tac >> gvs[] >>
  Cases_on `rr` >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[listTheory.MEM]
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
      >- (irule expr_sim_pre_builtin_arg >> simp[] >>
          qexistsl_tac [`ann`, `args`, `bt`, `es`] >> simp[]) >>
      gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  gvs[expr_sim_pre_def]
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
  expr_sim_pre cenv cx env (Builtin ann ECRecover args) es ==>
  ann = BaseT AddressT /\ LENGTH args = 4 /\
  EVERY (\e. is_word_type (expr_type e)) args
Proof
  simp[expr_sim_pre_def, well_typed_expr_def] >> strip_tac >>
  drule ecrecover_typing >> simp[] >> strip_tac >>
  `LENGTH args = 4` by simp[] >>
  gvs[LENGTH_EQ_NUM_compute] >> gvs[is_word_type_def]
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
  Cases_on `vh` >> gvs[value_has_type_def] >>
  simp[evaluate_ecrecover_def, typed_val_to_w256_def, PAD_LEFT, PAD_RIGHT] >>
  CASE_TAC >> simp[]
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
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  (!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts func)) /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sm x) /\
  stmt_state_rel func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel func cenv cx es' t /\ wb_frame cenv es sa s0 t /\
  eval_operand h t = SOME wh /\ eval_operand v t = SOME wv /\
  eval_operand r t = SOME wr /\ eval_operand sig t = SOME ws /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV AddressT) ==>
  frag_exec ctx sm sb (\s. s = t)
    (\u. expr_post func cenv cx e es sa sb s0 es'
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
  conj_tac >- (qexistsl_tac [`cx`, `func`] >> simp[]) >>
  qexistsl_tac [`es'`, `sm`, `input`] >>
  gvs[wb_frame_def, lookup_var_def] >> metis_tac[]
QED

Theorem ecrecover_expr_sim[local]:
  expr_sim_pre cenv cx env (Builtin ann ECRecover args) es /\
  EVERY (expr_sim_ok cenv) args ==>
  expr_sim ctx func cenv cx ty (Builtin ann ECRecover args) es
Proof
  strip_tac >> drule ecrecover_pre_types >> strip_tac >>
  `EVERY (\e. is_word_type (expr_type e) /\ expr_sim_ok cenv e) args` by
    gvs[EVERY_MEM] >>
  drule_all typed_stack_args_ready >>
  disch_then (qspecl_then [`func`, `ctx`, `\e. ty`] strip_assume_tac) >>
  rewrite_tac[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `stmt_state_rel func cenv cx es s0`)
  >- (`(\s. s = s0 /\ stmt_state_rel func cenv cx es s) = (\s. F)` by
        (simp[FUN_EQ_THM] >> metis_tac[]) >>
      simp[] >> irule frag_exec_false_pre) >>
  `MAP FDOM es.scopes = MAP FDOM es'.scopes` by
    (qpat_x_assum `bind _ _ es = (res,es')` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  drule_all lower_value_ecrecover_args >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sb` by metis_tac[compile_ecrecover_extends] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `ECRecover <> Len /\ builtin_args_length_ok ECRecover (LENGTH args)` by
    simp[builtin_args_length_ok_def] >>
  drule_all eval_expr_builtin_cases >> strip_tac
  >- (gvs[] >>
      `expr_sim_inv cenv cx env es` by gvs[expr_sim_pre_def] >>
      drule_all lower_typed_args_sim >>
      disch_then (qspec_then `s0` mp_tac) >> simp[wb_args_exit_def] >> strip_tac >>
      irule frag_exec_exit_prefix >> goal_assum (drule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) args vs` by
    (drule_all typed_builtin_stack_args_values >> simp[]) >>
  `well_typed_builtin_app ann ECRecover (MAP expr_type args)` by
    gvs[expr_sim_pre_def, well_typed_expr_def] >>
  drule_all ecrecover_typed_result >>
  disch_then (qspec_then `es'.accounts` strip_assume_tac) >>
  `expr_sim_inv cenv cx env es` by gvs[expr_sim_pre_def] >>
  drule_all lower_typed_args_sim >> disch_then (qspec_then `s0` mp_tac) >>
  simp[wb_args_exit_def] >> disch_then (mp_then Any irule wb_frag_then) >> simp[] >>
  qx_gen_tac `t` >> strip_tac >> gvs[] >>
  gvs[typed_args_post_def] >>
  `(!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts func))` by
    metis_tac[hash_emitted_inst_mem] >>
  `(!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sm x)` by
    (simp[] >> metis_tac[]) >>
  irule ecrecover_expr_tail >>
  simp[expr_type_def, is_word_type_def, vyperValueTheory.evaluate_type_def] >>
  metis_tac[]
QED

Theorem compile_ecrecover_call_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann ECRecover args)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (expr_sim_ok cenv) args` by
    (simp[EVERY_MEM] >> metis_tac[expr_sim_below_mem, expr_ok_def]) >>
  rewrite_tac[expr_vv_ok_def] >> rpt strip_tac >>
  `LENGTH args = 4` by
    (drule ecrecover_pre_types >> simp[] >> metis_tac[]) >>
  irule expr_vv_sim_stack >> simp[] >> conj_tac
  >- (gen_tac >> Cases_on `compile_expr cenv ty (Builtin ann ECRecover args) sa` >>
      drule_all compile_ecrecover_stack >> simp[] >> metis_tac[]) >>
  conj_tac
  >- metis_tac[eval_expr_builtin_value] >>
  irule ecrecover_expr_sim >> simp[] >> metis_tac[]
QED
